import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.EquivFin

/-!
# Counting the cycles of a permutation, and multiplying by a transposition

`cycCount π` is the number of cycles of `π`, fixed points included.  The only fact used about it later
(in the genus inequality for the Gurau degree, row G2-034) is how it moves when `π` is multiplied by a
transposition `swap a b`:

* `cycCount_mul_swap_lt`: if `a` and `b` are in different cycles of `π`, the two cycles merge, so the
  number of cycles drops;
* `cycCount_mul_swap_le`: in any case the number of cycles grows by at most one.

Mathlib has no such statement.

## Main definitions and results

* `Lightlike.GFT.cycCount`: the number of cycles of a permutation.
* `Lightlike.GFT.sameCycle_rel`: an equivalence relation stable under `π` contains `SameCycle π`.
* `Lightlike.GFT.cycCount_mul_swap_lt`, `Lightlike.GFT.cycCount_mul_swap_le`.
-/

open Equiv Equiv.Perm Function

namespace Lightlike.GFT

variable {X : Type*}

/-- The number of cycles of a permutation (fixed points count as cycles of length one). -/
noncomputable def cycCount (π : Perm X) : ℕ := Nat.card (Quotient (SameCycle.setoid π))

/-- A point is in the same cycle as its image. -/
lemma sameCycle_self_apply (π : Perm X) (x : X) : SameCycle π x (π x) := ⟨1, by simp⟩

section
variable [DecidableEq X] (π : Perm X) (a b : X)

lemma mul_swap_apply_left : (π * swap a b) a = π b := by simp [Perm.mul_apply]

lemma mul_swap_apply_right : (π * swap a b) b = π a := by simp [Perm.mul_apply]

lemma mul_swap_apply_of_ne {x : X} (ha : x ≠ a) (hb : x ≠ b) : (π * swap a b) x = π x := by
  simp [Perm.mul_apply, swap_apply_of_ne_of_ne ha hb]

end

variable [Finite X]

/-- An equivalence relation that relates every point to its image under `π` contains the
relation `SameCycle π`. -/
lemma sameCycle_rel {π : Perm X} {R : X → X → Prop} (hR : Equivalence R)
    (h : ∀ x, R x (π x)) {x y : X} (hxy : SameCycle π x y) : R x y := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => simpa using hR.refl x
  | succ n ih =>
    rw [pow_succ']
    exact hR.trans ih (h ((π ^ n) x))

variable [DecidableEq X] (π : Perm X) (a b : X)

/-- If `a`, `b` are in different cycles of `π`, then they are in the same cycle of `π * swap a b`:
the two cycles merge. -/
lemma sameCycle_mul_swap_of_not (h : ¬ SameCycle π a b) : SameCycle (π * swap a b) a b := by
  classical
  have hex : ∃ k, 0 < k ∧ (π ^ k) b = b :=
    ⟨orderOf π, orderOf_pos π, by simp [pow_orderOf_eq_one]⟩
  have hk : 0 < Nat.find hex ∧ (π ^ Nat.find hex) b = b := Nat.find_spec hex
  have hmin : ∀ j, 0 < j → j < Nat.find hex → (π ^ j) b ≠ b :=
    fun j hj hjk hb => Nat.find_min hex hjk ⟨hj, hb⟩
  have key : ∀ j, 1 ≤ j → j ≤ Nat.find hex → ((π * swap a b) ^ j) a = (π ^ j) b := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; simp [Perm.mul_apply]
    | succ j hj ih =>
      intro hjk
      have h1 : (π ^ j) b ≠ b := hmin j hj (by omega)
      have h2 : (π ^ j) b ≠ a := by
        intro e
        apply h
        have := (sameCycle_pow_right (f := π) (x := a) (y := b) (n := j)).1
        rw [e] at this
        exact this (SameCycle.refl _ _)
      rw [pow_succ' (π * swap a b), Perm.mul_apply, ih (by omega), pow_succ' π, Perm.mul_apply,
        Perm.mul_apply, swap_apply_of_ne_of_ne h2 h1]
  exact ⟨((Nat.find hex : ℕ) : ℤ), by rw [zpow_natCast, key _ hk.1 le_rfl, hk.2]⟩

/-- Merging: if `a`, `b` are in different cycles of `π`, then `SameCycle π` is contained in
`SameCycle (π * swap a b)`. -/
lemma sameCycle_le_of_not (h : ¬ SameCycle π a b) {x y : X} (hxy : SameCycle π x y) :
    SameCycle (π * swap a b) x y := by
  have hab := sameCycle_mul_swap_of_not π a b h
  refine sameCycle_rel (SameCycle.equivalence _) ?_ hxy
  intro x
  by_cases hxa : x = a
  · rw [hxa, ← mul_swap_apply_right π a b]
    exact hab.trans (sameCycle_self_apply _ _)
  by_cases hxb : x = b
  · rw [hxb, ← mul_swap_apply_left π a b]
    exact hab.symm.trans (sameCycle_self_apply _ _)
  · rw [← mul_swap_apply_of_ne π a b hxa hxb]
    exact sameCycle_self_apply _ _

/-- **Merging two cycles** lowers the number of cycles. -/
lemma cycCount_mul_swap_lt (h : ¬ SameCycle π a b) : cycCount (π * swap a b) < cycCount π := by
  classical
  have hab := sameCycle_mul_swap_of_not π a b h
  let f : Quotient (SameCycle.setoid π) → Quotient (SameCycle.setoid (π * swap a b)) :=
    Quotient.map id (fun x y hxy => sameCycle_le_of_not π a b h hxy)
  have hs : Surjective f := fun q => Quotient.inductionOn q fun y => ⟨⟦y⟧, rfl⟩
  have hni : ¬ Injective f := fun hi =>
    h (Quotient.exact (hi (show f ⟦a⟧ = f ⟦b⟧ from Quotient.sound hab)))
  have : Fintype X := Fintype.ofFinite X
  have : Fintype (Quotient (SameCycle.setoid π)) := Fintype.ofFinite _
  have : Fintype (Quotient (SameCycle.setoid (π * swap a b))) := Fintype.ofFinite _
  unfold cycCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective f hs hni

/-- **Splitting a cycle** (or merging) changes the number of cycles by at most one upwards. -/
lemma cycCount_mul_swap_le : cycCount (π * swap a b) ≤ cycCount π + 1 := by
  classical
  by_cases hab : SameCycle π a b
  swap
  · exact (cycCount_mul_swap_lt π a b hab).le.trans (Nat.le_succ _)
  set π' := π * swap a b with hπ'
  -- (A) the cycles of `π'` are contained in cycles of `π`
  have hA : ∀ {x y : X}, SameCycle π' x y → SameCycle π x y := by
    intro x y hxy
    refine sameCycle_rel (SameCycle.equivalence π) ?_ hxy
    intro x
    by_cases hxa : x = a
    · rw [hxa, hπ', mul_swap_apply_left]
      exact hab.trans (sameCycle_self_apply _ _)
    by_cases hxb : x = b
    · rw [hxb, hπ', mul_swap_apply_right]
      exact hab.symm.trans (sameCycle_self_apply _ _)
    · rw [hπ', mul_swap_apply_of_ne π a b hxa hxb]
      exact sameCycle_self_apply _ _
  -- (B) a cycle of `π` is a cycle of `π'`, or the union of the two cycles of `a`, `b` in `π'`
  let P : X → Prop := fun x => SameCycle π' x a ∨ SameCycle π' x b
  have hP : ∀ {x y : X}, SameCycle π' x y → P x → P y := by
    intro x y hxy hx
    rcases hx with hx | hx
    · exact Or.inl (hxy.symm.trans hx)
    · exact Or.inr (hxy.symm.trans hx)
  have hB : ∀ {x y : X}, SameCycle π x y → SameCycle π' x y ∨ (P x ∧ P y) := by
    intro x y hxy
    have heq : Equivalence (fun x y : X => SameCycle π' x y ∨ (P x ∧ P y)) := by
      refine ⟨fun x => Or.inl (SameCycle.refl _ _), ?_, ?_⟩
      · rintro x y (h | ⟨h1, h2⟩)
        · exact Or.inl h.symm
        · exact Or.inr ⟨h2, h1⟩
      · rintro x y z (h | ⟨h1, h2⟩) (h' | ⟨h3, h4⟩)
        · exact Or.inl (h.trans h')
        · exact Or.inr ⟨hP h.symm h3, h4⟩
        · exact Or.inr ⟨h1, hP h' h2⟩
        · exact Or.inr ⟨h1, h4⟩
    refine sameCycle_rel heq ?_ hxy
    intro x
    by_cases hxa : x = a
    · right
      refine ⟨Or.inl (hxa ▸ SameCycle.refl _ _), ?_⟩
      rw [hxa, ← mul_swap_apply_right π a b]
      exact Or.inr ((sameCycle_self_apply π' b).symm)
    by_cases hxb : x = b
    · right
      refine ⟨Or.inr (hxb ▸ SameCycle.refl _ _), ?_⟩
      rw [hxb, ← mul_swap_apply_left π a b]
      exact Or.inl ((sameCycle_self_apply π' a).symm)
    · left
      rw [← mul_swap_apply_of_ne π a b hxa hxb]
      exact sameCycle_self_apply _ _
  -- the injection into `Option (cycles of π)`
  let ψ : X → Option (Quotient (SameCycle.setoid π)) :=
    fun x => if SameCycle π' x b then none else some ⟦x⟧
  have hψ : ∀ x y : X, SameCycle π' x y → ψ x = ψ y := by
    intro x y hxy
    by_cases hx : SameCycle π' x b
    · have hy : SameCycle π' y b := hxy.symm.trans hx
      simp [ψ, hx, hy]
    · have hy : ¬ SameCycle π' y b := fun hy => hx (hxy.trans hy)
      simp only [ψ, hx, hy, ite_false]
      exact congrArg some (Quotient.sound (hA hxy))
  let g : Quotient (SameCycle.setoid π') → Option (Quotient (SameCycle.setoid π)) :=
    Quotient.lift ψ hψ
  have hg : Injective g := by
    intro p q
    induction p using Quotient.inductionOn with | _ x => ?_
    induction q using Quotient.inductionOn with | _ y => ?_
    intro hxy
    change ψ x = ψ y at hxy
    by_cases hx : SameCycle π' x b <;> by_cases hy : SameCycle π' y b
    · exact Quotient.sound (hx.trans hy.symm)
    · simp [ψ, hx, hy] at hxy
    · simp [ψ, hx, hy] at hxy
    · simp only [ψ, hx, hy, ite_false, Option.some.injEq] at hxy
      rcases hB (Quotient.exact hxy) with h | ⟨h1, h2⟩
      · exact Quotient.sound h
      · have hxa : SameCycle π' x a := h1.resolve_right hx
        have hya : SameCycle π' y a := h2.resolve_right hy
        exact Quotient.sound (hxa.trans hya.symm)
  unfold cycCount
  calc Nat.card (Quotient (SameCycle.setoid π'))
      ≤ Nat.card (Option (Quotient (SameCycle.setoid π))) := Nat.card_le_card_of_injective g hg
    _ = Nat.card (Quotient (SameCycle.setoid π)) + 1 := Finite.card_option

end Lightlike.GFT
