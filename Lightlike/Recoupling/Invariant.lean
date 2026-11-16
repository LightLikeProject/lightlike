import Lightlike.Recoupling.ThreeJ

/-!
# Invariant tensors of SU(2)

The recoupling identities behind the Pachner moves of 4-dimensional spin foam models are
consequences of one structural fact: a tensor built by contracting invariant tensors is invariant,
and an invariant tensor with two legs is a multiple of the identity (Schur's lemma). This file sets
up that language for tensors given by their components, in the doubled units used throughout the
library (spins `j ∈ ℕ`, projections `m ∈ ℤ` with `|m| ≤ j` and `j - m` even).

**Tensors.**

A tensor with legs `ι` (a finite type) and spins `j : ι → ℕ` is a function `X : (ι → ℤ) → ℝ`
giving the component of each assignment of projections to the legs. Each leg is *incoming*
(`d i = false`, a factor `V_j`) or *outgoing* (`d i = true`, a factor `V_j^*`). The orthonormal
bases are the standard ones (Condon–Shortley phases), in which the spin-`j/2` ladder operators have
real matrix elements

`J₊ |m⟩ = ½ rc j m |m + 2⟩`,  `J₋ |m + 2⟩ = ½ rc j m |m⟩`,  `rc j m = √((j - m)(j + m + 2))`.

On an outgoing leg the dual representation acts by `-Jᵀ`; since `J₊ᵀ = J₋`, this is again an
explicit shift of the components.

**Invariance.**

`IsInv j d X`: `X` is supported on admissible projections, has total weight `0`
(`Σ_in mᵢ - Σ_out mᵢ = 0`), and is annihilated by the total raising and lowering operators. This
is invariance under the Lie algebra `sl₂`, i.e. under SU(2).

## Main results

* `IsInv.reindex`, `IsInv.mul`, `IsInv.contr`: invariance is preserved by renaming legs, by
  tensor products, and by contracting an incoming leg with an outgoing leg of the same spin.
  `IsInv.add`, `IsInv.smul`, `IsInv.sum`: invariant tensors form a vector space.
* `IsInv.flip`: turning one leg around with the invariant bilinear form (`flipAt`) keeps a tensor
  invariant. `IsInv.dual`: reversing all legs does too.
* `isInv_idT`, `isInv_epsT`: the identity `δ_{m₀m₁}` and the bilinear form
  `ε_{m₀m₁} = (-1)^((a - m₀)/2) δ_{m₁,-m₀}` are invariant.
* `schur`: **Schur's lemma**: an invariant tensor with one incoming leg of spin `a` and one
  outgoing leg of spin `b` is `c δ_{ab} δ_{m₀m₁}`.

## References

- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439: §2.9 (intertwiners and Schur's lemma)
  and §5.2 (the invariant subspace of a tensor product).
-/

open Finset

namespace Lightlike.Recoupling

/-! ## Ladder coefficients -/

/-- The ladder coefficient `√((j - m)(j + m + 2))` (doubled units): the spin-`j/2` raising
operator is `J₊ |m⟩ = ½ rc j m |m + 2⟩`, and `J₋ |m + 2⟩ = ½ rc j m |m⟩`. -/
noncomputable def rc (j : ℕ) (m : ℤ) : ℝ :=
  Real.sqrt ((((j : ℤ) - m) * ((j : ℤ) + m + 2) : ℤ) : ℝ)

/-- `rc j (-m - 2) = rc j m`: the ladder coefficients are symmetric about `m = -1`. -/
lemma rc_neg_sub_two (j : ℕ) (m : ℤ) : rc j (-m - 2) = rc j m := by
  unfold rc
  congr 2
  ring

/-- The top of the ladder: `J₊ |j⟩ = 0`. -/
lemma rc_self (j : ℕ) : rc j j = 0 := by
  simp [rc]

/-- The bottom of the ladder: `J₋ |-j⟩ = 0`. -/
lemma rc_neg_self_sub_two (j : ℕ) : rc j (-(j : ℤ) - 2) = 0 := by
  rw [rc_neg_sub_two]
  exact rc_self j

/-- The ladder coefficient is positive strictly inside the ladder. -/
lemma rc_pos {j : ℕ} {m : ℤ} (h₁ : -(j : ℤ) - 2 < m) (h₂ : m < j) : 0 < rc j m := by
  unfold rc
  apply Real.sqrt_pos.mpr
  have : (0 : ℤ) < ((j : ℤ) - m) * ((j : ℤ) + m + 2) := mul_pos (by omega) (by omega)
  exact_mod_cast this

lemma admProj_neg {J : ℕ} {μ : ℤ} : AdmProj J (-μ) ↔ AdmProj J μ := by
  unfold AdmProj
  omega

/-- `(-1)^((x + 2)/2) = -(-1)^(x/2)` for every integer `x`. -/
lemma neg_one_zpow_add_two_div (x : ℤ) :
    (-1 : ℝ) ^ ((x + 2) / 2) = -(-1 : ℝ) ^ (x / 2) := by
  rw [show x + 2 = x + 1 * 2 by ring, Int.add_mul_ediv_right _ _ (by norm_num), zpow_add₀
    (by norm_num), zpow_one, mul_neg_one]

/-! ## Tensors and the action of the ladder operators -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The component at `m` of the raising operator on leg `i` applied to `X`, times `2`: on an
incoming leg `rc (m - 2) X(m - 2)`, on an outgoing leg (dual representation) `-rc m X(m + 2)`. -/
noncomputable def raiseAt (j : ι → ℕ) (d : ι → Bool) (X : (ι → ℤ) → ℝ) (m : ι → ℤ) (i : ι) :
    ℝ :=
  if d i then -(rc (j i) (m i) * X (Function.update m i (m i + 2)))
  else rc (j i) (m i - 2) * X (Function.update m i (m i - 2))

/-- **Invariant tensors.** `X` (legs `ι`, spins `j`, directions `d`, `true` = outgoing) is
supported on admissible projections, has weight `0`, and is annihilated by the total raising and
lowering operators. The lowering operator is the raising operator for the reversed directions,
up to sign, because `J₋ = J₊ᵀ`. -/
structure IsInv (j : ι → ℕ) (d : ι → Bool) (X : (ι → ℤ) → ℝ) : Prop where
  supp : ∀ m, X m ≠ 0 → ∀ i, AdmProj (j i) (m i)
  weight : ∀ m, X m ≠ 0 → ∑ i, (if d i then -m i else m i) = 0
  raise : ∀ m, ∑ i, raiseAt j d X m i = 0
  lower : ∀ m, ∑ i, raiseAt j (fun i => !d i) X m i = 0

variable {j : ι → ℕ} {d : ι → Bool} {X Y : (ι → ℤ) → ℝ}

lemma IsInv.eq_zero (hX : IsInv j d X) {m : ι → ℤ} {i : ι} (h : ¬AdmProj (j i) (m i)) :
    X m = 0 := by
  by_contra h'
  exact h (hX.supp m h' i)

lemma IsInv.congr (hX : IsInv j d X) (h : ∀ m, Y m = X m) : IsInv j d Y := by
  have : Y = X := funext h
  rwa [this]

omit [Fintype ι] in
lemma raiseAt_add (j : ι → ℕ) (d : ι → Bool) (X Y : (ι → ℤ) → ℝ) (m : ι → ℤ) (i : ι) :
    raiseAt j d (fun m => X m + Y m) m i = raiseAt j d X m i + raiseAt j d Y m i := by
  unfold raiseAt
  split_ifs <;> ring

omit [Fintype ι] in
lemma raiseAt_smul (j : ι → ℕ) (d : ι → Bool) (c : ℝ) (X : (ι → ℤ) → ℝ) (m : ι → ℤ) (i : ι) :
    raiseAt j d (fun m => c * X m) m i = c * raiseAt j d X m i := by
  unfold raiseAt
  split_ifs <;> ring

omit [Fintype ι] in
lemma raiseAt_sum {α : Type*} (s : Finset α) (j : ι → ℕ) (d : ι → Bool)
    (X : α → (ι → ℤ) → ℝ) (m : ι → ℤ) (i : ι) :
    raiseAt j d (fun m => ∑ a ∈ s, X a m) m i = ∑ a ∈ s, raiseAt j d (X a) m i := by
  unfold raiseAt
  split_ifs
  · rw [mul_sum, ← sum_neg_distrib]
  · rw [mul_sum]

/-- The zero tensor is invariant. -/
lemma isInv_zero : IsInv j d (fun _ => 0) where
  supp _ h := absurd rfl h
  weight _ h := absurd rfl h
  raise _ := by simp [raiseAt]
  lower _ := by simp [raiseAt]

/-- Sums of invariant tensors are invariant. -/
lemma IsInv.add (hX : IsInv j d X) (hY : IsInv j d Y) : IsInv j d (fun m => X m + Y m) where
  supp m h := by
    by_cases hx : X m = 0
    · exact hY.supp m (by rwa [hx, zero_add] at h)
    · exact hX.supp m hx
  weight m h := by
    by_cases hx : X m = 0
    · exact hY.weight m (by rwa [hx, zero_add] at h)
    · exact hX.weight m hx
  raise m := by simp only [raiseAt_add, sum_add_distrib, hX.raise, hY.raise, add_zero]
  lower m := by simp only [raiseAt_add, sum_add_distrib, hX.lower, hY.lower, add_zero]

/-- Multiples of invariant tensors are invariant. -/
lemma IsInv.smul (hX : IsInv j d X) (c : ℝ) : IsInv j d (fun m => c * X m) where
  supp m h := hX.supp m (right_ne_zero_of_mul h)
  weight m h := hX.weight m (right_ne_zero_of_mul h)
  raise m := by simp only [raiseAt_smul, ← mul_sum, hX.raise, mul_zero]
  lower m := by simp only [raiseAt_smul, ← mul_sum, hX.lower, mul_zero]

/-- Finite sums of invariant tensors are invariant. -/
lemma IsInv.sum {α : Type*} (s : Finset α) {X : α → (ι → ℤ) → ℝ}
    (hX : ∀ a ∈ s, IsInv j d (X a)) : IsInv j d (fun m => ∑ a ∈ s, X a m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isInv_zero : IsInv j d fun _ => 0)
  | insert a s ha ih =>
    simp only [sum_insert ha]
    exact (hX a (mem_insert_self a s)).add (ih fun b hb => hX b (mem_insert_of_mem hb))

/-- Reversing all legs keeps a tensor invariant (the raising and lowering conditions swap). -/
lemma IsInv.dual (hX : IsInv j d X) : IsInv j (fun i => !d i) X where
  supp := hX.supp
  weight m h := by
    have := hX.weight m h
    rw [← neg_eq_zero, ← this, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    cases d i <;> simp
  raise := hX.lower
  lower m := by simpa using hX.raise m

/-! ## Renaming legs, products -/

/-- Renaming the legs along an equivalence keeps a tensor invariant. -/
theorem IsInv.reindex (hX : IsInv j d X) (e : κ ≃ ι) :
    IsInv (j ∘ e) (d ∘ e) (fun m => X (m ∘ e.symm)) := by
  have hup : ∀ (m : κ → ℤ) (k : κ) (v : ℤ),
      Function.update m k v ∘ e.symm = Function.update (m ∘ e.symm) (e k) v := by
    intro m k v
    rw [Function.update_comp_equiv]
    simp
  have hr : ∀ (d' : ι → Bool) (m : κ → ℤ) (k : κ),
      raiseAt (j ∘ e) (d' ∘ e) (fun m => X (m ∘ e.symm)) m k =
        raiseAt j d' X (m ∘ e.symm) (e k) := by
    intro d' m k
    simp only [raiseAt, Function.comp_apply, hup, Equiv.symm_apply_apply]
  refine ⟨fun m h k => ?_, fun m h => ?_, fun m => ?_, fun m => ?_⟩
  · have := hX.supp _ h (e k)
    simpa using this
  · have := hX.weight _ h
    rw [← this, ← Equiv.sum_comp e]
    simp
  · simp only [hr]
    rw [Equiv.sum_comp e (fun i => raiseAt j d X (m ∘ e.symm) i)]
    exact hX.raise _
  · have := hr (fun i => !d i) m
    simp only [Function.comp_def] at this ⊢
    simp only [this]
    rw [Equiv.sum_comp e (fun i => raiseAt j (fun i => !d i) X (fun x => m (e.symm x)) i)]
    exact hX.lower _

variable {j' : κ → ℕ} {d' : κ → Bool} {Z : (κ → ℤ) → ℝ}

/-- The tensor product of two invariant tensors is invariant. -/
theorem IsInv.mul (hX : IsInv j d X) (hZ : IsInv j' d' Z) :
    IsInv (Sum.elim j j') (Sum.elim d d') (fun m => X (m ∘ Sum.inl) * Z (m ∘ Sum.inr)) := by
  have hl : ∀ (m : ι ⊕ κ → ℤ) (i : ι) (v : ℤ),
      Function.update m (Sum.inl i) v ∘ Sum.inl = Function.update (m ∘ Sum.inl) i v :=
    fun m i v => Function.update_comp_eq_of_injective m Sum.inl_injective i v
  have hl' : ∀ (m : ι ⊕ κ → ℤ) (i : ι) (v : ℤ),
      Function.update m (Sum.inl i) v ∘ Sum.inr = m ∘ Sum.inr := fun m i v => by
    funext k; simp
  have hr : ∀ (m : ι ⊕ κ → ℤ) (k : κ) (v : ℤ),
      Function.update m (Sum.inr k) v ∘ Sum.inr = Function.update (m ∘ Sum.inr) k v :=
    fun m k v => Function.update_comp_eq_of_injective m Sum.inr_injective k v
  have hr' : ∀ (m : ι ⊕ κ → ℤ) (k : κ) (v : ℤ),
      Function.update m (Sum.inr k) v ∘ Sum.inl = m ∘ Sum.inl := fun m k v => by
    funext i; simp
  have key : ∀ (e : ι → Bool) (e' : κ → Bool) (m : ι ⊕ κ → ℤ),
      ∑ x, raiseAt (Sum.elim j j') (Sum.elim e e')
        (fun m => X (m ∘ Sum.inl) * Z (m ∘ Sum.inr)) m x =
      (∑ i, raiseAt j e X (m ∘ Sum.inl) i) * Z (m ∘ Sum.inr) +
        X (m ∘ Sum.inl) * ∑ k, raiseAt j' e' Z (m ∘ Sum.inr) k := by
    intro e e' m
    rw [Fintype.sum_sum_type, sum_mul, mul_sum]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      simp only [raiseAt, Sum.elim_inl, hl, hl']
      split_ifs <;> simp <;> ring
    · refine sum_congr rfl fun k _ => ?_
      simp only [raiseAt, Sum.elim_inr, hr, hr']
      split_ifs <;> simp <;> ring
  refine ⟨fun m h x => ?_, fun m h => ?_, fun m => ?_, fun m => ?_⟩
  · rcases x with i | k
    · exact hX.supp _ (left_ne_zero_of_mul h) i
    · exact hZ.supp _ (right_ne_zero_of_mul h) k
  · have h1 := hX.weight _ (left_ne_zero_of_mul h)
    have h2 := hZ.weight _ (right_ne_zero_of_mul h)
    rw [Fintype.sum_sum_type]
    convert congrArg₂ (· + ·) h1 h2 using 1
    · rfl
    · simp
  · rw [key, hX.raise, hZ.raise, zero_mul, mul_zero, add_zero]
  · have : (fun x => !(Sum.elim d d' x)) = Sum.elim (fun i => !d i) (fun k => !d' k) := by
      funext x; cases x <;> rfl
    rw [this, key, hX.lower, hZ.lower, zero_mul, mul_zero, add_zero]

/-! ## Contraction -/

/-- The shift identity behind every contraction: for `F` supported on admissible projections,
`Σ_μ (rc (μ - 2) F(μ - 2, μ) - rc μ F(μ, μ + 2)) = 0`. -/
lemma sum_pair_cancel (a : ℕ) (F : ℤ → ℤ → ℝ)
    (hF : ∀ p q, F p q ≠ 0 → AdmProj a p ∧ AdmProj a q) :
    ∑ μ ∈ Icc (-(a : ℤ)) a, (rc a (μ - 2) * F (μ - 2) μ - rc a μ * F μ (μ + 2)) = 0 := by
  have hz : ∀ p q, ¬(AdmProj a p ∧ AdmProj a q) → F p q = 0 := fun p q h => by
    by_contra h'
    exact h (hF p q h')
  rw [sum_sub_distrib, sub_eq_zero]
  have h1 : ∑ μ ∈ Icc (-(a : ℤ)) a, rc a (μ - 2) * F (μ - 2) μ =
      ∑ ν ∈ Icc (-(a : ℤ) - 2) (a - 2), rc a ν * F ν (ν + 2) := by
    apply sum_nbij' (fun μ => μ - 2) (fun ν => ν + 2)
    · intro x hx; simp only [mem_Icc] at hx ⊢; omega
    · intro x hx; simp only [mem_Icc] at hx ⊢; omega
    · intro x _; ring
    · intro x _; ring
    · intro x _; simp
  have h2 : ∑ ν ∈ Icc (-(a : ℤ) - 2) (a - 2), rc a ν * F ν (ν + 2) =
      ∑ ν ∈ Icc (-(a : ℤ) - 2) a, rc a ν * F ν (ν + 2) := by
    apply sum_subset (Icc_subset_Icc le_rfl (by omega))
    intro x hx hx'
    simp only [mem_Icc] at hx hx'
    rw [hz x (x + 2) (fun h => by unfold AdmProj at h; omega), mul_zero]
  have h3 : ∑ ν ∈ Icc (-(a : ℤ)) a, rc a ν * F ν (ν + 2) =
      ∑ ν ∈ Icc (-(a : ℤ) - 2) a, rc a ν * F ν (ν + 2) := by
    apply sum_subset (Icc_subset_Icc (by omega) le_rfl)
    intro x hx hx'
    simp only [mem_Icc] at hx hx'
    rw [hz x (x + 2) (fun h => by unfold AdmProj at h; omega), mul_zero]
  rw [h1, h2, h3]

/-- **Contraction** of the incoming leg `inr false` with the outgoing leg `inr true`, both of
spin `a`: `(contr a X)(m) = Σ_μ X(m, μ, μ)`. -/
noncomputable def contr (a : ℕ) (X : (ι ⊕ Bool → ℤ) → ℝ) (m : ι → ℤ) : ℝ :=
  ∑ μ ∈ Icc (-(a : ℤ)) a, X (Sum.elim m fun _ => μ)

omit [Fintype ι] in
lemma update_elim_const (m : ι → ℤ) (b : Bool) (μ v : ℤ) :
    Function.update (Sum.elim m fun _ : Bool => μ) (Sum.inr b) v =
      Sum.elim m (fun c => if c = b then v else μ) := by
  rw [Sum.update_elim_inr]
  congr 1
  funext c
  by_cases h : c = b <;> simp [h, Function.update]

/-- The raising (or, with reversed directions, lowering) condition survives a contraction. -/
lemma raise_contr {j : ι ⊕ Bool → ℕ} {e : ι ⊕ Bool → Bool} {X : (ι ⊕ Bool → ℤ) → ℝ}
    (hsupp : ∀ m, X m ≠ 0 → ∀ i, AdmProj (j i) (m i)) (hX : ∀ m, ∑ x, raiseAt j e X m x = 0)
    (hj : j (Sum.inr true) = j (Sum.inr false)) (he : e (Sum.inr true) = !e (Sum.inr false))
    (m : ι → ℤ) :
    ∑ i, raiseAt (j ∘ Sum.inl) (e ∘ Sum.inl) (contr (j (Sum.inr false)) X) m i = 0 := by
  set a := j (Sum.inr false) with ha
  have hterm : ∀ i, raiseAt (j ∘ Sum.inl) (e ∘ Sum.inl) (contr a X) m i =
      ∑ μ ∈ Icc (-(a : ℤ)) a, raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inl i) := by
    intro i
    simp only [raiseAt, contr, Function.comp_apply, Sum.elim_inl, ← Sum.update_elim_inl]
    split_ifs
    · rw [mul_sum, ← sum_neg_distrib]
    · rw [mul_sum]
  simp only [hterm]
  rw [sum_comm]
  have hμ : ∀ μ, ∑ i, raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inl i) =
      -(raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inr false) +
        raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inr true)) := by
    intro μ
    have h := hX (Sum.elim m fun _ => μ)
    rw [Fintype.sum_sum_type, Fintype.sum_bool] at h
    linarith
  simp only [hμ, sum_neg_distrib, neg_eq_zero, sum_add_distrib]
  set F : ℤ → ℤ → ℝ := fun p q => X (Sum.elim m fun c => if c = false then p else q) with hFdef
  have hF : ∀ p q, F p q ≠ 0 → AdmProj a p ∧ AdmProj a q := fun p q h => by
    have h1 := hsupp _ h (Sum.inr false)
    have h2 := hsupp _ h (Sum.inr true)
    simp only [Sum.elim_inr, ite_true] at h1 h2
    rw [hj] at h2
    exact ⟨h1, h2⟩
  rcases hb : e (Sum.inr false) with _ | _
  · -- incoming `inr false`, outgoing `inr true`
    rw [hb] at he
    have := sum_pair_cancel a F hF
    rw [← sum_add_distrib]
    rw [sum_sub_distrib, sub_eq_zero] at this
    have e1 : ∀ μ, raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inr false) = rc a (μ - 2) * F (μ - 2) μ :=
      fun μ => by
        simp only [raiseAt, hb, Bool.false_eq_true, ite_false, Sum.elim_inr, update_elim_const, hFdef]
        rfl
    have e2 : ∀ μ, raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inr true) = -(rc a μ * F μ (μ + 2)) :=
      fun μ => by
        simp only [raiseAt, he, Bool.not_false, ite_true, Sum.elim_inr, update_elim_const, hFdef, hj]
        congr 3
        funext x
        rcases x with _ | (_ | _) <;> simp
    simp only [e1, e2, ← sub_eq_add_neg]
    rw [sum_sub_distrib, this, sub_self]
  · -- outgoing `inr false`, incoming `inr true`
    rw [hb] at he
    set G : ℤ → ℤ → ℝ := fun p q => F q p with hG
    have := sum_pair_cancel a G (fun p q h => (hF q p h).symm)
    rw [← sum_add_distrib]
    rw [sum_sub_distrib, sub_eq_zero] at this
    have e1 : ∀ μ, raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inr false) = -(rc a μ * G μ (μ + 2)) :=
      fun μ => by
        simp only [raiseAt, hb, ite_true, Sum.elim_inr, update_elim_const, hG, hFdef]
        rfl
    have e2 : ∀ μ, raiseAt j e X (Sum.elim m fun _ => μ) (Sum.inr true) = rc a (μ - 2) * G (μ - 2) μ :=
      fun μ => by
        simp only [raiseAt, he, Bool.not_true, Bool.false_eq_true, ite_false, Sum.elim_inr,
          update_elim_const, hG, hFdef, hj]
        congr 2
        funext x
        rcases x with _ | (_ | _) <;> simp
    simp only [e1, e2, neg_add_eq_sub]
    rw [sum_sub_distrib, this, sub_self]

/-- **Contracting an incoming with an outgoing leg** of the same spin keeps a tensor invariant. -/
theorem IsInv.contr {j : ι ⊕ Bool → ℕ} {d : ι ⊕ Bool → Bool} {X : (ι ⊕ Bool → ℤ) → ℝ}
    (hX : IsInv j d X) (hj : j (Sum.inr true) = j (Sum.inr false))
    (hd : d (Sum.inr true) = !d (Sum.inr false)) :
    IsInv (j ∘ Sum.inl) (d ∘ Sum.inl) (contr (j (Sum.inr false)) X) := by
  refine ⟨fun m h i => ?_, fun m h => ?_, raise_contr hX.supp hX.raise hj hd,
    raise_contr (e := fun x => !d x) hX.supp hX.lower hj (by simp [hd])⟩
  · obtain ⟨μ, -, hμ⟩ := exists_ne_zero_of_sum_ne_zero h
    simpa using hX.supp _ hμ (Sum.inl i)
  · obtain ⟨μ, -, hμ⟩ := exists_ne_zero_of_sum_ne_zero h
    have hw := hX.weight _ hμ
    rw [Fintype.sum_sum_type, Fintype.sum_bool, hd] at hw
    have h0 : ∀ b : Bool, ((if (!b) = true then -μ else μ) + (if b = true then -μ else μ)) = 0 := by
      intro b; cases b <;> simp
    simp only [Sum.elim_inl, Sum.elim_inr, h0, add_zero] at hw
    simpa using hw

/-! ## Turning a leg around -/

/-- Turning leg `i` (spin `a`) around with the invariant bilinear form:
`(flipAt a i X)(m) = (-1)^((a + mᵢ)/2) X(m with mᵢ ↦ -mᵢ)`. -/
noncomputable def flipAt (a : ℕ) (i : ι) (X : (ι → ℤ) → ℝ) (m : ι → ℤ) : ℝ :=
  (-1 : ℝ) ^ (((a : ℤ) + m i) / 2) * X (Function.update m i (-m i))

omit [Fintype ι] in
lemma raiseAt_flipAt (e : ι → Bool) (i : ι) (m : ι → ℤ) (k : ι) :
    raiseAt j (Function.update e i (!e i)) (flipAt (j i) i X) m k =
      (-1 : ℝ) ^ (((j i : ℤ) + m i) / 2) * raiseAt j e X (Function.update m i (-m i)) k := by
  by_cases hk : k = i
  · subst hk
    rcases hb : e k with _ | _
    · simp only [raiseAt, Function.update_self, hb, Bool.not_false, ite_true, Bool.false_eq_true,
        ite_false, flipAt, Function.update_idem]
      rw [show (j k : ℤ) + (m k + 2) = (j k + m k) + 2 by ring, neg_one_zpow_add_two_div,
        show -m k - 2 = -(m k + 2) by ring, ← rc_neg_sub_two (j k) (m k),
        show -(m k + 2) = -m k - 2 by ring]
      ring
    · simp only [raiseAt, Function.update_self, hb, Bool.not_true, Bool.false_eq_true, ite_false,
        ite_true, flipAt, Function.update_idem]
      have h1 : ((j k : ℤ) + (m k - 2)) / 2 = (j k + m k) / 2 - 1 := by omega
      rw [h1, zpow_sub₀ (by norm_num), zpow_one, show -(m k - 2) = -m k + 2 by ring,
        show m k - 2 = -(-m k) - 2 by ring, rc_neg_sub_two]
      ring
  · simp only [raiseAt, Function.update_of_ne hk, flipAt, Function.update_comm hk,
      Function.update_of_ne (Ne.symm hk)]
    split_ifs <;> ring

/-- **Turning a leg around keeps a tensor invariant**, with that leg's direction reversed. -/
theorem IsInv.flip (hX : IsInv j d X) (i : ι) :
    IsInv j (Function.update d i (!d i)) (flipAt (j i) i X) := by
  refine ⟨fun m h k => ?_, fun m h => ?_, fun m => ?_, fun m => ?_⟩
  · have := hX.supp _ (right_ne_zero_of_mul h) k
    by_cases hk : k = i
    · subst hk; simpa [admProj_neg] using this
    · simpa [Function.update_of_ne hk] using this
  · have hw := hX.weight _ (right_ne_zero_of_mul h)
    rw [← hw]
    refine sum_congr rfl fun k _ => ?_
    by_cases hk : k = i
    · subst hk; cases d k <;> simp
    · simp [Function.update_of_ne hk]
  · simp only [raiseAt_flipAt, ← mul_sum, hX.raise, mul_zero]
  · have : (fun k => !Function.update d i (!d i) k) =
        Function.update (fun k => !d k) i (!(fun k => !d k) i) := by
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    rw [this]
    simp only [raiseAt_flipAt, ← mul_sum, hX.lower, mul_zero]

/-! ## The identity and the invariant bilinear form -/

/-- `rc v` vanishes where the admissibility of `v` and of `v + 2` differ. -/
lemma rc_mul_adm (a : ℕ) (v : ℤ) :
    rc a v * (if AdmProj a v then 1 else 0) = rc a v * (if AdmProj a (v + 2) then 1 else 0) := by
  by_cases h1 : v = a
  · subst h1; rw [rc_self]; ring
  by_cases h2 : v = -(a : ℤ) - 2
  · subst h2; rw [rc_neg_self_sub_two]; ring
  congr 1
  unfold AdmProj
  by_cases h : -(a : ℤ) ≤ v ∧ v ≤ a ∧ ((a : ℤ) - v) % 2 = 0
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- The identity tensor `δ_{m₀ m₁}` of spin `a` (one incoming, one outgoing leg). -/
noncomputable def idT (a : ℕ) (m : Fin 2 → ℤ) : ℝ := if AdmProj a (m 0) ∧ m 1 = m 0 then 1 else 0

/-- The invariant bilinear form `ε_{m₀ m₁} = (-1)^((a - m₀)/2) δ_{m₁, -m₀}` of spin `a` (two
incoming legs). -/
noncomputable def epsT (a : ℕ) (m : Fin 2 → ℤ) : ℝ :=
  if AdmProj a (m 0) ∧ m 1 = -m 0 then (-1 : ℝ) ^ (((a : ℤ) - m 0) / 2) else 0

lemma upd0 (m : Fin 2 → ℤ) (v : ℤ) : Function.update m 0 v 0 = v ∧ Function.update m 0 v 1 = m 1 :=
  ⟨by simp, by simp⟩

lemma upd1 (m : Fin 2 → ℤ) (v : ℤ) : Function.update m 1 v 0 = m 0 ∧ Function.update m 1 v 1 = v :=
  ⟨by simp, by simp⟩

/-- The identity is invariant. -/
theorem isInv_idT (a : ℕ) : IsInv ![a, a] ![false, true] (idT a) := by
  refine ⟨fun m h i => ?_, fun m h => ?_, fun m => ?_, fun m => ?_⟩
  · unfold idT at h
    split_ifs at h with h'
    · fin_cases i
      · exact h'.1
      · simpa [h'.2] using h'.1
    · exact absurd rfl h
  · unfold idT at h
    split_ifs at h with h'
    · simp [Fin.sum_univ_two, h'.2]
    · exact absurd rfl h
  · simp only [Fin.sum_univ_two, raiseAt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Bool.false_eq_true, ite_false, ite_true, idT, (upd0 m _).1, (upd0 m _).2,
      (upd1 m _).1, (upd1 m _).2]
    generalize m 0 = p
    generalize m 1 = q
    by_cases h : q = p - 2
    · subst h
      have k := rc_mul_adm a (p - 2)
      rw [sub_add_cancel] at k
      simp only [and_true, sub_add_cancel]
      rw [k]
      ring
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right (fun h' => h (by omega))]
      ring
  · simp only [Fin.sum_univ_two, raiseAt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      idT, (upd0 m _).1, (upd0 m _).2, (upd1 m _).1, (upd1 m _).2]
    generalize m 0 = p
    generalize m 1 = q
    by_cases h : q = p + 2
    · subst h
      have k := rc_mul_adm a p
      simp only [and_true, add_sub_cancel_right]
      rw [k]
      ring
    · rw [ite_eq_right (fun h' => h h'.2), ite_eq_right (fun h' => h (by omega))]
      ring

lemma update_vec0 (x y v : ℤ) : Function.update ![x, y] 0 v = ![v, y] := by
  funext i; fin_cases i <;> simp

lemma update_vec1 (x y v : ℤ) : Function.update ![x, y] 1 v = ![x, v] := by
  funext i; fin_cases i <;> simp

lemma fin2_eq (m : Fin 2 → ℤ) : m = ![m 0, m 1] := by
  funext i; fin_cases i <;> rfl

/-! ## Schur's lemma -/

/-- **Schur's lemma.** An invariant tensor with an incoming leg of spin `a` and an outgoing leg of
spin `b` is a multiple of the identity if `a = b`, and zero otherwise:
`X(m) = X(a, a) δ_{ab} δ_{m₀ m₁}` (on admissible projections). -/
theorem schur {a b : ℕ} {X : (Fin 2 → ℤ) → ℝ} (hX : IsInv ![a, b] ![false, true] X)
    (m : Fin 2 → ℤ) : X m = if a = b then X ![(a : ℤ), a] * idT a m else 0 := by
  obtain ⟨p, q, rfl⟩ : ∃ p q, m = ![p, q] := ⟨m 0, m 1, fin2_eq m⟩
  set f : ℤ → ℝ := fun μ => X ![μ, μ] with hf
  have hdiag : ∀ p q : ℤ, q ≠ p → X ![p, q] = 0 := fun p q hm => by
    by_contra h
    have := hX.weight _ h
    simp [Fin.sum_univ_two] at this
    omega
  have hsupp : ∀ μ, f μ ≠ 0 → AdmProj a μ ∧ AdmProj b μ := fun μ h =>
    ⟨by simpa using hX.supp _ h 0, by simpa using hX.supp _ h 1⟩
  have hrec : ∀ μ, rc a μ * f μ = rc b μ * f (μ + 2) := fun μ => by
    have := hX.raise ![μ + 2, μ]
    simp only [Fin.sum_univ_two, raiseAt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Bool.false_eq_true, ite_false, ite_true, update_vec0, update_vec1,
      add_sub_cancel_right] at this
    simp only [hf]
    linarith
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left rfl]
    have hconst : ∀ n : ℕ, n ≤ a → f ((a : ℤ) - 2 * n) = f a := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have h1 := hrec ((a : ℤ) - 2 * (n + 1 : ℕ))
        have hpos : 0 < rc a ((a : ℤ) - 2 * (n + 1 : ℕ)) := rc_pos (by push_cast; omega)
          (by push_cast; omega)
        rw [show (a : ℤ) - 2 * (n + 1 : ℕ) + 2 = a - 2 * n by push_cast; ring,
          ih (by omega)] at h1
        exact mul_left_cancel₀ hpos.ne' h1
    by_cases hm : q = p
    · subst hm
      by_cases ha : AdmProj a q
      · obtain ⟨n, hn, hmn⟩ : ∃ n : ℕ, n ≤ a ∧ q = a - 2 * n :=
          ⟨((a - q) / 2).toNat, by unfold AdmProj at ha; omega, by unfold AdmProj at ha; omega⟩
        have e : X ![q, q] = f q := rfl
        rw [e, hmn, hconst n hn]
        simp [idT, ← hmn, ha, hf]
      · have h0 : X ![q, q] = 0 := hX.eq_zero (i := 0) (by simpa using ha)
        simp [h0, idT, ha]
    · rw [hdiag p q hm]
      simp [idT, hm]
  · rw [ite_eq_right hab]
    have hf0 : ∀ μ, f μ = 0 := by
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · have hup : ∀ n : ℕ, f (-(a : ℤ) + 2 * n) = 0 := by
          intro n
          induction n with
          | zero =>
            have h1 := hrec (-(a : ℤ) - 2)
            rw [rc_neg_self_sub_two, zero_mul, show -(a : ℤ) - 2 + 2 = -a by ring] at h1
            have hpos : 0 < rc b (-(a : ℤ) - 2) := rc_pos (by omega) (by omega)
            simpa using (mul_eq_zero.mp h1.symm).resolve_left hpos.ne'
          | succ n ih =>
            by_cases hb : -(a : ℤ) + 2 * n < b
            · have h1 := hrec (-(a : ℤ) + 2 * n)
              rw [ih, mul_zero] at h1
              have hpos : 0 < rc b (-(a : ℤ) + 2 * n) := rc_pos (by omega) hb
              have := (mul_eq_zero.mp h1.symm).resolve_left hpos.ne'
              rw [show -(a : ℤ) + 2 * ((n + 1 : ℕ) : ℤ) = -a + 2 * n + 2 by push_cast; ring]
              exact this
            · by_contra h
              have := (hsupp _ h).2
              unfold AdmProj at this
              push_cast at this
              omega
        intro μ
        by_contra h
        have ha := (hsupp μ h).1
        obtain ⟨n, hn⟩ : ∃ n : ℕ, μ = -(a : ℤ) + 2 * n :=
          ⟨((μ + a) / 2).toNat, by unfold AdmProj at ha; omega⟩
        exact h (hn ▸ hup n)
      · have hdown : ∀ n : ℕ, f ((b : ℤ) - 2 * n) = 0 := by
          intro n
          induction n with
          | zero =>
            have h1 := hrec (b : ℤ)
            rw [rc_self, zero_mul] at h1
            have hpos : 0 < rc a (b : ℤ) := rc_pos (by omega) (by omega)
            simpa using (mul_eq_zero.mp h1).resolve_left hpos.ne'
          | succ n ih =>
            by_cases ha : -(a : ℤ) - 2 < (b : ℤ) - 2 * n - 2
            · have h1 := hrec ((b : ℤ) - 2 * n - 2)
              rw [show (b : ℤ) - 2 * n - 2 + 2 = b - 2 * n by ring, ih, mul_zero] at h1
              have hpos : 0 < rc a ((b : ℤ) - 2 * n - 2) := rc_pos ha (by omega)
              have := (mul_eq_zero.mp h1).resolve_left hpos.ne'
              rw [show (b : ℤ) - 2 * ((n + 1 : ℕ) : ℤ) = b - 2 * n - 2 by push_cast; ring]
              exact this
            · by_contra h
              have := (hsupp _ h).1
              unfold AdmProj at this
              push_cast at this
              omega
        intro μ
        by_contra h
        have hb := (hsupp μ h).2
        obtain ⟨n, hn⟩ : ∃ n : ℕ, μ = (b : ℤ) - 2 * n :=
          ⟨((b - μ) / 2).toNat, by unfold AdmProj at hb; omega⟩
        exact h (hn ▸ hdown n)
    by_cases hm : q = p
    · subst hm; exact hf0 q
    · exact hdiag p q hm

end Lightlike.Recoupling
