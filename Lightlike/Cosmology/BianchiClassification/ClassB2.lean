import Lightlike.Cosmology.BianchiClassification.ClassB1

/-!
# Class B, part 2: the cases with one or two vanishing eigenvalues

`BNormalisable l a` says that the diagonal bracket `(diag l, a)` is isomorphic to one of the
class B normal forms `(diag t, (0, 0, α))`, `ClassBNormal t α`.  We treat the data with
`l ∈ {0, ±1}³`, `l_i a_i = 0` and exactly one or two nonzero `l_i` (the case `l = 0` is dealt with
in the next file).

## Main results

* `Lightlike.Cosmology.BianchiClassification.BNormalisable`
* `Lightlike.Cosmology.BianchiClassification.bnormalisable_one_zero`: `l = (±1, ±1, 0)`, `a = (0, 0, α)`.
* `Lightlike.Cosmology.BianchiClassification.bnormalisable_two_zero`: `l = (±1, 0, 0)`, `a₀ = 0`.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Cosmology.BianchiClassification

open Matrix

/-- `(diag l, a)` is isomorphic to a class B normal form. -/
def BNormalisable (l : Fin 3 → ℝ) (a : V3) : Prop :=
  ∃ t α, ClassBNormal t α ∧ BracketIso (diagonal l) a (diagonal t) ![0, 0, α]

theorem BNormalisable.of_iso {l m : Fin 3 → ℝ} {a b : V3}
    (h : BracketIso (diagonal l) a (diagonal m) b) (h' : BNormalisable m b) : BNormalisable l a := by
  obtain ⟨t, α, hc, hi⟩ := h'
  exact ⟨t, α, hc, h.trans hi⟩

theorem BNormalisable.of_iso' {l m l' : Fin 3 → ℝ} {a b a' : V3}
    (h : BracketIso (diagonal l) a (diagonal m) b) (hm : m = l') (hb : b = a')
    (h' : BNormalisable l' a') : BNormalisable l a := by
  subst hm hb
  exact BNormalisable.of_iso h h'

/-- `l = (1, ±1, 0)` and `a = (0, 0, α)` with `α > 0`. -/
theorem bnormalisable_one_zero_pos (s : ℝ) (hs : s = 1 ∨ s = -1) (α : ℝ) (hα : 0 < α) :
    BNormalisable ![1, s, 0] ![0, 0, α] := by
  rcases hs with rfl | rfl
  · exact ⟨![1, 1, 0], α, Or.inr (Or.inr (Or.inr ⟨rfl, hα⟩)), BracketIso.refl _ _⟩
  · exact ⟨![1, -1, 0], α, Or.inr (Or.inr (Or.inl ⟨rfl, hα⟩)), BracketIso.refl _ _⟩

/-- `l = (1, ±1, 0)` and `a = (0, 0, α)` with `α ≠ 0`. -/
theorem bnormalisable_one_zero_ne (s : ℝ) (hs : s = 1 ∨ s = -1) (α : ℝ) (hα : α ≠ 0) :
    BNormalisable ![1, s, 0] ![0, 0, α] := by
  rcases hα.lt_or_gt with h | h
  · have e : (![(![0, 0, α] : V3) 0, -(![0, 0, α] : V3) 1, -(![0, 0, α] : V3) 2] : V3) =
        ![0, 0, -α] := by
      ext i; fin_cases i <;> simp
    exact BNormalisable.of_iso' (bracketIso_flip12 ![1, s, 0] ![0, 0, α]) rfl e
      (bnormalisable_one_zero_pos s hs (-α) (by linarith))
  · exact bnormalisable_one_zero_pos s hs α h

/-- `l = (±1, ±1, 0)` and `a = (0, 0, α)`, `α ≠ 0`: one vanishing eigenvalue. -/
theorem bnormalisable_one_zero (s₀ s₁ : ℝ) (h₀ : s₀ = 1 ∨ s₀ = -1) (h₁ : s₁ = 1 ∨ s₁ = -1)
    (α : ℝ) (hα : α ≠ 0) : BNormalisable ![s₀, s₁, 0] ![0, 0, α] := by
  rcases h₀ with rfl | rfl
  · exact bnormalisable_one_zero_ne _ h₁ α hα
  · rcases h₁ with rfl | rfl
    · have k := bnormalisable_one_zero_ne (-1) (Or.inr rfl) (-α) (neg_ne_zero.mpr hα)
      have e1 : (![(![-1, 1, 0] : Fin 3 → ℝ) 1, (![-1, 1, 0] : Fin 3 → ℝ) 0,
          (![-1, 1, 0] : Fin 3 → ℝ) 2] : Fin 3 → ℝ) = ![1, -1, 0] := by
        ext i; fin_cases i <;> simp
      have e2 : (![-(![0, 0, α] : V3) 1, -(![0, 0, α] : V3) 0, -(![0, 0, α] : V3) 2] : V3) =
          ![0, 0, -α] := by
        ext i; fin_cases i <;> simp
      have h := bracketIso_swap01 ![-1, 1, 0] ![0, 0, α]
      exact BNormalisable.of_iso' h e1 e2 k
    · have k := bnormalisable_one_zero_ne 1 (Or.inl rfl) (-α) (neg_ne_zero.mpr hα)
      have e1 : (fun i => -(![-1, -1, 0] : Fin 3 → ℝ) i) = ![1, 1, 0] := by
        ext i; fin_cases i <;> simp
      have e2 : (fun i => -(![0, 0, α] : V3) i) = ![0, 0, -α] := by
        ext i; fin_cases i <;> simp
      have h := bracketIso_neg ![-1, -1, 0] ![0, 0, α]
      exact BNormalisable.of_iso' h e1 e2 k

/-- `l = (1, 0, 0)` and `a = (0, a₁, a₂) ≠ 0`: Bianchi type IV. -/
theorem bnormalisable_two_zero_pos (a : V3) (h0 : a 0 = 0) (hne : a 1 ≠ 0 ∨ a 2 ≠ 0) :
    BNormalisable ![1, 0, 0] a := by
  have hpos : 0 < a 1 ^ 2 + a 2 ^ 2 := by
    rcases hne with h | h
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (a 2)]
    · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg (a 1)]
  have hr : 0 < Real.sqrt (a 1 ^ 2 + a 2 ^ 2) := Real.sqrt_pos.mpr hpos
  set r := Real.sqrt (a 1 ^ 2 + a 2 ^ 2) with hrdef
  have hsc := bracketIso_diagonal_scale ![1, 0, 0] ![0, 0, r] ![r, 1, r]
    (by intro i; fin_cases i <;> simp [hr.ne'])
  have e1 : (fun i => (![1, 0, 0] : Fin 3 → ℝ) i * (![r, 1, r] : Fin 3 → ℝ) i ^ 2 /
      ((![r, 1, r] : Fin 3 → ℝ) 0 * (![r, 1, r] : Fin 3 → ℝ) 1 * (![r, 1, r] : Fin 3 → ℝ) 2)) =
      ![1, 0, 0] := by
    ext i; fin_cases i
    · simp; field_simp
    · simp
    · simp
  have e2 : (fun i => (![0, 0, r] : V3) i / (![r, 1, r] : Fin 3 → ℝ) i) = ![0, 0, 1] := by
    ext i; fin_cases i
    · simp
    · simp
    · simp [hr.ne']
  rw [e1, e2] at hsc
  exact BNormalisable.of_iso (bracketIso_rotate a h0 hne)
    ⟨![1, 0, 0], 1, Or.inr (Or.inl ⟨rfl, rfl⟩), hsc⟩

/-- `l = (±1, 0, 0)` and `a = (0, a₁, a₂) ≠ 0`. -/
theorem bnormalisable_two_zero (s : ℝ) (hs : s = 1 ∨ s = -1) (a : V3) (h0 : a 0 = 0)
    (hne : a 1 ≠ 0 ∨ a 2 ≠ 0) : BNormalisable ![s, 0, 0] a := by
  rcases hs with rfl | rfl
  · exact bnormalisable_two_zero_pos a h0 hne
  · refine BNormalisable.of_iso' (bracketIso_neg ![-1, 0, 0] a) ?_ rfl
      (bnormalisable_two_zero_pos (fun i => -a i) (by simp [h0]) (by simpa using hne))
    ext i; fin_cases i <;> simp

end Lightlike.Cosmology.BianchiClassification

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.BNormalisable := _root_.Lightlike.Cosmology.BianchiClassification.BNormalisable
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.BNormalisable.of_iso := _root_.Lightlike.Cosmology.BianchiClassification.BNormalisable.of_iso
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.BNormalisable.of_iso' := _root_.Lightlike.Cosmology.BianchiClassification.BNormalisable.of_iso'
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_one_zero := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_one_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_one_zero_ne := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_one_zero_ne
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_one_zero_pos := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_one_zero_pos
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_two_zero := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_two_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bnormalisable_two_zero_pos := _root_.Lightlike.Cosmology.BianchiClassification.bnormalisable_two_zero_pos
