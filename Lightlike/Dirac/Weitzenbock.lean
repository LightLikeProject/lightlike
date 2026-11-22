import Mathlib

/-!
# The algebraic heart of the Lichnerowicz formula

In the Weitzenböck computation of `D²` the curvature enters through the Clifford element
`∑ᵢⱼₖₗ Rᵢⱼₖₗ γᵢγⱼγₖγₗ`.  This file proves, for generators `γᵢ` of a Clifford algebra with
`γᵢγⱼ + γⱼγᵢ = -2δᵢⱼ` and an array `R` with the algebraic symmetries of a Riemann tensor
(antisymmetry in each pair, pair symmetry, first Bianchi identity), that

`∑ᵢⱼₖₗ Rᵢⱼₖₗ γᵢγⱼγₖγₗ = -2 (∑ᵢⱼ Rᵢⱼᵢⱼ) · 1`.

With the scalar curvature `∑ᵢⱼ Rᵢⱼᵢⱼ` this is the source of the term `R/4` in `D² = ∇*∇ + R/4`
(the factor: `½ ∑_{i<j} γᵢγⱼ Rˢ(eᵢ,eⱼ)` with `Rˢ(eᵢ,eⱼ) = ¼ ∑ₖₗ Rᵢⱼₖₗ γₖγₗ`, i.e.
`⅛ ∑ Rᵢⱼₖₗ γᵢγⱼγₖγₗ·½·2`, is worked out in a later file).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {A : Type*} [Ring A] [Algebra ℝ A]

/-- Relabelling a triple sum cyclically. -/
lemma sum_rot3 {M : Type*} [AddCommMonoid M] (f : Fin n → Fin n → Fin n → M) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ j, ∑ k, f j k i := by
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

/-- Moving a generator past a product of two: the cyclic rotation `γⱼγₖγᵢ`. -/
lemma rot_a (g : Fin n → A)
    (hg : ∀ j k, g j * g k + g k * g j = (if j = k then (-2 : ℝ) else 0) • (1 : A)) (i j k : Fin n) :
    g j * g k * g i = g i * g j * g k + (if j = i then (2 : ℝ) else 0) • g k
      - (if k = i then (2 : ℝ) else 0) • g j := by
  have e1 : g k * g i = (if k = i then (-2 : ℝ) else 0) • (1 : A) - g i * g k :=
    eq_sub_of_add_eq' (by rw [add_comm]; exact hg k i)
  have e2 : g j * g i = (if j = i then (-2 : ℝ) else 0) • (1 : A) - g i * g j :=
    eq_sub_of_add_eq' (by rw [add_comm]; exact hg j i)
  calc g j * g k * g i = g j * (g k * g i) := mul_assoc _ _ _
    _ = g j * ((if k = i then (-2 : ℝ) else 0) • (1 : A) - g i * g k) := by rw [e1]
    _ = (if k = i then (-2 : ℝ) else 0) • g j - (g j * g i) * g k := by
        rw [mul_sub, mul_smul_comm, mul_one, mul_assoc]
    _ = (if k = i then (-2 : ℝ) else 0) • g j
          - ((if j = i then (-2 : ℝ) else 0) • (1 : A) - g i * g j) * g k := by rw [e2]
    _ = _ := by
        rw [sub_mul, smul_mul_assoc, one_mul, mul_assoc]
        split_ifs <;> simp [two_smul] <;> abel

/-- The other cyclic rotation `γₖγᵢγⱼ`. -/
lemma rot_b (g : Fin n → A)
    (hg : ∀ j k, g j * g k + g k * g j = (if j = k then (-2 : ℝ) else 0) • (1 : A)) (i j k : Fin n) :
    g k * g i * g j = g i * g j * g k - (if k = i then (2 : ℝ) else 0) • g j
      + (if k = j then (2 : ℝ) else 0) • g i := by
  have h := rot_a g hg i j k
  have e1 : g j * g i = (if j = i then (-2 : ℝ) else 0) • (1 : A) - g i * g j :=
    eq_sub_of_add_eq' (by rw [add_comm]; exact hg j i)
  have e2 : g k * g j = (if k = j then (-2 : ℝ) else 0) • (1 : A) - g j * g k :=
    eq_sub_of_add_eq' (by rw [add_comm]; exact hg k j)
  calc g k * g i * g j = g k * (g i * g j) := mul_assoc _ _ _
    _ = g k * ((if j = i then (-2 : ℝ) else 0) • (1 : A) - g j * g i) := by
        rw [show g i * g j = (if j = i then (-2 : ℝ) else 0) • (1 : A) - g j * g i from
          eq_sub_of_add_eq (by rw [add_comm]; exact hg j i)]
    _ = (if j = i then (-2 : ℝ) else 0) • g k - (g k * g j) * g i := by
        rw [mul_sub, mul_smul_comm, mul_one, mul_assoc]
    _ = (if j = i then (-2 : ℝ) else 0) • g k
          - ((if k = j then (-2 : ℝ) else 0) • (1 : A) - g j * g k) * g i := by rw [e2]
    _ = (if j = i then (-2 : ℝ) else 0) • g k
          - (if k = j then (-2 : ℝ) else 0) • g i + g j * g k * g i := by
        rw [sub_mul, smul_mul_assoc, one_mul]; abel
    _ = _ := by
        rw [h]
        split_ifs <;> simp [two_smul] <;> abel

/-- The Ricci-type sum `∑ᵢₖₗ Rᵢₖᵢₗ γₖγₗ`. -/
def ricciClifford (g : Fin n → A) (R : Fin n → Fin n → Fin n → Fin n → ℝ) : A :=
  ∑ i, ∑ k, ∑ l, R i k i l • (g k * g l)

section collapse

variable (g : Fin n → A) (R : Fin n → Fin n → Fin n → Fin n → ℝ)

lemma collapse_F1 : ∑ i, ∑ j, ∑ k, ∑ l,
    R j k i l • (((if j = i then (2 : ℝ) else 0) • g k) * g l) = (2 : ℝ) • ricciClifford g R := by
  have h : ∀ i j, ∑ k, ∑ l, R j k i l • (((if j = i then (2 : ℝ) else 0) • g k) * g l) =
      if j = i then ∑ k, ∑ l, (2 : ℝ) • (R i k i l • (g k * g l)) else 0 := by
    intro i j
    by_cases h : j = i
    · subst h
      simp only [ite_true, smul_mul_assoc]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => smul_comm _ _ _
    · simp [h]
  simp only [h]
  simp [ricciClifford, Finset.smul_sum]

lemma collapse_F2 : ∑ i, ∑ j, ∑ k, ∑ l,
    R j k i l • (((if k = i then (2 : ℝ) else 0) • g j) * g l) = ∑ i, ∑ j, ∑ k, ∑ l,
    (if k = i then (2 : ℝ) • (R j i i l • (g j * g l)) else 0) := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h : k = i
  · subst h
    simp only [ite_true, smul_mul_assoc]
    exact smul_comm _ _ _
  · simp [h]

end collapse

end Lightlike.Dirac
