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

lemma collapse_F2 (hR1 : ∀ i j k l, R i j k l = - R j i k l) : ∑ i, ∑ j, ∑ k, ∑ l,
    R j k i l • (((if k = i then (2 : ℝ) else 0) • g j) * g l) =
      (-2 : ℝ) • ricciClifford g R := by
  have h : ∀ i j, ∑ k, ∑ l, R j k i l • (((if k = i then (2 : ℝ) else 0) • g j) * g l) =
      ∑ l, (-2 : ℝ) • (R i j i l • (g j * g l)) := by
    intro i j
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun l _ => ?_
      simp only [ite_true, smul_mul_assoc, smul_smul]
      rw [hR1 j i i l]
      congr 1
      ring
    · intro k _ hk
      simp [hk]
    · simp
  simp only [h]
  simp [ricciClifford, Finset.smul_sum]

lemma collapse_F3 (hR1 : ∀ i j k l, R i j k l = - R j i k l) : ∑ i, ∑ j, ∑ k, ∑ l,
    R k i j l • (((if k = i then (2 : ℝ) else 0) • g j) * g l) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.sum_eq_single i]
  · have : R i i j = fun _ => 0 := by
      funext l
      have := hR1 i i j l
      linarith
    simp [this]
  · intro k _ hk
    simp [hk]
  · simp

lemma collapse_F4 : ∑ i, ∑ j, ∑ k, ∑ l,
    R k i j l • (((if k = j then (2 : ℝ) else 0) • g i) * g l) = (2 : ℝ) • ricciClifford g R := by
  have h : ∀ i j, ∑ k, ∑ l, R k i j l • (((if k = j then (2 : ℝ) else 0) • g i) * g l) =
      ∑ l, (2 : ℝ) • (R j i j l • (g i * g l)) := by
    intro i j
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun l _ => ?_
      simp only [ite_true, smul_mul_assoc]
      exact smul_comm _ _ _
    · intro k _ hk
      simp [hk]
    · simp
  simp only [h]
  rw [Finset.sum_comm]
  simp [ricciClifford, Finset.smul_sum]

/-- The Ricci-type Clifford sum is minus the scalar-curvature sum, for pair-symmetric `R`. -/
lemma ricciClifford_eq (hg : ∀ j k, g j * g k + g k * g j = (if j = k then (-2 : ℝ) else 0) • (1 : A))
    (hP : ∀ i j k l, R i j k l = R k l i j) :
    ricciClifford g R = (-(∑ i, ∑ k, R i k i k)) • (1 : A) := by
  set c : Fin n → Fin n → ℝ := fun k l => ∑ i, R i k i l with hc
  have hQ : ricciClifford g R = ∑ k, ∑ l, c k l • (g k * g l) := by
    unfold ricciClifford
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    simp [hc, Finset.sum_smul]
  have hcs : ∀ k l, c k l = c l k := fun k l =>
    Finset.sum_congr rfl fun i _ => hP i k i l
  have hQ' : ricciClifford g R = ∑ k, ∑ l, c k l • (g l * g k) := by
    rw [hQ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hcs]
  have h2 : ricciClifford g R + ricciClifford g R =
      ∑ k, ∑ l, c k l • ((if k = l then (-2 : ℝ) else 0) • (1 : A)) := by
    have e : ricciClifford g R + ricciClifford g R =
        ∑ k, ∑ l, c k l • (g k * g l) + ∑ k, ∑ l, c k l • (g l * g k) := by
      rw [← hQ, ← hQ']
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← smul_add, hg]
  have h3 : ∑ k, ∑ l, c k l • ((if k = l then (-2 : ℝ) else 0) • (1 : A)) =
      (-2 * ∑ k, c k k) • (1 : A) := by
    have : ∀ k, ∑ l, c k l • ((if k = l then (-2 : ℝ) else 0) • (1 : A)) =
        (-2 * c k k) • (1 : A) := by
      intro k
      rw [Finset.sum_eq_single k]
      · simp [smul_smul, mul_comm]
      · intro l _ hl
        simp [Ne.symm hl]
      · simp
    simp only [this, Finset.mul_sum, Finset.sum_smul]
  have hsum : ∑ i, ∑ k, R i k i k = ∑ k, c k k := by
    simp only [hc]
    rw [Finset.sum_comm]
  have : ricciClifford g R = (1 / 2 : ℝ) • (ricciClifford g R + ricciClifford g R) := by module
  rw [this, h2, h3, hsum, smul_smul]
  congr 1
  ring

/-- **The Clifford sum of a curvature array.**  For generators with `γᵢγⱼ+γⱼγᵢ = -2δᵢⱼ` and `R`
with the symmetries of a Riemann tensor, `∑ Rᵢⱼₖₗ γᵢγⱼγₖγₗ = -2 (∑ Rᵢⱼᵢⱼ) · 1`. -/
theorem riemann_clifford_sum
    (hg : ∀ j k, g j * g k + g k * g j = (if j = k then (-2 : ℝ) else 0) • (1 : A))
    (hR1 : ∀ i j k l, R i j k l = - R j i k l)
    (hP : ∀ i j k l, R i j k l = R k l i j)
    (hB : ∀ i j k l, R i j k l + R j k i l + R k i j l = 0) :
    ∑ i, ∑ j, ∑ k, ∑ l, R i j k l • (g i * g j * g k * g l) =
      (-2 * ∑ i, ∑ k, R i k i k) • (1 : A) := by
  set S := ∑ i, ∑ j, ∑ k, ∑ l, R i j k l • (g i * g j * g k * g l) with hS
  have hS2 : S = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l • (g j * g k * g i * g l) := by
    rw [hS]
    exact sum_rot3 (fun i j k => ∑ l, R i j k l • (g i * g j * g k * g l))
  have hS3 : S = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l • (g k * g i * g j * g l) := by
    refine hS2.trans ?_
    exact sum_rot3 (fun i j k => ∑ l, R j k i l • (g j * g k * g i * g l))
  have hS2' : S = ∑ i, ∑ j, ∑ k, ∑ l, R j k i l • (g i * g j * g k * g l)
      + ∑ i, ∑ j, ∑ k, ∑ l, R j k i l • (((if j = i then (2 : ℝ) else 0) • g k) * g l)
      - ∑ i, ∑ j, ∑ k, ∑ l, R j k i l • (((if k = i then (2 : ℝ) else 0) • g j) * g l) := by
    have e : ∀ i j k l, R j k i l • (g j * g k * g i * g l) = R j k i l • (g i * g j * g k * g l)
        + R j k i l • (((if j = i then (2 : ℝ) else 0) • g k) * g l)
        - R j k i l • (((if k = i then (2 : ℝ) else 0) • g j) * g l) := by
      intro i j k l
      rw [rot_a g hg, sub_mul, add_mul, smul_sub, smul_add]
    rw [hS2]
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hS3' : S = ∑ i, ∑ j, ∑ k, ∑ l, R k i j l • (g i * g j * g k * g l)
      - ∑ i, ∑ j, ∑ k, ∑ l, R k i j l • (((if k = i then (2 : ℝ) else 0) • g j) * g l)
      + ∑ i, ∑ j, ∑ k, ∑ l, R k i j l • (((if k = j then (2 : ℝ) else 0) • g i) * g l) := by
    have e : ∀ i j k l, R k i j l • (g k * g i * g j * g l) = R k i j l • (g i * g j * g k * g l)
        - R k i j l • (((if k = i then (2 : ℝ) else 0) • g j) * g l)
        + R k i j l • (((if k = j then (2 : ℝ) else 0) • g i) * g l) := by
      intro i j k l
      rw [rot_b g hg, add_mul, sub_mul, smul_add, smul_sub]

    rw [hS3]
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hBi : ∑ i, ∑ j, ∑ k, ∑ l, R i j k l • (g i * g j * g k * g l)
      + ∑ i, ∑ j, ∑ k, ∑ l, R j k i l • (g i * g j * g k * g l)
      + ∑ i, ∑ j, ∑ k, ∑ l, R k i j l • (g i * g j * g k * g l) = 0 := by
    simp only [← Finset.sum_add_distrib, ← add_smul, hB, zero_smul, Finset.sum_const_zero]
  rw [collapse_F1, collapse_F2 g R hR1] at hS2'
  rw [collapse_F3 g R hR1, collapse_F4] at hS3'
  have h3 : S = (1 / 3 : ℝ) • (S + S + S) := by module
  have hQ := ricciClifford_eq g R hg hP
  set Q := ricciClifford g R
  have e : S + S + S = ((∑ i, ∑ j, ∑ k, ∑ l, R i j k l • (g i * g j * g k * g l))
      + (∑ i, ∑ j, ∑ k, ∑ l, R j k i l • (g i * g j * g k * g l))
      + (∑ i, ∑ j, ∑ k, ∑ l, R k i j l • (g i * g j * g k * g l)))
      + (2 : ℝ) • Q + (2 : ℝ) • Q + (2 : ℝ) • Q := by
    nth_rewrite 2 [hS2']
    nth_rewrite 2 [hS3']
    rw [hS]
    module
  rw [h3, e, hBi, hQ]
  module

end collapse

end Lightlike.Dirac
