import Lightlike.Dirac.Weitzenbock

/-!
# The curvature term of the Lichnerowicz formula

In a local orthonormal frame the spinor curvature of the spin connection is
`Rˢ(eᵢ,eⱼ) = ¼ ∑ₖₗ Rᵢⱼₖₗ γₖγₗ`, and the curvature term in the Weitzenböck formula for `D²` is
`½ ∑ᵢⱼ γᵢγⱼ Rˢ(eᵢ,eⱼ)`.  This file shows that, for a Riemann-symmetric array `R` and Clifford
generators `γᵢγⱼ+γⱼγᵢ = -2δᵢⱼ`, this term is the scalar `s/4`, where
`s = ∑ᵢⱼ Rᵢⱼⱼᵢ` is the scalar curvature in the convention `Rᵢⱼₖₗ = ⟨R(eᵢ,eⱼ)eₖ,eₗ⟩`
(so `s = 2` on the unit 2-sphere).  Replacing `¼` by `½` (the "`R/2` formula") gives `s/2`, which
differs from `s/4` whenever `s ≠ 0`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {A : Type*} [Ring A] [Algebra ℝ A]

/-- The spinor curvature `¼ ∑ₖₗ Rᵢⱼₖₗ γₖγₗ` of the frame data `R`. -/
noncomputable def spinorCurvature (g : Fin n → A) (R : Fin n → Fin n → Fin n → Fin n → ℝ) (i j : Fin n) : A :=
  ∑ k, ∑ l, ((1 / 4 : ℝ) * R i j k l) • (g k * g l)

/-- The curvature term `½ ∑ᵢⱼ γᵢγⱼ Rˢ(eᵢ,eⱼ)` of the Weitzenböck formula. -/
noncomputable def curvatureTerm (g : Fin n → A) (R : Fin n → Fin n → Fin n → Fin n → ℝ) : A :=
  (1 / 2 : ℝ) • ∑ i, ∑ j, g i * g j * spinorCurvature g R i j

/-- **Curvature term of the Lichnerowicz formula.**  `½ ∑ γᵢγⱼ Rˢ(eᵢ,eⱼ) = (s/4) · 1` with
`s = ∑ᵢⱼ Rᵢⱼⱼᵢ`. -/
theorem curvatureTerm_eq (g : Fin n → A) (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hg : ∀ j k, g j * g k + g k * g j = (if j = k then (-2 : ℝ) else 0) • (1 : A))
    (hR1 : ∀ i j k l, R i j k l = - R j i k l)
    (hP : ∀ i j k l, R i j k l = R k l i j)
    (hB : ∀ i j k l, R i j k l + R j k i l + R k i j l = 0) :
    curvatureTerm g R = ((1 / 4 : ℝ) * ∑ i, ∑ j, R i j j i) • (1 : A) := by
  have h := riemann_clifford_sum g R hg hR1 hP hB
  have hR2 : ∀ i j k l, R i j k l = - R i j l k := fun i j k l => by
    rw [hP i j k l, hR1 k l i j, ← hP l k i j]
  have hs : ∑ i, ∑ j, R i j j i = - ∑ i, ∑ k, R i k i k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hR2 i k k i
  have e : curvatureTerm g R
      = (1 / 8 : ℝ) • ∑ i, ∑ j, ∑ k, ∑ l, R i j k l • (g i * g j * g k * g l) := by
    unfold curvatureTerm spinorCurvature
    simp only [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_smul_comm, smul_smul, ← mul_assoc]
    congr 1
    ring
  rw [e, h, hs, smul_smul]
  congr 1
  ring

end Lightlike.Dirac
