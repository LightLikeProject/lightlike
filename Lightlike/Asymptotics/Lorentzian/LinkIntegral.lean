import Lightlike.Asymptotics.Lorentzian.Bridge

/-!
# One link of the principal-series vertex as an integral over the chart

Step 1 of the assembly of `eprlVertex = lorVertex`: the combination of EPRL matrix coefficients
along one link is an integral over `ℂ` of `e^S` times the density of `Ω`.
-/

open Matrix Complex
open scoped ComplexConjugate InnerProductSpace
open Lightlike Lightlike.Spin4 Lightlike.SU2 Lightlike.Lorentz Lightlike.SpinFoam

namespace Lightlike.Asymptotics.Lorentzian

/-- **Unitarity**: `⟪x, π(a⁻¹ b) y⟫ = ⟪π(a) x, π(b) y⟫`. -/
theorem inner_pi_inv_mul (n : ℤ) (ρ : ℝ) (a b : SL2C) (x y : L2C) :
    inner ℂ x (principalSeries n ρ (a⁻¹ * b) y) =
      inner ℂ (principalSeries n ρ a x) (principalSeries n ρ b y) := by
  have h : principalSeries n ρ b y = principalSeries n ρ a (principalSeries n ρ (a⁻¹ * b) y) := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
  rw [h, principalSeries_inner]

/-- **`suV` on a combination of basis vectors**: the combination `Σ c_m Y e_m` of EPRL vectors is the
image under `suV` of the coefficient vector `Σ c_m e_m`. -/
theorem eprlVec_sum (γ : ℝ) (J : ℕ) (c : Fin (dsp (J : ℤ) 0 + 1) → ℂ) :
    ∑ m : Fin (dsp (J : ℤ) 0 + 1), c m • eprlVec γ J m =
      suV (J : ℤ) (eprlRho γ J) 0 (∑ m : Fin (dsp (J : ℤ) 0 + 1),
        c m • EuclideanSpace.single m (1 : ℂ)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, eprlVec, dite_eq_left m.2]

/-- **The contracted matrix coefficients are one inner product**: since `eprlCoeff` is conjugate
linear in the bra slot, `Σ u_m v_{m'} D_{m m'}(g) = ⟪Σ conj(u_m) Y e_m, π(g) Σ v_{m'} Y e_{m'}⟫`. -/
theorem eprlCoeff_pair (γ : ℝ) (J : ℕ) (u v : Fin (dsp (J : ℤ) 0 + 1) → ℂ) (g : SL2C) :
    ∑ m : Fin (dsp (J : ℤ) 0 + 1), ∑ m' : Fin (dsp (J : ℤ) 0 + 1),
        u m * v m' * eprlCoeff γ J m m' g =
      inner ℂ (∑ m : Fin (dsp (J : ℤ) 0 + 1), conj (u m) • eprlVec γ J m)
        (principalSeries (J : ℤ) (eprlRho γ J) g
          (∑ m' : Fin (dsp (J : ℤ) 0 + 1), v m' • eprlVec γ J m')) := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right, eprlCoeff, Complex.conj_conj]
  ring

end Lightlike.Asymptotics.Lorentzian
