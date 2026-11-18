import Lightlike.Asymptotics.Tauberian.Psi
import Lightlike.Asymptotics.Tauberian.WindowSum

/-!
# Comparison of a measure with its smoothed version

`ρ(x) = 1_{x ≤ Δ} - ψ(Δ - x)`: pointwise bound in terms of `y = Δ - x` (`rho_bound`).
-/

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Lightlike.Tauberian

/-- The error function `1_{x ≤ Δ} - ψ(Δ - x)`, as a function of `y = Δ - x`. -/
def rhoErr (b β y : ℝ) : ℝ := (if 0 ≤ y then 1 else 0) - psiS b β y

lemma psiS_le_exp {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (y : ℝ) :
    psiS b β y ≤ Real.exp (β * max y 0) := by
  have hN := kapN_pos hb
  unfold psiS
  have h1 : ∫ u in Iio y, Real.exp (β * u) * kap b u ≤ ∫ u in Iio y, Real.exp (β * max y 0) * kap b u :=
    setIntegral_mono_on (integrableOn_exp_kap hb hβ y) ((integrable_kap hb).integrableOn.const_mul _)
      measurableSet_Iio fun u hu => mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.2 (by have : u < y := hu; nlinarith [le_max_left y 0])) (kap_nonneg b u)
  rw [integral_const_mul] at h1
  have h2 : ∫ u in Iio y, kap b u ≤ kapN b := setIntegral_le_integral (integrable_kap hb)
    (Filter.Eventually.of_forall fun u => kap_nonneg b u)
  calc 1 / kapN b * ∫ u in Iio y, Real.exp (β * u) * kap b u
      ≤ 1 / kapN b * (Real.exp (β * max y 0) * ∫ u in Iio y, kap b u) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 / kapN b * (Real.exp (β * max y 0) * kapN b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) (by positivity)
    _ = Real.exp (β * max y 0) := by field_simp

/-- **A crude bound for the error**: `|ρ(y)| ≤ 1 + e^{β max(y,0)}`. -/
lemma rhoErr_abs_le {b β : ℝ} (hb : 0 < b) (hβ : 0 ≤ β) (y : ℝ) :
    |rhoErr b β y| ≤ 1 + Real.exp (β * max y 0) := by
  have h0 := psiS_nonneg (β := β) hb y
  have h1 := psiS_le_exp hb hβ y
  have h2 : 1 ≤ Real.exp (β * max y 0) := Real.one_le_exp (mul_nonneg hβ (le_max_right _ _))
  unfold rhoErr
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

end Lightlike.Tauberian
