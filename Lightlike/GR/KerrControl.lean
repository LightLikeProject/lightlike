import Lightlike.GR.KerrRicci

/-!
# A negative control for the Kerr Ricci-flatness: the coefficient of `g_{tφ}`

`ctrlMetric M a k` is the Kerr metric with `g_{tφ}` multiplied by `k`: `k = 1` is Kerr, `k = -1` is Kerr
with `-a` (`kerrMetric_neg`, also Ricci-flat), and for `k = 1/2` (`M = 1`, `a = 1/2`) the Ricci tensor
does not vanish at `(r, θ) = (3, π/2)` (`ctrl_not_ricci_flat`).

Generated partials of the modified entry by the same script as `KerrJetEntries`. Gap row GE6, negative
control (the plan row asks for a sign flip of `g_{tφ}`, which is `k = -1`, still Ricci-flat; see `KerrHorizon`).
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

/-- The modified entry `g_tφ` of the control metric after the derivatives ``. -/
def kcg03 (M a k r t : ℝ) : ℝ := (-((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) / ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))))

/-- The modified entry `g_tφ` of the control metric after the derivatives `R`. -/
def kcg03R (M a k r t : ℝ) : ℝ := (-(((((((k * 2) * M) * a) * (Real.sin t ^ 2)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) - ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * (2 * r))) / (((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2)))

/-- The modified entry `g_tφ` of the control metric after the derivatives `T`. -/
def kcg03T (M a k r t : ℝ) : ℝ := (-((((((((k * 2) * M) * a) * r) * ((2 * Real.sin t) * Real.cos t)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) - ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t))))) / (((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2)))

/-- The modified entry `g_tφ` of the control metric after the derivatives `RR`. -/
def kcg03RR (M a k r t : ℝ) : ℝ := (-(((((((((k * 2) * M) * a) * (Real.sin t ^ 2)) * (2 * r)) - ((((((k * 2) * M) * a) * (Real.sin t ^ 2)) * (2 * r)) + ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * 2))) * (((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2)) - (((((((k * 2) * M) * a) * (Real.sin t ^ 2)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) - ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * (2 * r))) * ((2 * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) * (2 * r)))) / ((((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2) ^ 2)))

/-- The modified entry `g_tφ` of the control metric after the derivatives `RT`. -/
def kcg03RT (M a k r t : ℝ) : ℝ := (-((((((((((k * 2) * M) * a) * ((2 * Real.sin t) * Real.cos t)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) + (((((k * 2) * M) * a) * (Real.sin t ^ 2)) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t))))) - ((((((k * 2) * M) * a) * r) * ((2 * Real.sin t) * Real.cos t)) * (2 * r))) * (((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2)) - (((((((k * 2) * M) * a) * (Real.sin t ^ 2)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) - ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * (2 * r))) * ((2 * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t)))))) / ((((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2) ^ 2)))

/-- The modified entry `g_tφ` of the control metric after the derivatives `TR`. -/
def kcg03TR (M a k r t : ℝ) : ℝ := (-((((((((((k * 2) * M) * a) * ((2 * Real.sin t) * Real.cos t)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) + ((((((k * 2) * M) * a) * r) * ((2 * Real.sin t) * Real.cos t)) * (2 * r))) - (((((k * 2) * M) * a) * (Real.sin t ^ 2)) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t))))) * (((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2)) - ((((((((k * 2) * M) * a) * r) * ((2 * Real.sin t) * Real.cos t)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) - ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t))))) * ((2 * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) * (2 * r)))) / ((((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2) ^ 2)))

/-- The modified entry `g_tφ` of the control metric after the derivatives `TT`. -/
def kcg03TT (M a k r t : ℝ) : ℝ := (-(((((((((((k * 2) * M) * a) * r) * (((2 * Real.cos t) * Real.cos t) + ((2 * Real.sin t) * (-Real.sin t)))) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) + ((((((k * 2) * M) * a) * r) * ((2 * Real.sin t) * Real.cos t)) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t))))) - (((((((k * 2) * M) * a) * r) * ((2 * Real.sin t) * Real.cos t)) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t)))) + ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * ((a ^ 2) * (((2 * (-Real.sin t)) * (-Real.sin t)) + ((2 * Real.cos t) * (-Real.cos t))))))) * (((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2)) - ((((((((k * 2) * M) * a) * r) * ((2 * Real.sin t) * Real.cos t)) * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) - ((((((k * 2) * M) * a) * r) * (Real.sin t ^ 2)) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t))))) * ((2 * ((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2)))) * ((a ^ 2) * ((2 * Real.cos t) * (-Real.sin t)))))) / ((((r ^ 2) + ((a ^ 2) * (Real.cos t ^ 2))) ^ 2) ^ 2)))

theorem hd_kc_R (M a k r0 t0 : ℝ) (hS : ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ≠ 0)
    (hD : (((r0 ^ 2) - ((2 * M) * r0)) + (a ^ 2)) ≠ 0) :
    HasDerivAt (fun x : ℝ => (-((((((k * 2) * M) * a) * x) * (Real.sin t0 ^ 2)) / ((x ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))))) (-(((((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * (2 * r0))) / (((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2))) r0 := by
  refine (((((((((hasDerivAt_const r0 (k)).mul (hasDerivAt_const r0 (2))).mul (hasDerivAt_const r0 (M))).mul (hasDerivAt_const r0 (a))).mul (hasDerivAt_id' r0)).mul (((hasDerivAt_const r0 t0).sin).pow 2)).div (((hasDerivAt_id' r0).pow 2).add (((hasDerivAt_const r0 (a)).pow 2).mul (((hasDerivAt_const r0 t0).cos).pow 2))) (by try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]; apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])).neg)).congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply]
  have hD2 := pow_ne_zero 2 hD
  have hS2 := pow_ne_zero 2 hS
  try generalize (r0 ^ 2 - 2 * M * r0 + a ^ 2) = Dv at *
  field_simp
  ring

theorem hd_kc_RR (M a k r0 t0 : ℝ) (hS : ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ≠ 0)
    (hD : (((r0 ^ 2) - ((2 * M) * r0)) + (a ^ 2)) ≠ 0) :
    HasDerivAt (fun x : ℝ => (-(((((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * ((x ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * x) * (Real.sin t0 ^ 2)) * (2 * x))) / (((x ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2)))) (-(((((((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * (2 * r0)) - ((((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * (2 * r0)) + ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * 2))) * (((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2)) - (((((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * (2 * r0))) * ((2 * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) * (2 * r0)))) / ((((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2) ^ 2))) r0 := by
  refine ((((((((((hasDerivAt_const r0 (k)).mul (hasDerivAt_const r0 (2))).mul (hasDerivAt_const r0 (M))).mul (hasDerivAt_const r0 (a))).mul (((hasDerivAt_const r0 t0).sin).pow 2)).mul (((hasDerivAt_id' r0).pow 2).add (((hasDerivAt_const r0 (a)).pow 2).mul (((hasDerivAt_const r0 t0).cos).pow 2)))).sub (((((((hasDerivAt_const r0 (k)).mul (hasDerivAt_const r0 (2))).mul (hasDerivAt_const r0 (M))).mul (hasDerivAt_const r0 (a))).mul (hasDerivAt_id' r0)).mul (((hasDerivAt_const r0 t0).sin).pow 2)).mul ((hasDerivAt_const r0 (2)).mul (hasDerivAt_id' r0)))).div ((((hasDerivAt_id' r0).pow 2).add (((hasDerivAt_const r0 (a)).pow 2).mul (((hasDerivAt_const r0 t0).cos).pow 2))).pow 2) (by try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]; apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])).neg)).congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply]
  have hD2 := pow_ne_zero 2 hD
  have hS2 := pow_ne_zero 2 hS
  try generalize (r0 ^ 2 - 2 * M * r0 + a ^ 2) = Dv at *
  field_simp
  ring

theorem hd_kc_RT (M a k r0 t0 : ℝ) (hS : ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ≠ 0)
    (hD : (((r0 ^ 2) - ((2 * M) * r0)) + (a ^ 2)) ≠ 0) :
    HasDerivAt (fun x : ℝ => (-(((((((k * 2) * M) * a) * (Real.sin x ^ 2)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos x ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin x ^ 2)) * (2 * r0))) / (((r0 ^ 2) + ((a ^ 2) * (Real.cos x ^ 2))) ^ 2)))) (-((((((((((k * 2) * M) * a) * ((2 * Real.sin t0) * Real.cos t0)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) + (((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0))))) - ((((((k * 2) * M) * a) * r0) * ((2 * Real.sin t0) * Real.cos t0)) * (2 * r0))) * (((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2)) - (((((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * (2 * r0))) * ((2 * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0)))))) / ((((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2) ^ 2))) t0 := by
  refine ((((((((((hasDerivAt_const t0 (k)).mul (hasDerivAt_const t0 (2))).mul (hasDerivAt_const t0 (M))).mul (hasDerivAt_const t0 (a))).mul (((hasDerivAt_id' t0).sin).pow 2)).mul (((hasDerivAt_const t0 r0).pow 2).add (((hasDerivAt_const t0 (a)).pow 2).mul (((hasDerivAt_id' t0).cos).pow 2)))).sub (((((((hasDerivAt_const t0 (k)).mul (hasDerivAt_const t0 (2))).mul (hasDerivAt_const t0 (M))).mul (hasDerivAt_const t0 (a))).mul (hasDerivAt_const t0 r0)).mul (((hasDerivAt_id' t0).sin).pow 2)).mul ((hasDerivAt_const t0 (2)).mul (hasDerivAt_const t0 r0)))).div ((((hasDerivAt_const t0 r0).pow 2).add (((hasDerivAt_const t0 (a)).pow 2).mul (((hasDerivAt_id' t0).cos).pow 2))).pow 2) (by try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]; apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])).neg)).congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply]
  have hD2 := pow_ne_zero 2 hD
  have hS2 := pow_ne_zero 2 hS
  try generalize (r0 ^ 2 - 2 * M * r0 + a ^ 2) = Dv at *
  field_simp
  ring

theorem hd_kc_T (M a k r0 t0 : ℝ) (hS : ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ≠ 0)
    (hD : (((r0 ^ 2) - ((2 * M) * r0)) + (a ^ 2)) ≠ 0) :
    HasDerivAt (fun x : ℝ => (-((((((k * 2) * M) * a) * r0) * (Real.sin x ^ 2)) / ((r0 ^ 2) + ((a ^ 2) * (Real.cos x ^ 2)))))) (-((((((((k * 2) * M) * a) * r0) * ((2 * Real.sin t0) * Real.cos t0)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0))))) / (((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2))) t0 := by
  refine (((((((((hasDerivAt_const t0 (k)).mul (hasDerivAt_const t0 (2))).mul (hasDerivAt_const t0 (M))).mul (hasDerivAt_const t0 (a))).mul (hasDerivAt_const t0 r0)).mul (((hasDerivAt_id' t0).sin).pow 2)).div (((hasDerivAt_const t0 r0).pow 2).add (((hasDerivAt_const t0 (a)).pow 2).mul (((hasDerivAt_id' t0).cos).pow 2))) (by try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]; apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])).neg)).congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply]
  have hD2 := pow_ne_zero 2 hD
  have hS2 := pow_ne_zero 2 hS
  try generalize (r0 ^ 2 - 2 * M * r0 + a ^ 2) = Dv at *
  field_simp
  ring

theorem hd_kc_TR (M a k r0 t0 : ℝ) (hS : ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ≠ 0)
    (hD : (((r0 ^ 2) - ((2 * M) * r0)) + (a ^ 2)) ≠ 0) :
    HasDerivAt (fun x : ℝ => (-((((((((k * 2) * M) * a) * x) * ((2 * Real.sin t0) * Real.cos t0)) * ((x ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * x) * (Real.sin t0 ^ 2)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0))))) / (((x ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2)))) (-((((((((((k * 2) * M) * a) * ((2 * Real.sin t0) * Real.cos t0)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) + ((((((k * 2) * M) * a) * r0) * ((2 * Real.sin t0) * Real.cos t0)) * (2 * r0))) - (((((k * 2) * M) * a) * (Real.sin t0 ^ 2)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0))))) * (((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2)) - ((((((((k * 2) * M) * a) * r0) * ((2 * Real.sin t0) * Real.cos t0)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0))))) * ((2 * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) * (2 * r0)))) / ((((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2) ^ 2))) r0 := by
  refine (((((((((((hasDerivAt_const r0 (k)).mul (hasDerivAt_const r0 (2))).mul (hasDerivAt_const r0 (M))).mul (hasDerivAt_const r0 (a))).mul (hasDerivAt_id' r0)).mul (((hasDerivAt_const r0 (2)).mul ((hasDerivAt_const r0 t0).sin)).mul ((hasDerivAt_const r0 t0).cos))).mul (((hasDerivAt_id' r0).pow 2).add (((hasDerivAt_const r0 (a)).pow 2).mul (((hasDerivAt_const r0 t0).cos).pow 2)))).sub (((((((hasDerivAt_const r0 (k)).mul (hasDerivAt_const r0 (2))).mul (hasDerivAt_const r0 (M))).mul (hasDerivAt_const r0 (a))).mul (hasDerivAt_id' r0)).mul (((hasDerivAt_const r0 t0).sin).pow 2)).mul (((hasDerivAt_const r0 (a)).pow 2).mul (((hasDerivAt_const r0 (2)).mul ((hasDerivAt_const r0 t0).cos)).mul (((hasDerivAt_const r0 t0).sin).neg))))).div ((((hasDerivAt_id' r0).pow 2).add (((hasDerivAt_const r0 (a)).pow 2).mul (((hasDerivAt_const r0 t0).cos).pow 2))).pow 2) (by try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]; apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])).neg)).congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply]
  have hD2 := pow_ne_zero 2 hD
  have hS2 := pow_ne_zero 2 hS
  try generalize (r0 ^ 2 - 2 * M * r0 + a ^ 2) = Dv at *
  field_simp
  ring

theorem hd_kc_TT (M a k r0 t0 : ℝ) (hS : ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ≠ 0)
    (hD : (((r0 ^ 2) - ((2 * M) * r0)) + (a ^ 2)) ≠ 0) :
    HasDerivAt (fun x : ℝ => (-((((((((k * 2) * M) * a) * r0) * ((2 * Real.sin x) * Real.cos x)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos x ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin x ^ 2)) * ((a ^ 2) * ((2 * Real.cos x) * (-Real.sin x))))) / (((r0 ^ 2) + ((a ^ 2) * (Real.cos x ^ 2))) ^ 2)))) (-(((((((((((k * 2) * M) * a) * r0) * (((2 * Real.cos t0) * Real.cos t0) + ((2 * Real.sin t0) * (-Real.sin t0)))) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) + ((((((k * 2) * M) * a) * r0) * ((2 * Real.sin t0) * Real.cos t0)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0))))) - (((((((k * 2) * M) * a) * r0) * ((2 * Real.sin t0) * Real.cos t0)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0)))) + ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * ((a ^ 2) * (((2 * (-Real.sin t0)) * (-Real.sin t0)) + ((2 * Real.cos t0) * (-Real.cos t0))))))) * (((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2)) - ((((((((k * 2) * M) * a) * r0) * ((2 * Real.sin t0) * Real.cos t0)) * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) - ((((((k * 2) * M) * a) * r0) * (Real.sin t0 ^ 2)) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0))))) * ((2 * ((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2)))) * ((a ^ 2) * ((2 * Real.cos t0) * (-Real.sin t0)))))) / ((((r0 ^ 2) + ((a ^ 2) * (Real.cos t0 ^ 2))) ^ 2) ^ 2))) t0 := by
  refine (((((((((((hasDerivAt_const t0 (k)).mul (hasDerivAt_const t0 (2))).mul (hasDerivAt_const t0 (M))).mul (hasDerivAt_const t0 (a))).mul (hasDerivAt_const t0 r0)).mul (((hasDerivAt_const t0 (2)).mul ((hasDerivAt_id' t0).sin)).mul ((hasDerivAt_id' t0).cos))).mul (((hasDerivAt_const t0 r0).pow 2).add (((hasDerivAt_const t0 (a)).pow 2).mul (((hasDerivAt_id' t0).cos).pow 2)))).sub (((((((hasDerivAt_const t0 (k)).mul (hasDerivAt_const t0 (2))).mul (hasDerivAt_const t0 (M))).mul (hasDerivAt_const t0 (a))).mul (hasDerivAt_const t0 r0)).mul (((hasDerivAt_id' t0).sin).pow 2)).mul (((hasDerivAt_const t0 (a)).pow 2).mul (((hasDerivAt_const t0 (2)).mul ((hasDerivAt_id' t0).cos)).mul (((hasDerivAt_id' t0).sin).neg))))).div ((((hasDerivAt_const t0 r0).pow 2).add (((hasDerivAt_const t0 (a)).pow 2).mul (((hasDerivAt_id' t0).cos).pow 2))).pow 2) (by try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply, npowRec]; apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])).neg)).congr_deriv ?_
  try simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply, Pi.div_apply]
  have hD2 := pow_ne_zero 2 hD
  have hS2 := pow_ne_zero 2 hS
  try generalize (r0 ^ 2 - 2 * M * r0 + a ^ 2) = Dv at *
  field_simp
  ring

theorem pd_kcg03 (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (j : Fin 4) :
    pd j (fun z => kcg03 M a k (z 1) (z 2)) y =
      if j = 1 then kcg03R M a k (y 1) (y 2) else if j = 2 then kcg03T M a k (y 1) (y 2) else 0 := by
  have hS : (((y 1) ^ 2) + ((a ^ 2) * (Real.cos (y 2) ^ 2))) ≠ 0 := (kerrS_pos a hy.1).ne'
  have hD : ((((y 1) ^ 2) - ((2 * M) * (y 1))) + (a ^ 2)) ≠ 0 := hy.2.1
  refine pd_rθ (kcg03 M a k) ?_ (hd_kc_R M a k (y 1) (y 2) hS hD) (hd_kc_T M a k (y 1) (y 2) hS hD) j
  unfold kcg03
  fun_prop (disch := apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])

theorem pd_kcg03R (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (j : Fin 4) :
    pd j (fun z => kcg03R M a k (z 1) (z 2)) y =
      if j = 1 then kcg03RR M a k (y 1) (y 2) else if j = 2 then kcg03RT M a k (y 1) (y 2) else 0 := by
  have hS : (((y 1) ^ 2) + ((a ^ 2) * (Real.cos (y 2) ^ 2))) ≠ 0 := (kerrS_pos a hy.1).ne'
  have hD : ((((y 1) ^ 2) - ((2 * M) * (y 1))) + (a ^ 2)) ≠ 0 := hy.2.1
  refine pd_rθ (kcg03R M a k) ?_ (hd_kc_RR M a k (y 1) (y 2) hS hD) (hd_kc_RT M a k (y 1) (y 2) hS hD) j
  unfold kcg03R
  fun_prop (disch := apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])

theorem pd_kcg03T (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (j : Fin 4) :
    pd j (fun z => kcg03T M a k (z 1) (z 2)) y =
      if j = 1 then kcg03TR M a k (y 1) (y 2) else if j = 2 then kcg03TT M a k (y 1) (y 2) else 0 := by
  have hS : (((y 1) ^ 2) + ((a ^ 2) * (Real.cos (y 2) ^ 2))) ≠ 0 := (kerrS_pos a hy.1).ne'
  have hD : ((((y 1) ^ 2) - ((2 * M) * (y 1))) + (a ^ 2)) ≠ 0 := hy.2.1
  refine pd_rθ (kcg03T M a k) ?_ (hd_kc_TR M a k (y 1) (y 2) hS hD) (hd_kc_TT M a k (y 1) (y 2) hS hD) j
  unfold kcg03T
  fun_prop (disch := apply_rules [mul_ne_zero, pow_ne_zero, hS, hD, one_ne_zero])

/-- The entries of the control metric after the derivatives `` in `(r, θ)`, by index. -/
def gjetC0 (M a k r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00 M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kcg03 M a k r t
  else if i = 1 ∧ j = 1 then kgg11 M a r t
  else if i = 2 ∧ j = 2 then kgg22 M a r t
  else if i = 3 ∧ j = 3 then kgg33 M a r t
  else 0

/-- The entries of the control metric after the derivatives `R` in `(r, θ)`, by index. -/
def gjetCR (M a k r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00R M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kcg03R M a k r t
  else if i = 1 ∧ j = 1 then kgg11R M a r t
  else if i = 2 ∧ j = 2 then kgg22R M a r t
  else if i = 3 ∧ j = 3 then kgg33R M a r t
  else 0

/-- The entries of the control metric after the derivatives `T` in `(r, θ)`, by index. -/
def gjetCT (M a k r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00T M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kcg03T M a k r t
  else if i = 1 ∧ j = 1 then kgg11T M a r t
  else if i = 2 ∧ j = 2 then kgg22T M a r t
  else if i = 3 ∧ j = 3 then kgg33T M a r t
  else 0

/-- The entries of the control metric after the derivatives `RR` in `(r, θ)`, by index. -/
def gjetCRR (M a k r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00RR M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kcg03RR M a k r t
  else if i = 1 ∧ j = 1 then kgg11RR M a r t
  else if i = 2 ∧ j = 2 then kgg22RR M a r t
  else if i = 3 ∧ j = 3 then kgg33RR M a r t
  else 0

/-- The entries of the control metric after the derivatives `RT` in `(r, θ)`, by index. -/
def gjetCRT (M a k r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00RT M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kcg03RT M a k r t
  else if i = 1 ∧ j = 1 then kgg11RT M a r t
  else if i = 2 ∧ j = 2 then kgg22RT M a r t
  else if i = 3 ∧ j = 3 then kgg33RT M a r t
  else 0

/-- The entries of the control metric after the derivatives `TR` in `(r, θ)`, by index. -/
def gjetCTR (M a k r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00TR M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kcg03TR M a k r t
  else if i = 1 ∧ j = 1 then kgg11TR M a r t
  else if i = 2 ∧ j = 2 then kgg22TR M a r t
  else if i = 3 ∧ j = 3 then kgg33TR M a r t
  else 0

/-- The entries of the control metric after the derivatives `TT` in `(r, θ)`, by index. -/
def gjetCTT (M a k r t : ℝ) (i j : Fin 4) : ℝ :=
  if i = 0 ∧ j = 0 then kgg00TT M a r t
  else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then kcg03TT M a k r t
  else if i = 1 ∧ j = 1 then kgg11TT M a r t
  else if i = 2 ∧ j = 2 then kgg22TT M a r t
  else if i = 3 ∧ j = 3 then kgg33TT M a r t
  else 0

/-- `pd` of the control entries after the derivatives ``. -/
theorem pd_gjetC0 (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j l : Fin 4) :
    pd l (fun z => gjetC0 M a k (z 1) (z 2) i j) y =
      if l = 1 then gjetCR M a k (y 1) (y 2) i j else if l = 2 then gjetCT M a k (y 1) (y 2) i j else 0 := by
  by_cases h00 : i = 0 ∧ j = 0
  · simp only [gjetC0, gjetCR, gjetCT, h00, and_self, ite_true]
    exact pd_kgg00 M a hy l
  by_cases h03 : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  · simp only [gjetC0, gjetCR, gjetCT, h00, h03, ite_true, ite_false]
    exact pd_kcg03 M a k hy l
  by_cases h11 : i = 1 ∧ j = 1
  · simp only [gjetC0, gjetCR, gjetCT, h00, h03, h11, ite_true, ite_false]
    exact pd_kgg11 M a hy l
  by_cases h22 : i = 2 ∧ j = 2
  · simp only [gjetC0, gjetCR, gjetCT, h00, h03, h11, h22, ite_true, ite_false]
    exact pd_kgg22 M a hy l
  by_cases h33 : i = 3 ∧ j = 3
  · simp only [gjetC0, gjetCR, gjetCT, h00, h03, h11, h22, h33, ite_true, ite_false]
    exact pd_kgg33 M a hy l
  simp only [gjetC0, gjetCR, gjetCT, h00, h03, h11, h22, h33, ite_false]
  simp [pd_const]

/-- `pd` of the control entries after the derivatives `R`. -/
theorem pd_gjetCR (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j l : Fin 4) :
    pd l (fun z => gjetCR M a k (z 1) (z 2) i j) y =
      if l = 1 then gjetCRR M a k (y 1) (y 2) i j else if l = 2 then gjetCRT M a k (y 1) (y 2) i j else 0 := by
  by_cases h00 : i = 0 ∧ j = 0
  · simp only [gjetCR, gjetCRR, gjetCRT, h00, and_self, ite_true]
    exact pd_kgg00R M a hy l
  by_cases h03 : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  · simp only [gjetCR, gjetCRR, gjetCRT, h00, h03, ite_true, ite_false]
    exact pd_kcg03R M a k hy l
  by_cases h11 : i = 1 ∧ j = 1
  · simp only [gjetCR, gjetCRR, gjetCRT, h00, h03, h11, ite_true, ite_false]
    exact pd_kgg11R M a hy l
  by_cases h22 : i = 2 ∧ j = 2
  · simp only [gjetCR, gjetCRR, gjetCRT, h00, h03, h11, h22, ite_true, ite_false]
    exact pd_kgg22R M a hy l
  by_cases h33 : i = 3 ∧ j = 3
  · simp only [gjetCR, gjetCRR, gjetCRT, h00, h03, h11, h22, h33, ite_true, ite_false]
    exact pd_kgg33R M a hy l
  simp only [gjetCR, gjetCRR, gjetCRT, h00, h03, h11, h22, h33, ite_false]
  simp [pd_const]

/-- `pd` of the control entries after the derivatives `T`. -/
theorem pd_gjetCT (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j l : Fin 4) :
    pd l (fun z => gjetCT M a k (z 1) (z 2) i j) y =
      if l = 1 then gjetCTR M a k (y 1) (y 2) i j else if l = 2 then gjetCTT M a k (y 1) (y 2) i j else 0 := by
  by_cases h00 : i = 0 ∧ j = 0
  · simp only [gjetCT, gjetCTR, gjetCTT, h00, and_self, ite_true]
    exact pd_kgg00T M a hy l
  by_cases h03 : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  · simp only [gjetCT, gjetCTR, gjetCTT, h00, h03, ite_true, ite_false]
    exact pd_kcg03T M a k hy l
  by_cases h11 : i = 1 ∧ j = 1
  · simp only [gjetCT, gjetCTR, gjetCTT, h00, h03, h11, ite_true, ite_false]
    exact pd_kgg11T M a hy l
  by_cases h22 : i = 2 ∧ j = 2
  · simp only [gjetCT, gjetCTR, gjetCTT, h00, h03, h11, h22, ite_true, ite_false]
    exact pd_kgg22T M a hy l
  by_cases h33 : i = 3 ∧ j = 3
  · simp only [gjetCT, gjetCTR, gjetCTT, h00, h03, h11, h22, h33, ite_true, ite_false]
    exact pd_kgg33T M a hy l
  simp only [gjetCT, gjetCTR, gjetCTT, h00, h03, h11, h22, h33, ite_false]
  simp [pd_const]

/-- The control metric: the Kerr metric with `g_{tφ}` multiplied by `k`. -/
def ctrlMetric (M a k : ℝ) (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => gjetC0 M a k (y 1) (y 2) i j

theorem pd_ctrlMetric (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j l : Fin 4) :
    pd l (fun z => ctrlMetric M a k z i j) y =
      if l = 1 then gjetCR M a k (y 1) (y 2) i j else if l = 2 then gjetCT M a k (y 1) (y 2) i j else 0 := by
  simp only [ctrlMetric, Matrix.of_apply]
  exact pd_gjetC0 M a k hy i j l

theorem pd_pd_ctrlMetric (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ kerrU M a) (i j ν μ : Fin 4) :
    pd μ (fun w => pd ν (fun z => ctrlMetric M a k z i j) w) y =
      if μ = 1 then (if ν = 1 then gjetCRR M a k (y 1) (y 2) i j else if ν = 2 then gjetCTR M a k (y 1) (y 2) i j else 0)
      else if μ = 2 then (if ν = 1 then gjetCRT M a k (y 1) (y 2) i j else if ν = 2 then gjetCTT M a k (y 1) (y 2) i j else 0)
      else 0 := by
  have hev : (fun w => pd ν (fun z => ctrlMetric M a k z i j) w) =ᶠ[nhds y]
      fun w => if ν = 1 then gjetCR M a k (w 1) (w 2) i j else if ν = 2 then gjetCT M a k (w 1) (w 2) i j else 0 := by
    filter_upwards [(isOpen_kerrU M a).mem_nhds hy] with w hw
    exact pd_ctrlMetric M a k hw i j ν
  rw [pd_congr hev]
  by_cases h1 : ν = 1
  · simp only [h1, ite_true]
    exact pd_gjetCR M a k hy i j μ
  by_cases h2 : ν = 2
  · simp only [h1, h2, ite_true, ite_false]
    exact pd_gjetCT M a k hy i j μ
  simp only [h1, h2, ite_false]
  rw [pd_const]
  split_ifs <;> rfl

/-- The control metric agrees with Kerr off the `(t, φ)` off-diagonal entries. -/
theorem ctrlMetric_eq_kerr (M a k : ℝ) (y : Fin 4 → ℝ) (i j : Fin 4)
    (h : ¬ ((i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0))) : ctrlMetric M a k y i j = kerrMetric M a y i j := by
  rw [kerrMetric_eq_gjet]
  simp only [ctrlMetric, Matrix.of_apply, gjetC0, gjet0]
  split_ifs <;> simp_all

/-- The `(t, φ)` off-diagonal entry of the control metric. -/
theorem ctrlMetric_03 (M a k : ℝ) (y : Fin 4 → ℝ) : ctrlMetric M a k y 0 3 = kcg03 M a k (y 1) (y 2) := by
  simp [ctrlMetric, gjetC0]

theorem ctrlMetric_30 (M a k : ℝ) (y : Fin 4 → ℝ) : ctrlMetric M a k y 3 0 = kcg03 M a k (y 1) (y 2) := by
  simp [ctrlMetric, gjetC0]

/-- The determinant of the `(t, φ)` block of the control metric. -/
def ctrlDet (M a k : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  kgg00 M a (y 1) (y 2) * kgg33 M a (y 1) (y 2) - kcg03 M a k (y 1) (y 2) ^ 2

/-- The domain where the control metric is invertible (inside `kerrU`). -/
def ctrlU (M a k : ℝ) : Set (Fin 4 → ℝ) := {y | y ∈ kerrU M a ∧ (ctrlMetric M a k y).det ≠ 0}

/-- The determinant of the control metric. -/
theorem det_ctrlMetric (M a k : ℝ) (y : Fin 4 → ℝ) :
    (ctrlMetric M a k y).det =
      ctrlDet M a k y * (kgg11 M a (y 1) (y 2) * kgg22 M a (y 1) (y 2)) := by
  simp [ctrlMetric, gjetC0, ctrlDet, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem ctrlDet_ne (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ ctrlU M a k) : ctrlDet M a k y ≠ 0 := by
  have := hy.2
  rw [det_ctrlMetric] at this
  exact left_ne_zero_of_mul this

/-- The inverse of the control metric. -/
def ctrlInv (M a k : ℝ) (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![kgg33 M a (y 1) (y 2) / ctrlDet M a k y, 0, 0, -kcg03 M a k (y 1) (y 2) / ctrlDet M a k y;
     0, kerrD M a y / kerrS a y, 0, 0;
     0, 0, 1 / kerrS a y, 0;
     -kcg03 M a k (y 1) (y 2) / ctrlDet M a k y, 0, 0, kgg00 M a (y 1) (y 2) / ctrlDet M a k y]

theorem kgg11_eq (M a : ℝ) (y : Fin 4 → ℝ) :
    kgg11 M a (y 1) (y 2) = kerrS a y / kerrD M a y := rfl

theorem kgg22_eq (M a : ℝ) (y : Fin 4 → ℝ) : kgg22 M a (y 1) (y 2) = kerrS a y := rfl

theorem ctrlMetric_mul_ctrlInv (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ ctrlU M a k) :
    ctrlMetric M a k y * ctrlInv M a k y = 1 := by
  have hS : kerrS a y ≠ 0 := (kerrS_pos a hy.1.1).ne'
  have hD : kerrD M a y ≠ 0 := hy.1.2.1
  have hd : ctrlDet M a k y ≠ 0 := ctrlDet_ne M a k hy
  have hS2 : kerrS a y = y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 := rfl
  have hD2 : kerrD M a y = y 1 ^ 2 - 2 * M * y 1 + a ^ 2 := rfl
  have hS' : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := hS
  have hD' : y 1 ^ 2 - 2 * M * y 1 + a ^ 2 ≠ 0 := hD
  have hD'' : -(y 1 * M * 2) + y 1 ^ 2 + a ^ 2 ≠ 0 := by intro h; apply hD; linarith
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ctrlMetric, ctrlInv, gjetC0, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply,
      kgg11_eq, kgg22_eq] <;> field_simp <;> (try simp only [ctrlDet]) <;> ring

theorem ctrlMetric_inv (M a k : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ ctrlU M a k) :
    (ctrlMetric M a k y)⁻¹ = ctrlInv M a k y :=
  Matrix.inv_eq_right_inv (ctrlMetric_mul_ctrlInv M a k hy)

/-- The entries of the control metric are smooth on `kerrU`. -/
theorem ctrlMetric_smooth (M a k : ℝ) (i j : Fin 4) :
    ContDiffOn ℝ ∞ (fun y => ctrlMetric M a k y i j) (kerrU M a) := by
  by_cases h : (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  · intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    have hS : kerrS a y ≠ 0 := (kerrS_pos a hy.1).ne'
    have hS' : y 1 ^ 2 + a ^ 2 * cos (y 2) ^ 2 ≠ 0 := hS
    have e : (fun y => ctrlMetric M a k y i j) = fun y => kcg03 M a k (y 1) (y 2) := by
      funext z
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ctrlMetric_03 M a k z
      · exact ctrlMetric_30 M a k z
    rw [e]
    unfold kcg03
    fun_prop (disch := apply_rules [mul_ne_zero, pow_ne_zero, hS', one_ne_zero])
  · have e : (fun y => ctrlMetric M a k y i j) = fun y => kerrMetric M a y i j := by
      funext z; exact ctrlMetric_eq_kerr M a k z i j h
    rw [e]
    exact (isCoordMetric_kerr M a).smooth i j

theorem isOpen_ctrlU (M a k : ℝ) : IsOpen (ctrlU M a k) := by
  have hc : ContinuousOn (fun y => (ctrlMetric M a k y).det) (kerrU M a) :=
    (Regge.Conv3.cdo_det (U := kerrU M a) (k := ∞) (ctrlMetric M a k) (ctrlMetric_smooth M a k)).continuousOn
  exact hc.isOpen_inter_preimage (isOpen_kerrU M a) isOpen_ne

/-- The control metric is a coordinate metric on `ctrlU`. -/
theorem isCoordMetric_ctrl (M a k : ℝ) : IsCoordMetric (ctrlMetric M a k) (ctrlU M a k) where
  isOpen := isOpen_ctrlU M a k
  symm := fun y _ => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ctrlMetric, gjetC0]
  isUnit_det := fun y hy => (hy.2).isUnit
  smooth := fun i j => (ctrlMetric_smooth M a k i j).mono (fun y hy => hy.1)

/-- The test point `(t, r, θ, φ) = (0, 3, π/2, 0)`. -/
def ctrlPoint : Fin 4 → ℝ := ![0, 3, π / 2, 0]

theorem ctrlPoint_mem : ctrlPoint ∈ ctrlU 1 (1 / 2) (1 / 2) := by
  refine ⟨⟨by simp [ctrlPoint], ?_, by simp [ctrlPoint, Real.pi_pos], by simp [ctrlPoint, Real.pi_pos]⟩, ?_⟩
  · simp [kerrD, ctrlPoint]; norm_num
  · rw [det_ctrlMetric]
    simp [ctrlDet, kgg00, kgg03, kgg11, kgg22, kgg33, kcg03, kerrS, kerrD, ctrlPoint]
    norm_num

open Lightlike.Regge.Conv3 in
/-- **A real negative control.** The Kerr metric with `g_{tφ}` halved (`k = 1/2`; `M = 1`, `a = 1/2`) is
not Ricci-flat: `R_{22} = -25/456` at `(r, θ) = (3, π/2)`. -/
theorem ctrl_ricci_22 : ricci (ctrlMetric 1 (1 / 2) (1 / 2)) 2 2 ctrlPoint = -(25 / 456) := by
  have hy := ctrlPoint_mem
  have hg := isCoordMetric_ctrl 1 (1 / 2 : ℝ) (1 / 2)
  have hinv := ctrlMetric_inv 1 (1 / 2 : ℝ) (1 / 2) hy
  simp only [ricci, riemann_jet hg hy, dChr, christoffel,
    pd_ctrlMetric 1 (1 / 2) (1 / 2) hy.1, pd_pd_ctrlMetric 1 (1 / 2) (1 / 2) hy.1, hinv, Fin.sum_univ_four]
  simp [kgg00R, kgg00T, kgg00RR, kgg00RT, kgg00TR, kgg00TT, kgg11R, kgg11T, kgg11RR, kgg11RT, kgg11TR, kgg11TT, kgg22R, kgg22T, kgg22RR, kgg22RT, kgg22TR, kgg22TT, kgg33R, kgg33T, kgg33RR, kgg33RT, kgg33TR, kgg33TT, kcg03R, kcg03T, kcg03RR, kcg03RT, kcg03TR, kcg03TT, gjetCR, gjetCT, gjetCRR, gjetCRT, gjetCTR, gjetCTT, ctrlInv, ctrlDet, kerrS, kerrD, kcg03, kgg00, kgg11, kgg22, kgg33, ctrlPoint]
  norm_num

/-- **The control is not Ricci-flat**, in contrast to Kerr (`kerr_isVacuumSolution`) and to `a ↦ -a`
(`kerrMetric_neg`). -/
theorem ctrl_not_ricci_flat : ¬ ∀ y ∈ ctrlU 1 (1 / 2) (1 / 2), ∀ σ ν : Fin 4,
    ricci (ctrlMetric 1 (1 / 2) (1 / 2)) σ ν y = 0 := by
  intro h
  have := h ctrlPoint ctrlPoint_mem 2 2
  rw [ctrl_ricci_22] at this
  norm_num at this

end Lightlike
