import Mathlib
import Lightlike.Canonical.ParamIntegral

/-!
# Differentiation under the integral along a line of parameters

For a function `Φ` of parameters in a normed space `E` that are smooth functions `Z x`, `V x` of the point `x ∈ ℝᵈ`:
if `Φ` is `C¹` along `Z x + t V x`, and `Φ` and its derivative along `V x` vanish outside a compact set, then
`d/dt ∫ Φ (Z x + t V x) dx = ∫ Φ'(Z x) (V x) dx` at `t = 0`. This is the shape used for the smeared constraints:
the parameters are the values and derivatives of the lapse, the metric, the momentum and their variations.
-/

open MeasureTheory Metric Set Filter
open scoped Topology

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- **Differentiation under the integral sign along `Z + t V`.** -/
theorem integral_hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ)
    (Z V : (Fin d → ℝ) → E) {K : Set (Fin d → ℝ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hZ : Continuous Z) (hV : Continuous V)
    (hΦ : ∀ t : ℝ, |t| < ε → ∀ x, ContDiffAt ℝ 1 Φ (Z x + t • V x))
    (hzero : ∀ t : ℝ, ∀ x, x ∉ K → Φ (Z x + t • V x) = 0 ∧ fderiv ℝ Φ (Z x + t • V x) (V x) = 0) :
    Integrable (fun x => fderiv ℝ Φ (Z x) (V x)) volume ∧
      HasDerivAt (fun t : ℝ => ∫ x, Φ (Z x + t • V x)) (∫ x, fderiv ℝ Φ (Z x) (V x)) 0 := by
  have hline : ∀ (t : ℝ) (x : Fin d → ℝ), HasDerivAt (fun s : ℝ => Z x + s • V x) (V x) t := by
    intro t x
    have := ((hasDerivAt_id t).smul_const (V x)).const_add (Z x)
    exact HasDerivAt.congr_deriv this (by simp)
  have hderiv : ∀ t ∈ ball (0 : ℝ) ε, ∀ x, HasDerivAt (fun s => Φ (Z x + s • V x))
      (fderiv ℝ Φ (Z x + t • V x) (V x)) t := by
    intro t ht x
    have ht' : |t| < ε := by simpa [Real.dist_eq] using mem_ball.mp ht
    exact ((hΦ t ht' x).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hline t x)
  have hFc : ∀ t ∈ ball (0 : ℝ) ε, Continuous (fun x => Φ (Z x + t • V x)) := by
    intro t ht
    have ht' : |t| < ε := by simpa [Real.dist_eq] using mem_ball.mp ht
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact ContinuousAt.comp (g := Φ) (f := fun x => Z x + t • V x) (hΦ t ht' x).continuousAt
      (hZ.add (hV.const_smul t)).continuousAt
  have hF'c : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => fderiv ℝ Φ (Z p.2 + p.1 • V p.2) (V p.2))
      (closedBall (0 : ℝ) (ε / 2) ×ˢ univ) := by
    intro p hp
    have ht : |p.1| < ε := by
      have := mem_closedBall.mp hp.1
      rw [Real.dist_eq, sub_zero] at this
      linarith
    refine ContinuousAt.continuousWithinAt ?_
    have hW : Continuous (fun q : ℝ × (Fin d → ℝ) => Z q.2 + q.1 • V q.2) :=
      (hZ.comp continuous_snd).add (continuous_fst.smul (hV.comp continuous_snd))
    have h1 : ContinuousAt (fderiv ℝ Φ) (Z p.2 + p.1 • V p.2) :=
      ((hΦ p.1 ht p.2).fderiv_right (m := 0) (by simp)).continuousAt
    have hfd : ContinuousAt (fun q : ℝ × (Fin d → ℝ) => fderiv ℝ Φ (Z q.2 + q.1 • V q.2)) p :=
      ContinuousAt.comp (g := fderiv ℝ Φ) (f := fun q : ℝ × (Fin d → ℝ) => Z q.2 + q.1 • V q.2) h1
        hW.continuousAt
    exact hfd.clm_apply (hV.comp continuous_snd).continuousAt
  have hDI := hasDerivAt_integral_compact (F := fun t x => Φ (Z x + t • V x))
    (F' := fun t x => fderiv ℝ Φ (Z x + t • V x) (V x)) hK hε hzero hderiv hFc hF'c
  simpa using hDI

end Lightlike.Canonical

end
