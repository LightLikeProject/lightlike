import Lightlike.SpinFoam.VertexAsymptoticsHyp.RotatedAction

/-!
# Degenerate Hessian for rotated boundary data (SF10, P2 defect, T5, part 2)

If the overlap product of edge `k`, multiplied by the phase `c`, is a negative real number at a chart
point `a` and its imaginary part has nonzero differential there (and the other edges are off the
cut), then for the boundary data `rotSrc g k c` the chart action is not differentiable at `a`
(so `fderiv = 0` holds by the junk value of `fderiv`), has the same `Re S` as for `g`, and its
Hessian matrix is singular.  Together with `PhaseRotation` (closure, nondegeneracy, unit norms are
unchanged) this shows that `lorHessian_invertible_at_critical` fails as stated as soon as one
configuration `(g, x)` with `Re S(x) = 0` and these nondegeneracy conditions exists.
Supporting lemmas only.
-/

open Complex
open scoped ContDiff Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Asymptotics.EPRL
open Lightlike.Lorentz (SL2C)
open Lightlike.SpinFoam.CutAssemble Lightlike.SpinFoam.CutNondiff

/-- The hypotheses on the cut point, bundled. -/
structure CutPoint {n : ℕ} (g : BdryData) (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor))
    (a : Fin n → ℝ) (k : Fin 10) (c : ℂ) : Prop where
  hX : ∀ b i l, ContDiffAt ℝ ∞ (fun x => ((chart x).1 b : Matrix (Fin 2) (Fin 2) ℂ) i l) a
  hz : ∀ e, ContDiffAt ℝ ∞ (fun x => (chart x).2 e) a
  hP : ∀ e, e ≠ k → edgeOverlap g chart e a ∈ Complex.slitPlane
  hre : (c * edgeOverlap g chart k a).re < 0
  him : (c * edgeOverlap g chart k a).im = 0
  hD : Complex.imCLM.comp (fderiv ℝ (fun y => c * edgeOverlap g chart k y) a) ≠ 0

/-- `Z` and `Z'` of the cut edge are nonzero. -/
theorem CutPoint.ne_zero {n : ℕ} {g : BdryData}
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)} {a : Fin n → ℝ} {k : Fin 10}
    {c : ℂ} (h : CutPoint g chart a k c) : edgeZs chart k a ≠ 0 ∧ edgeZt chart k a ≠ 0 := by
  have hne : edgeOverlap g chart k a ≠ 0 := by
    intro h0
    have := h.hre
    rw [h0, mul_zero] at this
    simp at this
  exact ⟨fun h0 => left_ne_zero_of_mul hne (by rw [h0]; simp),
    fun h0 => right_ne_zero_of_mul hne (by rw [h0]; simp)⟩

/-- **The Hessian of the rotated data is singular at a cut point.** -/
theorem det_lorHessian_rotSrc_eq_zero {n : ℕ} (hn : 2 ≤ n) (j p : Fin 10 → ℝ) (g : BdryData)
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)} {a : Fin n → ℝ} {k : Fin 10}
    {c : ℂ} (hjk : j k ≠ 0) (h : CutPoint g chart a k c) :
    (lorHessian j p (rotSrc g k c) chart a).det = 0 := by
  have hw := contDiffAt_edgeOverlap g h.hX h.hz k
  have hf : ContDiffAt ℝ 1 (fun y => c * edgeOverlap g chart k y) a :=
    (contDiffAt_const.mul hw).of_le (by exact_mod_cast le_top)
  have hR : ContDiffAt ℝ 1 (rotRemainder j p g chart k) a :=
    (contDiffAt_rotRemainder j p g k h.hX h.hz h.ne_zero.1 h.ne_zero.2 h.hP).of_le
      (by exact_mod_cast le_top)
  exact det_hessMat_eq_zero_of_log_cut hn (lam := ((2 * j k : ℝ) : ℂ))
    (by simpa using hjk) (lorChartAction_rotSrc_eq j p g k c chart) hf hR h.hre h.him h.hD

/-- **The rotated action is not differentiable at a cut point**, so `fderiv = 0` there by the junk
value, i.e. the critical-point hypothesis `dS = 0` of `lorHessian_invertible_at_critical` holds
trivially. -/
theorem fderiv_lorChartAction_rotSrc_eq_zero {n : ℕ} (j p : Fin 10 → ℝ) (g : BdryData)
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)} {a : Fin n → ℝ} {k : Fin 10}
    {c : ℂ} (hjk : j k ≠ 0) (h : CutPoint g chart a k c) :
    fderiv ℝ (lorChartAction j p (rotSrc g k c) chart) a = 0 := by
  apply fderiv_zero_of_not_differentiableAt
  have hw := contDiffAt_edgeOverlap g h.hX h.hz k
  have hf : ContDiffAt ℝ 1 (fun y => c * edgeOverlap g chart k y) a :=
    (contDiffAt_const.mul hw).of_le (by exact_mod_cast le_top)
  have hR : ContDiffAt ℝ ∞ (rotRemainder j p g chart k) a :=
    contDiffAt_rotRemainder j p g k h.hX h.hz h.ne_zero.1 h.ne_zero.2 h.hP
  exact not_differentiableAt_of_cut (lam := ((2 * j k : ℝ) : ℂ)) (by simpa using hjk)
    (lorChartAction_rotSrc_eq j p g k c chart) (hf.differentiableAt one_ne_zero).hasFDerivAt
    hR.continuousAt h.hre h.him h.hD

end Lightlike.Asymptotics.Lorentzian
