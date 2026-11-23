import Lightlike.SpinFoam.VertexAsymptoticsHyp.RotatedDefect
import Lightlike.SpinFoam.VertexAsymptoticsHyp.PhaseRotation
import Lightlike.Asymptotics.Lorentzian.VertexFixChart

/-!
# `lorHessian_invertible_at_critical` fails whenever a cut configuration exists (SF10, P2 defect, T5/T6)

Let `(g, x)` satisfy all hypotheses of `lorHessian_invertible_at_critical` except that `dS x = 0` is
not assumed (only `Re S x = 0`).  If for some edge `k` and a phase `c` of modulus one the overlap
product of edge `k` of the *fixed-chart* vertex at `x` satisfies the `CutPoint` conditions
(`c · w_k(x) < 0`, nonzero transverse imaginary derivative, other edges off the cut), then the rotated
data `rotSrc g k c` satisfy *all* the hypotheses of `lorHessian_invertible_at_critical` at `x`
(including `dS x = 0`, by the junk value of `fderiv`) and yet `det(-H(x)) = 0`.  So the task statement
is false as soon as one such configuration exists; whether one exists is the (open) lemma T6.
Supporting lemma only.
-/

open Complex
open scoped ContDiff Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Asymptotics.EPRL

/-- For the fixed chart, smoothness of the chart at points of `fixDomain` is automatic: only the
overlap conditions remain. -/
theorem cutPoint_fixVertexChart (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (hl : IsLinearMap ℝ e) {x : Fin 44 → ℝ} (hx : x ∈ fixDomain e) (g : BdryData) (k : Fin 10)
    (c : ℂ)
    (hP : ∀ e', e' ≠ k → edgeOverlap g (fixVertexChart e) e' x ∈ Complex.slitPlane)
    (hre : (c * edgeOverlap g (fixVertexChart e) k x).re < 0)
    (him : (c * edgeOverlap g (fixVertexChart e) k x).im = 0)
    (hD : Complex.imCLM.comp (fderiv ℝ (fun y => c * edgeOverlap g (fixVertexChart e) k y) x) ≠ 0) :
    CutPoint g (fixVertexChart e) x k c :=
  ⟨fun b i l => (fixVertexChart_group_contDiffOn e hl b i l).contDiffAt
      ((isOpen_fixDomain e hl).mem_nhds hx),
    fun k' => (fixVertexChart_spinor_contDiff e hl k').contDiffAt, hP, hre, him, hD⟩

/-- **Defect assembly.** All hypotheses of `lorHessian_invertible_at_critical` hold for the rotated
data at `x`, but `det(-H(x)) = 0`. -/
theorem rotSrc_hypotheses_and_det_eq_zero {j p : Fin 10 → ℝ} (hj : ∀ k, 0 < j k)
    {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (hclos : ∀ (a : Fin 5) (i : Fin 3), ∑ k, ((if edgeSrc k = a then j k * spinVec (firstCol (g k 0)) i else 0) +
      (if edgeTgt k = a then j k * spinVec (firstCol (g k 1)) i else 0)) = 0)
    (hnd : ∀ (a : Fin 5) (v : Fin 3 → ℝ), (∀ k, (edgeSrc k = a → ∑ i, v i * spinVec (firstCol (g k 0)) i = 0) ∧
      (edgeTgt k = a → ∑ i, v i * spinVec (firstCol (g k 1)) i = 0)) → v = 0)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) {x : Fin 44 → ℝ}
    (hre : (lorChartAction j p g (fixVertexChart e) x).re = 0)
    {k : Fin 10} {c : ℂ} (hc : ‖c‖ = 1) (h : CutPoint g (fixVertexChart e) x k c) :
    (∀ k', ‖firstCol (rotSrc g k c k' 0)‖ = 1) ∧ (∀ k', ‖firstCol (rotSrc g k c k' 1)‖ = 1) ∧
    (∀ (a : Fin 5) (i : Fin 3), ∑ k', ((if edgeSrc k' = a then j k' * spinVec (firstCol (rotSrc g k c k' 0)) i else 0) +
      (if edgeTgt k' = a then j k' * spinVec (firstCol (rotSrc g k c k' 1)) i else 0)) = 0) ∧
    (∀ (a : Fin 5) (v : Fin 3 → ℝ), (∀ k', (edgeSrc k' = a →
        ∑ i, v i * spinVec (firstCol (rotSrc g k c k' 0)) i = 0) ∧
      (edgeTgt k' = a → ∑ i, v i * spinVec (firstCol (rotSrc g k c k' 1)) i = 0)) → v = 0) ∧
    (lorChartAction j p (rotSrc g k c) (fixVertexChart e) x).re = 0 ∧
    fderiv ℝ (lorChartAction j p (rotSrc g k c) (fixVertexChart e)) x = 0 ∧
    (-lorHessian j p (rotSrc g k c) (fixVertexChart e) x).det = 0 := by
  refine ⟨fun k' => ?_, fun k' => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_firstCol_rotSrc hc]; exact hξ k'
  · rw [norm_firstCol_rotSrc hc]; exact hξ' k'
  · intro a i
    simp only [spinVec_firstCol_rotSrc hc]
    exact hclos a i
  · intro a v hv
    simp only [spinVec_firstCol_rotSrc hc] at hv
    exact hnd a v hv
  · have := re_lorAction_rotSrc j p hc g k ((fixVertexChart e x).1) ((fixVertexChart e x).2)
    simpa only [lorChartAction] using this.trans hre
  · exact fderiv_lorChartAction_rotSrc_eq_zero j p g (hj k).ne' h
  · have := det_lorHessian_rotSrc_eq_zero (by norm_num) j p g (hj k).ne' h
    rw [Matrix.det_neg, this, mul_zero]

end Lightlike.Asymptotics.Lorentzian
