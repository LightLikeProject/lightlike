import Lightlike.Asymptotics.Lorentzian.VertexFixChart
import Lightlike.SpinFoam.VertexAsymptoticsHyp.HessianKernel
import Lightlike.SpinFoam.VertexAsymptoticsHyp.HessianSecondOrder

/-!
# Assembly of route 1 of task T-SF10-P2 for the Lorentzian vertex action

For the fixed-chart vertex action `S = lorChartAction j p g (fixVertexChart e)` and a point `x` of the
chart domain at which the overlap products `⟨Z,ξ⟩⟨Jξ',Z'⟩` lie in the slit plane, `S` is smooth near `x`
and `Re S ≤ 0` near `x`. With `Re S x = 0`, `dS x = 0`, the matrix `-H(x)` is complex symmetric with
positive semidefinite real part, so `det(-H(x)) ≠ 0` follows from the geometric statement `hker`
(`Im(-H)` injective on `ker Re(-H)`), which is the only part left open
(`lorHessian_det_ne_zero_of_ker`).

The slit-plane hypothesis at `x` is not part of the task statement T-SF10-P2: without it `S` need not be
differentiable at `x` (the principal logarithm jumps on the cut, and `fderiv` and `hessMat` then take
their junk value `0`).
-/

open Filter Topology Matrix
open Lightlike.Asymptotics.EPRL Lightlike.Oscillatory
open scoped ContDiff

namespace Lightlike.Asymptotics.Lorentzian

/-- The overlap product `⟨Z,ξ⟩⟨Jξ',Z'⟩` of edge `k` in the fixed charts (the argument of the
logarithm in `triAction`). -/
noncomputable def fixOverlap (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (g : BdryData) (k : Fin 10) (y : Fin 44 → ℝ) : ℂ :=
  inner ℂ (spinAct ((fixVertexChart e y).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      ((fixVertexChart e y).2 k)) (firstCol (g k 0)) *
    inner ℂ (jMap (firstCol (g k 1)))
      (spinAct ((fixVertexChart e y).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        ((fixVertexChart e y).2 k))

/-- The overlap product is smooth on the chart domain. -/
theorem fixOverlap_contDiffAt (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : IsLinearMap ℝ e) (g : BdryData) (k : Fin 10) {x : Fin 44 → ℝ} (hx : x ∈ fixDomain e) :
    ContDiffAt ℝ ∞ (fixOverlap e g k) x := by
  have hxn : fixDomain e ∈ 𝓝 x := (isOpen_fixDomain e he).mem_nhds hx
  have hM : ∀ a i k', ContDiffAt ℝ ∞
      (fun y => (((fixVertexChart e y).1 a : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) i k') x := by
    intro a i k'
    have := Complex.conjCLE.contDiff.contDiffAt.comp x
      ((fixVertexChart_group_contDiffOn e he a k' i).contDiffAt hxn)
    simpa [Function.comp_def, Matrix.conjTranspose_apply] using this
  have hz : ContDiffAt ℝ ∞ (fun y => (fixVertexChart e y).2 k) x :=
    (fixVertexChart_spinor_contDiff e he k).contDiffAt
  have hZs := contDiffAt_spinAct (hM (edgeSrc k)) hz
  have hZt := contDiffAt_spinAct (hM (edgeTgt k)) hz
  have hi1 := (contDiff_inner_left_spinor (firstCol (g k 0))).contDiffAt.comp x hZs
  have hi2 := (contDiff_inner_right_spinor (jMap (firstCol (g k 1)))).contDiffAt.comp x hZt
  unfold fixOverlap
  exact hi1.mul hi2

/-- A product of overlaps in the slit plane forces both spinors and both overlaps to be nonzero. -/
theorem overlap_facts {Z Z' ξ ξ' : Spinor}
    (h : inner ℂ Z ξ * inner ℂ (jMap ξ') Z' ∈ Complex.slitPlane) :
    Z ≠ 0 ∧ Z' ≠ 0 ∧ inner ℂ Z ξ ≠ 0 ∧ inner ℂ (jMap ξ') Z' ≠ 0 := by
  have hne := Complex.slitPlane_ne_zero h
  have h1 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  exact ⟨fun h0 => h1 (by rw [h0]; simp), fun h0 => h2 (by rw [h0]; simp), h1, h2⟩

/-- **P2 modulo the geometric kernel statement.** Let `x` be in the chart domain with all overlap
products in the slit plane, `Re S x = 0` and `dS x = 0`. If no nonzero real vector lies in the kernels
of both `Re(-H(x))` and `Im(-H(x))`, then `det(-H(x)) ≠ 0`. -/
theorem lorHessian_det_ne_zero_of_ker {j p : Fin 10 → ℝ} (hj : ∀ k, 0 ≤ j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (hl : IsLinearMap ℝ e)
    {x : Fin 44 → ℝ} (hx : x ∈ fixDomain e)
    (hPx : ∀ k, fixOverlap e g k x ∈ Complex.slitPlane)
    (hre : (lorChartAction j p g (fixVertexChart e) x).re = 0)
    (hker : ∀ v : Fin 44 → ℝ,
      ((-lorHessian j p g (fixVertexChart e) x).map Complex.re) *ᵥ v = 0 →
      ((-lorHessian j p g (fixVertexChart e) x).map Complex.im) *ᵥ v = 0 → v = 0) :
    (-lorHessian j p g (fixVertexChart e) x).det ≠ 0 := by
  set S := lorChartAction j p g (fixVertexChart e) with hS
  have hev : ∀ᶠ y in 𝓝 x, y ∈ fixDomain e ∧ ∀ k, fixOverlap e g k y ∈ Complex.slitPlane := by
    refine Filter.Eventually.and ((isOpen_fixDomain e hl).mem_nhds hx) ?_
    rw [Filter.eventually_all]
    intro k
    exact (fixOverlap_contDiffAt e hl g k hx).continuousAt.eventually_mem
      (Complex.isOpen_slitPlane.mem_nhds (hPx k))
  obtain ⟨U, hUsub, hUopen, hxU⟩ := eventually_nhds_iff.mp hev
  have hSU : ContDiffOn ℝ ∞ S U :=
    lorChartAction_fixVertexChart_contDiffOn e hl j p g hUopen (fun y hy => (hUsub y hy).1)
      (fun y hy k => (hUsub y hy).2 k)
  have hS2 : ContDiffAt ℝ 2 S x :=
    (hSU.contDiffAt (hUopen.mem_nhds hxU)).of_le (by simp)
  have hle : ∀ᶠ y in 𝓝 x, (S y).re ≤ (S x).re := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    rw [hre]
    have hP := (hUsub y hy).2
    refine re_lorAction_le_zero hj ?_ ?_ hξ hξ' ?_ ?_
    · exact fun k => (overlap_facts (hP k)).1
    · exact fun k => (overlap_facts (hP k)).2.1
    · exact fun k => (overlap_facts (hP k)).2.2.1
    · exact fun k => (overlap_facts (hP k)).2.2.2
  show (-hessMat S x).det ≠ 0
  refine det_ne_zero_of_re_psd_ker ?_ ?_ hker
  · rw [Matrix.transpose_neg]
    exact congrArg Neg.neg (hessMat_isSymm_local hS2)
  · intro u
    have h := dotProduct_re_hessMat_nonpos hS2 hle u
    have hm : (-hessMat S x).map Complex.re = -((hessMat S x).map Complex.re) := by
      ext i k; simp
    rw [hm, Matrix.neg_mulVec, dotProduct_neg]
    linarith

end Lightlike.Asymptotics.Lorentzian
