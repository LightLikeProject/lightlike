import Lightlike.SpinFoam.VertexAsymptoticsHyp.HessianAssemble
import Lightlike.SpinFoam.VertexAsymptoticsHyp.HessianIff

/-!
# The kernel criterion is necessary and sufficient for the Lorentzian vertex Hessian (SF10 P2, Tier 1)

At a chart point `x` with slit-plane overlaps and `Re S x = 0`, the matrix `B = -H(x)` of the
fixed-chart Lorentzian vertex action is complex symmetric with `Re B ≥ 0`
(`lorHessian_neg_symm_psd`).  Combining with `det_ne_zero_iff_ker_of_re_psd`, the hypothesis `hker` of
`lorHessian_det_ne_zero_of_ker` is *equivalent* to `det(-H(x)) ≠ 0`
(`lorHessian_det_ne_zero_iff_ker`).  Because `Re B` is positive semidefinite, its kernel is the null
set of its quadratic form (`mulVec_re_eq_zero_iff_of_psd`), which gives the second-order form of the
criterion (`det_ne_zero_iff_quad_of_re_psd`, `lorHessian_det_ne_zero_iff_quad`).
-/

open Filter Topology Matrix
open Lightlike.Asymptotics.EPRL Lightlike.Oscillatory
open scoped ContDiff

namespace Lightlike.Asymptotics.Lorentzian

/-- For a real symmetric matrix with nonnegative quadratic form, the kernel is the null set of the
quadratic form. -/
theorem mulVec_re_eq_zero_iff_of_psd {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.transpose = B) (hpsd : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ ((B.map Complex.re) *ᵥ u))
    (v : Fin n → ℝ) :
    (B.map Complex.re) *ᵥ v = 0 ↔ v ⬝ᵥ ((B.map Complex.re) *ᵥ v) = 0 := by
  have hAs : (B.map Complex.re).transpose = B.map Complex.re := by
    ext i k
    have := congrFun (congrFun hB i) k
    simp only [Matrix.transpose_apply, Matrix.map_apply] at this ⊢
    rw [this]
  have hPSD : (B.map Complex.re).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => by simpa using hpsd x⟩
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hAs
  have := (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hPSD (x := v)).symm
  simpa using this

/-- **Second-order form of the kernel criterion**: for complex symmetric `B` with `Re B ≥ 0`,
`B` is invertible iff `Im B` is injective on the null set of the quadratic form of `Re B`. -/
theorem det_ne_zero_iff_quad_of_re_psd {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : B.transpose = B) (hpsd : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ ((B.map Complex.re) *ᵥ u)) :
    B.det ≠ 0 ↔ ∀ v : Fin n → ℝ, v ⬝ᵥ ((B.map Complex.re) *ᵥ v) = 0 →
      (B.map Complex.im) *ᵥ v = 0 → v = 0 := by
  rw [det_ne_zero_iff_ker_of_re_psd hB hpsd]
  refine forall_congr' fun v => ?_
  rw [mulVec_re_eq_zero_iff_of_psd hB hpsd v]

/-- **`-H(x)` is complex symmetric with positive semidefinite real part** at a chart point with
slit-plane overlaps and `Re S x = 0`. -/
theorem lorHessian_neg_symm_psd {j p : Fin 10 → ℝ} (hj : ∀ k, 0 ≤ j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (hl : IsLinearMap ℝ e)
    {x : Fin 44 → ℝ} (hx : x ∈ fixDomain e)
    (hPx : ∀ k, fixOverlap e g k x ∈ Complex.slitPlane)
    (hre : (lorChartAction j p g (fixVertexChart e) x).re = 0) :
    (-lorHessian j p g (fixVertexChart e) x).transpose = -lorHessian j p g (fixVertexChart e) x ∧
    ∀ u : Fin 44 → ℝ,
      0 ≤ u ⬝ᵥ (((-lorHessian j p g (fixVertexChart e) x).map Complex.re) *ᵥ u) := by
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
  show (-hessMat S x).transpose = -hessMat S x ∧ ∀ u : Fin 44 → ℝ,
      0 ≤ u ⬝ᵥ (((-hessMat S x).map Complex.re) *ᵥ u)
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_neg]
    exact congrArg Neg.neg (hessMat_isSymm_local hS2)
  · intro u
    have h := dotProduct_re_hessMat_nonpos hS2 hle u
    have hm : (-hessMat S x).map Complex.re = -((hessMat S x).map Complex.re) := by
      ext i k; simp
    rw [hm, Matrix.neg_mulVec, dotProduct_neg]
    linarith

/-- **P2 as an equivalence.** At a chart point with slit-plane overlaps and `Re S x = 0`,
`det(-H(x)) ≠ 0` holds if and only if no nonzero real vector lies in `ker Re(-H) ∩ ker Im(-H)`. -/
theorem lorHessian_det_ne_zero_iff_ker {j p : Fin 10 → ℝ} (hj : ∀ k, 0 ≤ j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (hl : IsLinearMap ℝ e)
    {x : Fin 44 → ℝ} (hx : x ∈ fixDomain e)
    (hPx : ∀ k, fixOverlap e g k x ∈ Complex.slitPlane)
    (hre : (lorChartAction j p g (fixVertexChart e) x).re = 0) :
    (-lorHessian j p g (fixVertexChart e) x).det ≠ 0 ↔
      ∀ v : Fin 44 → ℝ,
        ((-lorHessian j p g (fixVertexChart e) x).map Complex.re) *ᵥ v = 0 →
        ((-lorHessian j p g (fixVertexChart e) x).map Complex.im) *ᵥ v = 0 → v = 0 := by
  obtain ⟨hs, hp⟩ := lorHessian_neg_symm_psd hj hξ hξ' e hl hx hPx hre
  exact det_ne_zero_iff_ker_of_re_psd hs hp

/-- **Second-order form of P2.** Under the same hypotheses, `det(-H(x)) ≠ 0` iff `Im(-H)` is
injective on the null set `{v | v·Re(-H)v = 0}` of the real part's quadratic form. -/
theorem lorHessian_det_ne_zero_iff_quad {j p : Fin 10 → ℝ} (hj : ∀ k, 0 ≤ j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (hl : IsLinearMap ℝ e)
    {x : Fin 44 → ℝ} (hx : x ∈ fixDomain e)
    (hPx : ∀ k, fixOverlap e g k x ∈ Complex.slitPlane)
    (hre : (lorChartAction j p g (fixVertexChart e) x).re = 0) :
    (-lorHessian j p g (fixVertexChart e) x).det ≠ 0 ↔
      ∀ v : Fin 44 → ℝ,
        v ⬝ᵥ (((-lorHessian j p g (fixVertexChart e) x).map Complex.re) *ᵥ v) = 0 →
        ((-lorHessian j p g (fixVertexChart e) x).map Complex.im) *ᵥ v = 0 → v = 0 := by
  obtain ⟨hs, hp⟩ := lorHessian_neg_symm_psd hj hξ hξ' e hl hx hPx hre
  exact det_ne_zero_iff_quad_of_re_psd hs hp

end Lightlike.Asymptotics.Lorentzian
