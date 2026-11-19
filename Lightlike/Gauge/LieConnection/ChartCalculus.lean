import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The derivative of conjugation in a chart (GC1, general Lie groups, attempt 2, part 2)

The calculus behind `D(Ad)_1 = ad` for a Lie group, in the chart at the identity: let `M : E × E → E` be `C²` near
`(y₀, y₀)` with `M(y₀, z) = z` and `M(y, y₀) = y` near `y₀` (the chart multiplication, `y₀` the identity), and `ι` with
`ι y₀ = y₀`, `M(y, ι y) = y₀` near `y₀` (the chart inverse). Then the derivative at `y₀` of
`y ↦ ∂_z M(M(y, z), ι y)|_{z = y₀} w` (the conjugation by the point `y`, differentiated in `z`) along `v` is
`∂_y(∂_z M(y, y₀) w) v - ∂_y(∂_z M(y, y₀) v) w`, which is the chart form of the Lie bracket `⁅v, w⁆` of the
left-invariant vector fields (`fderiv_conj_chart`).

Proof: with `D = DM(y₀, y₀)` and `D² = D²M(y₀, y₀)`: `D(0, w) = w`, `D(v, 0) = v`, `Dι = -id`, `D²((v, 0), (w, 0)) = 0`, and
the symmetry of `D²` (`IsSymmSndFDerivAt`).
-/

open Filter ContinuousLinearMap
open scoped Topology

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : E × E → E} {ι : E → E} {y₀ : E}

/-- If `M(y₀, z) = z` near `y₀`, then `DM(y₀, y₀)(0, w) = w`. -/
lemma fderiv_inr_eq (hM : DifferentiableAt ℝ M (y₀, y₀)) (h1 : ∀ᶠ z in 𝓝 y₀, M (y₀, z) = z) (w : E) :
    fderiv ℝ M (y₀, y₀) (0, w) = w := by
  have hd : HasFDerivAt (fun z => M (y₀, z)) ((fderiv ℝ M (y₀, y₀)).comp (inr ℝ E E)) y₀ :=
    hM.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right y₀ y₀)
  have hid : HasFDerivAt (fun z => M (y₀, z)) (ContinuousLinearMap.id ℝ E) y₀ :=
    (hasFDerivAt_id y₀).congr_of_eventuallyEq h1
  have := congrArg (fun L : E →L[ℝ] E => L w) (hd.unique hid)
  simpa using this

/-- If `M(y, p₂) = y` for `y` near `p₁`, then `DM(p₁, p₂)(v, 0) = v`. -/
lemma fderiv_inl_eq {p₁ p₂ : E} (hM : DifferentiableAt ℝ M (p₁, p₂)) (h2 : ∀ᶠ y in 𝓝 p₁, M (y, p₂) = y)
    (v : E) : fderiv ℝ M (p₁, p₂) (v, 0) = v := by
  have hd : HasFDerivAt (fun y => M (y, p₂)) ((fderiv ℝ M (p₁, p₂)).comp (inl ℝ E E)) p₁ :=
    hM.hasFDerivAt.comp p₁ (hasFDerivAt_prodMk_left p₁ p₂)
  have hid : HasFDerivAt (fun y => M (y, p₂)) (ContinuousLinearMap.id ℝ E) p₁ :=
    (hasFDerivAt_id p₁).congr_of_eventuallyEq h2
  have := congrArg (fun L : E →L[ℝ] E => L v) (hd.unique hid)
  simpa using this

variable (hM : ContDiffAt ℝ 2 M (y₀, y₀)) (h1 : ∀ᶠ z in 𝓝 y₀, M (y₀, z) = z)
  (h2 : ∀ᶠ y in 𝓝 y₀, M (y, y₀) = y) (hι : DifferentiableAt ℝ ι y₀) (hι0 : ι y₀ = y₀)
  (h3 : ∀ᶠ y in 𝓝 y₀, M (y, ι y) = y₀)
include hM

omit hM in
lemma eventually_differentiableAt_of_contDiffAt (hM : ContDiffAt ℝ 2 M (y₀, y₀)) :
    ∀ᶠ p in 𝓝 (y₀, y₀), DifferentiableAt ℝ M p :=
  (hM.eventually (by simp)).mono fun _ hp => hp.differentiableAt (by norm_num)

lemma differentiableAt_fderiv : DifferentiableAt ℝ (fderiv ℝ M) (y₀, y₀) :=
  (hM.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)

include h2 in
/-- `D²M((v, 0), (w, 0)) = 0`: the first partial derivative is the identity along `z = y₀`. -/
lemma snd_fderiv_inl_inl (v w : E) : fderiv ℝ (fderiv ℝ M) (y₀, y₀) (v, 0) (w, 0) = 0 := by
  have hev : ∀ᶠ y in 𝓝 y₀, fderiv ℝ M (y, y₀) (w, 0) = w := by
    have hT : Tendsto (fun y : E => (y, y₀)) (𝓝 y₀) (𝓝 (y₀, y₀)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [hT.eventually (eventually_differentiableAt_of_contDiffAt hM), h2.eventually_nhds]
      with y hy hy2
    exact fderiv_inl_eq hy hy2 w
  have hd : HasFDerivAt (fun y => fderiv ℝ M (y, y₀) (w, 0))
      (((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp (inl ℝ E E)).flip (w, 0)) y₀ := by
    have hL : HasFDerivAt (fun y => fderiv ℝ M (y, y₀))
        ((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp (inl ℝ E E)) y₀ :=
      (differentiableAt_fderiv hM).hasFDerivAt.comp (f := fun y : E => (y, y₀)) y₀ (hasFDerivAt_prodMk_left y₀ y₀)
    simpa using hL.clm_apply (hasFDerivAt_const ((w, 0) : E × E) y₀)
  have hc : HasFDerivAt (fun y => fderiv ℝ M (y, y₀) (w, 0)) (0 : E →L[ℝ] E) y₀ :=
    (hasFDerivAt_const w y₀).congr_of_eventuallyEq hev
  have := congrArg (fun L : E →L[ℝ] E => L v) (hd.unique hc)
  simpa using this

/-- The chart form of the bracket: `∂_y(∂_z M(y, y₀) w) v = D²M((v, 0), (0, w))`. -/
lemma fderiv_partial_snd (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ w) y₀ v =
      fderiv ℝ (fderiv ℝ M) (y₀, y₀) (v, 0) (0, w) := by
  have hT : Tendsto (fun y : E => (y, y₀)) (𝓝 y₀) (𝓝 (y₀, y₀)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hev : (fun y => fderiv ℝ (fun z => M (y, z)) y₀ w) =ᶠ[𝓝 y₀]
      fun y => fderiv ℝ M (y, y₀) (0, w) := by
    filter_upwards [hT.eventually (eventually_differentiableAt_of_contDiffAt hM)] with y hy
    rw [show (fun z => M (y, z)) = M ∘ Prod.mk y from rfl,
      (hy.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right y y₀)).fderiv]
    simp
  have hL : HasFDerivAt (fun y => fderiv ℝ M (y, y₀))
      ((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp (inl ℝ E E)) y₀ :=
    (differentiableAt_fderiv hM).hasFDerivAt.comp (f := fun y : E => (y, y₀)) y₀ (hasFDerivAt_prodMk_left y₀ y₀)
  have hd := hL.clm_apply (hasFDerivAt_const ((0, w) : E × E) y₀)
  rw [hev.fderiv_eq, hd.fderiv]
  simp

include h1 h2 hι hι0 h3 in
/-- The inverse in the chart has derivative `-id` at `y₀`. -/
lemma fderiv_inv_chart (v : E) : fderiv ℝ ι y₀ v = -v := by
  have hMd : HasFDerivAt M (fderiv ℝ M (y₀, y₀)) (y₀, ι y₀) := by
    rw [hι0]; exact (hM.differentiableAt (by norm_num)).hasFDerivAt
  have hd : HasFDerivAt (fun y => M (y, ι y))
      ((fderiv ℝ M (y₀, y₀)).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ι y₀))) y₀ :=
    hMd.comp y₀ ((hasFDerivAt_id y₀).prodMk hι.hasFDerivAt)
  have hc : HasFDerivAt (fun y => M (y, ι y)) (0 : E →L[ℝ] E) y₀ :=
    (hasFDerivAt_const y₀ y₀).congr_of_eventuallyEq h3
  have h := congrArg (fun L : E →L[ℝ] E => L v) (hd.unique hc)
  simp only [comp_apply, prod_apply, id_apply, zero_apply] at h
  have hsplit : ((v, fderiv ℝ ι y₀ v) : E × E) = (v, 0) + (0, fderiv ℝ ι y₀ v) := by simp
  have hD := hM.differentiableAt (by norm_num)
  rw [hsplit, map_add, fderiv_inl_eq hD h2, fderiv_inr_eq hD h1] at h
  rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
  exact h

include h1 h2 hι hι0 h3 in
/-- **The derivative of the conjugation in the chart**: along `v`, the derivative at `y₀` of
`y ↦ ∂_z M(M(y, z), ι y)|_{z = y₀} w` is `∂_y(∂_z M(y, y₀) w) v - ∂_y(∂_z M(y, y₀) v) w`. -/
theorem fderiv_conj_chart (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => M (M (y, z), ι y)) y₀ w) y₀ v =
      fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ w) y₀ v -
        fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ v) y₀ w := by
  rw [fderiv_partial_snd hM, fderiv_partial_snd hM]
  have hD := hM.differentiableAt (by norm_num)
  have hevD := eventually_differentiableAt_of_contDiffAt hM
  have hTι : Tendsto (fun y : E => (y, ι y)) (𝓝 y₀) (𝓝 (y₀, y₀)) := by
    have : ContinuousAt (fun y : E => (y, ι y)) y₀ := continuousAt_id.prodMk hι.continuousAt
    simpa [ContinuousAt, hι0] using this
  have hT0 : Tendsto (fun y : E => (y, y₀)) (𝓝 y₀) (𝓝 (y₀, y₀)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hev : (fun y => fderiv ℝ (fun z => M (M (y, z), ι y)) y₀ w) =ᶠ[𝓝 y₀]
      fun y => fderiv ℝ M (y, ι y) (fderiv ℝ M (y, y₀) (0, w), 0) := by
    filter_upwards [hTι.eventually hevD, hT0.eventually hevD, h2] with y hy1 hy2 hy3
    have hin : HasFDerivAt (fun z => M (y, z)) ((fderiv ℝ M (y, y₀)).comp (inr ℝ E E)) y₀ :=
      hy2.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right y y₀)
    have hout : HasFDerivAt M (fderiv ℝ M (y, ι y)) (M (y, y₀), ι y) := by
      rw [hy3]; exact hy1.hasFDerivAt
    have hcomp : HasFDerivAt (fun z => M (M (y, z), ι y))
        ((fderiv ℝ M (y, ι y)).comp (((fderiv ℝ M (y, y₀)).comp (inr ℝ E E)).prod 0)) y₀ :=
      hout.comp y₀ (hin.prodMk (hasFDerivAt_const (ι y) y₀))
    rw [hcomp.fderiv]
    simp
  have hL : HasFDerivAt (fun y => fderiv ℝ M (y, ι y))
      ((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ ι y₀))) y₀ := by
    have h' : HasFDerivAt (fderiv ℝ M) (fderiv ℝ (fderiv ℝ M) (y₀, y₀)) (y₀, ι y₀) := by
      rw [hι0]; exact (differentiableAt_fderiv hM).hasFDerivAt
    exact h'.comp y₀ ((hasFDerivAt_id y₀).prodMk hι.hasFDerivAt)
  have hL0 : HasFDerivAt (fun y => fderiv ℝ M (y, y₀))
      ((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp (inl ℝ E E)) y₀ :=
    (differentiableAt_fderiv hM).hasFDerivAt.comp (f := fun y : E => (y, y₀)) y₀ (hasFDerivAt_prodMk_left y₀ y₀)
  have hfin := hL.clm_apply ((hL0.clm_apply (hasFDerivAt_const ((0, w) : E × E) y₀)).prodMk
    (hasFDerivAt_const (0 : E) y₀))
  rw [hev.fderiv_eq, hfin.fderiv]
  simp only [add_apply, comp_apply, prod_apply, flip_apply, id_apply, zero_apply, inl_apply, comp_zero,
    zero_add]
  rw [hι0, fderiv_inl_eq hD h2, fderiv_inr_eq hD h1, fderiv_inv_chart hM h1 h2 hι hι0 h3]
  have hs : ((v, -v) : E × E) = (v, 0) - (0, v) := by simp
  rw [hs, map_sub, sub_apply, snd_fderiv_inl_inl hM h2 v w,
    (hM.isSymmSndFDerivAt (by simp)) (0, v) (w, 0)]
  abel

end Lightlike.Gauge
