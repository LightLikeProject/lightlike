import Lightlike.Gauge.LieConnection.LieGroupChart
import Lightlike.Gauge.LieConnection.ChartGauge

/-!
# Gauge covariance of the curvature for a general Lie group (GC1, attempt 2, part 4)

Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1: a gauge transformation `g : U → G` acts on a
local potential with values in the Lie algebra by `A' = Ad_g A - dg g⁻¹` (eq. (38), p. 30, with the right
Maurer–Cartan form `dg g⁻¹`), and the curvature transforms as `F' = Ad_g F` (eq. (64), p. 43).

Here `G` is a Lie group modelled on `𝓘(ℝ, E)` (no boundary), the Lie algebra is `GroupLieAlgebra` on its underlying
space `E`, and a potential is `A : F → F →L[ℝ] E` on a normed space `F`.
* `rightMCForm g x = d(R_{g(x)⁻¹})_{g(x)} ∘ dg(x)`, the right Maurer–Cartan form `dg g⁻¹`;
* `lieGaugeTransform g A = Ad_g ∘ A - dg g⁻¹` (eq. (38));
* `eventually_adjointE_eq`, `rightMCForm_eq_chart`: both in the chart at the identity, for `g = φ⁻¹ ∘ γ`;
* `lieCurvature_lieGaugeTransform_of_chart`: **eq. (64) at a point where `g = 1`**, from the derivative of `Ad` along
  the path and the Maurer–Cartan equation (`ChartGauge.lean`);
* `rightMCForm_mul_left`, `lieGaugeTransform_mul_left`: under `g ↦ g₀ g`, `dg g⁻¹ ↦ Ad_{g₀}(dg g⁻¹)` and
  `A' ↦ Ad_{g₀} A'`;
* `lieCurvature_lieGaugeTransform`: **eq. (64), `F' = Ad_g F`, for a `C²` gauge transformation of a general Lie
  group**, at every point (`g = g₀ · φ⁻¹(γ)` near `x₀`, with `g₀ = g(x₀)`).
-/

open Bundle Function VectorField Set Filter ContinuousLinearMap
open scoped Manifold Topology

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E G) in
/-- The multiplication in the chart at the identity as a map on `E × E`. -/
abbrev chartMulP : E × E → E := fun p => chartMul E G p.1 p.2

/-- **The right Maurer–Cartan form** of `g : F → G`, `dg g⁻¹ = d(R_{g(x)⁻¹})_{g(x)} ∘ dg(x)`, with values in the
Lie algebra (on its underlying space `E`). -/
def rightMCForm (g : F → G) (x : F) : F →L[ℝ] E :=
  (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => h * (g x)⁻¹) (g x)).comp (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) g x)

/-- **The gauge transform of a Lie-algebra-valued potential** (Svetlichny eq. (38)): `A' = Ad_g A - dg g⁻¹`. -/
def lieGaugeTransform (g : F → G) (A : F → F →L[ℝ] E) (x : F) : F →L[ℝ] E :=
  (adjointE 𝓘(ℝ, E) (g x)).comp (A x) - rightMCForm g x

/-- A manifold derivative of a map `E → G` is the derivative of the map written in the chart at its value. -/
lemma mfderiv_apply_eq_fderiv_of_model {f : E → G} {z : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) f z)
    (v : E) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f z v = fderiv ℝ (fun u => extChartAt 𝓘(ℝ, E) (f z) (f u)) z v := by
  rw [hf.mfderiv, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

/-- **The adjoint action in the chart**, as a linear map: near `y₀`, `Ad_{φ⁻¹(y)}` is the derivative at `y₀` of
`z ↦ M(M(y, z), ι y)`. -/
lemma eventually_adjointE_eq :
    ∀ᶠ y in 𝓝 (chartOne E G), adjointE 𝓘(ℝ, E) ((chart1 E G).symm y) =
      fderiv ℝ (fun z : E => chartMul E G (chartMul E G y z) (chartInv E G y)) (chartOne E G) := by
  filter_upwards [eventually_conj_eq_chartMul (E := E) (G := G)] with y hy
  ext w
  rw [← hy.fderiv_eq]
  exact adjoint_eq_fderiv_chart _ w

/-- **The right Maurer–Cartan form in the chart at the identity**: if `g = φ⁻¹ ∘ γ` near `x`, with `γ x` in the
chart target and `g(x)⁻¹` in the chart source, then `dg g⁻¹ (ξ) = ∂M(γ x, ι(γ x))(Dγ(x) ξ, 0)`. -/
lemma rightMCForm_eq_chart {g : F → G} {γ : F → E} {x : F} (hγ : DifferentiableAt ℝ γ x)
    (hg : g =ᶠ[𝓝 x] fun x => (chart1 E G).symm (γ x)) (hγt : γ x ∈ (chart1 E G).target)
    (hinv : (g x)⁻¹ ∈ (chart1 E G).source)
    (hMd : DifferentiableAt ℝ (chartMulP E G) (γ x, chartInv E G (γ x))) (ξ : F) :
    rightMCForm g x ξ = fderiv ℝ (chartMulP E G) (γ x, chartInv E G (γ x)) (fderiv ℝ γ x ξ, 0) := by
  have hgx : g x = (chart1 E G).symm (γ x) := hg.eq_of_nhds
  have hφs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G).symm (γ x) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) (x := (1 : G)) hγt
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at this
  have hγm : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) γ x := hγ.mdifferentiableAt
  have hR : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => h * (g x)⁻¹) ((chart1 E G).symm (γ x)) :=
    ((contMDiff_mul_right (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3) (G := G) (a := (g x)⁻¹)).contMDiffAt).mdifferentiableAt
      minSmoothness_three_ne_zero
  -- `dg = dφ⁻¹ ∘ Dγ`
  have h1 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) g x ξ =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G).symm (γ x) (fderiv ℝ γ x ξ : TangentSpace 𝓘(ℝ, E) (γ x)) := by
    rw [hg.mfderiv_eq, show (fun x => (chart1 E G).symm (γ x)) = (chart1 E G).symm ∘ γ from rfl,
      mfderiv_comp x hφs hγm, mfderiv_eq_fderiv]
    rfl
  -- `d(R ∘ φ⁻¹)` in the chart at `1`
  have hcomp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) ((fun h : G => h * (g x)⁻¹) ∘ (chart1 E G).symm) (γ x) :=
    hR.comp (γ x) hφs
  have h2 : ∀ p : G, p = (chart1 E G).symm (γ x) → ∀ v : E,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => h * p⁻¹) p
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G).symm (γ x) (v : TangentSpace 𝓘(ℝ, E) (γ x))) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((fun h : G => h * p⁻¹) ∘ (chart1 E G).symm) (γ x)
          (v : TangentSpace 𝓘(ℝ, E) (γ x)) := by
    intro p hp v
    subst hp
    have hRp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => h * ((chart1 E G).symm (γ x))⁻¹)
        ((chart1 E G).symm (γ x)) :=
      ((contMDiff_mul_right (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3) (G := G)
        (a := ((chart1 E G).symm (γ x))⁻¹)).contMDiffAt).mdifferentiableAt minSmoothness_three_ne_zero
    rw [mfderiv_comp (γ x) hRp hφs]
    rfl
  have hfun : (fun u => extChartAt 𝓘(ℝ, E) (((fun h : G => h * (g x)⁻¹) ∘ (chart1 E G).symm) (γ x))
      (((fun h : G => h * (g x)⁻¹) ∘ (chart1 E G).symm) u)) = fun u => chartMul E G u (chartInv E G (γ x)) := by
    funext u
    simp only [Function.comp_apply, hgx, mul_inv_cancel, chartMul, chartInv, (chart1 E G).left_inv (hgx ▸ hinv)]
  have h3' := hMd.hasFDerivAt.comp (f := fun e : E => (e, chartInv E G (γ x))) (γ x)
    (hasFDerivAt_prodMk_left (γ x) (chartInv E G (γ x)))
  have h3 : fderiv ℝ (fun u => chartMul E G u (chartInv E G (γ x))) (γ x) =
      (fderiv ℝ (chartMulP E G) (γ x, chartInv E G (γ x))).comp (inl ℝ E E) := h3'.fderiv
  show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => h * (g x)⁻¹) (g x) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) g x ξ) = _
  rw [h1, h2 (g x) hgx, mfderiv_apply_eq_fderiv_of_model hcomp, hfun, h3]
  rfl

section Covariance

variable [CompleteSpace E]

omit [CompleteSpace E] in
/-- The chart hypotheses of `ChartCalculus.lean` for the chart multiplication and inverse at the identity. -/
lemma chartMulP_contDiffAt : ContDiffAt ℝ 2 (chartMulP E G) (chartOne E G, chartOne E G) :=
  (contDiffAt_chartMul (E := E) (G := G)).of_le (by simp; norm_num)

/-- The bracket of the Lie algebra in its chart form. -/
lemma lieBr_eq_chart (u v : E) :
    lieBr 𝓘(ℝ, E) G u v =
      fderiv ℝ (fun y : E => fderiv ℝ (fun z => chartMulP E G (y, z)) (chartOne E G) v) (chartOne E G) u -
        fderiv ℝ (fun y : E => fderiv ℝ (fun z => chartMulP E G (y, z)) (chartOne E G) u) (chartOne E G) v := by
  unfold lieBr toLie
  exact bracket_eq_chart (E := E) (G := G) u v

/-- **Gauge covariance of the curvature for a general Lie group** (Svetlichny eq. (64)), at a point where the
gauge transformation is the identity: if `g = φ⁻¹ ∘ γ` near `x₀` with `γ` `C²` and `γ x₀ = φ(1)`, then the
curvature of `A' = Ad_g A - dg g⁻¹` at `x₀` is `Ad_{g(x₀)}` of the curvature of `A`. -/
theorem lieCurvature_lieGaugeTransform_of_chart {g : F → G} {γ : F → E} {A : F → F →L[ℝ] E} {x₀ : F}
    (hγ : ContDiffAt ℝ 2 γ x₀) (hγ0 : γ x₀ = chartOne E G)
    (hg : g =ᶠ[𝓝 x₀] fun x => (chart1 E G).symm (γ x)) (hA : DifferentiableAt ℝ A x₀) (η ξ : F) :
    lieCurvature 𝓘(ℝ, E) G (lieGaugeTransform g A) x₀ η ξ =
      adjointE 𝓘(ℝ, E) (g x₀) (lieCurvature 𝓘(ℝ, E) G A x₀ η ξ) := by
  -- the chart data
  have hM : ContDiffAt ℝ 2 (chartMulP E G) ((chartOne E G), (chartOne E G)) := chartMulP_contDiffAt
  have h1 : ∀ᶠ z in 𝓝 (chartOne E G), (chartMulP E G) ((chartOne E G), z) = z := eventually_chartMul_one_left (E := E) (G := G)
  have h2 : ∀ᶠ y in 𝓝 (chartOne E G), (chartMulP E G) (y, (chartOne E G)) = y := eventually_chartMul_one_right (E := E) (G := G)
  have hι : DifferentiableAt ℝ (chartInv E G) (chartOne E G) := differentiableAt_chartInv (E := E) (G := G)
  have hι0 : (chartInv E G) (chartOne E G) = (chartOne E G) := chartInv_chartOne
  have h3 : ∀ᶠ y in 𝓝 (chartOne E G), (chartMulP E G) (y, (chartInv E G) y) = (chartOne E G) := eventually_chartMul_chartInv (E := E) (G := G)
  have hD := hM.differentiableAt (by norm_num)
  have hγd : DifferentiableAt ℝ γ x₀ := hγ.differentiableAt (by norm_num)
  have hDγ : DifferentiableAt ℝ (fderiv ℝ γ) x₀ :=
    (hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hγc : Tendsto γ (𝓝 x₀) (𝓝 (chartOne E G)) := by
    have := hγd.continuousAt; rwa [ContinuousAt, hγ0] at this
  have hg0 : g x₀ = 1 := by rw [hg.eq_of_nhds, hγ0, chart1_symm_chartOne]
  -- the explicit chart form of `A'`
  let AdC : E → E →L[ℝ] E := fun y => (fderiv ℝ (chartMulP E G) (y, (chartInv E G) y)).comp ((inl ℝ E E).comp ((fderiv ℝ (chartMulP E G) (y, (chartOne E G))).comp
    (inr ℝ E E)))
  let θC : F → F →L[ℝ] E := fun x => (fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x))).comp ((inl ℝ E E).comp (fderiv ℝ γ x))
  let B : F → F →L[ℝ] E := fun x => (AdC (γ x)).comp (A x) - θC x
  have hevD := eventually_differentiableAt_of_contDiffAt hM
  have hTι : Tendsto (fun y : E => (y, (chartInv E G) y)) (𝓝 (chartOne E G)) (𝓝 ((chartOne E G), (chartOne E G))) := by
    have : ContinuousAt (fun y : E => (y, (chartInv E G) y)) (chartOne E G) := continuousAt_id.prodMk hι.continuousAt
    simpa [ContinuousAt, hι0] using this
  have hT0 : Tendsto (fun y : E => (y, (chartOne E G))) (𝓝 (chartOne E G)) (𝓝 ((chartOne E G), (chartOne E G))) :=
    (continuous_id.prodMk continuous_const).continuousAt
  -- near `(chartOne E G)`, `Ad_{φ⁻¹(y)} = AdC y`
  have hAd : ∀ᶠ y in 𝓝 (chartOne E G), adjointE 𝓘(ℝ, E) ((chart1 E G).symm y) = AdC y := by
    filter_upwards [eventually_adjointE_eq (E := E) (G := G), hTι.eventually hevD, hT0.eventually hevD, h2]
      with y hy hy1 hy2 hy3
    rw [hy]
    have hin : HasFDerivAt (fun z => (chartMulP E G) (y, z)) ((fderiv ℝ (chartMulP E G) (y, (chartOne E G))).comp (inr ℝ E E)) (chartOne E G) :=
      hy2.hasFDerivAt.comp (chartOne E G) (hasFDerivAt_prodMk_right y (chartOne E G))
    have hout : HasFDerivAt (chartMulP E G) (fderiv ℝ (chartMulP E G) (y, (chartInv E G) y)) ((chartMulP E G) (y, (chartOne E G)), (chartInv E G) y) := by rw [hy3]; exact hy1.hasFDerivAt
    have hcomp := hout.comp (chartOne E G) (hin.prodMk (hasFDerivAt_const ((chartInv E G) y) (chartOne E G)))
    have hf : fderiv ℝ (fun z : E => chartMul E G (chartMul E G y z) (chartInv E G y)) (chartOne E G) =
        (fderiv ℝ (chartMulP E G) (y, chartInv E G y)).comp
          (((fderiv ℝ (chartMulP E G) (y, chartOne E G)).comp (inr ℝ E E)).prod 0) := hcomp.fderiv
    rw [hf]
    ext w
    simp [AdC]
  -- near `x₀`, `A' = B`
  have hevγ : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 γ x := hγ.eventually (by simp)
  have hA'B : lieGaugeTransform g A =ᶠ[𝓝 x₀] B := by
    filter_upwards [hg, hg.eventuallyEq_nhds, hevγ, hγc.eventually hAd,
      hγc.eventually (target_mem_nhds_chartOne (E := E) (G := G)),
      hγc.eventually (eventually_inv_mem_source (E := E) (G := G)), hγc.eventually (hTι.eventually hevD)]
      with x hx hxn hxc hxAd hxt hxinv hxd
    ext ξ'
    simp only [lieGaugeTransform, B, sub_apply, ContinuousLinearMap.comp_apply]
    rw [hx, hxAd, rightMCForm_eq_chart (hxc.differentiableAt (by norm_num)) hxn hxt (by rw [hx]; exact hxinv) hxd]
    simp [θC]
  -- `B` is differentiable at `x₀`
  have hιγ : DifferentiableAt ℝ (fun x => (chartInv E G) (γ x)) x₀ := by
    have : DifferentiableAt ℝ (chartInv E G) (γ x₀) := by rw [hγ0]; exact hι
    exact this.comp x₀ hγd
  have hK2 : DifferentiableAt ℝ (fun x => fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x))) x₀ := by
    have h' : DifferentiableAt ℝ (fderiv ℝ (chartMulP E G)) (γ x₀, (chartInv E G) (γ x₀)) := by
      rw [hγ0, hι0]; exact differentiableAt_fderiv hM
    exact h'.comp x₀ (hγd.prodMk hιγ)
  have hK1 : DifferentiableAt ℝ (fun x => fderiv ℝ (chartMulP E G) (γ x, (chartOne E G))) x₀ := by
    have h' : DifferentiableAt ℝ (fderiv ℝ (chartMulP E G)) (γ x₀, (chartOne E G)) := by rw [hγ0]; exact differentiableAt_fderiv hM
    exact h'.comp x₀ (hγd.prodMk (differentiableAt_const (chartOne E G)))
  have hAdC : DifferentiableAt ℝ (fun x => AdC (γ x)) x₀ :=
    hK2.clm_comp ((differentiableAt_const (inl ℝ E E)).clm_comp (hK1.clm_comp (differentiableAt_const _)))
  have hθC : DifferentiableAt ℝ θC x₀ :=
    hK2.clm_comp ((differentiableAt_const (inl ℝ E E)).clm_comp hDγ)
  have hB : DifferentiableAt ℝ B x₀ := (hAdC.clm_comp hA).sub hθC
  -- the directional derivatives
  have happ : ∀ {C : F → F →L[ℝ] E}, DifferentiableAt ℝ C x₀ → ∀ u v : F,
      fderiv ℝ C x₀ u v = fderiv ℝ (fun x => C x v) x₀ u := fun hC u v => by
    rw [fderiv_clm_apply hC (differentiableAt_const v)]; simp
  have hBapp : ∀ v : F, (fun x => B x v) = fun x =>
      fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x)) (fderiv ℝ (chartMulP E G) (γ x, (chartOne E G)) (0, A x v), 0) -
        fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x)) (fderiv ℝ γ x v, 0) := fun v => by
    funext x; simp [B, AdC, θC]
  have hAv : ∀ v : F, DifferentiableAt ℝ (fun x => A x v) x₀ := fun v => hA.clm_apply (differentiableAt_const v)
  have hθv : ∀ v : F, DifferentiableAt ℝ (fun x => fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x)) (fderiv ℝ γ x v, 0)) x₀ := fun v =>
    hK2.clm_apply ((hDγ.clm_apply (differentiableAt_const v)).prodMk (differentiableAt_const 0))
  have hAdv : ∀ v : F, DifferentiableAt ℝ
      (fun x => fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x)) (fderiv ℝ (chartMulP E G) (γ x, (chartOne E G)) (0, A x v), 0)) x₀ := fun v =>
    hK2.clm_apply ((hK1.clm_apply ((differentiableAt_const 0).prodMk (hAv v))).prodMk (differentiableAt_const 0))
  have hdB : ∀ u v : F, fderiv ℝ (lieGaugeTransform g A) x₀ u v =
      fderiv ℝ A x₀ u v + lieBr 𝓘(ℝ, E) G (fderiv ℝ γ x₀ u) (A x₀ v) -
        fderiv ℝ (fun x => fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x)) (fderiv ℝ γ x v, 0)) x₀ u := by
    intro u v
    rw [hA'B.fderiv_eq, happ hB, hBapp, fderiv_fun_sub (hAdv v) (hθv v), sub_apply,
      fderiv_conjApply_explicit hM h1 h2 hι hι0 h3 hγd hγ0 (hAv v), ← happ hA, lieBr_eq_chart]
  -- the value at `x₀`
  have hval : ∀ v : F, lieGaugeTransform g A x₀ v = A x₀ v - fderiv ℝ γ x₀ v := by
    intro v
    rw [hA'B.eq_of_nhds]
    simp only [B, AdC, θC, sub_apply, ContinuousLinearMap.comp_apply, inl_apply, inr_apply, hγ0, hι0]
    rw [fderiv_inr_eq hD h1, fderiv_inl_eq hD h2, fderiv_inl_eq hD h2]
  -- assemble
  unfold lieCurvature
  rw [hdB η ξ, hdB ξ η, hval η, hval ξ, hg0, adjointE, adjoint_one]
  show _ = fderiv ℝ A x₀ η ξ - fderiv ℝ A x₀ ξ η + lieBr 𝓘(ℝ, E) G (A x₀ η) (A x₀ ξ)
  have hmc := maurerCartan_chart hM h1 h2 hι hι0 h3 hγ hγ0 η ξ
  rw [← lieBr_eq_chart] at hmc
  have hsub : ∀ a b c d : E, lieBr 𝓘(ℝ, E) G (a - b) (c - d) =
      lieBr 𝓘(ℝ, E) G a c - lieBr 𝓘(ℝ, E) G a d - lieBr 𝓘(ℝ, E) G b c + lieBr 𝓘(ℝ, E) G b d := by
    intro a b c d
    unfold lieBr
    have e1 : toLie 𝓘(ℝ, E) G (a - b) =
        (toLie 𝓘(ℝ, E) G a - toLie 𝓘(ℝ, E) G b : GroupLieAlgebra 𝓘(ℝ, E) G) := rfl
    have e2 : toLie 𝓘(ℝ, E) G (c - d) =
        (toLie 𝓘(ℝ, E) G c - toLie 𝓘(ℝ, E) G d : GroupLieAlgebra 𝓘(ℝ, E) G) := rfl
    rw [e1, e2, sub_lie, lie_sub, lie_sub]
    show (_ : GroupLieAlgebra 𝓘(ℝ, E) G) =
      (⁅toLie 𝓘(ℝ, E) G a, toLie 𝓘(ℝ, E) G c⁆ - ⁅toLie 𝓘(ℝ, E) G a, toLie 𝓘(ℝ, E) G d⁆ -
        ⁅toLie 𝓘(ℝ, E) G b, toLie 𝓘(ℝ, E) G c⁆ + ⁅toLie 𝓘(ℝ, E) G b, toLie 𝓘(ℝ, E) G d⁆ :
          GroupLieAlgebra 𝓘(ℝ, E) G)
    abel
  rw [hsub, lieBr_skew (fderiv ℝ γ x₀ ξ) (A x₀ η)]
  rw [eq_add_of_sub_eq hmc]
  abel
/-- The gauge transform is differentiable at `x₀` (through its chart form). -/
lemma differentiableAt_lieGaugeTransform_of_chart {g : F → G} {γ : F → E} {A : F → F →L[ℝ] E} {x₀ : F}
    (hγ : ContDiffAt ℝ 2 γ x₀) (hγ0 : γ x₀ = chartOne E G)
    (hg : g =ᶠ[𝓝 x₀] fun x => (chart1 E G).symm (γ x)) (hA : DifferentiableAt ℝ A x₀) :
    DifferentiableAt ℝ (lieGaugeTransform g A) x₀ := by
  -- the chart data
  have hM : ContDiffAt ℝ 2 (chartMulP E G) ((chartOne E G), (chartOne E G)) := chartMulP_contDiffAt
  have h1 : ∀ᶠ z in 𝓝 (chartOne E G), (chartMulP E G) ((chartOne E G), z) = z := eventually_chartMul_one_left (E := E) (G := G)
  have h2 : ∀ᶠ y in 𝓝 (chartOne E G), (chartMulP E G) (y, (chartOne E G)) = y := eventually_chartMul_one_right (E := E) (G := G)
  have hι : DifferentiableAt ℝ (chartInv E G) (chartOne E G) := differentiableAt_chartInv (E := E) (G := G)
  have hι0 : (chartInv E G) (chartOne E G) = (chartOne E G) := chartInv_chartOne
  have h3 : ∀ᶠ y in 𝓝 (chartOne E G), (chartMulP E G) (y, (chartInv E G) y) = (chartOne E G) := eventually_chartMul_chartInv (E := E) (G := G)
  have hD := hM.differentiableAt (by norm_num)
  have hγd : DifferentiableAt ℝ γ x₀ := hγ.differentiableAt (by norm_num)
  have hDγ : DifferentiableAt ℝ (fderiv ℝ γ) x₀ :=
    (hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hγc : Tendsto γ (𝓝 x₀) (𝓝 (chartOne E G)) := by
    have := hγd.continuousAt; rwa [ContinuousAt, hγ0] at this
  have hg0 : g x₀ = 1 := by rw [hg.eq_of_nhds, hγ0, chart1_symm_chartOne]
  -- the explicit chart form of `A'`
  let AdC : E → E →L[ℝ] E := fun y => (fderiv ℝ (chartMulP E G) (y, (chartInv E G) y)).comp ((inl ℝ E E).comp ((fderiv ℝ (chartMulP E G) (y, (chartOne E G))).comp
    (inr ℝ E E)))
  let θC : F → F →L[ℝ] E := fun x => (fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x))).comp ((inl ℝ E E).comp (fderiv ℝ γ x))
  let B : F → F →L[ℝ] E := fun x => (AdC (γ x)).comp (A x) - θC x
  have hevD := eventually_differentiableAt_of_contDiffAt hM
  have hTι : Tendsto (fun y : E => (y, (chartInv E G) y)) (𝓝 (chartOne E G)) (𝓝 ((chartOne E G), (chartOne E G))) := by
    have : ContinuousAt (fun y : E => (y, (chartInv E G) y)) (chartOne E G) := continuousAt_id.prodMk hι.continuousAt
    simpa [ContinuousAt, hι0] using this
  have hT0 : Tendsto (fun y : E => (y, (chartOne E G))) (𝓝 (chartOne E G)) (𝓝 ((chartOne E G), (chartOne E G))) :=
    (continuous_id.prodMk continuous_const).continuousAt
  -- near `(chartOne E G)`, `Ad_{φ⁻¹(y)} = AdC y`
  have hAd : ∀ᶠ y in 𝓝 (chartOne E G), adjointE 𝓘(ℝ, E) ((chart1 E G).symm y) = AdC y := by
    filter_upwards [eventually_adjointE_eq (E := E) (G := G), hTι.eventually hevD, hT0.eventually hevD, h2]
      with y hy hy1 hy2 hy3
    rw [hy]
    have hin : HasFDerivAt (fun z => (chartMulP E G) (y, z)) ((fderiv ℝ (chartMulP E G) (y, (chartOne E G))).comp (inr ℝ E E)) (chartOne E G) :=
      hy2.hasFDerivAt.comp (chartOne E G) (hasFDerivAt_prodMk_right y (chartOne E G))
    have hout : HasFDerivAt (chartMulP E G) (fderiv ℝ (chartMulP E G) (y, (chartInv E G) y)) ((chartMulP E G) (y, (chartOne E G)), (chartInv E G) y) := by rw [hy3]; exact hy1.hasFDerivAt
    have hcomp := hout.comp (chartOne E G) (hin.prodMk (hasFDerivAt_const ((chartInv E G) y) (chartOne E G)))
    have hf : fderiv ℝ (fun z : E => chartMul E G (chartMul E G y z) (chartInv E G y)) (chartOne E G) =
        (fderiv ℝ (chartMulP E G) (y, chartInv E G y)).comp
          (((fderiv ℝ (chartMulP E G) (y, chartOne E G)).comp (inr ℝ E E)).prod 0) := hcomp.fderiv
    rw [hf]
    ext w
    simp [AdC]
  -- near `x₀`, `A' = B`
  have hevγ : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 γ x := hγ.eventually (by simp)
  have hA'B : lieGaugeTransform g A =ᶠ[𝓝 x₀] B := by
    filter_upwards [hg, hg.eventuallyEq_nhds, hevγ, hγc.eventually hAd,
      hγc.eventually (target_mem_nhds_chartOne (E := E) (G := G)),
      hγc.eventually (eventually_inv_mem_source (E := E) (G := G)), hγc.eventually (hTι.eventually hevD)]
      with x hx hxn hxc hxAd hxt hxinv hxd
    ext ξ'
    simp only [lieGaugeTransform, B, sub_apply, ContinuousLinearMap.comp_apply]
    rw [hx, hxAd, rightMCForm_eq_chart (hxc.differentiableAt (by norm_num)) hxn hxt (by rw [hx]; exact hxinv) hxd]
    simp [θC]
  -- `B` is differentiable at `x₀`
  have hιγ : DifferentiableAt ℝ (fun x => (chartInv E G) (γ x)) x₀ := by
    have : DifferentiableAt ℝ (chartInv E G) (γ x₀) := by rw [hγ0]; exact hι
    exact this.comp x₀ hγd
  have hK2 : DifferentiableAt ℝ (fun x => fderiv ℝ (chartMulP E G) (γ x, (chartInv E G) (γ x))) x₀ := by
    have h' : DifferentiableAt ℝ (fderiv ℝ (chartMulP E G)) (γ x₀, (chartInv E G) (γ x₀)) := by
      rw [hγ0, hι0]; exact differentiableAt_fderiv hM
    exact h'.comp x₀ (hγd.prodMk hιγ)
  have hK1 : DifferentiableAt ℝ (fun x => fderiv ℝ (chartMulP E G) (γ x, (chartOne E G))) x₀ := by
    have h' : DifferentiableAt ℝ (fderiv ℝ (chartMulP E G)) (γ x₀, (chartOne E G)) := by rw [hγ0]; exact differentiableAt_fderiv hM
    exact h'.comp x₀ (hγd.prodMk (differentiableAt_const (chartOne E G)))
  have hAdC : DifferentiableAt ℝ (fun x => AdC (γ x)) x₀ :=
    hK2.clm_comp ((differentiableAt_const (inl ℝ E E)).clm_comp (hK1.clm_comp (differentiableAt_const _)))
  have hθC : DifferentiableAt ℝ θC x₀ :=
    hK2.clm_comp ((differentiableAt_const (inl ℝ E E)).clm_comp hDγ)
  have hB : DifferentiableAt ℝ B x₀ := (hAdC.clm_comp hA).sub hθC
  exact hB.congr_of_eventuallyEq hA'B

omit [CompleteSpace E] in
/-- **The right Maurer–Cartan form under a left translation**: `d(g₀ h)(g₀ h)⁻¹ = Ad_{g₀}(dh h⁻¹)`. -/
lemma rightMCForm_mul_left (g₀ : G) {h : F → G} {x : F} (hh : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) h x) (ξ : F) :
    rightMCForm (fun y => g₀ * h y) x ξ = adjointE 𝓘(ℝ, E) g₀ (rightMCForm h x ξ) := by
  have hL : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun k : G => g₀ * k) (h x) := mdifferentiableAt_mul_left' g₀ (h x)
  have hRg : ∀ a b : G, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun k : G => k * a) b := fun a b =>
    ((contMDiff_mul_right (I := 𝓘(ℝ, E)) (n := minSmoothness ℝ 3) (G := G) (a := a)).contMDiffAt).mdifferentiableAt
      minSmoothness_three_ne_zero
  have hfun : (fun k : G => k * (g₀ * h x)⁻¹) ∘ (fun k : G => g₀ * k) =
      conjMap g₀ ∘ (fun k : G => k * (h x)⁻¹) := by
    funext k; simp [conjMap, mul_assoc]
  -- the three chain rules, applied
  have e1 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ((fun k : G => g₀ * k) ∘ h) x (ξ : TangentSpace 𝓘(ℝ, F) x) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun k : G => g₀ * k) (h x)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) h x (ξ : TangentSpace 𝓘(ℝ, F) x)) := by
    rw [mfderiv_comp x hL hh]; rfl
  have e2 : ∀ v : TangentSpace 𝓘(ℝ, E) (h x), mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun k : G => k * (g₀ * h x)⁻¹) (g₀ * h x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun k : G => g₀ * k) (h x) v) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((fun k : G => k * (g₀ * h x)⁻¹) ∘ (fun k : G => g₀ * k)) (h x) v := by
    intro v; rw [mfderiv_comp (h x) (hRg _ _) hL]; rfl
  have e3 : ∀ v : TangentSpace 𝓘(ℝ, E) (h x),
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (conjMap g₀ ∘ (fun k : G => k * (h x)⁻¹)) (h x) v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (conjMap g₀) (h x * (h x)⁻¹)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun k : G => k * (h x)⁻¹) (h x) v) := by
    intro v; rw [mfderiv_comp (h x) (mdifferentiableAt_conjMap g₀ _) (hRg _ _)]; rfl
  have e4 : ∀ q : G, q = 1 → ∀ v : TangentSpace 𝓘(ℝ, E) q,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (conjMap g₀) q v = adjointE 𝓘(ℝ, E) g₀ v := by
    rintro q rfl v; rfl
  show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun k : G => k * (g₀ * h x)⁻¹) (g₀ * h x)
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ((fun k : G => g₀ * k) ∘ h) x (ξ : TangentSpace 𝓘(ℝ, F) x)) = _
  rw [e1, e2, hfun, e3, e4 _ (mul_inv_cancel (h x))]
  rfl

omit [CompleteSpace E] in
/-- **The gauge transform under a left translation**: `(g₀ h)·A = Ad_{g₀} ∘ (h·A)`. -/
lemma lieGaugeTransform_mul_left (g₀ : G) {h : F → G} (A : F → F →L[ℝ] E) {x : F}
    (hh : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) h x) :
    lieGaugeTransform (fun y => g₀ * h y) A x = (adjointE 𝓘(ℝ, E) g₀).comp (lieGaugeTransform h A x) := by
  ext ξ
  simp only [lieGaugeTransform, sub_apply, ContinuousLinearMap.comp_apply, map_sub]
  rw [rightMCForm_mul_left g₀ hh ξ, adjointE, adjointE, adjointE, adjoint_mul]
  rfl

/-- **Gauge covariance of the curvature for a general Lie group** (Svetlichny eq. (64)): if near `x₀` the gauge
transformation is `g = g₀ · φ⁻¹(γ)` with `γ` `C²` and `γ x₀ = φ(1)` (any `C²` gauge transformation, with
`g₀ = g(x₀)`, written in the chart at the identity), then the curvature of `A' = Ad_g A - dg g⁻¹` at `x₀` is
`Ad_{g(x₀)}` of the curvature of `A`. -/
theorem lieCurvature_lieGaugeTransform {g : F → G} {g₀ : G} {γ : F → E} {A : F → F →L[ℝ] E} {x₀ : F}
    (hγ : ContDiffAt ℝ 2 γ x₀) (hγ0 : γ x₀ = chartOne E G)
    (hg : g =ᶠ[𝓝 x₀] fun x => g₀ * (chart1 E G).symm (γ x)) (hA : DifferentiableAt ℝ A x₀) (η ξ : F) :
    lieCurvature 𝓘(ℝ, E) G (lieGaugeTransform g A) x₀ η ξ =
      adjointE 𝓘(ℝ, E) (g x₀) (lieCurvature 𝓘(ℝ, E) G A x₀ η ξ) := by
  set h : F → G := fun x => (chart1 E G).symm (γ x) with hhdef
  have hγc : Tendsto γ (𝓝 x₀) (𝓝 (chartOne E G)) := by
    have := (hγ.differentiableAt (by norm_num)).continuousAt; rwa [ContinuousAt, hγ0] at this
  have hevγ : ∀ᶠ x in 𝓝 x₀, ContDiffAt ℝ 2 γ x := hγ.eventually (by simp)
  -- `h` is differentiable near `x₀`
  have hhd : ∀ᶠ x in 𝓝 x₀, MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, E) h x := by
    filter_upwards [hevγ, hγc.eventually (target_mem_nhds_chartOne (E := E) (G := G))] with x hx hxt
    have hφs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (chart1 E G).symm (γ x) := by
      have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, E)) (x := (1 : G)) hxt
      rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at this
    exact hφs.comp x (hx.differentiableAt (by norm_num)).mdifferentiableAt
  -- near `x₀`, `A'_g = Ad_{g₀} ∘ A'_h`
  have hev : lieGaugeTransform g A =ᶠ[𝓝 x₀] fun x => (adjointE 𝓘(ℝ, E) g₀).comp (lieGaugeTransform h A x) := by
    filter_upwards [hg.eventuallyEq_nhds, hhd] with x hxn hxd
    have e : lieGaugeTransform g A x = lieGaugeTransform (fun y => g₀ * h y) A x := by
      ext ξ'
      simp only [lieGaugeTransform, rightMCForm, sub_apply, ContinuousLinearMap.comp_apply]
      rw [hxn.eq_of_nhds, hxn.mfderiv_eq]
      rfl
    rw [e, lieGaugeTransform_mul_left g₀ A hxd]
  have hdh : DifferentiableAt ℝ (lieGaugeTransform h A) x₀ :=
    differentiableAt_lieGaugeTransform_of_chart hγ hγ0 (Filter.EventuallyEq.refl _ _) hA
  have hcurv : lieCurvature 𝓘(ℝ, E) G (lieGaugeTransform g A) x₀ η ξ =
      lieCurvature 𝓘(ℝ, E) G (fun x => (adjointE 𝓘(ℝ, E) g₀).comp (lieGaugeTransform h A x)) x₀ η ξ := by
    unfold lieCurvature
    rw [hev.fderiv_eq, hev.eq_of_nhds]
  rw [hcurv, lieCurvature_adjoint g₀ hdh,
    lieCurvature_lieGaugeTransform_of_chart hγ hγ0 (Filter.EventuallyEq.refl _ _) hA, hg.eq_of_nhds]
  have hid : adjointE 𝓘(ℝ, E) (1 : G) = ContinuousLinearMap.id ℝ E := adjoint_one
  rw [show (chart1 E G).symm (γ x₀) = 1 by rw [hγ0, chart1_symm_chartOne], hid, mul_one]
  rfl

end Covariance

end Lightlike.Gauge
