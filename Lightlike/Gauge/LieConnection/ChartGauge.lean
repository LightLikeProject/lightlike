import Lightlike.Gauge.LieConnection.ChartCalculus

/-!
# The Maurer–Cartan equation in a chart (GC1, general Lie groups, attempt 2, part 3)

The setting of `ChartCalculus.lean`: `M : E × E → E` is `C²` near `(y₀, y₀)` with `M(y₀, z) = z`, `M(y, y₀) = y`
and `M(y, ι y) = y₀` near `y₀` (the multiplication and the inverse of a Lie group in the chart at the identity).
For a `C²` path of group elements written in the chart, `γ : F → E` with `γ x₀ = y₀`, the right Maurer–Cartan form
`θ = dg g⁻¹` is, in the chart, `θ(x)(ξ) = ∂₁M(γ x, ι(γ x))(Dγ(x) ξ)` (the derivative of the right translation by
`g(x)⁻¹` at `g(x)`).

* `fderiv_conjApply_chart`: **the derivative of the adjoint action along the path**: the derivative at `x₀` of
  `x ↦ Ad_{g(x)} a(x)` along `η` is `Da(η) + ⁅Dγ η, a x₀⁆`;
* `maurerCartan_chart`: **the Maurer–Cartan equation at `x₀`**: `∂_η θ(ξ) - ∂_ξ θ(η) = ⁅θ(η), θ(ξ)⁆`, where
  `θ(x₀) = Dγ(x₀)` and the bracket is the chart form `⁅u, v⁆ = ∂_y(∂_z M(y, y₀) v) u - ∂_y(∂_z M(y, y₀) u) v` of
  `bracket_eq_chart`. The second derivative of `γ` cancels by its symmetry, `∂₁∂₁M(·, y₀) = 0`, `Dι = -id`, and the
  mixed partials of `M` are symmetric.
-/

open Filter ContinuousLinearMap
open scoped Topology

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {M : E × E → E} {ι : E → E} {y₀ : E}

variable (hM : ContDiffAt ℝ 2 M (y₀, y₀)) (h1 : ∀ᶠ z in 𝓝 y₀, M (y₀, z) = z)
  (h2 : ∀ᶠ y in 𝓝 y₀, M (y, y₀) = y) (hι : DifferentiableAt ℝ ι y₀) (hι0 : ι y₀ = y₀)
  (h3 : ∀ᶠ y in 𝓝 y₀, M (y, ι y) = y₀)

include hM hι hι0 in
/-- The derivative of `x ↦ ∂M(γ x, ι(γ x))(Dγ(x) ξ, 0)` at `x₀` along `η`. -/
lemma fderiv_rightMC_chart {γ : F → E} {x₀ : F} (hγ : ContDiffAt ℝ 2 γ x₀) (hγ0 : γ x₀ = y₀) (η ξ : F) :
    fderiv ℝ (fun x => fderiv ℝ M (γ x, ι (γ x)) (fderiv ℝ γ x ξ, 0)) x₀ η =
      fderiv ℝ (fderiv ℝ M) (y₀, y₀) (fderiv ℝ γ x₀ η, fderiv ℝ ι y₀ (fderiv ℝ γ x₀ η)) (fderiv ℝ γ x₀ ξ, 0) +
        fderiv ℝ M (y₀, y₀) (fderiv ℝ (fderiv ℝ γ) x₀ η ξ, 0) := by
  have hγd : DifferentiableAt ℝ γ x₀ := hγ.differentiableAt (by norm_num)
  have hDγ : DifferentiableAt ℝ (fderiv ℝ γ) x₀ :=
    (hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hιγ : HasFDerivAt (fun x => ι (γ x)) ((fderiv ℝ ι y₀).comp (fderiv ℝ γ x₀)) x₀ := by
    have : HasFDerivAt ι (fderiv ℝ ι y₀) (γ x₀) := by rw [hγ0]; exact hι.hasFDerivAt
    exact this.comp x₀ hγd.hasFDerivAt
  have hpair : HasFDerivAt (fun x => (γ x, ι (γ x))) ((fderiv ℝ γ x₀).prod ((fderiv ℝ ι y₀).comp (fderiv ℝ γ x₀)))
      x₀ := hγd.hasFDerivAt.prodMk hιγ
  have hK : HasFDerivAt (fun x => fderiv ℝ M (γ x, ι (γ x)))
      ((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp
        ((fderiv ℝ γ x₀).prod ((fderiv ℝ ι y₀).comp (fderiv ℝ γ x₀)))) x₀ := by
    have h' : HasFDerivAt (fderiv ℝ M) (fderiv ℝ (fderiv ℝ M) (y₀, y₀)) (γ x₀, ι (γ x₀)) := by
      rw [hγ0, hι0]; exact (differentiableAt_fderiv hM).hasFDerivAt
    exact h'.comp x₀ hpair
  have hw := (hDγ.hasFDerivAt.clm_apply (hasFDerivAt_const ξ x₀)).prodMk (hasFDerivAt_const (0 : E) x₀)
  rw [(hK.clm_apply hw).fderiv]
  simp only [add_apply, comp_apply, prod_apply, flip_apply, zero_apply, comp_zero, zero_add, add_zero, hγ0, hι0]
  abel

include hM h1 h2 hι hι0 h3 in
/-- **The Maurer–Cartan equation in the chart at the identity**: for the right Maurer–Cartan form
`θ(x)(ξ) = ∂M(γ x, ι(γ x))(Dγ(x) ξ, 0)` of a `C²` path with `γ x₀ = y₀`,
`∂_η θ(ξ) - ∂_ξ θ(η) = ⁅Dγ η, Dγ ξ⁆` in the chart form of the bracket. -/
theorem maurerCartan_chart {γ : F → E} {x₀ : F} (hγ : ContDiffAt ℝ 2 γ x₀) (hγ0 : γ x₀ = y₀) (η ξ : F) :
    fderiv ℝ (fun x => fderiv ℝ M (γ x, ι (γ x)) (fderiv ℝ γ x ξ, 0)) x₀ η -
        fderiv ℝ (fun x => fderiv ℝ M (γ x, ι (γ x)) (fderiv ℝ γ x η, 0)) x₀ ξ =
      fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ (fderiv ℝ γ x₀ ξ)) y₀ (fderiv ℝ γ x₀ η) -
        fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ (fderiv ℝ γ x₀ η)) y₀ (fderiv ℝ γ x₀ ξ) := by
  have hD := hM.differentiableAt (by norm_num)
  rw [fderiv_rightMC_chart hM hι hι0 hγ hγ0, fderiv_rightMC_chart hM hι hι0 hγ hγ0,
    fderiv_partial_snd hM, fderiv_partial_snd hM, fderiv_inl_eq hD h2, fderiv_inl_eq hD h2,
    fderiv_inv_chart hM h1 h2 hι hι0 h3, fderiv_inv_chart hM h1 h2 hι hι0 h3]
  set u := fderiv ℝ γ x₀ η
  set v := fderiv ℝ γ x₀ ξ
  have hsγ : fderiv ℝ (fderiv ℝ γ) x₀ η ξ = fderiv ℝ (fderiv ℝ γ) x₀ ξ η :=
    (ContDiffAt.isSymmSndFDerivAt hγ (by simp)) η ξ
  have hsM := ContDiffAt.isSymmSndFDerivAt hM (by simp)
  have hsplit : ∀ a : E, ((a, -a) : E × E) = (a, 0) - (0, a) := fun a => by simp
  rw [hsplit u, hsplit v, map_sub, map_sub, sub_apply, sub_apply, snd_fderiv_inl_inl hM h2 u v,
    snd_fderiv_inl_inl hM h2 v u, hsM (0, u) (v, 0), hsM (0, v) (u, 0), hsγ]
  abel

include hM h1 h2 hι hι0 h3 in
/-- The derivative of the adjoint action along a path in its explicit form
`x ↦ ∂M(γ x, ι(γ x))(∂M(γ x, y₀)(0, a x), 0)` (which is `Ad_{g(x)} a(x)` near `x₀`): `Da(η) + ⁅Dγ η, a x₀⁆`. -/
lemma fderiv_conjApply_explicit {γ a : F → E} {x₀ : F} (hγ : DifferentiableAt ℝ γ x₀) (hγ0 : γ x₀ = y₀)
    (ha : DifferentiableAt ℝ a x₀) (η : F) :
    fderiv ℝ (fun x => fderiv ℝ M (γ x, ι (γ x)) (fderiv ℝ M (γ x, y₀) (0, a x), 0)) x₀ η =
      fderiv ℝ a x₀ η +
        (fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ (a x₀)) y₀ (fderiv ℝ γ x₀ η) -
          fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ (fderiv ℝ γ x₀ η)) y₀ (a x₀)) := by
  have hD := hM.differentiableAt (by norm_num)
  -- the derivatives of the two partial derivatives along the path
  have hιγ : HasFDerivAt (fun x => ι (γ x)) ((fderiv ℝ ι y₀).comp (fderiv ℝ γ x₀)) x₀ := by
    have : HasFDerivAt ι (fderiv ℝ ι y₀) (γ x₀) := by rw [hγ0]; exact hι.hasFDerivAt
    exact this.comp x₀ hγ.hasFDerivAt
  have hK2 : HasFDerivAt (fun x => fderiv ℝ M (γ x, ι (γ x)))
      ((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp
        ((fderiv ℝ γ x₀).prod ((fderiv ℝ ι y₀).comp (fderiv ℝ γ x₀)))) x₀ := by
    have h' : HasFDerivAt (fderiv ℝ M) (fderiv ℝ (fderiv ℝ M) (y₀, y₀)) (γ x₀, ι (γ x₀)) := by
      rw [hγ0, hι0]; exact (differentiableAt_fderiv hM).hasFDerivAt
    exact h'.comp x₀ (hγ.hasFDerivAt.prodMk hιγ)
  have hK1 : HasFDerivAt (fun x => fderiv ℝ M (γ x, y₀))
      ((fderiv ℝ (fderiv ℝ M) (y₀, y₀)).comp ((fderiv ℝ γ x₀).prod 0)) x₀ := by
    have h' : HasFDerivAt (fderiv ℝ M) (fderiv ℝ (fderiv ℝ M) (y₀, y₀)) (γ x₀, y₀) := by
      rw [hγ0]; exact (differentiableAt_fderiv hM).hasFDerivAt
    exact h'.comp x₀ (hγ.hasFDerivAt.prodMk (hasFDerivAt_const y₀ x₀))
  have hin := hK1.clm_apply ((hasFDerivAt_const (0 : E) x₀).prodMk ha.hasFDerivAt)
  have hfin := hK2.clm_apply (hin.prodMk (hasFDerivAt_const (0 : E) x₀))
  rw [hfin.fderiv]
  simp only [add_apply, comp_apply, prod_apply, flip_apply, zero_apply, comp_zero, zero_add, add_zero, hγ0, hι0]
  simp only [fderiv_partial_snd hM, fderiv_inr_eq hD h1, fderiv_inl_eq hD h2, fderiv_inv_chart hM h1 h2 hι hι0 h3]
  have hsM := ContDiffAt.isSymmSndFDerivAt hM (by simp)
  have hs : ((fderiv ℝ γ x₀ η, -fderiv ℝ γ x₀ η) : E × E) = (fderiv ℝ γ x₀ η, 0) - (0, fderiv ℝ γ x₀ η) := by
    simp
  rw [hs, map_sub, sub_apply, snd_fderiv_inl_inl hM h2, hsM (0, fderiv ℝ γ x₀ η) (a x₀, 0)]
  abel

include hM h1 h2 hι hι0 h3 in
/-- **The derivative of the adjoint action along a path**, in the chart at the identity: for `γ` and `a`
differentiable at `x₀` with `γ x₀ = y₀`, the derivative at `x₀` along `η` of
`x ↦ ∂_z M(M(γ x, z), ι(γ x))|_{z = y₀} (a x)` (that is `Ad_{g(x)} a(x)`) is `Da(η) + ⁅Dγ η, a x₀⁆`, the bracket in
its chart form. -/
theorem fderiv_conjApply_chart {γ a : F → E} {x₀ : F} (hγ : DifferentiableAt ℝ γ x₀) (hγ0 : γ x₀ = y₀)
    (ha : DifferentiableAt ℝ a x₀) (η : F) :
    fderiv ℝ (fun x => fderiv ℝ (fun z => M (M (γ x, z), ι (γ x))) y₀ (a x)) x₀ η =
      fderiv ℝ a x₀ η +
        (fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ (a x₀)) y₀ (fderiv ℝ γ x₀ η) -
          fderiv ℝ (fun y => fderiv ℝ (fun z => M (y, z)) y₀ (fderiv ℝ γ x₀ η)) y₀ (a x₀)) := by
  have hD := hM.differentiableAt (by norm_num)
  have hevD := eventually_differentiableAt_of_contDiffAt hM
  have hγc : Tendsto γ (𝓝 x₀) (𝓝 y₀) := by
    have := hγ.continuousAt; rwa [ContinuousAt, hγ0] at this
  have hTι : Tendsto (fun y : E => (y, ι y)) (𝓝 y₀) (𝓝 (y₀, y₀)) := by
    have : ContinuousAt (fun y : E => (y, ι y)) y₀ := continuousAt_id.prodMk hι.continuousAt
    simpa [ContinuousAt, hι0] using this
  have hT0 : Tendsto (fun y : E => (y, y₀)) (𝓝 y₀) (𝓝 (y₀, y₀)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  -- near `x₀`, the conjugation differentiated in `z` is the composite of the two partial derivatives
  have hev : (fun x => fderiv ℝ (fun z => M (M (γ x, z), ι (γ x))) y₀ (a x)) =ᶠ[𝓝 x₀]
      fun x => fderiv ℝ M (γ x, ι (γ x)) (fderiv ℝ M (γ x, y₀) (0, a x), 0) := by
    filter_upwards [hγc.eventually (hTι.eventually hevD), hγc.eventually (hT0.eventually hevD),
      hγc.eventually h2] with x hx1 hx2 hx3
    have hin : HasFDerivAt (fun z => M (γ x, z)) ((fderiv ℝ M (γ x, y₀)).comp (inr ℝ E E)) y₀ :=
      hx2.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right (γ x) y₀)
    have hout : HasFDerivAt M (fderiv ℝ M (γ x, ι (γ x))) (M (γ x, y₀), ι (γ x)) := by
      rw [hx3]; exact hx1.hasFDerivAt
    have hcomp : HasFDerivAt (fun z => M (M (γ x, z), ι (γ x)))
        ((fderiv ℝ M (γ x, ι (γ x))).comp (((fderiv ℝ M (γ x, y₀)).comp (inr ℝ E E)).prod 0)) y₀ :=
      hout.comp y₀ (hin.prodMk (hasFDerivAt_const (ι (γ x)) y₀))
    rw [hcomp.fderiv]
    simp
  rw [hev.fderiv_eq]
  exact fderiv_conjApply_explicit hM h1 h2 hι hι0 h3 hγ hγ0 ha η

end Lightlike.Gauge
