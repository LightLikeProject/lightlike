import Lightlike.Gauge.Connection.PrincipalAssociated
import Lightlike.Gauge.Connection.PrincipalCurvature
import Lightlike.Gauge.Connection.PrincipalSmooth

/-!
# The curvature as a form with values in the adjoint bundle (Svetlichny p. 42)

The adjoint representation `Ad : G →* (g →L g)` (`adRep`) gives the associated bundle `P ×_Ad g` (Svetlichny p. 42),
here `adjointBundle`, the vector bundle with transition maps `Ad_{g_ij}`. By (63), `F_j = Ad_{g_ij} F_i`, the local
curvatures are the representatives of a single `P ×_Ad g`-valued 2-form (`curvatureForm`): its expression in the
trivialization over `U_i` is `F_i` for every `i` (`localTriv_curvatureForm`), "an antisymmetric bilinear bundle map
`T M × T M → P^g`" (p. 42). The bracket is a continuous bilinear map, `⁅u, v⁆ = K u v - K v u` with `K` the mixed second
derivative of the chart multiplication (`lieBrCLM`, `lieBr_eq_lieBrCLM`), so `F_i(x) = DA_i(x) - DA_i(x)ᵀ +
⁅A_i(x) ·, A_i(x) ·⁆` is a bilinear-map-valued function (`curvBilin`), `C^m` for `C^{m+1}` potentials
(`contDiffOn_curvBilin`); hence the curvature form is `C^m` in every trivialization of `P ×_Ad g`
(`contDiffOn_curvatureForm`).
-/

open Set Filter Bundle
open scoped ContDiff Manifold Topology

universe u

namespace Lightlike.Gauge

namespace PrincipalCocycle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {G : Type u} [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G]

/-- **The adjoint representation** `Ad : G →* (g →L g)`. -/
noncomputable def adRep : G →* (E →L[ℝ] E) where
  toFun g := adjointE 𝓘(ℝ, E) g
  map_one' := by simp only [adjointE, adjoint_one]; rfl
  map_mul' a b := by simp only [adjointE, adjoint_mul]; rfl

omit [CompleteSpace E] in
/-- The adjoint representation is continuous. -/
lemma continuous_adRep : Continuous (adRep (G := G) (E := E)) := by
  have : IsManifold 𝓘(ℝ, E) 1 G := IsManifold.of_le one_le_minSmoothness_three
  have h : ∀ k₀ : G, ContinuousAt (fun k : G => adjointE 𝓘(ℝ, E) k⁻¹) k₀ := fun k₀ =>
    (contMDiffAt_adjointE_inv (n := minSmoothness ℝ 3) (m := 0)
      (by simp) k₀).continuousAt
  have hc : Continuous fun k : G => adjointE 𝓘(ℝ, E) k⁻¹ := continuous_iff_continuousAt.2 h
  have : (adRep (G := G) (E := E) : G → E →L[ℝ] E) = (fun k : G => adjointE 𝓘(ℝ, E) k⁻¹) ∘ fun k => k⁻¹ := by
    funext k; simp [adRep]
  rw [this]
  exact hc.comp (contMDiff_inv 𝓘(ℝ, E) (minSmoothness ℝ 3)).continuous

variable (E G) in
/-- The mixed second derivative `∂_y ∂_z M(y, z)` of the chart multiplication at `(φ(1), φ(1))`. -/
noncomputable def chartMixed : E →L[ℝ] E →L[ℝ] E :=
  fderiv ℝ (fun y : E => fderiv ℝ (fun z => chartMulP E G (y, z)) (chartOne E G)) (chartOne E G)

omit [CompleteSpace E] in
lemma differentiableAt_chartPartial :
    DifferentiableAt ℝ (fun y : E => fderiv ℝ (fun z => chartMulP E G (y, z)) (chartOne E G)) (chartOne E G) := by
  set y₀ := chartOne E G
  have hM := chartMulP_contDiffAt (E := E) (G := G)
  have hev : ∀ᶠ p in 𝓝 (y₀, y₀), DifferentiableAt ℝ (chartMulP E G) p :=
    (hM.eventually (by simp)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ (chartMulP E G)) (y₀, y₀) :=
    (hM.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpair : Tendsto (fun y : E => (y, y₀)) (𝓝 y₀) (𝓝 (y₀, y₀)) :=
    (continuous_id.prodMk continuous_const).tendsto y₀
  have hev' : (fun y : E => fderiv ℝ (fun z => chartMulP E G (y, z)) y₀) =ᶠ[𝓝 y₀]
      fun y => (fderiv ℝ (chartMulP E G) (y, y₀)).comp (ContinuousLinearMap.inr ℝ E E) := by
    filter_upwards [hpair.eventually hev] with y hy
    have h1 : (fun z => chartMulP E G (y, z)) = chartMulP E G ∘ fun z => (y, z) := rfl
    rw [h1, fderiv_comp y₀ hy ((differentiableAt_const y).prodMk differentiableAt_id),
      (hasFDerivAt_prodMk_right y y₀).fderiv]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev'
  exact (hD.comp (f := fun y : E => (y, y₀)) y₀ (differentiableAt_id.prodMk (differentiableAt_const y₀))).clm_comp
    (differentiableAt_const _)

omit [CompleteSpace E] in
lemma chart_partial_apply (u v : E) :
    fderiv ℝ (fun y : E => fderiv ℝ (fun z => chartMulP E G (y, z)) (chartOne E G) v) (chartOne E G) u =
      chartMixed E G u v := by
  rw [fderiv_clm_apply (differentiableAt_chartPartial (E := E) (G := G)) (differentiableAt_const v)]
  simp [chartMixed]

variable (E G) in
/-- **The bracket of the Lie algebra as a continuous bilinear map**: `⁅u, v⁆ = K u v - K v u` with `K` the mixed
second derivative of the chart multiplication. -/
noncomputable def lieBrCLM : E →L[ℝ] E →L[ℝ] E := chartMixed E G - (chartMixed E G).flip

/-- The bracket is the continuous bilinear map `lieBrCLM`. -/
lemma lieBr_eq_lieBrCLM (u v : E) : lieBr 𝓘(ℝ, E) G u v = lieBrCLM E G u v := by
  rw [lieBr_eq_chart, chart_partial_apply, chart_partial_apply]
  simp [lieBrCLM]

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (G) in
/-- **The curvature (62) as a bilinear map**: `F(x) = DA(x) - DA(x)ᵀ + ⁅A(x) ·, A(x) ·⁆`. -/
noncomputable def curvBilin (A : F → F →L[ℝ] E) (x : F) : F →L[ℝ] F →L[ℝ] E :=
  fderiv ℝ A x - (fderiv ℝ A x).flip + (((lieBrCLM E G).comp (A x)).flip.comp (A x)).flip

/-- `curvBilin` is the curvature (62). -/
lemma curvBilin_apply (A : F → F →L[ℝ] E) (x η ξ : F) :
    curvBilin G A x η ξ = lieCurvature 𝓘(ℝ, E) G A x η ξ := by
  simp [curvBilin, lieCurvature, lieBr_eq_lieBrCLM]

omit [CompleteSpace E] [LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G] in
/-- The flip of bilinear maps is smooth (it is a continuous linear map). -/
lemma contDiff_flip (X Y Z : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {m : ℕ∞ω} :
    ContDiff ℝ m (fun f : X →L[ℝ] Y →L[ℝ] Z => f.flip) :=
  ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := X →L[ℝ] Y →L[ℝ] Z) (F := Y →L[ℝ] X →L[ℝ] Z) (n := m)
    ((ContinuousLinearMap.flipₗᵢ ℝ X Y Z).toContinuousLinearEquiv : (X →L[ℝ] Y →L[ℝ] Z) →L[ℝ] (Y →L[ℝ] X →L[ℝ] Z))

omit [CompleteSpace E] [LieGroup 𝓘(ℝ, E) (minSmoothness ℝ 3) G] in
/-- **The curvature of a `C^{m+1}` potential is `C^m`** as a bilinear-map-valued function. -/
lemma contDiffOn_curvBilin {A : F → F →L[ℝ] E} {U : Set F} (hU : IsOpen U) {m : ℕ∞ω}
    (hA : ContDiffOn ℝ (m + 1) A U) : ContDiffOn ℝ m (curvBilin G A) U := by
  have h1 : ContDiffOn ℝ m (fun x => fderiv ℝ A x) U := hA.fderiv_of_isOpen hU le_rfl
  have hA0 : ContDiffOn ℝ m A U := hA.of_le le_self_add
  have hfl : ContDiffOn ℝ m (fun x => (fderiv ℝ A x).flip) U := (contDiff_flip F F E).comp_contDiffOn h1
  have hb1 : ContDiffOn ℝ m (fun x => (lieBrCLM E G).comp (A x)) U := contDiffOn_const.clm_comp hA0
  have hb2 : ContDiffOn ℝ m (fun x => ((lieBrCLM E G).comp (A x)).flip) U :=
    (contDiff_flip F E E).comp_contDiffOn hb1
  have hb3 : ContDiffOn ℝ m (fun x => ((lieBrCLM E G).comp (A x)).flip.comp (A x)) U := hb2.clm_comp hA0
  have hb4 : ContDiffOn ℝ m (fun x => (((lieBrCLM E G).comp (A x)).flip.comp (A x)).flip) U :=
    (contDiff_flip F F E).comp_contDiffOn hb3
  have h3 : ContDiffOn ℝ m (fun x => fderiv ℝ A x - (fderiv ℝ A x).flip +
      (((lieBrCLM E G).comp (A x)).flip.comp (A x)).flip) U := (h1.sub hfl).add hb4
  exact h3

variable [ContinuousMul G] (c : PrincipalCocycle F G)

variable (E) in
/-- **The adjoint bundle** `P ×_Ad g` (Svetlichny p. 42). -/
noncomputable abbrev adjointBundle (hcov : ∀ x, ∃ i, x ∈ c.U i) : VectorBundleCore ℝ F E c.ι :=
  c.assocCore hcov (adRep (G := G) (E := E)) (continuous_adRep (G := G) (E := E))

variable (A : c.ι → F → F →L[ℝ] E)

/-- **The curvature 2-form with values in the adjoint bundle**: at `x`, the local curvature (62) in the preferred
trivialization at `x`. -/
noncomputable def curvatureForm (hcov : ∀ x, ∃ i, x ∈ c.U i) (x η ξ : F) : (c.adjointBundle E hcov).Fiber x :=
  (lieCurvature 𝓘(ℝ, E) G (A ((c.adjointBundle E hcov).indexAt x)) x η ξ : E)

variable {c A}

/-- **The local curvatures are the representatives of one `P ×_Ad g`-valued 2-form** (Svetlichny p. 42): in the
trivialization over every `U_i ∋ x`, the curvature form reads `F_i(x)`. -/
theorem localTriv_curvatureForm (hcov : ∀ x, ∃ i, x ∈ c.U i) (hA : c.IsCompatible 𝓘(ℝ, F) A)
    (hg : ∀ i j, ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    (hAd : ∀ i, ∀ x ∈ c.U i, DifferentiableAt ℝ (A i) x) {i : c.ι} {x : F} (hx : x ∈ c.U i) (η ξ : F) :
    ((c.adjointBundle E hcov).localTriv i ⟨x, c.curvatureForm A hcov x η ξ⟩).2 =
      lieCurvature 𝓘(ℝ, E) G (A i) x η ξ := by
  set k := (c.adjointBundle E hcov).indexAt x
  have hk : x ∈ c.U k := (c.adjointBundle E hcov).mem_baseSet_at x
  rw [VectorBundleCore.localTriv_apply]
  change adjointE 𝓘(ℝ, E) (c.g k i x) (lieCurvature 𝓘(ℝ, E) G (A k) x η ξ) = _
  exact (lieCurvature_transition c hA hg hk hx (hAd k x hk) η ξ).symm

omit [ContinuousMul G] in
/-- The curvature form is antisymmetric. -/
theorem curvatureForm_antisymm (hcov : ∀ x, ∃ i, x ∈ c.U i) (x η ξ : F) :
    c.curvatureForm A hcov x η ξ = -c.curvatureForm A hcov x ξ η := by
  have h := lieCurvature_antisymm (I := 𝓘(ℝ, E)) (G := G) (A ((c.adjointBundle E hcov).indexAt x)) x η ξ
  exact h

/-- **The `P ×_Ad g`-valued curvature form is `C^m`** (Svetlichny's "bundle map", p. 42): if the potentials are
`C^{m+1}`, then in the trivialization of the adjoint bundle over every `U_i` the curvature form is the `C^m` map
`x ↦ F_i(x)` into the bilinear maps (`curvBilin`). -/
theorem contDiffOn_curvatureForm (hcov : ∀ x, ∃ i, x ∈ c.U i) (hA : c.IsCompatible 𝓘(ℝ, F) A)
    (hg : ∀ i j, ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) (minSmoothness ℝ 3) (c.g i j) (c.U i ⊓ c.U j))
    {m : ℕ∞ω} (hAm : ∀ i, ContDiffOn ℝ (m + 1) (A i) (c.U i)) (i : c.ι) :
    ContDiffOn ℝ m (curvBilin G (A i)) (c.U i) ∧
      ∀ x ∈ c.U i, ∀ η ξ : F,
        ((c.adjointBundle E hcov).localTriv i ⟨x, c.curvatureForm A hcov x η ξ⟩).2 = curvBilin G (A i) x η ξ := by
  refine ⟨contDiffOn_curvBilin (c.U i).isOpen (hAm i), fun x hx η ξ => ?_⟩
  have hAd : ∀ j, ∀ y ∈ c.U j, DifferentiableAt ℝ (A j) y := fun j y hy =>
    ((hAm j).contDiffAt ((c.U j).isOpen.mem_nhds hy)).differentiableAt (by simp)
  rw [curvBilin_apply]
  exact localTriv_curvatureForm hcov hA hg hAd hx η ξ

end PrincipalCocycle

end Lightlike.Gauge
