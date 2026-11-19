import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Gluing local gauge potentials into a covariant derivative (Svetlichny, Theorem 10, on a vector bundle)

Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1, Theorem 10 (p. 31): given trivializations over
an open cover and local potentials `A_U` related by (38) on the overlaps, `A_V = g_VU A_U g_VU⁻¹ - dg_VU g_VU⁻¹`,
there is a unique connection whose local representatives are the `A_U`.

Here the theorem is formalised for a `C¹` vector bundle `V` over a manifold `M` with model fiber `F` (the bundle
associated to the frame bundle; its structure group is `GL(F)`), and a connection is a covariant derivative in
Mathlib's sense (`CovariantDerivative`). In a trivialization `e` a local potential is an `End(F)`-valued one-form
`A`, and the connection it represents is `∇σ = e⁻¹(dσ_e + A σ_e)` with `σ_e` the local representative of `σ`
(`localCov`).
* `localCov_isCovariantDerivativeOn`: `d + A` is a covariant derivative on the base set of `e`;
* `localCov_eq_of_mem`: if `A'` and `A` are related by (38) through the coordinate change `g = e'∘e⁻¹`, the two
  local covariant derivatives agree at the points of both base sets;
* `exists_covariantDerivative_of_local`, `covariantDerivative_eq_of_local`: **Theorem 10** for the vector bundle:
  local potentials satisfying (38) on all overlaps are the representatives of a covariant derivative, and two
  covariant derivatives with the same representatives agree on all sections differentiable at the point.
-/

open Bundle Set NormedSpace Filter ContinuousLinearMap
open scoped Manifold ContDiff Topology

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The tangent spaces of `M` are normable (they are the model space `E`). -/
instance instIsNormableSpaceTangentSpaceGauge (x : M) : IsNormableSpace ℝ (TangentSpace I x) :=
  inferInstanceAs (IsNormableSpace ℝ E)

/-- The derivative of a function into a normed space depends only on its germ. -/
lemma mvfderiv_congr_of_eventuallyEq {f g : M → F} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mvfderiv I f x = mvfderiv I g x := by
  ext v
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [h.mfderiv_eq]
  rfl

/-- **The product rule** for `x ↦ c(x)(u(x))` with `c` operator-valued and `u` vector-valued, on a manifold. -/
lemma mvfderiv_clm_apply' {c : M → F →L[ℝ] F} {u : M → F} {x : M}
    (hc : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F) c x) (hu : MDifferentiableAt I 𝓘(ℝ, F) u x)
    (v : TangentSpace I x) :
    mvfderiv I (fun y => c y (u y)) x v = c x (mvfderiv I u x v) + mvfderiv I c x v (u x) := by
  have hx : (extChartAt I x).symm (extChartAt I x x) = x := (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hmem : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x ((extChartAt I x).map_source (mem_extChartAt_source x))
  have key := fderivWithin_clm_apply (I.uniqueDiffOn _ hmem) hc.differentiableWithinAt_writtenInExtChartAt
    hu.differentiableWithinAt_writtenInExtChartAt
  let w : E := v
  have hk := DFunLike.congr_fun key w
  have h1 : mvfderiv I (fun y => c y (u y)) x v =
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, F) x (fun y => c y (u y))) (range I) (extChartAt I x x) w :=
    congrArg (fun L : TangentSpace I x →L[ℝ] F => L v) (hc.clm_apply hu).mvfderiv
  have h2 : mvfderiv I u x v = fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, F) x u) (range I) (extChartAt I x x) w :=
    congrArg (fun L : TangentSpace I x →L[ℝ] F => L v) hu.mvfderiv
  have h3 : mvfderiv I c x v =
      fderivWithin ℝ (writtenInExtChartAt I 𝓘(ℝ, F →L[ℝ] F) x c) (range I) (extChartAt I x x) w :=
    congrArg (fun L : TangentSpace I x →L[ℝ] (F →L[ℝ] F) => L v) hc.mvfderiv
  rw [h1, h2, h3]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, flip_apply] at hk
  convert hk using 2 <;> (try simp [writtenInExtChartAt, hx]) <;> rfl

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The local representative of a section in a trivialization: `σ_e(x) = e(σ(x))`. -/
def localRep (e : Trivialization F (π F V)) (σ : Π x : M, V x) : M → F := fun x => (e (σ x)).2

variable (I) in
/-- **The covariant derivative of a local potential** `A` (an `End(F)`-valued one-form) in a trivialization `e`:
`∇σ = e⁻¹(dσ_e + A σ_e)`. -/
def localCov (e : Trivialization F (π F V)) [e.IsLinear ℝ]
    (A : Π x : M, TangentSpace I x →L[ℝ] F →L[ℝ] F) (σ : Π x : M, V x) (x : M) :
    TangentSpace I x →L[ℝ] V x :=
  (e.symmL ℝ x).comp (mvfderiv I (localRep e σ) x + (A x).flip (localRep e σ x))

lemma localRep_eq_clm (e : Trivialization F (π F V)) [e.IsLinear ℝ] (σ : Π x : M, V x) {y : M}
    (hy : y ∈ e.baseSet) : localRep e σ y = e.continuousLinearMapAt ℝ y (σ y) :=
  (e.continuousLinearMapAt_apply_of_mem ℝ hy (σ y)).symm

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

/-- **The local covariant derivative `d + A` is a covariant derivative** on the base set of the trivialization. -/
theorem localCov_isCovariantDerivativeOn (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    (A : Π x : M, TangentSpace I x →L[ℝ] F →L[ℝ] F) :
    IsCovariantDerivativeOn F (localCov I e A) e.baseSet where
  add {σ σ' x} hσ hσ' hx := by
    have h1 : MDifferentiableAt I 𝓘(ℝ, F) (localRep e σ) x := (e.mdifferentiableAt_section_iff I σ hx).1 hσ
    have h2 : MDifferentiableAt I 𝓘(ℝ, F) (localRep e σ') x := (e.mdifferentiableAt_section_iff I σ' hx).1 hσ'
    have hev : localRep e (σ + σ') =ᶠ[𝓝 x] localRep e σ + localRep e σ' := by
      filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
      simp only [Pi.add_apply]
      rw [localRep_eq_clm e _ hy, localRep_eq_clm e _ hy, localRep_eq_clm e _ hy, Pi.add_apply, map_add]
    simp only [localCov]
    rw [mvfderiv_congr_of_eventuallyEq hev, mvfderiv_add h1 h2, hev.eq_of_nhds]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, flip_apply, Pi.add_apply, map_add]
    abel
  leibniz {σ g x} hσ hg hx := by
    have h1 : MDifferentiableAt I 𝓘(ℝ, F) (localRep e σ) x := (e.mdifferentiableAt_section_iff I σ hx).1 hσ
    have hev : localRep e (g • σ) =ᶠ[𝓝 x] g • localRep e σ := by
      filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
      rw [Pi.smul_apply', localRep_eq_clm e _ hy, localRep_eq_clm e _ hy, Pi.smul_apply', map_smul]
    simp only [localCov]
    rw [mvfderiv_congr_of_eventuallyEq hev, mvfderiv_smul hg h1, hev.eq_of_nhds]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, flip_apply, Pi.smul_apply',
      ContinuousLinearMap.smul_apply, smulRight_apply, map_add, map_smul]
    rw [localRep_eq_clm e σ hx, e.symmL_continuousLinearMapAt hx, smul_add]
    abel

/-- **(38) makes the local covariant derivatives agree**: with the coordinate change `g = e' ∘ e⁻¹` and
`A' = g A g⁻¹ - dg g⁻¹` at `x`, the covariant derivatives `d + A` in `e` and `d + A'` in `e'` agree at `x`. -/
theorem localCov_eq_of_mem {e e' : Trivialization F (π F V)} [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (A A' : Π x : M, TangentSpace I x →L[ℝ] F →L[ℝ] F) {σ : Π x : M, V x} {x : M}
    (hx : x ∈ e.baseSet ∩ e'.baseSet) (hσ : MDiffAt (T% σ) x)
    (h38 : ∀ v w, A' x v w = e.coordChangeL ℝ e' x (A x v ((e.coordChangeL ℝ e' x).symm w)) -
      mvfderiv I (fun y => (e.coordChangeL ℝ e' y : F →L[ℝ] F)) x v ((e.coordChangeL ℝ e' x).symm w)) :
    localCov I e' A' σ x = localCov I e A σ x := by
  have hu : MDifferentiableAt I 𝓘(ℝ, F) (localRep e σ) x := (e.mdifferentiableAt_section_iff I σ hx.1).1 hσ
  have hc : MDifferentiableAt I 𝓘(ℝ, F →L[ℝ] F) (fun y => (e.coordChangeL ℝ e' y : F →L[ℝ] F)) x :=
    mdifferentiableAt_coordChangeL hx.1 hx.2
  -- `σ_{e'} = g σ_e` near `x`
  have hev : localRep e' σ =ᶠ[𝓝 x] fun y => (e.coordChangeL ℝ e' y : F →L[ℝ] F) (localRep e σ y) := by
    filter_upwards [(e.open_baseSet.inter e'.open_baseSet).mem_nhds hx] with y hy
    simp only [localRep, ContinuousLinearEquiv.coe_coe]
    rw [e.coordChangeL_apply e' hy, e.symm_apply_apply_mk hy.1]
  -- `e'⁻¹ ∘ g = e⁻¹` at `x`
  have key : ∀ w : F, e'.symmL ℝ x (e.coordChangeL ℝ e' x w) = e.symmL ℝ x w := by
    intro w
    rw [e'.symmL_apply hx.2, e.symmL_apply hx.1, e.coordChangeL_apply e' hx, e'.symm_apply_apply_mk hx.2]
  simp only [localCov]
  rw [mvfderiv_congr_of_eventuallyEq hev, hev.eq_of_nhds]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, flip_apply]
  rw [mvfderiv_clm_apply' hc hu v, h38]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [← key]
  congr 1
  rw [map_add]
  abel

/-- **Theorem 10 on a vector bundle, existence**: local potentials on trivializations covering `M` that satisfy
(38) on every overlap are the local representatives of a covariant derivative. -/
theorem exists_covariantDerivative_of_local {ι : Type*} (e : ι → Trivialization F (π F V))
    [∀ i, MemTrivializationAtlas (e i)] (hcov : ∀ x : M, ∃ i, x ∈ (e i).baseSet)
    (A : ι → Π x : M, TangentSpace I x →L[ℝ] F →L[ℝ] F)
    (h38 : ∀ i j (x : M), x ∈ (e i).baseSet ∩ (e j).baseSet → ∀ v w,
      A j x v w = (e i).coordChangeL ℝ (e j) x (A i x v (((e i).coordChangeL ℝ (e j) x).symm w)) -
        mvfderiv I (fun y => ((e i).coordChangeL ℝ (e j) y : F →L[ℝ] F)) x v
          (((e i).coordChangeL ℝ (e j) x).symm w)) :
    ∃ cov : CovariantDerivative I F V, ∀ i (x : M) (σ : Π x : M, V x), x ∈ (e i).baseSet →
      MDiffAt (T% σ) x → cov σ x = localCov I (e i) (A i) σ x := by
  choose i hi using hcov
  let cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x) := fun σ x => localCov I (e (i x)) (A (i x)) σ x
  have hc : IsCovariantDerivativeOn F cov Set.univ :=
    { add := fun {σ σ' x} hσ hσ' _ =>
        (localCov_isCovariantDerivativeOn (e (i x)) (A (i x))).add hσ hσ' (hi x)
      leibniz := fun {σ g x} hσ hg _ =>
        (localCov_isCovariantDerivativeOn (e (i x)) (A (i x))).leibniz hσ hg (hi x) }
  refine ⟨⟨cov, hc⟩, fun j x σ hx hσ => ?_⟩
  show localCov I (e (i x)) (A (i x)) σ x = localCov I (e j) (A j) σ x
  exact (localCov_eq_of_mem (A (i x)) (A j) ⟨hi x, hx⟩ hσ (h38 (i x) j x ⟨hi x, hx⟩)).symm

omit [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] in
/-- **Theorem 10 on a vector bundle, uniqueness**: two covariant derivatives with the same local representatives on
trivializations covering `M` agree on every section differentiable at the point. -/
theorem covariantDerivative_eq_of_local {ι : Type*} (e : ι → Trivialization F (π F V)) [∀ i, (e i).IsLinear ℝ]
    (hcov : ∀ x : M, ∃ i, x ∈ (e i).baseSet) (A : ι → Π x : M, TangentSpace I x →L[ℝ] F →L[ℝ] F)
    (cov cov' : CovariantDerivative I F V)
    (h : ∀ i (x : M) (σ : Π x : M, V x), x ∈ (e i).baseSet → MDiffAt (T% σ) x →
      cov σ x = localCov I (e i) (A i) σ x)
    (h' : ∀ i (x : M) (σ : Π x : M, V x), x ∈ (e i).baseSet → MDiffAt (T% σ) x →
      cov' σ x = localCov I (e i) (A i) σ x)
    (σ : Π x : M, V x) (x : M) (hσ : MDiffAt (T% σ) x) : cov σ x = cov' σ x := by
  obtain ⟨i, hi⟩ := hcov x
  rw [h i x σ hi hσ, h' i x σ hi hσ]

end Lightlike.Gauge
