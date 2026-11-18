import Lightlike.Spacetime.Coordinates
import Lightlike.Spacetime.Minkowski
import Lightlike.Spacetime.Curvature
/-!
# Lorentzian coordinate metrics on open subsets of `ℝⁿ` as Lorentzian metrics on the manifold

For an open set `U ⊆ ℝⁿ` and a Lorentzian coordinate metric `g` on `U` (`IsLorentzianCoordMetric g U`, signature
`−+⋯+`), `openMetric U g hg` is the smooth Lorentzian metric (`LorentzianMetric`) of the manifold `↥U` (an `Opens` of
`ℝⁿ`, modelled on `𝓘(ℝ, Fin n → ℝ)`) whose components at the point `y` are `g y`.

* `opens_extChartAt_apply`, `opens_extChartAt_symm`: the charts of `↥U` are restrictions of the identity;
* `opens_coordChange`, `opens_symmL`, `opens_continuousLinearMapAt`: the tangent trivializations of `↥U` are the identity;
* `contMDiff_matForm`: the section `y ↦ matForm (A y)` of the bundle of bilinear forms is smooth when the entries of
  `A` are smooth on `U`;
* `matForm_isLorentzian`: the form of a matrix `Pᵀ η P` with `P` invertible has a Lorentz frame;
* `openMetric_coordMetric` (**the bridge**): in every chart of `↥U` the coordinate components of `openMetric U g hg` are
  `g`.

**Limits.** Open subsets of `ℝⁿ` only (the manifold `↥U` has the single global chart); `U` is not required to be
connected or to carry any global structure. No curvature statement here.
-/

open Manifold TopologicalSpace Bundle Matrix
open scoped ContDiff
noncomputable section
namespace Lightlike
variable {n : ℕ}

/-- The bilinear form of a matrix: `B(v,w) = Σ A i j v i w j`. -/
def matForm (A : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j, A i j • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)

/-- The value of `matForm A` on two vectors. -/
theorem matForm_apply (A : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    matForm A v w = ∑ i, ∑ j, v i * A i j * w j := by
  simp [matForm, _root_.sum_apply, _root_.smul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section Opens
variable (U : Opens (Fin n → ℝ))

/-- The chart of an open subset of `ℝⁿ` is the restriction of the identity. -/
theorem opens_extChartAt_apply (p q : U) : extChartAt 𝓘(ℝ, Fin n → ℝ) p q = q.1 := by
  simp [extChartAt, Opens.chartAt_eq, chartAt_self_eq]

/-- The inverse chart of `↥U` is the inclusion on the chart target. -/
theorem opens_extChartAt_symm (p : U) {y : Fin n → ℝ} (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).target) :
    ((extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm y : U).1 = y := by
  have := OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt (Fin n → ℝ) p.1) (U := U) ⟨p⟩ (y := y) (by
    simpa [extChartAt, Opens.chartAt_eq] using hy)
  simpa [extChartAt, Opens.chartAt_eq, chartAt_self_eq] using this

/-- The change of tangent trivialization between two charts of `↥U` is the identity. -/
theorem opens_coordChange (b b' z : U) :
    (tangentBundleCore 𝓘(ℝ, Fin n → ℝ) U).coordChange (achart (Fin n → ℝ) b) (achart (Fin n → ℝ) b') z = 1 := by
  rw [tangentBundleCore_coordChange_achart]
  have hz : extChartAt 𝓘(ℝ, Fin n → ℝ) b z ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) b).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) b).map_source (by rw [extChartAt_source]; simp [Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source])
  have hev : (extChartAt 𝓘(ℝ, Fin n → ℝ) b' ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b).symm) =ᶠ[nhds (extChartAt 𝓘(ℝ, Fin n → ℝ) b z)]
      (id : (Fin n → ℝ) → (Fin n → ℝ)) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin n → ℝ)) b).mem_nhds hz] with w hw
    simp only [Function.comp_apply, id, opens_extChartAt_apply, opens_extChartAt_symm U b hw]
  have hx : (extChartAt 𝓘(ℝ, Fin n → ℝ) b' ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) b).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) b z) =
      id (extChartAt 𝓘(ℝ, Fin n → ℝ) b z) := by
    rw [Function.comp_apply, opens_extChartAt_apply, opens_extChartAt_symm U b hz]
    rfl
  rw [Filter.EventuallyEq.fderivWithin_eq (hev.filter_mono nhdsWithin_le_nhds) hx]
  simp [ModelWithCorners.range_eq_univ]
  rfl

/-- The inverse tangent trivialization of `↥U` is the identity. -/
theorem opens_symmL (b₀ b : U) :
    (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) b₀).symmL ℝ b =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by simp [Opens.chartAt_eq, chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_source]), opens_coordChange]
  rfl

/-- The tangent trivialization of `↥U` is the identity. -/
theorem opens_continuousLinearMapAt (b₀ b : U) :
    (trivializationAt (Fin n → ℝ) (TangentSpace 𝓘(ℝ, Fin n → ℝ)) b₀).continuousLinearMapAt ℝ b =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (by simp [Opens.chartAt_eq, chartAt_self_eq,
    OpenPartialHomeomorph.subtypeRestr_source]), opens_coordChange]
  rfl
end Opens

set_option backward.isDefEq.respectTransparency false in
/-- The section `y ↦ matForm (A y)` of the bundle of bilinear forms of `↥U` is smooth when the entries of `A` are. -/
theorem contMDiff_matForm (U : Opens (Fin n → ℝ)) (A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun y => A y i j) U) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)) ∞
      (fun x : U => TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
        (E := fun x : U => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x
        (matForm (A x.1))) := by
  intro x
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, opens_symmL, opens_continuousLinearMapAt]
  have e : ∀ y : U, Trivialization.continuousLinearMapAt ℝ
          (trivializationAt ((Fin n → ℝ) →L[ℝ] ℝ) (fun x => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x) y =
      ContinuousLinearMap.id ℝ ((Fin n → ℝ) →L[ℝ] ℝ) := fun y => by
    ext φ v
    have hb : y ∈ (trivializationAt ((Fin n → ℝ) →L[ℝ] ℝ) (fun x => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x).baseSet := by
      simp [hom_trivializationAt_baseSet, Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
    have hs : y ∈ (chartAt (Fin n → ℝ) x).source := by
      simp [Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
    simp only [Trivialization.continuousLinearMapAt, ContinuousLinearMap.coe_mk', Trivialization.coe_linearMapAt_of_mem _ hb]
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, opens_symmL, Trivialization.continuousLinearMapAt]
    simp [Trivialization.linearMapAt_apply]
    rfl
  have e' : ∀ y : U, (Trivialization.continuousLinearMapAt ℝ
          (trivializationAt ((Fin n → ℝ) →L[ℝ] ℝ) (fun x => TangentSpace 𝓘(ℝ, Fin n → ℝ) x →L[ℝ] ℝ) x) y) ∘SL
        matForm (A y.1) ∘SL ContinuousLinearMap.id ℝ (Fin n → ℝ) = matForm (A y.1) := fun y => by
    rw [e y]; rfl
  simp only [e']
  have hd : ∀ i j, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (fun y : U => A y.1 i j) x := fun i j => by
    have h1 : ContDiffAt ℝ ∞ (fun y => A y i j) x.1 := (hA i j).contDiffAt (U.isOpen.mem_nhds x.2)
    exact h1.contMDiffAt.comp x (contMDiff_subtype_val x)
  unfold matForm
  exact ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => (hd i j).smul contMDiffAt_const

/-- `matForm A v w = v · (A w)`. -/
theorem matForm_eq_dotProduct (A : Matrix (Fin n) (Fin n) ℝ) (v w : Fin n → ℝ) :
    matForm A v w = v ⬝ᵥ (A.mulVec w) := by
  rw [matForm_apply]
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- The form of a matrix `Pᵀ η P` with `P` invertible is Lorentzian. -/
theorem matForm_isLorentzian (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P.det) :
    IsLorentzianForm n (matForm (Pᵀ * eta n * P)) := by
  haveI : Invertible P := Matrix.invertibleOfIsUnitDet P hP
  refine ⟨(Pi.basisFun ℝ (Fin n)).map (Matrix.toLinearEquiv' P⁻¹ (by infer_instance)), fun i j => ?_⟩
  simp only [Module.Basis.map_apply, Pi.basisFun_apply, Matrix.toLinearEquiv'_apply, matForm_eq_dotProduct]
  change (P⁻¹ *ᵥ (Pi.single i 1 : Fin n → ℝ)) ⬝ᵥ ((Pᵀ * eta n * P) *ᵥ (P⁻¹ *ᵥ (Pi.single j 1 : Fin n → ℝ))) = eta n i j
  have h1 : P *ᵥ (P⁻¹ *ᵥ (Pi.single j 1 : Fin n → ℝ)) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have h2 : P *ᵥ (P⁻¹ *ᵥ (Pi.single i 1 : Fin n → ℝ)) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h2]
  simp [eta_apply, Matrix.mulVec, dotProduct, Pi.single_apply, eta, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/-- `matForm A` on standard basis vectors is the entry of `A`. -/
theorem matForm_single (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    matForm A (Pi.single i 1) (Pi.single j 1) = A i j := by
  rw [matForm_apply]
  simp [Pi.single_apply]

/-- **A Lorentzian coordinate metric on an open set of `ℝⁿ` is a Lorentzian metric on the open subset** (the
manifold `↥U`, modelled on `ℝⁿ`). -/
def openMetric (U : Opens (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsLorentzianCoordMetric g U) : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) U n where
  g x := matForm (g x.1)
  lorentzian x := by
    obtain ⟨P, hP, h⟩ := hg.2 x.1 x.2
    rw [h]
    exact matForm_isLorentzian P hP
  contMDiff := contMDiff_matForm U g hg.1.smooth

/-- **The bridge**: in every chart of `↥U` the coordinate components of `openMetric U g hg` are `g`. -/
theorem openMetric_coordMetric (U : Opens (Fin n → ℝ)) (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : IsLorentzianCoordMetric g U) (x₀ : U) {y : Fin n → ℝ}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).target) :
    (openMetric U g hg).coordMetric x₀ y = g y := by
  ext i j
  rw [LorentzianMetric.coordMetric_eq _ x₀ hy, coordBasis_apply, coordBasis_apply, opens_symmL]
  show matForm (g ((extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).symm y : U).1) (Pi.single i 1) (Pi.single j 1) = g y i j
  rw [matForm_single, opens_extChartAt_symm U x₀ hy]
end Lightlike
