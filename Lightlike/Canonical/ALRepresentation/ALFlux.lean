import Lightlike.Canonical.ALRepresentation.AL
import Mathlib.MeasureTheory.Group.Measure

/-!
# The Ashtekar–Lewandowski representation of one graph (G2-011), flux part

On `L²(K, μ)` for a compact group `K` with a left invariant measure `μ`, the exponentiated flux `k`
acts by translation, `(U_k ξ)(x) = ξ (k⁻¹ x)`. Together with the multiplication operators of `AL.lean`
this is a representation `alRep : HFRep K (L²(K, μ))` of the holonomy–flux algebra of one graph.

Supporting definitions; no catalogue entry.
-/

noncomputable section

open MeasureTheory

namespace Lightlike.Canonical.ALRepresentation

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [OpensMeasurableSpace K] [MeasurableMul K] (μ : Measure K)
  [μ.IsMulLeftInvariant]

/-- Translation `ξ ↦ ξ (k⁻¹ · )` on `L²(K, μ)` as a linear isometry. -/
def shiftIso (k : K) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => k⁻¹ * x) (measurePreserving_mul_left μ k⁻¹)

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [OpensMeasurableSpace K] in
lemma shiftIso_ae (k : K) (ξ : Lp ℂ 2 μ) : shiftIso μ k ξ =ᵐ[μ] fun x => ξ (k⁻¹ * x) :=
  Lp.coeFn_compMeasurePreserving ξ _

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [OpensMeasurableSpace K] in
lemma shiftIso_mul (k l : K) (ξ : Lp ℂ 2 μ) :
    shiftIso μ (k * l) ξ = shiftIso μ k (shiftIso μ l ξ) := by
  refine Lp.ext ?_
  have hq := (measurePreserving_mul_left μ k⁻¹).quasiMeasurePreserving
  filter_upwards [shiftIso_ae μ (k * l) ξ, shiftIso_ae μ k (shiftIso μ l ξ),
    hq.ae_eq_comp (shiftIso_ae μ l ξ)] with x h1 h2 h3
  simp only [Function.comp_apply] at h3
  rw [h1, h2, h3]
  simp [mul_assoc]

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [OpensMeasurableSpace K] in
lemma shiftIso_one (ξ : Lp ℂ 2 μ) : shiftIso μ 1 ξ = ξ := by
  refine Lp.ext ?_
  filter_upwards [shiftIso_ae μ 1 ξ] with x h
  rw [h]; simp

/-- Translation by `k` as a unitary of `L²(K, μ)`. -/
def shiftEquiv (k : K) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  { toFun := shiftIso μ k
    map_add' := (shiftIso μ k).map_add
    map_smul' := (shiftIso μ k).map_smul
    invFun := shiftIso μ k⁻¹
    left_inv := fun ξ => by
      rw [← shiftIso_mul, inv_mul_cancel, shiftIso_one]
    right_inv := fun ξ => by
      rw [← shiftIso_mul, mul_inv_cancel, shiftIso_one]
    norm_map' := (shiftIso μ k).norm_map }

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [OpensMeasurableSpace K] in
lemma shiftEquiv_apply (k : K) (ξ : Lp ℂ 2 μ) : shiftEquiv μ k ξ = shiftIso μ k ξ := rfl

/-- The exponentiated fluxes act on `L²(K, μ)` by translation: a unitary representation of `K`. -/
def alFlux : K →* (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) where
  toFun := shiftEquiv μ
  map_one' := LinearIsometryEquiv.ext fun ξ => by
    rw [shiftEquiv_apply, shiftIso_one]; rfl
  map_mul' k l := LinearIsometryEquiv.ext fun ξ => by
    rw [shiftEquiv_apply, shiftIso_mul]; rfl

omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [OpensMeasurableSpace K] in
lemma alFlux_apply (k : K) (ξ : Lp ℂ 2 μ) : alFlux μ k ξ = shiftIso μ k ξ := rfl

lemma shiftIso_mulOp (k : K) (f : C(K, ℂ)) (ξ : Lp ℂ 2 μ) :
    shiftIso μ k (mulOp μ f ξ) = mulOp μ (translate K k f) (shiftIso μ k ξ) := by
  refine Lp.ext ?_
  have hq := (measurePreserving_mul_left μ k⁻¹).quasiMeasurePreserving
  filter_upwards [shiftIso_ae μ k (mulOp μ f ξ), hq.ae_eq_comp (mulOp_ae μ f ξ),
    mulOp_ae μ (translate K k f) (shiftIso μ k ξ), shiftIso_ae μ k ξ] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h2
  rw [h1, h2, h3, h4]
  simp

/-- **The Ashtekar–Lewandowski representation of the holonomy–flux algebra of one graph** on
`L²(K, μ)`: holonomies act by multiplication, fluxes by translation. -/
def alRep : HFRep K (Lp ℂ 2 μ) where
  hol := alHol μ
  flux := alFlux μ
  covariant k f ξ := shiftIso_mulOp μ k f ξ

end Lightlike.Canonical.ALRepresentation

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.alFlux := _root_.Lightlike.Canonical.ALRepresentation.alFlux
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.alFlux_apply := _root_.Lightlike.Canonical.ALRepresentation.alFlux_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.alRep := _root_.Lightlike.Canonical.ALRepresentation.alRep
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.shiftEquiv := _root_.Lightlike.Canonical.ALRepresentation.shiftEquiv
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.shiftEquiv_apply := _root_.Lightlike.Canonical.ALRepresentation.shiftEquiv_apply
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.shiftIso := _root_.Lightlike.Canonical.ALRepresentation.shiftIso
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.shiftIso_ae := _root_.Lightlike.Canonical.ALRepresentation.shiftIso_ae
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.shiftIso_mul := _root_.Lightlike.Canonical.ALRepresentation.shiftIso_mul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.shiftIso_mulOp := _root_.Lightlike.Canonical.ALRepresentation.shiftIso_mulOp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_011.shiftIso_one := _root_.Lightlike.Canonical.ALRepresentation.shiftIso_one
