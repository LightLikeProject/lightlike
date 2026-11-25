import Lightlike.Canonical.ALRepresentation.Algebra
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Ashtekar–Lewandowski representation of one graph (G2-011), holonomy part

For a compact group `K` with Haar probability measure `μ`, the Ashtekar–Lewandowski (AL) representation
of the holonomy–flux algebra of a graph lives on `L²(K, μ)`: holonomy functions act by multiplication
and fluxes by translation. This file builds the holonomy part: the multiplication operator
`mulOp f` by a continuous function `f` and the `*`-homomorphism `alHol : C(K, ℂ) →⋆ₐ B(L²)`.

Supporting definitions; no catalogue entry.
-/

noncomputable section

open MeasureTheory

namespace Lightlike.Rows.G2_011

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (μ : Measure K)

private lemma mul_bound (f : C(K, ℂ)) (ξ : Lp ℂ 2 μ) :
    MemLp (fun x => f x * ξ x) 2 μ :=
  MemLp.of_le_mul (c := ‖f‖) (Lp.memLp ξ)
    ((f.continuous.aestronglyMeasurable).mul (Lp.aestronglyMeasurable ξ))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg _))

/-- Multiplication of an `L²` class by a continuous function. -/
def mulFun (f : C(K, ℂ)) (ξ : Lp ℂ 2 μ) : Lp ℂ 2 μ := (mul_bound μ f ξ).toLp _

lemma mulFun_ae (f : C(K, ℂ)) (ξ : Lp ℂ 2 μ) : mulFun μ f ξ =ᵐ[μ] fun x => f x * ξ x :=
  MemLp.coeFn_toLp _

/-- The multiplication operator by a continuous function on `L²(K, μ)`. -/
def mulOp (f : C(K, ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := mulFun μ f
      map_add' := fun ξ η => by
        refine Lp.ext ?_
        filter_upwards [mulFun_ae μ f (ξ + η), mulFun_ae μ f ξ, mulFun_ae μ f η,
          Lp.coeFn_add ξ η, Lp.coeFn_add (mulFun μ f ξ) (mulFun μ f η)]
          with x h1 h2 h3 h4 h5
        rw [h5, h1, Pi.add_apply, h2, h3, h4]; simp [mul_add]
      map_smul' := fun c ξ => by
        refine Lp.ext ?_
        filter_upwards [mulFun_ae μ f (c • ξ), mulFun_ae μ f ξ,
          Lp.coeFn_smul c ξ, Lp.coeFn_smul c (mulFun μ f ξ)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h4, h1, Pi.smul_apply, h2, h3]; simp [mul_left_comm] }
    ‖f‖ (fun ξ => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [mulFun_ae μ f ξ] with x h1
      show ‖(mulFun μ f ξ) x‖ ≤ ‖f‖ * ‖ξ x‖
      rw [h1, norm_mul]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg _))

lemma mulOp_ae (f : C(K, ℂ)) (ξ : Lp ℂ 2 μ) : mulOp μ f ξ =ᵐ[μ] fun x => f x * ξ x :=
  mulFun_ae μ f ξ

lemma mulOp_add (f g : C(K, ℂ)) : mulOp μ (f + g) = mulOp μ f + mulOp μ g := by
  ext1 ξ
  refine Lp.ext ?_
  filter_upwards [mulOp_ae μ (f + g) ξ, mulOp_ae μ f ξ, mulOp_ae μ g ξ,
    Lp.coeFn_add (mulOp μ f ξ) (mulOp μ g ξ)] with x h1 h2 h3 h4
  rw [add_apply, h4, h1, Pi.add_apply, h2, h3]
  simp [add_mul]

lemma mulOp_mul (f g : C(K, ℂ)) : mulOp μ (f * g) = mulOp μ f * mulOp μ g := by
  ext1 ξ
  refine Lp.ext ?_
  have h0 := mulOp_ae μ g ξ
  filter_upwards [mulOp_ae μ (f * g) ξ, mulOp_ae μ f (mulOp μ g ξ), h0] with x h1 h2 h3
  rw [mul_apply_eq_comp, h2, h3, h1]
  simp [mul_assoc]

lemma mulOp_one : mulOp μ (1 : C(K, ℂ)) = 1 := by
  ext1 ξ
  refine Lp.ext ?_
  filter_upwards [mulOp_ae μ (1 : C(K, ℂ)) ξ] with x h1
  rw [h1]; simp

lemma mulOp_zero : mulOp μ (0 : C(K, ℂ)) = 0 := by
  ext1 ξ
  refine Lp.ext ?_
  filter_upwards [mulOp_ae μ (0 : C(K, ℂ)) ξ, Lp.coeFn_zero ℂ 2 μ] with x h1 h2
  have h3 : ((0 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) ξ) = 0 := rfl
  rw [h1, h3, h2]; simp

lemma mulOp_algebraMap (r : ℂ) : mulOp μ (algebraMap ℂ C(K, ℂ) r) = algebraMap ℂ _ r := by
  ext1 ξ
  refine Lp.ext ?_
  filter_upwards [mulOp_ae μ (algebraMap ℂ C(K, ℂ) r) ξ,
    Lp.coeFn_smul r ξ] with x h1 h2
  rw [h1]
  simp [Algebra.algebraMap_eq_smul_one, h2]

lemma mulOp_inner (f : C(K, ℂ)) (ξ η : Lp ℂ 2 μ) :
    inner ℂ (mulOp μ (star f) ξ) η = inner ℂ ξ (mulOp μ f η) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulOp_ae μ (star f) ξ, mulOp_ae μ f η] with x h1 h2
  rw [h1, h2]
  simp; ring

/-- The holonomy functions act on `L²(K, μ)` by multiplication: a `*`-homomorphism
`C(K, ℂ) → B(L²(K, μ))`. -/
def alHol : C(K, ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := mulOp μ
  map_one' := mulOp_one μ
  map_mul' := mulOp_mul μ
  map_zero' := mulOp_zero μ
  map_add' := mulOp_add μ
  commutes' := mulOp_algebraMap μ
  map_star' := fun f => by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
    exact fun ξ η => mulOp_inner μ f ξ η

end Lightlike.Rows.G2_011
