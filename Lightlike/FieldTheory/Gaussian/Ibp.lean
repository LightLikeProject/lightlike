import Lightlike.FieldTheory.Gaussian.Measure
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Gaussian integration by parts

For a symmetric `A`, the weight `exp (-(1/2) xᵀ A x)` has line derivative `-(A x)ⱼ · weight` along the
coordinate direction `eⱼ`. With the integration by parts formula for line derivatives this gives
`∫ (A x)ⱼ g(x) exp(…) dx = ∫ ∂ⱼ g(x) exp(…) dx` (`integral_mulVec_mul_weight`).
-/

open MeasureTheory ProbabilityTheory Matrix Real

noncomputable section

namespace Lightlike.FieldTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The coordinate direction `eⱼ`. -/
abbrev e (j : ι) : EuclideanSpace ℝ ι := EuclideanSpace.single j 1

lemma quad_add_smul {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : EuclideanSpace ℝ ι) (j : ι) (t : ℝ) :
    (WithLp.ofLp (x + t • e j)) ⬝ᵥ A *ᵥ (WithLp.ofLp (x + t • e j)) =
      (WithLp.ofLp x ⬝ᵥ A *ᵥ WithLp.ofLp x) + 2 * t * (A *ᵥ WithLp.ofLp x) j + t ^ 2 * A j j := by
  have hT : Aᵀ = A := by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hu : WithLp.ofLp (x + t • e j) = WithLp.ofLp x + t • (Pi.single j (1 : ℝ) : ι → ℝ) := by
    simp [e]
  rw [hu]
  have h1 : (WithLp.ofLp x) ⬝ᵥ A *ᵥ (Pi.single j (1 : ℝ) : ι → ℝ) = (A *ᵥ WithLp.ofLp x) j := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
    simp
  have h2 : (Pi.single j (1 : ℝ) : ι → ℝ) ⬝ᵥ A *ᵥ WithLp.ofLp x = (A *ᵥ WithLp.ofLp x) j := by simp
  have h3 : (Pi.single j (1 : ℝ) : ι → ℝ) ⬝ᵥ A *ᵥ (Pi.single j (1 : ℝ) : ι → ℝ) = A j j := by simp
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, h1, h2, h3, smul_eq_mul]
  ring

/-- The line derivative of the Gaussian weight. -/
lemma hasLineDerivAt_weight {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : EuclideanSpace ℝ ι) (j : ι) :
    HasLineDerivAt ℝ (weight A) (-((A *ᵥ x) j) * weight A x) x (e j) := by
  unfold HasLineDerivAt
  have hq : ∀ t : ℝ, weight A (x + t • e j) =
      Real.exp (-(1 / 2) * ((x ⬝ᵥ A *ᵥ x) + 2 * t * (A *ᵥ x) j + t ^ 2 * A j j)) := by
    intro t; unfold weight; rw [quad_add_smul hA]
  simp_rw [hq]
  have hd : HasDerivAt (fun t : ℝ => -(1 / 2) * ((x ⬝ᵥ A *ᵥ x) + 2 * t * (A *ᵥ x) j + t ^ 2 * A j j))
      (-(A *ᵥ x) j) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const ((A *ᵥ x) j)).const_add (x ⬝ᵥ A *ᵥ x)
    have h2 := (((hasDerivAt_pow 2 (0 : ℝ))).mul_const (A j j))
    have := ((this.add h2).const_mul (-(1 / 2 : ℝ)))
    convert this using 1
    norm_num
    ring
  have := hd.exp
  convert this using 1
  simp [weight]
  ring

/-- **Gaussian integration by parts** for the unnormalised weight. -/
theorem integral_weight_mul_lineDeriv {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {g g' : EuclideanSpace ℝ ι → ℝ}
    (j : ι) (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x (e j))
    (h1 : Integrable (fun x : EuclideanSpace ℝ ι => weight A x * g x))
    (h2 : Integrable (fun x : EuclideanSpace ℝ ι => weight A x * g' x))
    (h3 : Integrable (fun x : EuclideanSpace ℝ ι => (-((A *ᵥ x.ofLp) j) * weight A x) * g x)) :
    ∫ x, weight A x * g' x = ∫ x, (A *ᵥ x.ofLp) j * (weight A x * g x) := by
  have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (EuclideanSpace ℝ ι))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := weight A) (f' := fun x : EuclideanSpace ℝ ι => -((A *ᵥ x.ofLp) j) * weight A x) (g := g) (g' := g') (v := e j)
    h3 h2 h1 (fun x _ => hasLineDerivAt_weight hA x j) (fun x _ => hg x)
  simp only [ContinuousLinearMap.mul_apply'] at this
  rw [this, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x : EuclideanSpace ℝ ι => ?_)
  ring

end Lightlike.FieldTheory
