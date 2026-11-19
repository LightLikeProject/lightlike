import Lightlike.Spacetime.RaychaudhuriCoord
import Lightlike.Spacetime.VariationInverse
import Lightlike.Spacetime.PalatiniCoord
import Lightlike.Spacetime.RicciContinuous

/-!
# Null hypersurfaces are ruled by null geodesics, in coordinates (G1-009)

For a function `u` and the gradient `ℓᵃ = gᵃᵇ ∂_b u` of `u` for a coordinate metric `g`, the covariant derivative is the
Hessian, `∇_b ℓᵃ = gᵃᵈ (∂_b ∂_d u - Γᵉ_{bd} ∂_e u)` (`covD_gradVec`), and so
`ℓᵇ ∇_b ℓᵃ = ½ gᵃᵈ ∂_d (ℓ · ℓ)` (`covDMat_gradVec_mulVec`). If the level sets of `u` are null near a point
(`ℓ · ℓ = 0` there), the gradient is geodesic there: `∇_ℓ ℓ = 0` (`gradVec_geodesic_of_null`), and for
`ℓ' = e^ρ ℓ`, `∇_{ℓ'} ℓ' = κ ℓ'` with `κ = ⟨dρ, ℓ'⟩` (`covDMat_exp_smul_gradVec_of_null`): the integral curves of the
null normal are the null generators, geodesics with a non-affine parameter in general.

## References

* E. Gourgoulhon, J. L. Jaramillo, *A 3+1 perspective on null hypersurfaces and isolated horizons*,
  arXiv:gr-qc/0503113, section 2.5, eqs. (2.17)–(2.22), pp. 21–22 (`ℓ = e^ρ du` on a neighbourhood foliated by null
  hypersurfaces, `∇_ℓ ℓ = κ ℓ`, `κ = ⟨dρ, ℓ⟩`).
-/

open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The gradient `ℓᵃ = gᵃᵇ ∂_b u` of a function `u` for a coordinate metric `g`. -/
def gradVec (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (u : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  (g y)⁻¹ *ᵥ fun b => pd b u y

/-- The square `ℓ · ℓ = gᵃᵇ ∂_a u ∂_b u` of the gradient. -/
def gradSq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (u : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) : ℝ :=
  (fun b => pd b u y) ⬝ᵥ gradVec g u y

section

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}

variable (hg : IsCoordMetric g U) (hgs : ∀ y a b, g y a b = g y b a) (hu : ContDiffOn ℝ ∞ u U) (hx : x ∈ U)
include hg hgs hu hx

/-- **The covariant derivative of the gradient is the Hessian**: `∇_b ℓᵃ = gᵃᵈ (∂_b ∂_d u - Γᵉ_{bd} ∂_e u)`. -/
theorem covD_gradVec (a b : Fin n) :
    covD g (gradVec g u) a b x =
      ∑ d, (g x)⁻¹ a d * (pd b (fun y => pd d u y) x - ∑ e, christoffel g e b d x * pd e u x) := by
  have hdp : ∀ d, DifferentiableAt ℝ (fun y => pd d u y) x := fun d =>
    differentiableAt_of_contDiffOn (contDiffOn_pd hu hg.isOpen d) hg.isOpen hx
  have hdi : ∀ a d, DifferentiableAt ℝ (fun y => (g y)⁻¹ a d) x := fun a d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a d) hg.isOpen hx
  have hdg : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hx
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have hl : (fun z => gradVec g u z a) = fun z => ∑ d, (g z)⁻¹ a d * pd d u z := by
    funext z; simp [gradVec, mulVec, dotProduct]
  have hlx : ∀ c, gradVec g u x c = ∑ d, (g x)⁻¹ c d * pd d u x := fun c => by
    simp [gradVec, mulVec, dotProduct]
  unfold covD
  rw [hl, pd_sum Finset.univ (f := fun d y => (g y)⁻¹ a d * pd d u y) (fun d _ => (hdi a d).fun_mul (hdp d)) b,
    Finset.sum_congr rfl fun d _ => pd_mul (hdi a d) (hdp d) b]
  simp only [pd_inv_eq g x hgs hdg hdet, hlx]
  have e1 : ∑ d, ∑ α, christoffel g a b α x * (g x)⁻¹ α d * pd d u x =
      ∑ c, christoffel g a b c x * ∑ d, (g x)⁻¹ c d * pd d u x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have e2 : ∑ d, ∑ α, christoffel g d b α x * (g x)⁻¹ a α * pd d u x =
      ∑ d, (g x)⁻¹ a d * ∑ e, christoffel g e b d x * pd e u x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  have e3 : ∑ d, ((-∑ α, (christoffel g a b α x * (g x)⁻¹ α d + christoffel g d b α x * (g x)⁻¹ a α)) * pd d u x +
        (g x)⁻¹ a d * pd b (fun y => pd d u y) x) =
      -(∑ d, ∑ α, christoffel g a b α x * (g x)⁻¹ α d * pd d u x) -
        (∑ d, ∑ α, christoffel g d b α x * (g x)⁻¹ a α * pd d u x) +
        ∑ d, (g x)⁻¹ a d * pd b (fun y => pd d u y) x := by
    simp only [neg_mul, Finset.sum_mul, add_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  rw [e3, e1, e2]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **The derivative of the square of the gradient**: `∂_d (ℓ · ℓ) = 2 ℓᵇ (∂_d ∂_b u - Γᵉ_{db} ∂_e u)`. -/
theorem pd_gradSq (d : Fin n) :
    pd d (gradSq g u) x =
      2 * ∑ b, gradVec g u x b * (pd d (fun y => pd b u y) x - ∑ e, christoffel g e d b x * pd e u x) := by
  have hdp : ∀ d, DifferentiableAt ℝ (fun y => pd d u y) x := fun d =>
    differentiableAt_of_contDiffOn (contDiffOn_pd hu hg.isOpen d) hg.isOpen hx
  have hdi : ∀ a d, DifferentiableAt ℝ (fun y => (g y)⁻¹ a d) x := fun a d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a d) hg.isOpen hx
  have hdg : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x := fun a b =>
    differentiableAt_of_contDiffOn (hg.smooth a b) hg.isOpen hx
  have hdet : (g x).det ≠ 0 := (hg.isUnit_det x hx).ne_zero
  have hGs : ∀ b c, (g x)⁻¹ b c = (g x)⁻¹ c b := fun b c => by
    have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
      have : (g x)ᵀ = g x := by ext k l; exact hgs x l k
      rw [Matrix.transpose_nonsing_inv, this]
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hT c) b)
  have hlx : ∀ c, gradVec g u x c = ∑ d, (g x)⁻¹ c d * pd d u x := fun c => by
    simp [gradVec, mulVec, dotProduct]
  have hsq : gradSq g u = fun y => ∑ b, ∑ c, pd b u y * (g y)⁻¹ b c * pd c u y := by
    funext y
    simp only [gradSq, gradVec, dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have hterm : ∀ b c, pd d (fun y => pd b u y * (g y)⁻¹ b c * pd c u y) x =
      (pd d (fun y => pd b u y) x * (g x)⁻¹ b c + pd b u x * pd d (fun y => (g y)⁻¹ b c) x) * pd c u x +
        pd b u x * (g x)⁻¹ b c * pd d (fun y => pd c u y) x := fun b c => by
    rw [pd_mul ((hdp b).fun_mul (hdi b c)) (hdp c) d, pd_mul (hdp b) (hdi b c) d]
  rw [hsq, pd_sum Finset.univ (f := fun b y => ∑ c, pd b u y * (g y)⁻¹ b c * pd c u y)
    (fun b _ => DifferentiableAt.fun_sum fun c _ => ((hdp b).fun_mul (hdi b c)).fun_mul (hdp c)) d]
  rw [Finset.sum_congr rfl fun b _ => pd_sum Finset.univ (f := fun c y => pd b u y * (g y)⁻¹ b c * pd c u y)
    (fun c _ => ((hdp b).fun_mul (hdi b c)).fun_mul (hdp c)) d]
  simp only [hterm, pd_inv_eq g x hgs hdg hdet, hlx]
  -- the four sums
  have eT1 : ∑ b, ∑ c, pd d (fun y => pd b u y) x * (g x)⁻¹ b c * pd c u x =
      ∑ b, (∑ c, (g x)⁻¹ b c * pd c u x) * pd d (fun y => pd b u y) x := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  have eT3 : ∑ b, ∑ c, pd b u x * (g x)⁻¹ b c * pd d (fun y => pd c u y) x =
      ∑ b, (∑ c, (g x)⁻¹ b c * pd c u x) * pd d (fun y => pd b u y) x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by rw [hGs]; ring
  have eT2a : ∑ b, ∑ c, pd b u x * (∑ α, christoffel g b d α x * (g x)⁻¹ α c) * pd c u x =
      ∑ α, (∑ c, (g x)⁻¹ α c * pd c u x) * ∑ e, christoffel g e d α x * pd e u x := by
    calc ∑ b, ∑ c, pd b u x * (∑ α, christoffel g b d α x * (g x)⁻¹ α c) * pd c u x
        = ∑ b, ∑ c, ∑ α, pd b u x * christoffel g b d α x * (g x)⁻¹ α c * pd c u x := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun α _ => by ring
      _ = ∑ α, ∑ c, ∑ b, pd b u x * christoffel g b d α x * (g x)⁻¹ α c * pd c u x := by
          rw [Finset.sum_comm]
          rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
          rw [Finset.sum_comm]
      _ = _ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
  have eT2b : ∑ b, ∑ c, pd b u x * (∑ α, christoffel g c d α x * (g x)⁻¹ b α) * pd c u x =
      ∑ α, (∑ c, (g x)⁻¹ α c * pd c u x) * ∑ e, christoffel g e d α x * pd e u x := by
    calc ∑ b, ∑ c, pd b u x * (∑ α, christoffel g c d α x * (g x)⁻¹ b α) * pd c u x
        = ∑ b, ∑ c, ∑ α, pd b u x * christoffel g c d α x * (g x)⁻¹ b α * pd c u x := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun α _ => by ring
      _ = ∑ α, ∑ b, ∑ c, pd b u x * christoffel g c d α x * (g x)⁻¹ b α * pd c u x := by
          rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
          rw [Finset.sum_comm]
      _ = _ := by
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by rw [hGs b α]; ring
  have eS : ∑ b, ∑ c, ((pd d (fun y => pd b u y) x * (g x)⁻¹ b c +
        pd b u x * -∑ α, (christoffel g b d α x * (g x)⁻¹ α c + christoffel g c d α x * (g x)⁻¹ b α)) * pd c u x +
        pd b u x * (g x)⁻¹ b c * pd d (fun y => pd c u y) x) =
      (∑ b, ∑ c, pd d (fun y => pd b u y) x * (g x)⁻¹ b c * pd c u x) -
        (∑ b, ∑ c, pd b u x * (∑ α, christoffel g b d α x * (g x)⁻¹ α c) * pd c u x) -
        (∑ b, ∑ c, pd b u x * (∑ α, christoffel g c d α x * (g x)⁻¹ b α) * pd c u x) +
        ∑ b, ∑ c, pd b u x * (g x)⁻¹ b c * pd d (fun y => pd c u y) x := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_add_distrib]
    ring
  rw [eS, eT1, eT2a, eT2b, eT3]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring_nf
  simp only [Finset.sum_mul]

/-- **`∇_ℓ ℓ = ½ grad (ℓ · ℓ)`** for the gradient `ℓ` of a function: `ℓᵇ ∇_b ℓᵃ = ½ gᵃᵈ ∂_d (ℓ · ℓ)`. -/
theorem covDMat_gradVec_mulVec :
    covDMat g (gradVec g u) x *ᵥ gradVec g u x =
      fun a => ∑ d, (g x)⁻¹ a d * ((1 / 2) * pd d (gradSq g u) x) := by
  funext a
  simp only [mulVec, dotProduct, covDMat, Matrix.of_apply, covD_gradVec hg hgs hu hx, pd_gradSq hg hgs hu hx]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show ∀ S : ℝ, (1 / 2 : ℝ) * (2 * S) = S from fun S => by ring, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hc : pd b (fun y => pd d u y) x = pd d (fun y => pd b u y) x := pd_pd_comm hu hg.isOpen hx b d
  have hΓ : ∀ e, christoffel g e b d x = christoffel g e d b x := fun e => christoffel_symm g hgs e b d x
  rw [hc]
  simp only [hΓ]
  ring

/-- **The gradient of a function whose level sets are null near a point is geodesic there**: if `ℓ · ℓ = 0` near
`x`, then `∇_ℓ ℓ = 0` at `x`. -/
theorem gradVec_geodesic_of_null (hN : gradSq g u =ᶠ[𝓝 x] fun _ => 0) :
    covDMat g (gradVec g u) x *ᵥ gradVec g u x = 0 := by
  rw [covDMat_gradVec_mulVec hg hgs hu hx]
  have h0 : ∀ d, pd d (gradSq g u) x = 0 := fun d => by
    unfold pd
    rw [hN.fderiv_eq]
    simp
  funext a
  simp [h0]

/-- **The null generators with a non-affine normalization** (Gourgoulhon–Jaramillo (2.21)–(2.22)): for
`ℓ' = e^ρ ℓ` with `ℓ` the gradient of `u` and `ℓ · ℓ = 0` near `x`, `∇_{ℓ'} ℓ' = κ ℓ'` with `κ = ⟨dρ, ℓ'⟩`. -/
theorem covDMat_exp_smul_gradVec_of_null {ρ : (Fin n → ℝ) → ℝ} (hρ : DifferentiableAt ℝ ρ x)
    (hN : gradSq g u =ᶠ[𝓝 x] fun _ => 0) :
    covDMat g (fun y => Real.exp (ρ y) • gradVec g u y) x *ᵥ (Real.exp (ρ x) • gradVec g u x) =
      (∑ b, pd b ρ x * (Real.exp (ρ x) • gradVec g u x) b) • (Real.exp (ρ x) • gradVec g u x) := by
  have hdp : ∀ d, DifferentiableAt ℝ (fun y => pd d u y) x := fun d =>
    differentiableAt_of_contDiffOn (contDiffOn_pd hu hg.isOpen d) hg.isOpen hx
  have hdi : ∀ a d, DifferentiableAt ℝ (fun y => (g y)⁻¹ a d) x := fun a d =>
    differentiableAt_of_contDiffOn (hg.contDiffOn_inv a d) hg.isOpen hx
  have hdl : ∀ a, DifferentiableAt ℝ (fun y => gradVec g u y a) x := fun a => by
    have : (fun y => gradVec g u y a) = fun y => ∑ d, (g y)⁻¹ a d * pd d u y := by
      funext y; simp [gradVec, mulVec, dotProduct]
    rw [this]
    exact DifferentiableAt.fun_sum fun d _ => (hdi a d).fun_mul (hdp d)
  have hde : DifferentiableAt ℝ (fun y => Real.exp (ρ y)) x := hρ.exp
  have hpe : ∀ b, pd b (fun y => Real.exp (ρ y)) x = Real.exp (ρ x) * pd b ρ x := fun b => by
    unfold pd
    rw [(hρ.hasFDerivAt.exp).fderiv]
    simp [smul_eq_mul]
  have hcov : ∀ a b, covD g (fun y => Real.exp (ρ y) • gradVec g u y) a b x =
      Real.exp (ρ x) * (pd b ρ x * gradVec g u x a + covD g (gradVec g u) a b x) := fun a b => by
    unfold covD
    have : (fun z => (Real.exp (ρ z) • gradVec g u z) a) = fun z => Real.exp (ρ z) * gradVec g u z a := by
      funext z; simp [smul_eq_mul]
    rw [this, pd_mul hde (hdl a) b, hpe]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_add, mul_add, Finset.mul_sum, Finset.sum_congr rfl fun c _ =>
      (by ring : christoffel g a b c x * (Real.exp (ρ x) * gradVec g u x c) =
        Real.exp (ρ x) * (christoffel g a b c x * gradVec g u x c))]
    ring
  have hgeo := gradVec_geodesic_of_null hg hgs hu hx hN
  funext a
  have hga := congrFun hgeo a
  simp only [mulVec, dotProduct, covDMat, Matrix.of_apply, Pi.zero_apply] at hga
  simp only [mulVec, dotProduct, covDMat, Matrix.of_apply, hcov, Pi.smul_apply, smul_eq_mul]
  have e : ∑ b, Real.exp (ρ x) * (pd b ρ x * gradVec g u x a + covD g (gradVec g u) a b x) *
        (Real.exp (ρ x) * gradVec g u x b) =
      Real.exp (ρ x) * Real.exp (ρ x) * ((∑ b, pd b ρ x * gradVec g u x b) * gradVec g u x a +
        ∑ b, covD g (gradVec g u) a b x * gradVec g u x b) := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e, hga, add_zero, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

end

end Lightlike
