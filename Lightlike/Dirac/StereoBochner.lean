import Mathlib
import Lightlike.Dirac.StereoCurved
import Lightlike.Dirac.RicciIdentity
import Lightlike.Dirac.SpinDeriv

/-!
# Integrated Bochner identity on the round sphere in the stereographic chart

Pointwise (any frame with skew connection matrices, skew Clifford module):
`⟪∇ₐ∇ₐ f, f⟫ = ∂_{Fₐ}⟪∇ₐ f, f⟫ − ‖∇ₐ f‖²` (`inner_nablaF_nablaF`).  On the round sphere the divergence
term is compensated by the connection term of the frame Hessian after integration against the
Riemannian density `h^{-n}`, which gives `∫ ⟪−∑ ∇²f(Fᵢ,Fᵢ), f⟫ = ∫ ∑ ‖∇ᵢ f‖²`
(`integral_inner_neg_hess_stereo`) and the integrated Lichnerowicz formula.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open scoped RealInnerProductSpace

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `⟪γᵢγⱼ u, v⟫ = ⟪u, γⱼγᵢ v⟫` for a skew Clifford module. -/
lemma inner_gam_mul_gam {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (i j : Fin n) (u v : V) :
    inner ℝ ((gam ρ i * gam ρ j) u) v = inner ℝ u ((gam ρ j * gam ρ i) v) := by
  have hρ' : ∀ (i : Fin n) (w u : V), inner ℝ (gam ρ i w) u = -inner ℝ w (gam ρ i u) := hρ
  simp only [mul_apply_eq_comp, hρ', neg_neg]

/-- The spinorial connection form of a skew matrix is skew-adjoint on a skew Clifford module. -/
lemma spinForm_inner_skew {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, M i j = -M j i) (u v : V) :
    inner ℝ (spinForm ρ M u) v = -inner ℝ u (spinForm ρ M v) := by
  have h1 : inner ℝ (spinForm ρ M u) v =
      (1 / 4 : ℝ) * ∑ i, ∑ j, M i j * inner ℝ u ((gam ρ j * gam ρ i) v) := by
    simp only [spinForm, smul_apply, sum_apply,
      real_inner_smul_left, sum_inner, inner_gam_mul_gam hρ]
  have h2 : inner ℝ u (spinForm ρ M v) =
      (1 / 4 : ℝ) * ∑ i, ∑ j, M i j * inner ℝ u ((gam ρ i * gam ρ j) v) := by
    simp only [spinForm, smul_apply, sum_apply,
      real_inner_smul_right, inner_sum]
  rw [h1, h2, Finset.sum_comm (f := fun i j => M i j * inner ℝ u ((gam ρ j * gam ρ i) v))]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hM j i]
  ring

/-- **Pointwise Bochner identity.** For a skew Clifford module and a skew connection matrix `ω x a`,
`⟪∇ₐ∇ₐ f, f⟫ = ∂_{Fₐ}⟪∇ₐ f, f⟫ − ‖∇ₐ f‖²` at `x`. -/
lemma inner_nablaF_nablaF {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n} (a : Fin n)
    (hskew : ∀ k l, ω x a k l = -ω x a l k)
    (hfd : DifferentiableAt ℝ f x)
    (hu : DifferentiableAt ℝ (fun y => nablaF ρ F ω a f y) x) :
    inner ℝ (nablaF ρ F ω a (fun y => nablaF ρ F ω a f y) x) (f x) =
      fderiv ℝ (fun y => inner ℝ (nablaF ρ F ω a f y) (f y)) x (F x a) -
        ‖nablaF ρ F ω a f x‖ ^ 2 := by
  have hG := hu.hasFDerivAt.inner ℝ hfd.hasFDerivAt
  rw [hG.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply]
  have e1 : nablaF ρ F ω a (fun y => nablaF ρ F ω a f y) x =
      fderiv ℝ (fun y => nablaF ρ F ω a f y) x (F x a) +
        spinForm ρ (ω x a) (nablaF ρ F ω a f x) := rfl
  have hu0 : nablaF ρ F ω a f x = fderiv ℝ f x (F x a) + spinForm ρ (ω x a) (f x) := rfl
  have hn : ‖nablaF ρ F ω a f x‖ ^ 2 = inner ℝ (nablaF ρ F ω a f x) (fderiv ℝ f x (F x a)) +
      inner ℝ (nablaF ρ F ω a f x) (spinForm ρ (ω x a) (f x)) := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_right, ← hu0]
  rw [e1, inner_add_left, spinForm_inner_skew hρ hskew, hn]
  ring

end Lightlike.Dirac
