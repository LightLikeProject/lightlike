import Lightlike.OperatorAlgebras.QuasiFreeState.Covariance

/-!
# The quasi-free functional on the Weyl coefficients, and its positivity

For a covariance `η` the quasi-free functional is the linear map `qfFunctional ω η` on finitely supported coefficient
functions `f : V →₀ ℂ` (the algebraic Weyl algebra, with basis `W(φ)`), `W(φ) ↦ exp(-¼ η(φ, φ))`
(Bratteli-Robinson 2, Chapter 5; Dereziński, arXiv:math-ph/0511030, Section 9.1).

* `qfFunctional_single_zero`: normalization `ω_η(W(0)) = 1`.
* `qfFunctional_twNormSq`: `ω_η(a* a) = ∑ conj(fᵩ) f_ψ ⟨W(φ) Ω, W(ψ) Ω⟩`, the quadratic form of `qfKer`.
* `qfFunctional_twNormSq_nonneg`: **positivity**, `ω_η(a* a) ≥ 0` (from `posSemidef_qfKer`).
* `qfFunctional_comp_linearCombination_nonneg`: the same for any Weyl system in any star algebra.
-/

open scoped ComplexOrder ComplexConjugate

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω η : LinearMap.BilinForm ℝ V}

/-- **The quasi-free functional** on the coefficients of the Weyl algebra: `W(φ) ↦ exp(-¼ η(φ, φ))`, extended
linearly. -/
noncomputable def qfFunctional (η : LinearMap.BilinForm ℝ V) : (V →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun f => ((gaussVal η f : ℝ) : ℂ))

lemma qfFunctional_single (η : LinearMap.BilinForm ℝ V) (f : V) (c : ℂ) :
    qfFunctional η (Finsupp.single f c) = c * (gaussVal η f : ℂ) := by
  simp [qfFunctional, Finsupp.linearCombination_single]

/-- **Normalization**: the quasi-free functional takes the value `1` on `W(0) = 1`. -/
theorem qfFunctional_single_zero (η : LinearMap.BilinForm ℝ V) :
    qfFunctional η (Finsupp.single 0 1) = 1 := by
  simp [qfFunctional_single, gaussVal]

/-- The quasi-free functional on `a* a`, `a = ∑ fᵩ W(φ)`, is the quadratic form of the Gram kernel `qfKer`. -/
theorem qfFunctional_twNormSq (f : V →₀ ℂ) :
    qfFunctional η (twNormSq ω f) =
      f.sum fun φ a => f.sum fun ψ b => star a * qfKer ω η φ ψ * b := by
  simp only [twNormSq, map_finsuppSum, qfFunctional_single, qfKer, Matrix.of_apply]
  refine Finsupp.sum_congr fun φ _ => Finsupp.sum_congr fun ψ _ => ?_
  have h1 : η (-φ + ψ) (-φ + ψ) = η (ψ - φ) (ψ - φ) := by rw [neg_add_eq_sub]
  have h2 : ω (-φ) ψ = -ω φ ψ := by simp
  simp only [gaussVal, h1, h2, Complex.ofReal_exp, Complex.ofReal_neg, neg_div, mul_neg, neg_neg]
  simp only [Complex.ofReal_div]
  push_cast
  simp only [Complex.star_def]
  ring_nf

/-- **Positivity of the quasi-free functional**: `ω_η(a* a) ≥ 0` for every `a = ∑ fᵩ W(φ)`. -/
theorem qfFunctional_twNormSq_nonneg (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η)
    (f : V →₀ ℂ) : 0 ≤ qfFunctional η (twNormSq ω f) := by
  rw [qfFunctional_twNormSq]
  exact (posSemidef_qfKer hω hη).2 f

/-- `∑ (twNormSq f)ᵩ W(φ) = (∑ fᵩ W(φ))* (∑ fᵩ W(φ))` in any unital star algebra (the version in `WeylAlgebra.lean`
is stated under C*-algebra section hypotheses). -/
lemma linearCombination_twNormSq' {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {W : V → A}
    (hW : IsWeylSystem ω W) (f : V →₀ ℂ) :
    Finsupp.linearCombination ℂ W (twNormSq ω f) =
      star (Finsupp.linearCombination ℂ W f) * Finsupp.linearCombination ℂ W f := by
  simp only [twNormSq, map_sum, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [star_smul, ← hW.map_neg, smul_mul_smul_comm, hW.mul, smul_smul, mul_comm]
  exact Finsupp.sum_single_index (h := fun x (c : ℂ) => c • W x) (zero_smul ℂ _)

/-- **Positivity on any Weyl system**: for a Weyl system `W` of `(V, ω)` in a unital star algebra `A`, any linear
functional `ρ` on `A` with `ρ(W(φ)) = exp(-¼ η(φ, φ))` satisfies `ρ(a* a) ≥ 0` on the span of the `W(φ)`. -/
theorem qfFunctional_comp_linearCombination_nonneg {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {W : V → A} (hW : IsWeylSystem ω W) (ρ : A →ₗ[ℂ] ℂ) (hρ : ∀ φ, ρ (W φ) = (gaussVal η φ : ℂ))
    (hω : ∀ a b, ω a b = -ω b a) (hη : IsCovariance ω η) (f : V →₀ ℂ) :
    0 ≤ ρ (star (Finsupp.linearCombination ℂ W f) * Finsupp.linearCombination ℂ W f) := by
  have hρ' : ρ.comp (Finsupp.linearCombination ℂ W) = qfFunctional η := by
    apply Finsupp.lhom_ext
    intro φ c
    simp [qfFunctional, hρ]
  have h2 := linearCombination_twNormSq' hW f
  have := LinearMap.congr_fun hρ' (twNormSq ω f)
  simp only [LinearMap.comp_apply] at this
  rw [← h2, this]
  exact qfFunctional_twNormSq_nonneg hω hη f

end Lightlike.OperatorAlgebras.QuasiFreeState
