import Lightlike.OperatorAlgebras.Spectral.Stone.Theorem
import Lightlike.OperatorAlgebras.Spectral.Unbounded.Cayley

/-!
# Operators commuting with a one-parameter unitary group

A bounded operator `T` commuting with every `U(t)` of a one-parameter unitary group maps the domain of the generator
`A` into itself and commutes with `A` (`commute_generator`), hence with every resolvent `(A − λ)⁻¹`
(`commute_resolvent`) and with the Cayley transform of `A` (`commute_cayley`). Two commuting strongly continuous
one-parameter unitary groups therefore have commuting Cayley transforms (`cayley_commute_of_commute`), the first
step towards their joint spectral measure.

Supporting results for the joint spectral measure of the translations; no catalogue entry.
-/

open scoped InnerProductSpace LinearPMap Topology
open Filter Lightlike.OperatorAlgebras.Spectral Lightlike.OperatorAlgebras.Spectral.Stone
  Lightlike.OperatorAlgebras.Spectral.Unbounded

namespace Lightlike.Poincare

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A bounded operator commuting with every `U(t)` commutes with the generator.** -/
lemma commute_generator {U : ℝ → (H ≃ₗᵢ[ℂ] H)} (T : H →L[ℂ] H) (hT : ∀ t ψ, T (U t ψ) = U t (T ψ))
    (ψ : (generator U).domain) :
    ∃ h : T ψ ∈ (generator U).domain, generator U ⟨T ψ, h⟩ = T (generator U ψ) := by
  rw [exists_generator_eq_iff]
  have h := (exists_generator_eq_iff U ψ (generator U ψ)).1 ⟨ψ.2, rfl⟩
  have e : generatorQuotient U (T ψ) = fun t => T (generatorQuotient U ψ t) := by
    funext t
    simp only [generatorQuotient, map_smul, map_sub, hT]
  rw [e]
  exact (T.continuous.tendsto _).comp h

/-- **A bounded operator commuting with `A` commutes with every resolvent of `A`.** -/
lemma commute_resolvent {A : H →ₗ.[ℂ] H} {lam : ℂ} {B : H →L[ℂ] H} (hB : IsResolvent A lam B) (T : H →L[ℂ] H)
    (hT : ∀ ψ : A.domain, ∃ h : T ψ ∈ A.domain, A ⟨T ψ, h⟩ = T (A ψ)) (φ : H) : B (T φ) = T (B φ) := by
  obtain ⟨h, hA⟩ := hT ⟨B φ, hB.mem_domain φ⟩
  have h1 := hB.rightInverse φ
  have h2 := hB.leftInverse ⟨T (B φ), h⟩
  simp only at h2
  rw [hA, ← map_smul, ← map_sub, h1] at h2
  exact h2

/-- **A bounded operator commuting with `A` commutes with its Cayley transform.** -/
lemma commute_cayley {A : H →ₗ.[ℂ] H} {B C : H →L[ℂ] H} (hC : IsCayleyTransform A B C) (T : H →L[ℂ] H)
    (hT : ∀ ψ : A.domain, ∃ h : T ψ ∈ A.domain, A ⟨T ψ, h⟩ = T (A ψ)) (φ : H) : C (T φ) = T (C φ) := by
  have hB := commute_resolvent hC.isResolvent T hT
  obtain ⟨h3, e3⟩ := hT ⟨B φ, hC.isResolvent.mem_domain φ⟩
  have e2 : (⟨B (T φ), hC.isResolvent.mem_domain (T φ)⟩ : A.domain) = ⟨T (B φ), h3⟩ := Subtype.ext (hB φ)
  rw [hC.apply_eq (T φ), hC.apply_eq φ, e2, e3, map_add, map_smul, hB φ]

/-- A bounded operator commuting with every `U(t)` commutes with the Cayley transform of the generator. -/
lemma commute_cayley_of_commute_group {U : ℝ → (H ≃ₗᵢ[ℂ] H)} {B C : H →L[ℂ] H}
    (hC : IsCayleyTransform (generator U) B C) (T : H →L[ℂ] H) (hT : ∀ t ψ, T (U t ψ) = U t (T ψ)) (φ : H) :
    C (T φ) = T (C φ) :=
  commute_cayley hC T (commute_generator T hT) φ

/-- **Commuting one-parameter unitary groups have commuting Cayley transforms.** -/
theorem cayley_commute_of_commute {U V : ℝ → (H ≃ₗᵢ[ℂ] H)} (hUV : ∀ s t ψ, U s (V t ψ) = V t (U s ψ))
    {B C B' C' : H →L[ℂ] H} (hC : IsCayleyTransform (generator U) B C)
    (hC' : IsCayleyTransform (generator V) B' C') (φ : H) : C (C' φ) = C' (C φ) := by
  -- `C` commutes with every `V(t)`
  have h1 : ∀ t ψ, C (V t ψ) = V t (C ψ) := fun t ψ =>
    commute_cayley_of_commute_group hC (V t).toContinuousLinearEquiv.toContinuousLinearMap
      (fun s χ => (hUV s t χ).symm) ψ
  exact (commute_cayley_of_commute_group hC' C h1 φ).symm

end

end Lightlike.Poincare
