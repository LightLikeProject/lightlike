import Lightlike.OperatorAlgebras.FiniteGNS
import Lightlike.OperatorAlgebras.GramUnitary

/-!
# Uniqueness of the GNS representation of a faithful state on a matrix algebra

Jakšić, Ogata, Pautrat and Pillet, arXiv:1106.3786, Exercise 2.15 (3), p. 61 (read): every cyclic representation associated with the state
`ν` is equivalent to the GNS representation. Here `gns_unique`: a cyclic `*`-representation `(H, π, ψ)` of `Matrix n n ℂ` with
`⟪ψ, π(A) ψ⟫ = tr(ν A)` (`ν` positive definite) is unitarily equivalent to `(GNSMat ν, gnsRep ν, gnsVec ν)`, through the repo's
`exists_unitary_of_gram_eq` (equal Gram matrices `⟪π(A) ψ, π(B) ψ⟫ = tr(ν A* B)`).
-/

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace Lightlike.OperatorAlgebras

open GNSMat

variable {n : Type*} [Fintype n] [DecidableEq n] (ν : Matrix n n ℂ) [Fact ν.PosDef]

lemma inner_gnsRep_gnsVec (A B : Matrix n n ℂ) :
    ⟪gnsRep ν A (gnsVec ν), gnsRep ν B (gnsVec ν)⟫_ℂ = (ν * (Aᴴ * B)).trace := by
  rw [gnsVec, gnsRep_toGNS, gnsRep_toGNS, inner_toGNS, Matrix.mul_one, Matrix.mul_one, trace_mul_cycle]
  exact trace_mul_comm _ _

/-- **The GNS representation is unique** (Jakšić-Ogata-Pautrat-Pillet, Exercise 2.15 (3), p. 61): a cyclic `*`-representation
`(H, π, ψ)` of `Matrix n n ℂ` with `⟪ψ, π(A) ψ⟫ = tr(ν A)` is unitarily equivalent to the GNS representation, by a unitary that maps
`ψ` to `η_ν` and intertwines `π` with `π_ν`. -/
theorem gns_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix n n ℂ → H →L[ℂ] H) (hmul : ∀ A B, π (A * B) = (π A).comp (π B)) (hone : π 1 = ContinuousLinearMap.id ℂ H)
    (hadd : ∀ A B, π (A + B) = π A + π B) (hsmul : ∀ (c : ℂ) A, π (c • A) = c • π A)
    (hstar : ∀ A x y, ⟪π A x, y⟫_ℂ = ⟪x, π Aᴴ y⟫_ℂ) (ψ : H)
    (hcyc : Dense ((Submodule.span ℂ (Set.range fun A => π A ψ) : Submodule ℂ H) : Set H))
    (hstate : ∀ A, ⟪ψ, π A ψ⟫_ℂ = (ν * A).trace) :
    ∃ U : H ≃ₗᵢ[ℂ] GNSMat ν, U ψ = gnsVec ν ∧ ∀ A x, U (π A x) = gnsRep ν A (U x) := by
  set Φ₁ : (Matrix n n ℂ →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ fun A => π A ψ with hΦ₁
  set Φ₂ : (Matrix n n ℂ →₀ ℂ) →ₗ[ℂ] GNSMat ν := Finsupp.linearCombination ℂ fun A => gnsRep ν A (gnsVec ν) with hΦ₂
  have hgram : ∀ A B, ⟪Φ₁ (Finsupp.single A 1), Φ₁ (Finsupp.single B 1)⟫_ℂ =
      ⟪Φ₂ (Finsupp.single A 1), Φ₂ (Finsupp.single B 1)⟫_ℂ := by
    intro A B
    simp only [hΦ₁, hΦ₂, Finsupp.linearCombination_single, one_smul]
    rw [inner_gnsRep_gnsVec, hstar, ← ContinuousLinearMap.comp_apply, ← hmul, hstate]
  have hd₁ : Dense ((LinearMap.range Φ₁ : Submodule ℂ H) : Set H) := by
    rwa [hΦ₁, Finsupp.range_linearCombination]
  have hd₂ : Dense ((LinearMap.range Φ₂ : Submodule ℂ (GNSMat ν)) : Set (GNSMat ν)) := by
    rw [hΦ₂, Finsupp.range_linearCombination]
    refine Dense.mono (fun x _ => ?_) dense_univ
    obtain ⟨A, hA⟩ := gnsRep_gnsVec_surjective ν x
    exact Submodule.subset_span ⟨A, hA⟩
  obtain ⟨U, hU⟩ := exists_unitary_of_gram_eq hgram hd₁ hd₂
  have hUA : ∀ A, U (π A ψ) = gnsRep ν A (gnsVec ν) := by
    intro A
    have := hU (Finsupp.single A 1)
    simpa [hΦ₁, hΦ₂, Finsupp.linearCombination_single] using this
  refine ⟨U, ?_, fun A x => ?_⟩
  · have := hUA 1
    rwa [hone, gnsRep_one, ContinuousLinearMap.id_apply, LinearMap.id_apply] at this
  · -- both sides are continuous in `x` and agree on the dense span of the `π B ψ`
    have hc1 : Continuous fun x => U (π A x) := U.continuous.comp (π A).continuous
    have hc2 : Continuous fun x => gnsRep ν A (U x) :=
      (LinearMap.continuous_of_finiteDimensional (gnsRep ν A)).comp U.continuous
    have heq : Set.EqOn (fun x => U (π A x)) (fun x => gnsRep ν A (U x))
        (Submodule.span ℂ (Set.range fun B => π B ψ) : Set H) := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => U (π A x) = gnsRep ν A (U x)) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨B, rfl⟩
        rw [← ContinuousLinearMap.comp_apply, ← hmul, hUA, hUA, ← LinearMap.comp_apply, ← gnsRep_mul]
      · simp
      · intro x y _ _ hx hy
        simp only [map_add, hx, hy]
      · intro c x _ hx
        simp only [map_smul, hx]
    exact congrFun (Continuous.ext_on hcyc hc1 hc2 heq) x

end Lightlike.OperatorAlgebras
