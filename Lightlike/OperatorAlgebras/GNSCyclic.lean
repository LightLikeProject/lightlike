import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Lightlike.OperatorAlgebras.GramUnitary

/-!
# The cyclic vector of the GNS representation, and its uniqueness

Mathlib's `PositiveLinearMap.GNS` is the Hilbert space of a positive linear functional `f` on a C*-algebra `A`, and
`f.gnsStarAlgHom` its `*`-representation; the cyclic vector is left open there. Here, for a unital `A`: the class `ζ_f` of `1` satisfies
`⟪ζ_f, π_f(a) ζ_f⟫ = f a` (`inner_gnsCyclicVec`) and is cyclic (`denseRange_gnsCyclicVec`), and every cyclic `*`-representation
`(H, π, ψ)` with `⟪ψ, π(a) ψ⟫ = f a` is unitarily equivalent to it (`gns_unique_cstar`).

For `A = B(K)` (matrices) this is Jakšić, Ogata, Pautrat and Pillet, arXiv:1106.3786, Exercise 2.15, p. 61 (read), for every state:
the cyclic representation associated with `ν` exists and is unique up to unitary equivalence.
-/

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace Lightlike.OperatorAlgebras

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

/-- The GNS cyclic vector `ζ_f`, the class of `1`. -/
noncomputable def gnsCyclicVec : f.GNS := ((f.toPreGNS 1 : f.PreGNS) : f.GNS)

lemma gnsStarAlgHom_cyclicVec (a : A) :
    f.gnsStarAlgHom a (gnsCyclicVec f) = ((f.toPreGNS a : f.PreGNS) : f.GNS) := by
  simp [gnsCyclicVec]

/-- **The state is the vector state of the cyclic vector**: `⟪ζ_f, π_f(a) ζ_f⟫ = f a`. -/
theorem inner_gnsCyclicVec (a : A) : ⟪gnsCyclicVec f, f.gnsStarAlgHom a (gnsCyclicVec f)⟫_ℂ = f a := by
  rw [gnsStarAlgHom_cyclicVec, gnsCyclicVec, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
  simp

/-- **The cyclic vector is cyclic**: the vectors `π_f(a) ζ_f` are dense. -/
theorem denseRange_gnsCyclicVec : DenseRange fun a : A => f.gnsStarAlgHom a (gnsCyclicVec f) := by
  have h : (fun a : A => f.gnsStarAlgHom a (gnsCyclicVec f)) = (fun x : f.PreGNS => (x : f.GNS)) ∘ f.toPreGNS := by
    funext a
    exact gnsStarAlgHom_cyclicVec f a
  rw [h, DenseRange, f.toPreGNS.surjective.range_comp]
  exact Completion.denseRange_coe

/-- **Uniqueness of the GNS representation**: a cyclic `*`-representation `(H, π, ψ)` with `⟪ψ, π(a) ψ⟫ = f a` is unitarily
equivalent to `(f.GNS, π_f, ζ_f)`. -/
theorem gns_unique_cstar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : H)
    (hcyc : Dense ((Submodule.span ℂ (Set.range fun a => π a ψ) : Submodule ℂ H) : Set H))
    (hstate : ∀ a, ⟪ψ, π a ψ⟫_ℂ = f a) :
    ∃ U : H ≃ₗᵢ[ℂ] f.GNS, U ψ = gnsCyclicVec f ∧ ∀ a x, U (π a x) = f.gnsStarAlgHom a (U x) := by
  set Φ₁ : (A →₀ ℂ) →ₗ[ℂ] H := Finsupp.linearCombination ℂ fun a => π a ψ with hΦ₁
  set Φ₂ : (A →₀ ℂ) →ₗ[ℂ] f.GNS := Finsupp.linearCombination ℂ fun a => f.gnsStarAlgHom a (gnsCyclicVec f) with hΦ₂
  have hπstar : ∀ a x y, ⟪π a x, y⟫_ℂ = ⟪x, π (star a) y⟫_ℂ := by
    intro a x y
    rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hgram : ∀ a b, ⟪Φ₁ (Finsupp.single a 1), Φ₁ (Finsupp.single b 1)⟫_ℂ =
      ⟪Φ₂ (Finsupp.single a 1), Φ₂ (Finsupp.single b 1)⟫_ℂ := by
    intro a b
    simp only [hΦ₁, hΦ₂, Finsupp.linearCombination_single, one_smul]
    rw [hπstar, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul, hstate,
      gnsStarAlgHom_cyclicVec, gnsStarAlgHom_cyclicVec, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]
    simp
  have hd₁ : Dense ((LinearMap.range Φ₁ : Submodule ℂ H) : Set H) := by
    rwa [hΦ₁, Finsupp.range_linearCombination]
  have hd₂ : Dense ((LinearMap.range Φ₂ : Submodule ℂ f.GNS) : Set f.GNS) := by
    rw [hΦ₂, Finsupp.range_linearCombination]
    exact (denseRange_gnsCyclicVec f).mono Submodule.subset_span
  obtain ⟨U, hU⟩ := exists_unitary_of_gram_eq hgram hd₁ hd₂
  have hUa : ∀ a, U (π a ψ) = f.gnsStarAlgHom a (gnsCyclicVec f) := by
    intro a
    have := hU (Finsupp.single a 1)
    simpa [hΦ₁, hΦ₂, Finsupp.linearCombination_single] using this
  refine ⟨U, ?_, fun a x => ?_⟩
  · have := hUa 1
    simpa using this
  · have hc1 : Continuous fun x => U (π a x) := U.continuous.comp (π a).continuous
    have hc2 : Continuous fun x => f.gnsStarAlgHom a (U x) := (f.gnsStarAlgHom a).continuous.comp U.continuous
    have heq : Set.EqOn (fun x => U (π a x)) (fun x => f.gnsStarAlgHom a (U x))
        (Submodule.span ℂ (Set.range fun b => π b ψ) : Set H) := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => U (π a x) = f.gnsStarAlgHom a (U x)) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨b, rfl⟩
        rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul, hUa, hUa, map_mul,
          ContinuousLinearMap.mul_apply]
      · simp
      · intro x y _ _ hx hy
        simp only [map_add, hx, hy]
      · intro c x _ hx
        simp only [map_smul, hx]
    exact congrFun (Continuous.ext_on hcyc hc1 hc2 heq) x

end Lightlike.OperatorAlgebras
