import Lightlike.OperatorAlgebras.QuasiFreeState.Pure
import Lightlike.OperatorAlgebras.FockIrreducible
import Lightlike.OperatorAlgebras.QuasiFree

/-!
# The Fock vacuum state is a pure quasi-free state

For a Fock representation `R : FockRep h K` of the CCR over a complex Hilbert space `h`, the vacuum vector state
`a ↦ ⟨Ω, a Ω⟩` on any star subalgebra `A ⊆ B(K)` containing the Weyl unitaries `W(f)` is

* a state with `ω(W(f)) = exp(-‖f‖²/4)` (`fockState_W`), i.e. the quasi-free state of the covariance
  `η = Re⟨·,·⟩` (`isCovariance_fock`: `|Im⟨f, g⟩|² ≤ ‖f‖² ‖g‖²`), and
* **pure** (`isPureState_fock`): the vacuum is cyclic and the commutant of the Weyl unitaries is trivial
  (`commutant_scalar`), so `isPureState_vecState` applies.

The same argument gives the purity criterion for a general quasi-free state in terms of its GNS representation
(`isPureState_of_irreducible`): if the commutant of the Weyl unitaries of the GNS space is trivial, the quasi-free state
is pure.

Reference: Bratteli–Robinson 2, Chapter 5 (`bratteli-robinson-1997`); no equation number is claimed.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

section Generic

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Purity of a vector state from generators**: let `S ⊆ A` be a set of operators such that `{s Ω : s ∈ S}` spans a
dense subspace and every operator commuting with `S` is a scalar. Then `a ↦ ⟨Ω, a Ω⟩` is a pure state of `A`. -/
theorem isPureState_vecState_of_gen {S : Set (K →L[ℂ] K)} (A : StarSubalgebra ℂ (K →L[ℂ] K)) (hSA : S ⊆ A)
    {Ω : K} (hΩ : ‖Ω‖ = 1)
    (hdense : Dense (Submodule.span ℂ ((fun s : K →L[ℂ] K => s Ω) '' S) : Set K))
    (hirr : ∀ T : K →L[ℂ] K, (∀ s ∈ S, T * s = s * T) → ∃ c : ℂ, T = c • 1) :
    IsPureState (vecState A Ω) := by
  refine isPureState_vecState hΩ ?_ fun T hT => hirr T fun s hs => hT s (hSA hs)
  have hsub : (Submodule.span ℂ ((fun s : K →L[ℂ] K => s Ω) '' S) : Set K) ⊆ Set.range (evalVec A Ω) := by
    intro v hv
    have : Submodule.span ℂ ((fun s : K →L[ℂ] K => s Ω) '' S) ≤ LinearMap.range (evalVec A Ω) :=
      Submodule.span_le.2 (by rintro _ ⟨s, hs, rfl⟩; exact ⟨⟨s, hSA hs⟩, rfl⟩)
    exact this hv
  exact hdense.mono hsub

end Generic

section Fock

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The Weyl unitary `W(f)` of a Fock representation as a bounded operator. -/
noncomputable def fockOp (R : FockRep h K) (f : h) : K →L[ℂ] K :=
  ((R.W f : K ≃ₗᵢ[ℂ] K) : K →L[ℂ] K)

lemma fockOp_apply (R : FockRep h K) (f : h) (ψ : K) : fockOp R f ψ = R.W f ψ := rfl

variable [CompleteSpace K]

/-- **The vacuum state of a Fock representation is pure** on every star subalgebra of `B(K)` containing the Weyl
unitaries (e.g. the algebra they generate, or its norm closure). -/
theorem isPureState_fock (R : FockRep h K) (A : StarSubalgebra ℂ (K →L[ℂ] K))
    (hA : ∀ f, fockOp R f ∈ A) : IsPureState (vecState A R.Ω) := by
  refine isPureState_vecState_of_gen A (S := Set.range (fockOp R)) (by rintro _ ⟨f, rfl⟩; exact hA f)
    R.norm_Ω ?_ ?_
  · rw [← Set.range_comp]
    have h1 : (Submodule.span ℂ (Set.range fun f => R.W f R.Ω)).topologicalClosure = ⊤ := R.cyclic
    rw [← Submodule.dense_iff_topologicalClosure_eq_top] at h1
    exact h1
  · intro T hT
    obtain ⟨c, hc⟩ := commutant_scalar R T fun f ψ => by
      have := congrArg (fun L : K →L[ℂ] K => L ψ) (hT (fockOp R f) ⟨f, rfl⟩)
      exact this
    exact ⟨c, ContinuousLinearMap.ext fun ψ => by simpa using hc ψ⟩

/-- **The Fock vacuum expectation**: `⟨Ω, W(f) Ω⟩ = exp(-‖f‖²/4)` on any star subalgebra containing `W(f)`. -/
theorem fockState_W (R : FockRep h K) (A : StarSubalgebra ℂ (K →L[ℂ] K)) (f : h) (hf : fockOp R f ∈ A) :
    vecState A R.Ω ⟨fockOp R f, hf⟩ = Complex.exp (-(‖f‖ ^ 2 / 4 : ℝ)) :=
  R.vacuum_expectation f

end Fock

section Cov

attribute [local instance] InnerProductSpace.complexToReal

variable (h : Type*) [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- **The Fock covariance** `η = Re⟨·,·⟩` satisfies `ω(f, g)² ≤ η(f, f) η(g, g)` for `ω = Im⟨·,·⟩`. -/
theorem isCovariance_fock : IsCovariance (symplecticForm h) (innerₗ h) where
  symm a b := real_inner_comm b a
  nonneg a := by
    rw [show innerₗ h a a = ‖a‖ ^ 2 from real_inner_self_eq_norm_sq a]; positivity
  sq_le a b := by
    rw [show innerₗ h a a = ‖a‖ ^ 2 from real_inner_self_eq_norm_sq a,
      show innerₗ h b b = ‖b‖ ^ 2 from real_inner_self_eq_norm_sq b, symplecticForm_apply, symp]
    have h1 := Complex.abs_im_le_norm ⟪a, b⟫_ℂ
    have h2 : ‖⟪a, b⟫_ℂ‖ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm _ _
    have h3 : |(⟪a, b⟫_ℂ).im| ≤ ‖a‖ * ‖b‖ := h1.trans h2
    calc (⟪a, b⟫_ℂ).im ^ 2 = |(⟪a, b⟫_ℂ).im| ^ 2 := (sq_abs _).symm
      _ ≤ (‖a‖ * ‖b‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by ring

end Cov

section QF

universe u

variable {V : Type u} [AddCommGroup V] [Module ℝ V] (ω η : LinearMap.BilinForm ℝ V)
  [Fact (qfKerM ω η).PosSemidef]

/-- **The quasi-free state is the vacuum vector state of its GNS representation.** -/
theorem qfState_eq_vecState (hω : ∀ a b, ω a b = -ω b a) :
    qfState ω η hω = vecState (qfAlgebra ω η hω) (qfVac ω η) := rfl

/-- **Purity criterion for quasi-free states** (the easy half): if the commutant of the Weyl unitaries of the GNS
representation of `ω_η` is trivial (the representation is irreducible), then the quasi-free state is pure. -/
theorem isPureState_qfState (hω : ∀ a b, ω a b = -ω b a)
    (hirr : ∀ T : QFSpace ω η →L[ℂ] QFSpace ω η, (∀ φ, T * qfOp ω η hω φ = qfOp ω η hω φ * T) →
      ∃ c : ℂ, T = c • 1) :
    IsPureState (qfState ω η hω) := by
  rw [qfState_eq_vecState]
  refine isPureState_vecState_of_gen (qfAlgebra ω η hω) (S := Set.range (qfOp ω η hω))
    (by rintro _ ⟨f, rfl⟩; exact (qfWA ω η hω f).2) (norm_qfVac ω η hω) ?_
    fun T hT => hirr T fun φ => hT _ ⟨φ, rfl⟩
  rw [← Set.range_comp]
  exact qfVac_cyclic ω η hω

end QF

end Lightlike.OperatorAlgebras.QuasiFreeState
