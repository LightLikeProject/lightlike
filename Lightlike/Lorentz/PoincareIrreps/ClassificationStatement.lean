module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Classification

/-!
# The classification of positive-energy irreducible Poincaré representations: a lockable statement (HA6)

This file **states** (it does not prove) Wigner's classification of the irreducible unitary
positive-energy representations of the Poincaré group `ISL2C = ℝ^{1,3} ⋊ SL(2,ℂ)` as a `Prop`-valued
definition `WignerClassification`, built from checkable pieces:

* `IsStronglyContinuous ρ`: continuity of `a ↦ ρ(a) ψ` on `Herm2` and of `A ↦ ρ(A) ψ` on `SL2C`;
* `HasPositiveEnergy ρ`: the spectral condition. For each `ψ` the positive-definite function
  `a ↦ ⟪ψ, ρ(a) ψ⟫` is the Fourier transform `∫ e^{i p·a} dμ_ψ(p)` of a finite measure supported in the
  closed forward cone `forwardCone` (`P² ≥ 0`, `P⁰ ≥ 0`);
* `IsIrreducible ρ`: no closed invariant subspace except `0` and the whole space;
* `EquivMassive ρ hm n` / `EquivMassless ρ h`: `ρ` is unitarily equivalent to the induced representation
  `poincareRep hm n` / `lightPoincareRep h` constructed in this folder, i.e. there is a dense-range
  isometry from an invariant space of square-integrable functions into the Hilbert space intertwining
  the two actions.

`WignerClassification` says that every irreducible strongly continuous unitary positive-energy
representation is (a) translation-trivial (a unitary irreducible representation of `SL(2,ℂ)`, the
zero-momentum sector), or (b) massive of mass `m > 0` and spin `n/2`, or (c) massless of finite helicity
`h/2`, or (d) a massless representation which is not of finite helicity (the infinite/continuous-spin
sector: the translations of the little group `ISO(2)` act non-trivially). The disjunct (d)
`MasslessNotHelicity` is only characterised negatively and by the support of the spectral measures in the
light cone; this is the honest content of the statement in this code base.

**Status.** `WignerClassification` is a statement, **not** a theorem here: its proof needs Mackey's
imprimitivity theorem and the spectral theorem for the translations. The sanity result
`trivialRep_admissible` shows that the hypotheses are satisfied by an example (so the definition is not
vacuous), and `trivialRep_classified` that it falls in case (a).

Reference: E. Wigner (1939); S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2. No equation
numbers are claimed.
-/

@[expose] public section

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

/-- The closed forward cone `P² ≥ 0`, `P⁰ ≥ 0` in the spinor model of momentum space. -/
def forwardCone : Set Herm2 :=
  {P | 0 ≤ P.1.det.re ∧ 0 ≤ P.1.trace.re}


section Statement

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The translation `a ∈ Herm2` as an element of `ISL2C`. -/
def transl (a : Herm2) : ISL2C := SemidirectProduct.inl (Multiplicative.ofAdd a)

/-- The Lorentz element `A` as an element of `ISL2C`. -/
def lorentzEl (A : SL2C) : ISL2C := SemidirectProduct.inr A

/-- **Strong continuity** of a unitary representation of `ISL2C`, on the two factors. -/
def IsStronglyContinuous (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  (∀ ψ : H, Continuous fun a : Herm2 => ρ (transl a) ψ) ∧
    ∀ ψ : H, Continuous fun A : SL2C => ρ (lorentzEl A) ψ

/-- **Spectral support**: for every vector `ψ`, the translation matrix coefficient
`a ↦ ⟪ψ, ρ(a) ψ⟫` is `∫ e^{i p·a} dμ(p)` for a finite measure `μ` carrying no mass outside `S`. -/
def SpectrumIn (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)) (S : Set Herm2) : Prop :=
  ∀ ψ : H, ∃ μ : Measure Herm2, IsFiniteMeasure μ ∧ μ Sᶜ = 0 ∧
    ∀ a : Herm2, ⟪ψ, ρ (transl a) ψ⟫_ℂ =
      ∫ p, Complex.exp (Complex.I * (pairing p a : ℂ)) ∂μ

/-- **Positive energy** (spectral condition): the translation spectrum lies in the closed forward
cone. -/
def HasPositiveEnergy (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  SpectrumIn ρ forwardCone

/-- **Irreducibility**: a nonzero space with no closed invariant subspaces except `0` and `⊤`. -/
def IsIrreducible (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  Nontrivial H ∧ ∀ K : Submodule ℂ H, IsClosed (K : Set H) → (∀ g v, v ∈ K → ρ g v ∈ K) →
    K = ⊥ ∨ K = ⊤

variable {m : ℝ}

/-- **Unitary equivalence with the massive induced representation** `poincareRep hm n` (completed
to `L²(shellMeasure)`): an invariant space `D` of measurable square-integrable functions and a linear
map `J : D → H` which is isometric for the `L²` norm, has dense range and intertwines the actions. -/
def EquivMassive (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)) (hm : 0 < m) (n : ℕ) : Prop :=
  ∃ (D : Submodule ℂ (massShell m → Fin (n + 1) → ℂ)) (J : D →ₗ[ℂ] H),
    (∀ g, ∀ ψ ∈ D, poincareRep hm n g ψ ∈ D) ∧
    (∀ ψ : D, Measurable (fun P => ENNReal.ofReal (fibreNormSq (ψ.1 P))) ∧
      ∫⁻ P, ENNReal.ofReal (fibreNormSq (ψ.1 P)) ∂shellMeasure hm < ⊤ ∧
      ‖J ψ‖ ^ 2 = (∫⁻ P, ENNReal.ofReal (fibreNormSq (ψ.1 P)) ∂shellMeasure hm).toReal) ∧
    (LinearMap.range J).topologicalClosure = ⊤ ∧
    ∀ (g : ISL2C) (ψ φ : D), (φ : massShell m → Fin (n + 1) → ℂ) = poincareRep hm n g ψ →
      ρ g (J ψ) = J φ

/-- **Unitary equivalence with the massless induced representation** `lightPoincareRep h` (completed
to `L²(coneMeasure)`); same shape as `EquivMassive`. -/
def EquivMassless (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)) (h : ℤ) : Prop :=
  ∃ (D : Submodule ℂ (lightCone → ℂ)) (J : D →ₗ[ℂ] H),
    (∀ g, ∀ ψ ∈ D, lightPoincareRep h g ψ ∈ D) ∧
    (∀ ψ : D, Measurable (fun P => ENNReal.ofReal (‖ψ.1 P‖ ^ 2)) ∧
      ∫⁻ P, ENNReal.ofReal (‖ψ.1 P‖ ^ 2) ∂coneMeasure < ⊤ ∧
      ‖J ψ‖ ^ 2 = (∫⁻ P, ENNReal.ofReal (‖ψ.1 P‖ ^ 2) ∂coneMeasure).toReal) ∧
    (LinearMap.range J).topologicalClosure = ⊤ ∧
    ∀ (g : ISL2C) (ψ φ : D), (φ : lightCone → ℂ) = lightPoincareRep h g ψ →
      ρ g (J ψ) = J φ

/-- The remaining massless sector (infinite / continuous spin): spectrum in the light cone, but not
equivalent to any finite-helicity representation. -/
def MasslessNotHelicity (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)) : Prop :=
  SpectrumIn ρ (lightCone ∪ {0}) ∧ ∀ h : ℤ, ¬ EquivMassless ρ h

end Statement

/-- **Wigner's classification (statement, not proved here).** Every irreducible, strongly continuous,
unitary, positive-energy representation of the Poincaré group `ISL2C` on a Hilbert space is (a) trivial
on the translations, or (b) equivalent to a massive representation `poincareRep hm n` (mass `m > 0`,
spin `n/2`), or (c) equivalent to a massless finite-helicity representation `lightPoincareRep h`, or
(d) massless of infinite spin (`MasslessNotHelicity`). -/
def WignerClassification : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : ISL2C →* (H ≃ₗᵢ[ℂ] H)),
    IsStronglyContinuous ρ → HasPositiveEnergy ρ → IsIrreducible ρ →
      (∀ a : Herm2, ρ (transl a) = 1) ∨
      (∃ (m : ℝ) (hm : 0 < m) (n : ℕ), EquivMassive ρ hm n) ∨
      (∃ h : ℤ, EquivMassless ρ h) ∨
      MasslessNotHelicity ρ

/-! ## Non-vacuity: the trivial representation on `ℂ` -/

/-- The trivial representation of `ISL2C` on `ℂ`. -/
noncomputable def trivialRep : ISL2C →* (ℂ ≃ₗᵢ[ℂ] ℂ) := 1

lemma pairing_zero_left (a : Herm2) : pairing 0 a = 0 := by
  simp [pairing]

/-- The trivial representation is strongly continuous, of positive energy and irreducible. -/
theorem trivialRep_admissible :
    IsStronglyContinuous trivialRep ∧ HasPositiveEnergy trivialRep ∧ IsIrreducible trivialRep := by
  refine ⟨⟨fun ψ => ?_, fun ψ => ?_⟩, fun ψ => ?_, ⟨inferInstance, fun K _ _ => ?_⟩⟩
  · simpa [trivialRep] using continuous_const
  · simpa [trivialRep] using continuous_const
  · have h0 : (0 : Herm2) ∈ forwardCone := by simp [forwardCone]
    refine ⟨ENNReal.ofReal (‖ψ‖ ^ 2) • Measure.dirac (0 : Herm2), ?_, ?_, fun a => ?_⟩
    · exact Measure.smul_finite _ ENNReal.ofReal_ne_top
    · have : Measure.dirac (0 : Herm2) forwardConeᶜ = 0 := by
        rw [Measure.dirac_apply]
        simp [h0]
      simp [this]
    · rw [integral_smul_measure, integral_dirac]
      simp [trivialRep, pairing_zero_left, inner_self_eq_norm_sq_to_K]
  · exact eq_bot_or_eq_top K

/-- The trivial representation falls in case (a) of `WignerClassification`. -/
theorem trivialRep_classified : ∀ a : Herm2, trivialRep (transl a) = 1 := fun _ => rfl

end Lightlike.Lorentz.Poincare
