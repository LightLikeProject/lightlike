import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The Weyl relations, Fock representations and Bogoliubov transformations

Definitions for the statement of Shale's criterion (milestone OP2). Let `h` be a complex Hilbert space
(the one-particle space) with the symplectic form `σ(f, g) = Im ⟪f, g⟫`.

* `Bogoliubov h`: a bounded real-linear bijection of `h` that preserves `σ`; its complex-linear part `α`
  and antilinear part `β` are `alphaPart` and `betaPart` (`T f = α f + β f`).
* `IsHilbertSchmidt B`: `∑ ‖B bᵢ‖² < ∞` for every Hilbert basis `b` of `h`.
* `CCRRep h K`: a representation of the Weyl relations `W f ∘ W g = exp(-i σ(f, g) / 2) • W (f + g)` by
  unitaries `W f` of a Hilbert space `K`, strongly continuous along every real line.
* `FockRep h K`: a CCR representation with a unit cyclic vector `Ω` (the vacuum) with the Fock expectation
  `⟪Ω, W f Ω⟫ = exp(-‖f‖² / 4)`.
* `Implements R T`: the Bogoliubov transformation `T` is implemented by a unitary `U` of `K`,
  `U (W f ψ) = W (T f) (U ψ)`.

**Design choice.** The Fock space is not built here (Mathlib has only `SymmetricAlgebra`, `lp` and tensor
products, and no Fock construction), so the *Fock representation* is characterized as the cyclic
representation with the vacuum expectation `exp(-‖f‖²/4)`, which is the GNS representation of the Fock
state (Bratteli–Robinson 2, Chapter 5). Whether such a representation exists, and that it is unique up to
unitary equivalence, are statements (`T-OP2-P1`, `T-OP2-P2`), not part of the definition.
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

variable (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- The symplectic form `σ(f, g) = Im ⟪f, g⟫` of a complex Hilbert space. -/
noncomputable def symp (f g : h) : ℝ := (⟪f, g⟫_ℂ).im

/-- **A Bogoliubov transformation** of the one-particle space `h`: a continuous real-linear bijection
that preserves the symplectic form `σ(f, g) = Im ⟪f, g⟫`. -/
structure Bogoliubov where
  /-- The underlying real-linear homeomorphism. -/
  toEquiv : h ≃L[ℝ] h
  /-- It preserves the symplectic form. -/
  symp_map : ∀ f g, symp h (toEquiv f) (toEquiv g) = symp h f g

variable {h}

/-- The complex-linear part `α f = (T f - i T (i f)) / 2` of a Bogoliubov transformation. -/
noncomputable def Bogoliubov.alphaPart (T : Bogoliubov h) (f : h) : h :=
  (1 / 2 : ℂ) • (T.toEquiv f - Complex.I • T.toEquiv (Complex.I • f))

/-- The antilinear part `β f = (T f + i T (i f)) / 2` of a Bogoliubov transformation, so that
`T f = α f + β f`. -/
noncomputable def Bogoliubov.betaPart (T : Bogoliubov h) (f : h) : h :=
  (1 / 2 : ℂ) • (T.toEquiv f + Complex.I • T.toEquiv (Complex.I • f))

/-- **A Hilbert–Schmidt map** `B` of `h`: `∑ ‖B bᵢ‖² < ∞` for every Hilbert basis `b` of `h`. -/
def IsHilbertSchmidt (B : h → h) : Prop :=
  ∀ (ι : Type u) (b : HilbertBasis ι ℂ h), Summable fun i => ‖B (b i)‖ ^ 2

variable (h) (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **A representation of the Weyl relations** (CCR) of `h` on a Hilbert space `K`: unitaries `W f` with
`W 0 = 1`, `W f ∘ W g = exp(-i σ(f, g) / 2) • W (f + g)`, and `t ↦ W (t • f) ψ` continuous. -/
structure CCRRep where
  /-- The Weyl unitary of a vector `f`. -/
  W : h → (K ≃ₗᵢ[ℂ] K)
  /-- `W 0 = 1`. -/
  W_zero : W 0 = LinearIsometryEquiv.refl ℂ K
  /-- The Weyl relation. -/
  weyl : ∀ f g ψ, W f (W g ψ) = Complex.exp (-(Complex.I * (symp h f g / 2 : ℝ))) • W (f + g) ψ
  /-- Strong continuity along every real line. -/
  continuous_line : ∀ (f : h) (ψ : K), Continuous fun t : ℝ => W ((t : ℂ) • f) ψ

/-- **A Fock representation**: a CCR representation with a unit vector `Ω` (the vacuum), cyclic for the
Weyl unitaries, with `⟪Ω, W f Ω⟫ = exp(-‖f‖² / 4)`. -/
structure FockRep extends CCRRep h K where
  /-- The vacuum. -/
  Ω : K
  /-- The vacuum is a unit vector. -/
  norm_Ω : ‖Ω‖ = 1
  /-- The vacuum is cyclic. -/
  cyclic : (Submodule.span ℂ (Set.range fun f => W f Ω)).topologicalClosure = ⊤
  /-- The Fock expectation of the Weyl unitaries. -/
  vacuum_expectation : ∀ f, ⟪Ω, W f Ω⟫_ℂ = Complex.exp (-(‖f‖ ^ 2 / 4 : ℝ))

variable {h K}

/-- **A Bogoliubov transformation is implemented** in a CCR representation `R` by a unitary `U` of `K` with
`U (W f ψ) = W (T f) (U ψ)`. -/
def Implements (R : CCRRep h K) (T : Bogoliubov h) : Prop :=
  ∃ U : K ≃ₗᵢ[ℂ] K, ∀ f ψ, U (R.W f ψ) = R.W (T.toEquiv f) (U ψ)

end Lightlike.OperatorAlgebras
