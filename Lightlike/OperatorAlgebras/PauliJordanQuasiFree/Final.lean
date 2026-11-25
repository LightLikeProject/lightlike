import Lightlike.OperatorAlgebras.PauliJordanQuasiFree.OneParticle
import Lightlike.OperatorAlgebras.FockIrreducible

/-!
# G2-077: the positive part of the Pauli–Jordan matrix defines a pure quasi-free state

Let `Δ` be a real antisymmetric matrix (for a finite causal set, `Δ = K - Kᵀ`, Johnston 2009, eq. (10)),
and `σ(f, g) = fᵀ Δ g` the symplectic form on `ℝ^ι`.  The *Sorkin–Johnston* state is the quasi-free state of
the Weyl algebra of `(ℝ^ι, σ)` with two-point function `Re (fᵀ P f)`, `P = (iΔ)⁺` the positive part of `iΔ`.

* `PureQuasiFreeRep Δ H`: a regular irreducible representation of the Weyl relations
  `W f W g = exp(-i σ(f,g)/2) W (f+g)` on a Hilbert space `H` with a cyclic unit vector `Ω` such that
  `⟪Ω, W f Ω⟫ = exp(-(fᵀ|Δ|f)/4)`; here `fᵀ|Δ|f = 2 Re (fᵀ P f)` (`inner_Tvec`).  Cyclicity of `Ω` and
  irreducibility say that the state `ω(W f) = ⟪Ω, W f Ω⟫` is pure (its GNS representation is irreducible).
* `exists_pure_quasiFree`: **for every real antisymmetric `Δ` such a representation exists** (the Fock
  representation over the one-particle space `range √P`, with `W f = fockW (T f)`).
-/

open scoped Matrix MatrixOrder ComplexOrder

universe u

namespace Lightlike.OperatorAlgebras.PauliJordanQuasiFree

open Lightlike.OperatorAlgebras

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {Δ : Matrix ι ι ℝ}

/-- **A pure quasi-free state** with covariance `|Δ|` on the Weyl algebra of `(ℝ^ι, fᵀΔg)`, given by its GNS
data: Weyl unitaries `W f` on a Hilbert space `H` satisfying the Weyl relations, strongly continuous along
real lines, a cyclic unit vector `Ω` with `⟪Ω, W f Ω⟫ = exp(-(fᵀ|Δ|f)/4)`, and trivial commutant
(irreducibility, i.e. purity of the state). -/
structure PureQuasiFreeRep (Δ : Matrix ι ι ℝ) (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The Weyl unitaries. -/
  W : (ι → ℝ) → (H ≃ₗᵢ[ℂ] H)
  /-- `W 0 = 1`. -/
  W_zero : W 0 = LinearIsometryEquiv.refl ℂ H
  /-- The Weyl relation for the symplectic form `fᵀΔg`. -/
  weyl : ∀ f g ψ, W f (W g ψ) =
    Complex.exp (-(Complex.I * ((f ⬝ᵥ Δ *ᵥ g) / 2 : ℝ))) • W (f + g) ψ
  /-- Strong continuity along real lines. -/
  continuous_line : ∀ (f : ι → ℝ) (ψ : H), Continuous fun t : ℝ => W (t • f) ψ
  /-- The state vector. -/
  Ω : H
  /-- It is a unit vector. -/
  norm_Ω : ‖Ω‖ = 1
  /-- It is cyclic. -/
  cyclic : (Submodule.span ℂ (Set.range fun f => W f Ω)).topologicalClosure = ⊤
  /-- The quasi-free expectation values `ω(W f) = exp(-(fᵀ|Δ|f)/4)`. -/
  expectation : ∀ f, inner ℂ Ω (W f Ω) = Complex.exp (-((f ⬝ᵥ absRe Δ *ᵥ f) / 4 : ℝ))
  /-- Irreducibility: a bounded operator commuting with all `W f` is a scalar. -/
  irreducible : ∀ C : H →L[ℂ] H, (∀ f ψ, C (W f ψ) = W f (C ψ)) → ∃ c : ℂ, ∀ ψ, C ψ = c • ψ

lemma Tvec_add (Δ : Matrix ι ι ℝ) (f g : ι → ℝ) : Tvec Δ (f + g) = Tvec Δ f + Tvec Δ g := by
  have : embR (f + g) = embR f + embR g := by ext i; simp [embR, ofR]
  rw [Tvec, Tvec, Tvec, this, map_add, smul_add]

lemma Tvec_zero (Δ : Matrix ι ι ℝ) : Tvec Δ 0 = 0 := by
  have : embR (0 : ι → ℝ) = 0 := by ext i; simp [embR, ofR]
  rw [Tvec, this, map_zero, smul_zero]

lemma Tvec_smul (Δ : Matrix ι ι ℝ) (c : ℝ) (f : ι → ℝ) : Tvec Δ (c • f) = (c : ℂ) • Tvec Δ f := by
  rw [Tvec, Tvec, embR_smul, map_smul, smul_comm]

/-- **The Sorkin–Johnston state is a pure quasi-free state** (task T-CS7, `milestones.md` OP; Johnston 2009,
eq. (10); Afshordi–Aslanbeigi–Sorkin 2012, §3): for every real antisymmetric matrix `Δ`, the positive part
`P = (iΔ)⁺` defines a pure quasi-free state of the Weyl algebra of `(ℝ^ι, fᵀΔg)`, namely the vacuum state of
the Fock representation over `range √P` composed with the real-linear map `f ↦ √2 √P f`. -/
theorem exists_pure_quasiFree (hΔ : Δᵀ = -Δ) :
    ∃ H : Type u, ∃ (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
      Nonempty (PureQuasiFreeRep Δ H) := by
  let h' := oneParticle Δ
  let R := fockRepOf h'
  let T : (ι → ℝ) → h' := fun f => ⟨Tvec Δ f, Tvec_mem Δ f⟩
  have hT : ∀ g : h', ∃ f, T f = g := fun g => by
    obtain ⟨f, hf⟩ := exists_T_eq hΔ g.2
    exact ⟨f, Subtype.ext hf⟩
  have hTadd : ∀ f g, T (f + g) = T f + T g := fun f g => Subtype.ext (Tvec_add Δ f g)
  refine ⟨FockSpace h', inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  refine
    { W := fun f => R.W (T f)
      W_zero := ?_
      weyl := ?_
      continuous_line := ?_
      Ω := R.Ω
      norm_Ω := R.norm_Ω
      cyclic := ?_
      expectation := ?_
      irreducible := ?_ }
  · have : T 0 = 0 := Subtype.ext (Tvec_zero Δ)
    show R.W (T 0) = _
    rw [this]; exact R.W_zero
  · intro f g ψ
    have hs : symp h' (T f) (T g) = f ⬝ᵥ Δ *ᵥ g := im_inner_Tvec hΔ f g
    show R.W (T f) (R.W (T g) ψ) = _ • R.W (T (f + g)) ψ
    rw [R.weyl, hs, hTadd]
  · intro f ψ
    have : ∀ t : ℝ, T (t • f) = (t : ℂ) • T f := fun t => Subtype.ext (Tvec_smul Δ t f)
    simp only [this]
    exact R.continuous_line (T f) ψ
  · have hr : (Set.range fun f : ι → ℝ => R.W (T f) R.Ω) = Set.range fun g : h' => R.W g R.Ω := by
      ext x
      constructor
      · rintro ⟨f, rfl⟩; exact ⟨T f, rfl⟩
      · rintro ⟨g, rfl⟩; obtain ⟨f, rfl⟩ := hT g; exact ⟨f, rfl⟩
    rw [hr]; exact R.cyclic
  · intro f
    have hn : ‖Tvec Δ f‖ ^ 2 = f ⬝ᵥ absRe Δ *ᵥ f := norm_sq_Tvec hΔ f
    show inner ℂ R.Ω (R.W (T f) R.Ω) = _
    rw [R.vacuum_expectation]
    show _ = _
    congr 2
    have : ‖T f‖ = ‖Tvec Δ f‖ := rfl
    rw [this, hn]
  · intro C hC
    refine commutant_scalar R C fun g ψ => ?_
    obtain ⟨f, rfl⟩ := hT g
    exact hC f ψ

end Lightlike.OperatorAlgebras.PauliJordanQuasiFree

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.W := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.W
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.W_zero := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.W_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.continuous_line := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.continuous_line
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.cyclic := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.cyclic
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.expectation := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.expectation
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.irreducible := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.irreducible
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.«norm_Ω» := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.«norm_Ω»
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.weyl := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.weyl
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.PureQuasiFreeRep.«Ω» := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.PureQuasiFreeRep.«Ω»
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.Tvec_add := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.Tvec_add
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.Tvec_smul := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.Tvec_smul
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.Tvec_zero := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.Tvec_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.exists_pure_quasiFree := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.exists_pure_quasiFree
