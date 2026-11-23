module

public import Mathlib
public import Lightlike.Upstream.SU2Spin.SpinRep
public import Lightlike.Lorentz.PoincareIrreps.Fibre
public import Lightlike.Lorentz.PoincareIrreps.Poincare
public import Lightlike.Lorentz.PoincareIrreps.LightPoincare
public import Lightlike.Lorentz.PoincareIrreps.PauliLubanski
public import Lightlike.Lorentz.PoincareIrreps.MasslessPL
public import Lightlike.Lorentz.PoincareIrreps.MasslessMeasure

/-!
# Wigner's one-particle representations: summary and the little-group irreducibility piece (HA6)

This file does two things.

1. **Irreducibility at the fibre** (`atRest_irreducible`): the states at the rest momentum
   `(m,0,0,0)` form a copy of `ℂ^{n+1}` on which the little group `SU(2)` (the stabiliser of the rest
   momentum, `stabilizer_restMom`) acts through the spin-`n/2` representation
   (`inducedRep_ofSU2_rest`); this representation is irreducible (`SU2Spin`), so a subspace of the
   states at the rest momentum stable under the little group is `0` or everything. This is the
   fibre-wise half of Wigner's irreducibility statement.
2. **Collected statements** `wigner_massive` and `wigner_massless`: for each mass `m > 0`, spin `n/2`
   (resp. helicity `h/2`), the induced Poincaré representation is unitary for the invariant measure,
   has `P² = m²` (resp. `0`), `W² = −m² s(s+1)` (resp. `W = (h/2) P`), and the fibre has `n+1` states.

**Not proved here** (and not claimed): that the induced representation on `L²` is irreducible
(Mackey's imprimitivity theorem) and Wigner's classification of *all* irreducible positive-energy
representations. Those need the Hilbert-space completion, strong continuity and the spectral
condition, which are not in the code base.

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2; only the statements
proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

variable {m : ℝ} (hm : 0 < m)

include hm in
/-- The standard boost of the rest momentum is the identity. -/
lemma boost_restShell : boost hm (restShell hm) = 1 := by
  apply Subtype.ext
  rw [coe_boost]
  have h1 := boostScale_sq hm (P := restMom m) (by simp [restMom, hm])
  have h2 : boostScale m (restMom m) = (2 * m)⁻¹ := by
    have hpos : 0 < boostScale m (restMom m) := by
      unfold boostScale
      have : 0 < m * ((restMom m).1.trace.re + 2 * m) := by
        have : (restMom m).1.trace.re = 2 * m := by simp [restMom]; ring
        rw [this]; positivity
      positivity
    have h3 : (restMom m).1.trace.re = 2 * m := by
      simp [restMom]; ring
    rw [h3] at h1
    have h4 : (boostScale m (restMom m) * (2 * m)) ^ 2 = 1 := by nlinarith
    have h5 : boostScale m (restMom m) * (2 * m) = 1 := by
      have : 0 < boostScale m (restMom m) * (2 * m) := by positivity
      nlinarith
    field_simp
    linarith
  change boostMat m (restMom m) = (1 : Matrix (Fin 2) (Fin 2) ℂ)
  unfold boostMat
  rw [h2]
  simp only [restMom, Matrix.smul_one_eq_diagonal]
  ext i j
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  by_cases hij : i = j
  · subst hij
    simp
    field_simp
    ring
  · simp [hij]

include hm in
/-- The little group `SU(2)` fixes the rest momentum on the mass shell. -/
lemma shellSMul_ofSU2_restShell (g : Lightlike.SU2) :
    shellSMul hm (SL2C.ofSU2 g) (restShell hm) = restShell hm := by
  apply Subtype.ext
  have h : SL2C.ofSU2 g ∈ MulAction.stabilizer SL2C (restMom m) := by
    rw [stabilizer_restMom hm.ne']
    exact ⟨g, rfl⟩
  exact MulAction.mem_stabilizer_iff.mp h

include hm in
/-- **On the little group the Wigner rotation is the group element itself**: `W(g, rest) = g`. -/
lemma wignerSU2_ofSU2 (g : Lightlike.SU2) : wignerSU2 hm (SL2C.ofSU2 g) (restShell hm) = g := by
  apply SL2C.ofSU2_injective
  rw [ofSU2_wignerSU2, wignerSL, shellSMul_ofSU2_restShell hm, boost_restShell hm]
  simp

include hm in
/-- **At the rest momentum, the induced representation restricted to the little group `SU(2)` is the
spin-`n/2` representation**: `(U(g) ψ)(rest) = D^{n/2}(g) ψ(rest)`. -/
theorem inducedRep_ofSU2_rest (n : ℕ) (g : Lightlike.SU2) (ψ : massShell m → Fin (n + 1) → ℂ) :
    inducedRep hm n (SL2C.ofSU2 g) ψ (restShell hm) =
      SU2Spin.spinMat n g *ᵥ ψ (restShell hm) := by
  have h := inducedRep_apply_smul hm n (SL2C.ofSU2 g) ψ (restShell hm)
  rw [shellSMul_ofSU2_restShell hm, wignerSU2_ofSU2 hm] at h
  exact h

include hm in
/-- **The little-group irreducibility of the fibre.** A subspace of the space of states supported at
the rest momentum, stable under the induced action of the little group `SU(2)`, is `0` or the whole
space `atMomentum m n (rest)` (`≃ ℂ^{n+1}`, spin `n/2`). -/
theorem atRest_irreducible (n : ℕ) (W : Submodule ℂ (massShell m → Fin (n + 1) → ℂ))
    (hWle : W ≤ atMomentum m n (restShell hm))
    (hinv : ∀ g : Lightlike.SU2, ∀ ψ ∈ W, inducedRep hm n (SL2C.ofSU2 g) ψ ∈ W) :
    W = ⊥ ∨ W = atMomentum m n (restShell hm) := by
  classical
  set W' : Submodule ℂ (Fin (n + 1) → ℂ) := W.map (LinearMap.proj (restShell hm)) with hW'
  have hI : SU2Spin.IsInvariant n W' := by
    intro g v hv
    obtain ⟨ψ, hψ, rfl⟩ := hv
    refine ⟨inducedRep hm n (SL2C.ofSU2 g) ψ, hinv g ψ hψ, ?_⟩
    simpa using inducedRep_ofSU2_rest hm n g ψ
  have hz : ∀ ψ ∈ atMomentum m n (restShell hm), ψ (restShell hm) = 0 → ψ = 0 := by
    intro ψ hψ h0
    funext Q
    by_cases hQ : Q = restShell hm
    · subst hQ; simpa using h0
    · exact hψ Q hQ
  rcases SU2Spin.isInvariant_eq_bot_or_eq_top hI with hb | ht
  · left
    rw [eq_bot_iff]
    intro ψ hψ
    have : ψ (restShell hm) ∈ W' := ⟨ψ, hψ, rfl⟩
    rw [hb] at this
    have h0 : ψ (restShell hm) = 0 := by simpa using this
    simpa using hz ψ (hWle hψ) h0
  · right
    apply le_antisymm hWle
    intro ψ hψ
    have : ψ (restShell hm) ∈ W' := by rw [ht]; trivial
    obtain ⟨φ, hφ, hφψ⟩ := this
    have hφψ' : φ (restShell hm) = ψ (restShell hm) := hφψ
    have : φ - ψ = 0 := hz _ ((atMomentum m n (restShell hm)).sub_mem (hWle hφ) hψ)
      (by simp [hφψ'])
    have hφeq : φ = ψ := sub_eq_zero.mp this
    rw [← hφeq]; exact hφ

/-! ## Collected statements -/

variable (m) in
/-- **Massive one-particle representation (summary).** For `m > 0` and spin `n/2`, the induced
representation `poincareRep hm n` of the Poincaré group (`ISL2C`) satisfies: it preserves the
`L²(shellMeasure)` norm; the translations are covariant; every momentum on the shell has `P² = m²`;
the Pauli–Lubanski square is `W² = −m² s(s+1)` with `s = n/2` (signature `(+,−,−,−)`); and the space
of states at one momentum has dimension `n + 1`. -/
theorem wigner_massive (n : ℕ) :
    (∀ (A : SL2C) (ψ : massShell m → Fin (n + 1) → ℂ),
      Measurable (fun P => ENNReal.ofReal (fibreNormSq (ψ P))) →
      ∫⁻ P, ENNReal.ofReal (fibreNormSq (inducedRep hm n A ψ P)) ∂shellMeasure hm =
        ∫⁻ P, ENNReal.ofReal (fibreNormSq (ψ P)) ∂shellMeasure hm) ∧
    (∀ (A : SL2C) (a : Herm2), inducedRep hm n A ∘ₗ translateOp n a =
        translateOp n (A • a) ∘ₗ inducedRep hm n A) ∧
    (∀ P : massShell m, P.1.1.det = ((m ^ 2 : ℝ) : ℂ)) ∧
    (∀ A : SL2C,
      pauliLubanski m n A 0 * pauliLubanski m n A 0 - pauliLubanski m n A 1 * pauliLubanski m n A 1 -
        pauliLubanski m n A 2 * pauliLubanski m n A 2 -
        pauliLubanski m n A 3 * pauliLubanski m n A 3 =
      (-((m : ℂ) ^ 2 * ((n : ℂ) * (n + 2) / 4))) •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
    (∀ P : massShell m, Module.finrank ℂ (atMomentum m n P) = n + 1) :=
  ⟨fun A ψ hψ => lintegral_inducedRep_normSq hm n A ψ hψ,
    fun A a => inducedRep_translate hm n A a,
    fun P => det_of_mem_massShell P,
    fun A => pauliLubanski_square m n A,
    fun P => finrank_atMomentum m n P⟩

/-- **Massless one-particle representation (summary).** For helicity `h/2`, the representation
`lightPoincareRep h` preserves the `L²(coneMeasure)` norm, every momentum on the cone has `P² = 0`,
and the Pauli–Lubanski vector is `W = (h/2) P`, hence `W² = 0`. -/
theorem wigner_massless (h : ℤ) :
    (∀ (A : SL2C) (ψ : lightCone → ℂ), Measurable (fun P => ENNReal.ofReal (‖ψ P‖ ^ 2)) →
      ∫⁻ P, ENNReal.ofReal (‖lightInducedRep h A ψ P‖ ^ 2) ∂coneMeasure =
        ∫⁻ P, ENNReal.ofReal (‖ψ P‖ ^ 2) ∂coneMeasure) ∧
    (∀ P : lightCone, P.1.1.det = 0) ∧
    (∀ (A : SL2C) (μ : Fin 4),
      lightPL h A μ = (lightHelicity h : ℂ) * (coord (A • lightMom 1) μ : ℝ)) ∧
    (∀ A : SL2C, lightPL h A 0 * lightPL h A 0 - lightPL h A 1 * lightPL h A 1 -
      lightPL h A 2 * lightPL h A 2 - lightPL h A 3 * lightPL h A 3 = 0) :=
  ⟨fun A ψ hψ => lintegral_lightInducedRep_normSq h A ψ hψ,
    fun P => det_of_mem_lightCone P,
    fun A μ => lightPL_eq h A μ,
    fun A => lightPL_square h A⟩

end Lightlike.Lorentz.Poincare
