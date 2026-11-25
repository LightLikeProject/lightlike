module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Classification
public import Lightlike.Lorentz.PoincareIrreps.ClassificationStatement

/-!
# Wigner's little-group construction: summary of the HA6 done-when (row G1-055)

The construction itself lives in `Lightlike/Lorentz/PoincareIrreps/`. This file gathers the done-when
and the trust checks of the milestone HA6 into one conjunction each, so that a reader (or the
catalogue) has a single statement to point at. Nothing new is proved beyond the packaging.

* `wigner_massive_summary`: for a mass `m`, spin `n/2`: `P² = m²` on the mass shell, the Pauli–Lubanski
  square `W² = −m² s(s+1)` (signature `(+,−,−,−)`), the induced representation is isometric for the
  invariant measure, and the fibre at one momentum is `n+1`-dimensional (two states for spin 1/2).
* `wigner_massless_summary`: the light-like momentum has `P² = 0`, `W = (h/2) P`, and the induced
  representation of helicity `h/2` is isometric for the invariant cone measure.
* `wigner_tachyon_summary`: the tachyonic little group is not compact.

Reference: E. Wigner (1939); S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2. No
equation numbers are claimed. The classification itself is the lockable statement
`Lightlike.Lorentz.Poincare.WignerClassification`, stated but not proved.
-/

@[expose] public section

open Lightlike.Lorentz Lightlike.Lorentz.Poincare MeasureTheory

namespace Lightlike.Lorentz.WignerOrbits

/-- **Massive one-particle representation, summary.** On the mass shell `P² = m²`; the induced
representation `inducedRep` preserves the `L²` norm; `W² = −m² s(s+1)` with `s = n/2`; the space of
states at a fixed momentum has dimension `n + 1`. -/
theorem wigner_massive_summary {m : ℝ} (hm : 0 < m) (n : ℕ) :
    (∀ P : massShell m, P.1.1.det = ((m ^ 2 : ℝ) : ℂ)) ∧
    (∀ (A : SL2C) (ψ : massShell m → Fin (n + 1) → ℂ),
      Measurable (fun P => ENNReal.ofReal (fibreNormSq (ψ P))) →
        ∫⁻ P, ENNReal.ofReal (fibreNormSq (inducedRep hm n A ψ P)) ∂shellMeasure hm =
          ∫⁻ P, ENNReal.ofReal (fibreNormSq (ψ P)) ∂shellMeasure hm) ∧
    (∀ A : SL2C,
      pauliLubanski m n A 0 * pauliLubanski m n A 0 - pauliLubanski m n A 1 * pauliLubanski m n A 1 -
        pauliLubanski m n A 2 * pauliLubanski m n A 2 -
        pauliLubanski m n A 3 * pauliLubanski m n A 3 =
      (-((m : ℂ) ^ 2 * ((n : ℂ) * (n + 2) / 4))) •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) ∧
    (∀ P : massShell m, Module.finrank ℂ (atMomentum m n P) = n + 1) :=
  ⟨fun P => det_of_mem_massShell P, fun A ψ hψ => lintegral_inducedRep_normSq hm n A ψ hψ,
    fun A => pauliLubanski_square m n A, fun P => finrank_atMomentum m n P⟩

/-- **Massless one-particle representation, summary.** `P² = 0` at the standard light-like momentum;
`W^μ = (h/2) P^μ` at every momentum of the orbit; the induced representation is isometric for the
invariant cone measure. -/
theorem wigner_massless_summary (h : ℤ) :
    (lightMom 1).1.det = 0 ∧
    (∀ (A : SL2C) (μ : Fin 4),
      lightPL h A μ = (lightHelicity h : ℂ) * (coord (A • lightMom 1) μ : ℝ)) ∧
    (∀ (A : SL2C) (ψ : lightCone → ℂ),
      Measurable (fun P => ENNReal.ofReal (‖ψ P‖ ^ 2)) →
        ∫⁻ P, ENNReal.ofReal (‖lightInducedRep h A ψ P‖ ^ 2) ∂coneMeasure =
          ∫⁻ P, ENNReal.ofReal (‖ψ P‖ ^ 2) ∂coneMeasure) :=
  ⟨by rw [lightMom_eq_ofVec, det_ofVec]; simp, fun A μ => lightPL_eq h A μ,
    fun A ψ hψ => lintegral_lightInducedRep_normSq h A ψ hψ⟩

/-- **Tachyonic orbit, summary.** `P² = −m²` at the standard tachyonic momentum and its stabilizer in
`SL(2,ℂ)` is not compact. -/
theorem wigner_tachyon_summary (m : ℝ) :
    (tachMom m).1.det = ((-m ^ 2 : ℝ) : ℂ) ∧
    ¬ IsCompact ((MulAction.stabilizer SL2C (tachMom m) : Subgroup SL2C) : Set SL2C) :=
  ⟨by rw [tachMom_eq_ofVec, det_ofVec]; simp, not_isCompact_stabilizer_tachMom m⟩

end Lightlike.Lorentz.WignerOrbits

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.wigner_massive_summary := _root_.Lightlike.Lorentz.WignerOrbits.wigner_massive_summary
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.wigner_massless_summary := _root_.Lightlike.Lorentz.WignerOrbits.wigner_massless_summary
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Lorentz.HARow055.wigner_tachyon_summary := _root_.Lightlike.Lorentz.WignerOrbits.wigner_tachyon_summary
