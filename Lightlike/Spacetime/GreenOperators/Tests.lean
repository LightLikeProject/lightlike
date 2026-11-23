import Mathlib
import Lightlike.Spacetime.GreenOperators.IntegralForm
import Lightlike.Spacetime.GreenOperators.Cylinder
import Lightlike.Spacetime.GreenOperators.MassiveAdvanced

/-!
# Sanity checks for the Green operators on 1+1 Minkowski space (G1-021)

Examples applying the main results of the folder: the Pauli–Jordan function takes the values
`-1/2` (future cone), `1/2` (past cone) and `0` (spacelike separation); the retarded solution is
the unique `C²` solution vanishing in the past; on the cylinder uniqueness fails.
-/

open Lightlike.GreenOperators

example : pauliJordan (1, 0) = -(1 / 2 : ℝ) := pauliJordan_of_future (by norm_num)
example : pauliJordan (-1, 0) = (1 / 2 : ℝ) := pauliJordan_of_past (by norm_num)
example : pauliJordan (0, 1) = 0 := pauliJordan_of_spacelike (by norm_num)

/-- The retarded solution is the unique one vanishing before the support of the source. -/
example {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {T : ℝ}
    (h0 : ∀ p : ℝ × ℝ, p.1 < T → f p = 0) (u : ℝ × ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (hk : ∀ p, kgOp 0 u p = f p) (hz : ∀ p : ℝ × ℝ, p.1 < T → u p = 0) :
    u = retardedSol f :=
  ((massless_retarded_existsUnique hf hc h0).unique ⟨hu, hk, hz⟩
    ⟨retardedSol_contDiff hf hc, kgOp_retardedSol hf hc, retardedSol_eq_zero h0⟩)

/-- For a massive field, the retarded solution is the unique one vanishing in the past. -/
example (m : ℝ) {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {T : ℝ}
    (h0 : ∀ p : ℝ × ℝ, p.1 < T → f p = 0) (u : ℝ × ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (hk : ∀ p, kgOp m u p = f p) (hz : ∀ p : ℝ × ℝ, p.1 < T → u p = 0) :
    u = massiveSol m f :=
  ((retarded_existsUnique m hf hc h0).unique ⟨hu, hk, hz⟩
    ⟨massiveSol_contDiff m hf hc, kgOp_massiveSol m hf hc, massiveSol_eq_zero h0⟩)

/-- Pauli–Jordan: `G⁺ f - G⁻ f` is the convolution with `pauliJordan`. -/
example {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (p : ℝ × ℝ) :
    retardedSol f p - advancedSol f p = ∫ q, pauliJordan (p - q) * f q :=
  retarded_sub_advanced_eq_integral hf hc p
