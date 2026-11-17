import Lightlike.CausalSets.MyrheimGen

/-!
# The Myrheim–Meyer relation probability in `3 + 1` dimensions

Two independent uniform points of the causal diamond of `ℝ^{3+1}` are related with probability
`1/20` (`relProb_three_eq`), so `n` uniform points have `n (n - 1) / 20` relations in expectation
(`expected_relations_diamond_three`). This is the case of spacetime dimension `4` of the
Myrheim–Meyer formula `Γ(D + 1) Γ(D / 2) / (4 Γ(3 D / 2))`, which is `1/20` at `D = 4`, proved in
every dimension in `Lightlike/CausalSets/MyrheimGen.lean` (`myrheimMeyer_eq`). The comparison of the
values with the sources is pending (they have not been read at a location). This is part of a bridge
between Lorentzian geometry and causal sets.

## References

* J. Myrheim, *Statistical geometry*, CERN preprint TH-2538 (1978).
* D. A. Meyer, *The dimension of causal sets*, PhD thesis, MIT (1988).
* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open MeasureTheory
open Lightlike

namespace Lightlike.CausalSets

/-- **The Myrheim–Meyer relation probability in four dimensions**: two uniform points of the causal
diamond of `ℝ^{3+1}` are related with probability `1/20`. -/
theorem relProb_three_eq : relProb 3 = 1 / 20 := by
  rw [myrheimMeyer_eq]
  have e1 : Real.Gamma (((3 : ℕ) : ℝ) + 2) = 24 := by
    rw [show (((3 : ℕ) : ℝ) + 2) = ((4 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  have e2 : Real.Gamma ((((3 : ℕ) : ℝ) + 1) / 2) = 1 := by
    rw [show ((((3 : ℕ) : ℝ) + 1) / 2) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; norm_num
  have e3 : Real.Gamma (3 * (((3 : ℕ) : ℝ) + 1) / 2) = 120 := by
    rw [show (3 * (((3 : ℕ) : ℝ) + 1) / 2) = ((5 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [e1, e2, e3]; norm_num

/-- **Expected number of relations in `3 + 1` dimensions**: `n` uniform points of the causal diamond
have `n (n - 1) / 20` pairs `x ≺ y` in expectation (the case `D = 4` of the Myrheim–Meyer count). -/
theorem expected_relations_diamond_three (n : ℕ) :
    ∫ ω, (relCount {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) | coneLT p.1 p.2} ω : ℝ)
        ∂Measure.pi (fun _ : Fin n => diamondMeasure 3) = (n : ℝ) * (n - 1) / 20 := by
  rw [expected_relations_diamond, relProb_three_eq]; ring

end Lightlike.CausalSets
