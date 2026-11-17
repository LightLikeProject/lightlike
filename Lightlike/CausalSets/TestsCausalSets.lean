import Lightlike.CausalSets.Myrheim4D
import Lightlike.CausalSets.Rectangle
import Lightlike.CausalSets.BetaReal

/-!
# Checks of the causal-set definitions

Trust checks for `Lightlike/CausalSets/`: the cone order of Minkowski space gives the expected
relations on explicit points, differs from the product order of `ℝ²` (a wrong model), and four
explicit points of `ℝ^{1+1}` induce the 4-element diamond causal set; the sprinkling
expectation is `n (n - 1) / 4` in `1 + 1` dimensions, so `1/2` for `n = 2`.

## References

* S. Surya, *The causal set approach to the problem of quantum gravity*, Living Reviews in
  Relativity 22 (2019), section 2.
-/

open MeasureTheory

namespace Lightlike.CausalSets

namespace TestsCausalSets

/-- The point `(t, x)` of `ℝ^{1+1}`. -/
noncomputable def pt (t x : ℝ) : Fin 2 → ℝ := ![t, x]

/-- Timelike separated points are related. -/
example : coneLE (pt 0 0) (pt 1 (1 / 2)) := by
  rw [coneLE_iff_spatial]; simp [pt, spatialSq]; norm_num

/-- Trust check (wrong model): `(1, 2)` is spacelike to the origin, so it is not in the causal
future, although it is in the future for the product order of `ℝ²`. -/
example : ¬ coneLE (pt 0 0) (pt 1 2) ∧ ((pt 0 0) ≤ (pt 1 2)) := by
  refine ⟨?_, ?_⟩
  · rw [coneLE_iff_spatial]; simp [pt, spatialSq]
  · intro i; fin_cases i <;> simp [pt]

/-- Trust check: the relation is not symmetric, the past is not in the future. -/
example : ¬ coneLE (pt 1 0) (pt 0 0) := by
  rw [coneLE_iff_spatial]; simp [pt, spatialSq]

/-- Four points of `ℝ^{1+1}` (bottom, left, right, top) whose induced order is the diamond. -/
noncomputable def diamondPts : Fin 4 → Fin 2 → ℝ := ![pt 0 0, pt 1 (1 / 2), pt 1 (-1 / 2), pt 2 0]

/-- **The sprinkled order of four explicit points is the 4-element diamond causal set**: the
cone order on `diamondPts` agrees with the relation of `Diamond` (bottom `0`, top `3`, the two
middle points `1`, `2` unrelated). -/
example : ∀ i j : Fin 4, coneLE (diamondPts i) (diamondPts j) ↔ Diamond.rel i j := by
  intro i j
  rw [coneLE_iff_spatial]
  fin_cases i <;> fin_cases j <;>
    simp [diamondPts, pt, spatialSq, Diamond.rel] <;> norm_num

/-- The expected number of relations of two uniform points of the diamond in `1 + 1` dimensions
is `1/2`. -/
example : ∫ ω, (relCount {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | coneLT p.1 p.2} ω : ℝ)
    ∂Measure.pi (fun _ : Fin 2 => diamondMeasure 1) = 1 / 2 := by
  rw [expected_relations_diamond_one]; norm_num

/-- In `3 + 1` dimensions two uniform points of the diamond are related with probability `1/20`, so
the expected number of relations of two points is `1/10`, and not the `1/2` of `1 + 1` dimensions. -/
example : ∫ ω, (relCount {p : (Fin 4 → ℝ) × (Fin 4 → ℝ) | coneLT p.1 p.2} ω : ℝ)
    ∂Measure.pi (fun _ : Fin 2 => diamondMeasure 3) = 1 / 10 := by
  rw [expected_relations_diamond_three]; norm_num

/-- The diamond measure is a probability measure (non-vacuity of the hypotheses of the
sprinkling theorems). -/
example (d : ℕ) : IsProbabilityMeasure (diamondMeasure d) := inferInstance

/-- The real Beta integral gives `B(2, 3) = 1/12`, which is the value of the integral of
`s (1 - s)²` over `[0, 1]`. -/
example : ∫ s in (0 : ℝ)..1, s ^ ((2 : ℝ) - 1) * (1 - s) ^ ((3 : ℝ) - 1) = 1 / 12 := by
  rw [real_beta (by norm_num) (by norm_num)]
  have e2 : Real.Gamma 2 = 1 := by simp
  have e3 : Real.Gamma 3 = 2 := by simp
  have e5 : Real.Gamma (2 + 3) = 24 := by norm_num
  rw [e2, e3, e5]; norm_num

end TestsCausalSets

end Lightlike.CausalSets
