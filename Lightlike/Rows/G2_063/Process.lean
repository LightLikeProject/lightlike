import Mathlib
import Lightlike.CausalSets.Expected

/-!
# The Poisson point process on a finite measure space

For a finite measure `μ` on a measurable space `α` the **Poisson point process** of intensity `μ`
(Last–Penrose, *Lectures on the Poisson process*, Chapter: Poisson Processes) is a random finite
set of points of `α`: the number `N` of points is Poisson distributed with mean `μ α`, and given
`N = n` the points are `n` independent samples of the normalised measure `μ / μ α`.

Mathlib has the Poisson distribution on `ℕ` (`ProbabilityTheory.poissonMeasure`) but no point
process. Here the process is a measure `sprinkling μ` on the type `Config α = Σ n, Fin n → α` of
finite sequences of points (a *configuration* with a chosen labelling of the points), defined as the
mixture over `n` of the product measures, weighted by the Poisson probabilities. Conditioning on
the count is then the definition.

The main use is the Poisson sprinkling into a region of Minkowski space
(`Lightlike/Rows/G2_063/Sprinkling.lean`), where `μ` is the intensity times the Lebesgue measure on
the region.

## Main definitions

* `Config α`: the finite sequences of points of `α`.
* `unitLaw μ`: the normalised measure `μ / μ α`.
* `sprinkling μ`: the law of the Poisson point process of intensity `μ`.

## References

* G. Last, M. Penrose, *Lectures on the Poisson process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Lightlike.PoissonSprinkling

variable {α : Type*} [MeasurableSpace α]

/-- A **configuration**: a finite sequence of points of `α`, with its length. -/
abbrev Config (α : Type*) := Σ n : ℕ, Fin n → α

/-- The normalised measure `μ / μ α` (a probability measure when `0 < μ α < ∞`). -/
noncomputable def unitLaw (μ : Measure α) : Measure α := (μ Set.univ)⁻¹ • μ

/-- The **Poisson weight** `e^{-r} r^n / n!` of `n` points, as an extended nonnegative real. -/
noncomputable def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ))

/-- The **Poisson point process** of intensity `μ` on `α`: given the count `n`, which is Poisson
distributed with mean `μ α`, the points are `n` independent samples of `μ / μ α`. It is a measure
on configurations (finite sequences of points); a probability measure when `0 < μ α < ∞`. -/
noncomputable def sprinkling (μ : Measure α) : Measure (Config α) :=
  Measure.sum fun n => poissonWeight (μ Set.univ).toNNReal n •
    (Measure.pi fun _ : Fin n => unitLaw μ).map (Sigma.mk n)

/-- Integration against the process is the Poisson-weighted sum of the integrals against the
`n`-point product measures: this is conditioning on the number of points. -/
theorem lintegral_sprinkling (μ : Measure α) {F : Config α → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂sprinkling μ = ∑' n : ℕ, poissonWeight (μ Set.univ).toNNReal n *
      ∫⁻ ω, F ⟨n, ω⟩ ∂Measure.pi (fun _ : Fin n => unitLaw μ) := by
  unfold sprinkling
  rw [lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  have hm : Measurable (@Sigma.mk ℕ (fun n => Fin n → α) n) :=
    fun s hs => (MeasurableSpace.measurableSet_iInf.1 hs) n
  rw [lintegral_smul_measure, lintegral_map hF hm, smul_eq_mul]

/-- The normalised measure of a measure of finite positive total mass is a probability measure. -/
theorem isProbabilityMeasure_unitLaw (μ : Measure α) (h0 : μ Set.univ ≠ 0)
    (h1 : μ Set.univ ≠ ⊤) : IsProbabilityMeasure (unitLaw μ) :=
  ⟨by simp [unitLaw, ENNReal.inv_mul_cancel h0 h1]⟩

/-- **The Poisson process is a probability measure** (for a measure of finite positive mass): the
Poisson weights sum to `1`. -/
theorem isProbabilityMeasure_sprinkling (μ : Measure α) (h0 : μ Set.univ ≠ 0)
    (h1 : μ Set.univ ≠ ⊤) : IsProbabilityMeasure (sprinkling μ) := by
  have := isProbabilityMeasure_unitLaw μ h0 h1
  refine ⟨?_⟩
  have hm : ∀ n : ℕ, Measurable (@Sigma.mk ℕ (fun n => Fin n → α) n) := fun n s hs =>
    (MeasurableSpace.measurableSet_iInf.1 hs) n
  unfold sprinkling
  rw [Measure.sum_apply _ MeasurableSet.univ]
  have : ∀ n : ℕ, ((poissonWeight (μ Set.univ).toNNReal n •
      (Measure.pi fun _ : Fin n => unitLaw μ).map (@Sigma.mk ℕ (fun n => Fin n → α) n))
        Set.univ) = poissonWeight (μ Set.univ).toNNReal n := by
    intro n
    rw [Measure.smul_apply, Measure.map_apply (hm n) MeasurableSet.univ]
    simp
  simp_rw [this, poissonWeight]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_one_poissonMeasure _).summable, (hasSum_one_poissonMeasure _).tsum_eq]
  simp

end Lightlike.PoissonSprinkling
