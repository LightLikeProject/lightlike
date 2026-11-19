import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Couplings and the `1`-Wasserstein distance on a compact metric space

W. Huang, R. Wang, Y. Wu, D. Meng, arXiv:2610.21070, Section 3.2.1, p. 5 (read): for Borel probability measures `ν`, `η`
on a compact metric space `(M, d)`, `Π(ν, η)` is the set of probability couplings with these marginals and
`W₁(ν, η) = inf_{γ ∈ Π(ν, η)} ∫ d dγ`; "the easy direction is immediate: for any coupling `γ` and unit Lipschitz function
`u`, `∫ u d(ν - η) ≤ ∫ d dγ`".

* `couplings μ ν`, `prod_mem_couplings` (the product coupling);
* `wasserstein1 μ ν`;
* `integral_sub_le_of_mem_couplings`, `integral_sub_le_wasserstein1`: the easy direction of Kantorovich-Rubinstein;
* `wasserstein1_dirac`: `W₁(δₓ, δ_y) = d(x, y)`.
-/

open MeasureTheory

namespace Lightlike.OperatorAlgebras.Transport

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The couplings** of two measures on `X`: probability measures on `X × X` with marginals `μ` and `ν`. -/
def couplings (μ ν : Measure X) : Set (Measure (X × X)) :=
  {π | IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

/-- **The product coupling** `μ ⊗ ν`. -/
lemma prod_mem_couplings (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ.prod ν ∈ couplings μ ν := by
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_fst_prod, measure_univ, one_smul]
  · rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- **The `1`-Wasserstein distance** `W₁(μ, ν) = inf_{π ∈ Π(μ, ν)} ∫ d dπ`. -/
noncomputable def wasserstein1 (μ ν : Measure X) : ℝ :=
  sInf ((fun π : Measure (X × X) => ∫ p, dist p.1 p.2 ∂π) '' couplings μ ν)

lemma integral_comp_fst {π : Measure (X × X)} {μ : Measure X} (h : π.map Prod.fst = μ) (u : X → ℝ)
    (hu : Continuous u) : ∫ x, u x ∂μ = ∫ p, u p.1 ∂π := by
  rw [← h, integral_map measurable_fst.aemeasurable hu.aestronglyMeasurable]

lemma integral_comp_snd {π : Measure (X × X)} {ν : Measure X} (h : π.map Prod.snd = ν) (u : X → ℝ)
    (hu : Continuous u) : ∫ x, u x ∂ν = ∫ p, u p.2 ∂π := by
  rw [← h, integral_map measurable_snd.aemeasurable hu.aestronglyMeasurable]

/-- A continuous function on the compact `X × X` is integrable for a finite measure. -/
lemma integrable_of_continuous {π : Measure (X × X)} [IsFiniteMeasure π] {f : X × X → ℝ} (hf : Continuous f) :
    Integrable f π :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- **The easy direction** (arXiv:2610.21070, Section 3.2.1, p. 5): for a coupling `π` and a `1`-Lipschitz `u`,
`∫ u dμ - ∫ u dν ≤ ∫ d dπ`. -/
theorem integral_sub_le_of_mem_couplings {μ ν : Measure X} {π : Measure (X × X)} (hπ : π ∈ couplings μ ν)
    {u : X → ℝ} (hu : LipschitzWith 1 u) : ∫ x, u x ∂μ - ∫ x, u x ∂ν ≤ ∫ p, dist p.1 p.2 ∂π := by
  haveI := hπ.1
  have hc := hu.continuous
  rw [integral_comp_fst hπ.2.1 u hc, integral_comp_snd hπ.2.2 u hc,
    ← integral_sub (integrable_of_continuous (f := fun p : X × X => u p.1) (hc.comp continuous_fst))
      (integrable_of_continuous (f := fun p : X × X => u p.2) (hc.comp continuous_snd))]
  refine integral_mono (integrable_of_continuous ((hc.comp continuous_fst).sub (hc.comp continuous_snd)))
    (integrable_of_continuous continuous_dist) fun p => ?_
  have := hu.dist_le_mul p.1 p.2
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at this
  exact (le_abs_self _).trans this

/-- **`∫ u dμ - ∫ u dν ≤ W₁(μ, ν)`** for `1`-Lipschitz `u`. -/
theorem integral_sub_le_wasserstein1 (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : X → ℝ} (hu : LipschitzWith 1 u) : ∫ x, u x ∂μ - ∫ x, u x ∂ν ≤ wasserstein1 μ ν :=
  le_csInf ⟨_, ⟨μ.prod ν, prod_mem_couplings μ ν, rfl⟩⟩ fun _ ⟨π, hπ, hπe⟩ =>
    hπe ▸ integral_sub_le_of_mem_couplings hπ hu

/-- `W₁(μ, ν) ≤ ∫ d dπ` for every coupling. -/
lemma wasserstein1_le {μ ν : Measure X} {π : Measure (X × X)} (hπ : π ∈ couplings μ ν) :
    wasserstein1 μ ν ≤ ∫ p, dist p.1 p.2 ∂π :=
  csInf_le ⟨0, fun _ ⟨π', hπ', he⟩ => he ▸ integral_nonneg fun p => dist_nonneg⟩ ⟨π, hπ, rfl⟩

/-- **`W₁(δₓ, δ_y) = d(x, y)`**: the product coupling gives `≤`, the `1`-Lipschitz `d(·, y)` gives `≥`. -/
theorem wasserstein1_dirac (x y : X) : wasserstein1 (Measure.dirac x) (Measure.dirac y) = dist x y := by
  apply le_antisymm
  · have h := wasserstein1_le (prod_mem_couplings (Measure.dirac x) (Measure.dirac y))
    rwa [Measure.dirac_prod_dirac, integral_dirac] at h
  · have h := integral_sub_le_wasserstein1 (Measure.dirac x) (Measure.dirac y)
      (u := fun z => dist z y) (LipschitzWith.dist_left y)
    rwa [integral_dirac, integral_dirac, dist_self, sub_zero] at h

end Lightlike.OperatorAlgebras.Transport
