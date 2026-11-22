import Lightlike.Rows.G2_011.Algebra
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Invariant positive functionals on a compact group are multiples of Haar measure (G2-011)

The key analytic input of the graph-level uniqueness theorem: a positive linear functional on the
continuous functions of a compact group `K` that is invariant under left translation is a multiple
of the Haar integral. We prove the real-valued form (`real_invariant_functional_eq_haar`) with the
Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`) and Mathlib's uniqueness of left invariant
measures (`MeasureTheory.Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport`), and
the complex-valued form (`invariant_functional_eq_haar`) for functionals positive on the elements
`f̄ f`, which is the positivity of a vector state of a `HFRep`.

Supporting lemmas; no catalogue entry.
-/

open MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported

noncomputable section

namespace Lightlike.Rows.G2_011

section
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Left translation of a real valued continuous function, `(f ∘ (k⁻¹ · ))`. -/
def translateR (k : K) (f : C(K, ℝ)) : C(K, ℝ) :=
  f.comp ⟨fun x => k⁻¹ * x, by fun_prop⟩

@[simp] lemma translateR_apply (k : K) (f : C(K, ℝ)) (x : K) : translateR k f x = f (k⁻¹ * x) :=
  rfl
end

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] [MeasurableSpace K] [BorelSpace K]

/-- **Positive left-invariant functionals are Haar integrals (real form).** A positive real linear
functional `Λ` on `C(K, ℝ)` of a compact group, invariant under left translation, is
`Λ f = Λ 1 · ∫ f dμ` for a Haar probability measure `μ`. -/
theorem real_invariant_functional_eq_haar (Λ : C(K, ℝ) →ₗ[ℝ] ℝ)
    (hpos : ∀ f : C(K, ℝ), 0 ≤ f → 0 ≤ Λ f)
    (hinv : ∀ (k : K) (f : C(K, ℝ)), Λ (translateR k f) = Λ f)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (f : C(K, ℝ)) :
    Λ f = Λ 1 * ∫ x, f x ∂μ := by
  let ofC : C(K, ℝ) → C_c(K, ℝ) := fun g => ⟨g, HasCompactSupport.of_compactSpace g⟩
  let Λc : C_c(K, ℝ) →ₚ[ℝ] ℝ :=
  { toFun g := Λ ⟨g, g.continuous⟩
    map_add' g g' := by
      rw [← Λ.map_add]; rfl
    map_smul' c g := by
      rw [← Λ.map_smul]; rfl
    monotone' g g' h := by
      have := hpos (⟨g', g'.continuous⟩ - ⟨g, g.continuous⟩) (fun x => sub_nonneg.2 (h x))
      rw [Λ.map_sub] at this
      exact sub_nonneg.1 this }
  have hΛc : ∀ g : C(K, ℝ), Λc (ofC g) = Λ g := fun g => rfl
  set ν : Measure K := RealRMK.rieszMeasure Λc with hν
  have hint : ∀ g : C(K, ℝ), ∫ x, g x ∂ν = Λ g := fun g => by
    have := RealRMK.integral_rieszMeasure Λc (ofC g)
    rw [hΛc] at this
    exact this
  have : ν.Regular := RealRMK.regular_rieszMeasure Λc
  have : IsFiniteMeasure ν := inferInstance
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun b => ?_⟩
    have : (Measure.map (b * ·) ν).Regular := Measure.Regular.map (Homeomorph.mulLeft b)
    refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
    have hm : Measurable (fun x : K => b * x) := by fun_prop
    have e := integral_map (μ := ν) (φ := fun x => b * x) hm.aemeasurable
      (f := fun y => g y) g.continuous.aestronglyMeasurable
    rw [e]
    have h1 := hint ⟨fun x => g (b * x), by have := g.continuous; fun_prop⟩
    have h2 := hint ⟨g, g.continuous⟩
    have h3 := hinv b⁻¹ ⟨g, g.continuous⟩
    simp only [translateR, inv_inv] at h3
    rw [show (fun x => g (b * x)) = ⇑(⟨fun x => g (b * x), by have := g.continuous; fun_prop⟩ :
      C(K, ℝ)) from rfl, h1]
    exact h3.trans h2.symm
  have hscal := fun g : C(K, ℝ) =>
    Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μ g.continuous
      (HasCompactSupport.of_compactSpace g)
  have key : ∀ g : C(K, ℝ), Λ g = (ν.haarScalarFactor μ : ℝ) * ∫ x, g x ∂μ := fun g => by
    rw [← hint g, hscal g, integral_smul_nnreal_measure]
    rfl
  have h1 := key 1
  simp [Measure.real] at h1
  rw [key f, h1]

end Lightlike.Rows.G2_011
