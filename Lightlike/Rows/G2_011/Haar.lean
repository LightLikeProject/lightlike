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

open scoped ComplexOrder

section
variable {X : Type*} [TopologicalSpace X]

/-- A real continuous function viewed as a complex one. -/
def cplx (u : C(X, ℝ)) : C(X, ℂ) := ⟨fun x => (u x : ℂ), by fun_prop⟩

@[simp] lemma cplx_apply (u : C(X, ℝ)) (x : X) : cplx u x = (u x : ℂ) := rfl

lemma cplx_add (u v : C(X, ℝ)) : cplx (u + v) = cplx u + cplx v := by ext x; simp

lemma cplx_sub (u v : C(X, ℝ)) : cplx (u - v) = cplx u - cplx v := by ext x; simp

lemma cplx_smul (c : ℝ) (u : C(X, ℝ)) : cplx (c • u) = (c : ℂ) • cplx u := by ext x; simp
end

omit [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] in
lemma cplx_translateR (k : K) (u : C(K, ℝ)) : cplx (translateR k u) = translate K k (cplx u) := by
  ext x; simp

/-- **Positive left-invariant functionals are Haar integrals (complex form).** A linear functional
`Λ` on `C(K, ℂ)` of a compact group with `0 ≤ Λ (f̄ f)` for all `f`, invariant under left
translation, is `Λ f = Λ 1 · ∫ f dμ` for a Haar probability measure `μ`. -/
theorem invariant_functional_eq_haar (Λ : C(K, ℂ) →ₗ[ℂ] ℂ)
    (hpos : ∀ f : C(K, ℂ), 0 ≤ Λ (star f * f))
    (hinv : ∀ (k : K) (f : C(K, ℂ)), Λ (translate K k f) = Λ f)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ] (f : C(K, ℂ)) :
    Λ f = Λ 1 * ∫ x, f x ∂μ := by
  -- nonnegative real functions are sent to nonnegative numbers
  have hnn : ∀ u : C(K, ℝ), 0 ≤ u → 0 ≤ Λ (cplx u) := fun u hu => by
    have h := hpos (cplx ⟨fun x => Real.sqrt (u x), by fun_prop⟩)
    convert h using 2
    ext x
    simp [← Complex.ofReal_mul]
    exact (Real.mul_self_sqrt (hu x)).symm
  -- hence real functions are sent to real numbers
  have him : ∀ u : C(K, ℝ), (Λ (cplx u)).im = 0 := fun u => by
    have hp : 0 ≤ u ⊔ 0 := fun x => by simp
    have hq : 0 ≤ (u ⊔ 0) - u := fun x => by simp
    have e : u = (u ⊔ 0) - ((u ⊔ 0) - u) := by ext x; simp
    rw [e, cplx_sub, map_sub]
    simp [(Complex.nonneg_iff.1 (hnn _ hp)).2.symm, (Complex.nonneg_iff.1 (hnn _ hq)).2.symm]
  let Λr : C(K, ℝ) →ₗ[ℝ] ℝ :=
  { toFun u := (Λ (cplx u)).re
    map_add' u v := by simp [cplx_add]
    map_smul' c u := by
      rw [cplx_smul, RingHom.id_apply, smul_eq_mul]
      simp }
  have hreal := fun u : C(K, ℝ) =>
    real_invariant_functional_eq_haar Λr
      (fun u hu => (Complex.nonneg_iff.1 (hnn u hu)).1)
      (fun k u => by
        show (Λ (cplx (translateR k u))).re = (Λ (cplx u)).re
        rw [cplx_translateR, hinv])
      μ u
  have hΛ : ∀ u : C(K, ℝ), Λ (cplx u) = ((Λr 1 * ∫ x, u x ∂μ : ℝ) : ℂ) := fun u => by
    rw [← hreal u]
    exact Complex.ext (by simp [Λr]) (by simpa [Λr] using him u)
  have hone : Λ 1 = (Λr 1 : ℂ) := by
    have := hΛ 1
    have h1 : cplx (1 : C(K, ℝ)) = 1 := by ext x; simp
    rw [h1] at this
    rw [this]
    simp
  have hdecomp : f = cplx ⟨fun x => (f x).re, by fun_prop⟩ +
      Complex.I • cplx ⟨fun x => (f x).im, by fun_prop⟩ := by
    ext x
    simp only [ContinuousMap.add_apply, cplx_apply, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, ContinuousMap.coe_mk]
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hint : Integrable (fun x => f x) μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set fr : C(K, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩ with hfr
  set fi : C(K, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩ with hfi
  have hre : ∫ x, fr x ∂μ = (∫ x, f x ∂μ).re := integral_re hint
  have him' : ∫ x, fi x ∂μ = (∫ x, f x ∂μ).im := integral_im hint
  conv_lhs => rw [hdecomp]
  rw [map_add, map_smul, hΛ, hΛ, hone, hre, him', smul_eq_mul]
  conv_rhs => rw [← Complex.re_add_im (∫ x, f x ∂μ)]
  push_cast
  ring

end Lightlike.Rows.G2_011
