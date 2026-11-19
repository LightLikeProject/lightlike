import Mathlib
import Lightlike.Asymptotics.Tauberian.Window

/-!
# Karamata's method: the weighted functional of a Laplace transform

For a measure `ρ` on `[0, ∞)` with Laplace transform `L β = ∫ exp (-β x) dρ` (`Tauberian.laplace`), put
`weighted ρ β h = ∫ exp (-β x) * h (exp (-β x)) dρ`. Then `weighted ρ β (u ↦ u ^ k) = L ((k + 1) β)`, so the
convergence of the ratios `L ((k + 1) β) / L β` as `β → 0⁺` to the moments `∫ exp (-t) ^ k dν` of a finite
measure `ν` on `[0, ∞)` gives the convergence of `weighted ρ β h / L β` to `∫ h (exp (-t)) dν`, first for
polynomials `h` (`tendsto_weighted_polynomial`) and then for continuous `h` by the Weierstrass theorem
(`tendsto_weighted_continuous`).

Supporting lemmas for Karamata's Tauberian theorem; no catalogue entry.
-/

open MeasureTheory Set Filter Topology Polynomial

noncomputable section

namespace Lightlike.Karamata

open Lightlike.Tauberian

variable {ρ : Measure ℝ}

/-- The weighted functional `h ↦ ∫ exp (-β x) * h (exp (-β x)) dρ` of Karamata's method. -/
def weighted (ρ : Measure ℝ) (β : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∫ x, Real.exp (-β * x) * h (Real.exp (-β * x)) ∂ρ

lemma ae_nonneg_of_Iio {ν : Measure ℝ} (hν : ν (Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  have h : {x : ℝ | ¬ 0 ≤ x} = Iio 0 := by
    ext x
    simp
  rw [h]
  exact hν

lemma exp_neg_mul_mem_Icc {β x : ℝ} (hβ : 0 < β) (hx : 0 ≤ x) : Real.exp (-β * x) ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by nlinarith)⟩

lemma exp_neg_mem_Icc {t : ℝ} (ht : 0 ≤ t) : Real.exp (-t) ∈ Icc (0 : ℝ) 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by linarith)⟩

lemma exists_bound_Icc {h : ℝ → ℝ} (hh : Continuous h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u ∈ Icc (0 : ℝ) 1, |h u| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hh.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun u hu => (hM u hu).trans (le_max_left _ _)⟩

lemma weighted_pow (β : ℝ) (k : ℕ) : weighted ρ β (fun u => u ^ k) = laplace ρ ((k + 1) * β) := by
  unfold weighted laplace
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-β * x) * Real.exp (-β * x) ^ k = Real.exp (-((k + 1) * β) * x)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma weighted_const_mul (β a : ℝ) (h : ℝ → ℝ) :
    weighted ρ β (fun u => a * h u) = a * weighted ρ β h := by
  unfold weighted
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-β * x) * (a * h (Real.exp (-β * x))) = a * (Real.exp (-β * x) * h (Real.exp (-β * x)))
  ring

lemma weighted_const (β c : ℝ) : weighted ρ β (fun _ => c) = c * laplace ρ β := by
  unfold weighted laplace
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-β * x) * c = c * Real.exp (-β * x)
  ring

/-- A continuous function of `exp (-t)` is integrable for a finite measure on `[0, ∞)`. -/
lemma integrable_comp_exp_neg {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0) {h : ℝ → ℝ}
    (hh : Continuous h) : Integrable (fun t => h (Real.exp (-t))) ν := by
  obtain ⟨M, -, hM⟩ := exists_bound_Icc hh
  have hc : Continuous fun t : ℝ => h (Real.exp (-t)) := by fun_prop
  refine Integrable.mono' (integrable_const M) hc.aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_of_Iio hν] with t ht
  rw [Real.norm_eq_abs]
  exact hM _ (exp_neg_mem_Icc ht)

section

variable (hρ : ρ (Iio 0) = 0)
  (hint : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => Real.exp (-β * x)) ρ)
include hρ hint

lemma integrable_weighted {β : ℝ} (hβ : 0 < β) {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (fun x => Real.exp (-β * x) * h (Real.exp (-β * x))) ρ := by
  obtain ⟨M, -, hM⟩ := exists_bound_Icc hh
  have hc : Continuous fun x : ℝ => Real.exp (-β * x) * h (Real.exp (-β * x)) := by fun_prop
  refine Integrable.mono' ((hint β hβ).const_mul M) hc.aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_of_Iio hρ] with x hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    mul_comm (Real.exp (-β * x)) |h (Real.exp (-β * x))|]
  exact mul_le_mul_of_nonneg_right (hM _ (exp_neg_mul_mem_Icc hβ hx)) (Real.exp_pos _).le

lemma weighted_add {β : ℝ} (hβ : 0 < β) {h₁ h₂ : ℝ → ℝ} (c₁ : Continuous h₁) (c₂ : Continuous h₂) :
    weighted ρ β (fun u => h₁ u + h₂ u) = weighted ρ β h₁ + weighted ρ β h₂ := by
  unfold weighted
  rw [← integral_add (integrable_weighted hρ hint hβ c₁) (integrable_weighted hρ hint hβ c₂)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Real.exp (-β * x) * (h₁ (Real.exp (-β * x)) + h₂ (Real.exp (-β * x))) =
    Real.exp (-β * x) * h₁ (Real.exp (-β * x)) + Real.exp (-β * x) * h₂ (Real.exp (-β * x))
  ring

lemma weighted_mono {β : ℝ} (hβ : 0 < β) {h₁ h₂ : ℝ → ℝ} (c₁ : Continuous h₁) (c₂ : Continuous h₂)
    (hle : ∀ u ∈ Icc (0 : ℝ) 1, h₁ u ≤ h₂ u) : weighted ρ β h₁ ≤ weighted ρ β h₂ := by
  unfold weighted
  refine integral_mono_ae (integrable_weighted hρ hint hβ c₁) (integrable_weighted hρ hint hβ c₂) ?_
  filter_upwards [ae_nonneg_of_Iio hρ] with x hx
  exact mul_le_mul_of_nonneg_left (hle _ (exp_neg_mul_mem_Icc hβ hx)) (Real.exp_pos _).le

lemma weighted_add_const {β : ℝ} (hβ : 0 < β) {h : ℝ → ℝ} (hh : Continuous h) (c : ℝ) :
    weighted ρ β (fun u => h u + c) = weighted ρ β h + c * laplace ρ β := by
  rw [weighted_add hρ hint hβ hh (continuous_const : Continuous fun _ : ℝ => c), weighted_const]

variable {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν (Iio 0) = 0)
  (hmom : ∀ k : ℕ, Tendsto (fun β => laplace ρ ((k + 1) * β) / laplace ρ β) (𝓝[>] 0)
    (𝓝 (∫ t, Real.exp (-t) ^ k ∂ν)))
include hν hmom

/-- Convergence of the weighted functional on polynomials, from the convergence of the moments. -/
theorem tendsto_weighted_polynomial (p : ℝ[X]) :
    Tendsto (fun β => weighted ρ β (fun u => p.eval u) / laplace ρ β) (𝓝[>] 0)
      (𝓝 (∫ t, p.eval (Real.exp (-t)) ∂ν)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hip : Integrable (fun t => p.eval (Real.exp (-t))) ν := integrable_comp_exp_neg hν p.continuous
    have hiq : Integrable (fun t => q.eval (Real.exp (-t))) ν := integrable_comp_exp_neg hν q.continuous
    have hlim : ∫ t, (p + q).eval (Real.exp (-t)) ∂ν =
        ∫ t, p.eval (Real.exp (-t)) ∂ν + ∫ t, q.eval (Real.exp (-t)) ∂ν := by
      simp only [Polynomial.eval_add]
      exact integral_add hip hiq
    rw [hlim]
    refine (hp.add hq).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with β hβ
    have hβ' : 0 < β := hβ
    show weighted ρ β (fun u => p.eval u) / laplace ρ β + weighted ρ β (fun u => q.eval u) / laplace ρ β =
      weighted ρ β (fun u => (p + q).eval u) / laplace ρ β
    simp only [Polynomial.eval_add]
    rw [weighted_add hρ hint hβ' p.continuous q.continuous, add_div]
  | monomial n a =>
    have h1 : ∀ β : ℝ, weighted ρ β (fun u => (monomial n a).eval u) =
        a * laplace ρ ((n + 1) * β) := by
      intro β
      simp only [Polynomial.eval_monomial]
      rw [weighted_const_mul, weighted_pow]
    have h2 : ∫ t, (monomial n a).eval (Real.exp (-t)) ∂ν = a * ∫ t, Real.exp (-t) ^ n ∂ν := by
      simp only [Polynomial.eval_monomial]
      rw [integral_const_mul]
    rw [h2]
    simp_rw [h1, mul_div_assoc]
    exact (hmom n).const_mul a

/-- Convergence of the weighted functional on continuous functions (Weierstrass approximation). -/
theorem tendsto_weighted_continuous (hpos : ∀ᶠ β in 𝓝[>] (0 : ℝ), 0 < laplace ρ β) {h : ℝ → ℝ}
    (hh : Continuous h) :
    Tendsto (fun β => weighted ρ β h / laplace ρ β) (𝓝[>] 0) (𝓝 (∫ t, h (Real.exp (-t)) ∂ν)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ν.real univ := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact measureReal_nonneg
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ε / (3 + m) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδm : 3 * δ + δ * m = ε := by
    rw [hδ]
    field_simp
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 h hh.continuousOn δ hδ0
  have hP := tendsto_weighted_polynomial hρ hint hν hmom p
  rw [Metric.tendsto_nhds] at hP
  filter_upwards [hP δ hδ0, hpos, self_mem_nhdsWithin] with β hβP hL hβ
  have hβ' : 0 < β := hβ
  have hA : |weighted ρ β h / laplace ρ β - weighted ρ β (fun u => p.eval u) / laplace ρ β| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos hL, div_le_iff₀ hL, abs_le]
    have u1 : weighted ρ β h ≤ weighted ρ β (fun u => p.eval u + δ) :=
      weighted_mono hρ hint hβ' hh (p.continuous.add continuous_const) (fun u hu => by
      have h1 := abs_lt.1 (hp u hu)
      show h u ≤ p.eval u + δ
      linarith [h1.1])
    have u2 : weighted ρ β (fun u => p.eval u) ≤ weighted ρ β (fun u => h u + δ) :=
      weighted_mono hρ hint hβ' p.continuous (hh.add continuous_const) (fun u hu => by
      have h1 := abs_lt.1 (hp u hu)
      show p.eval u ≤ h u + δ
      linarith [h1.2])
    rw [weighted_add_const hρ hint hβ' p.continuous] at u1
    rw [weighted_add_const hρ hint hβ' hh] at u2
    constructor <;> linarith
  have hB : |∫ t, p.eval (Real.exp (-t)) ∂ν - ∫ t, h (Real.exp (-t)) ∂ν| ≤ δ * m := by
    rw [← integral_sub (integrable_comp_exp_neg hν p.continuous) (integrable_comp_exp_neg hν hh), hm]
    exact norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun t => p.eval (Real.exp (-t)) - h (Real.exp (-t))) (C := δ) (by
        filter_upwards [ae_nonneg_of_Iio hν] with t ht
        rw [Real.norm_eq_abs]
        exact (hp _ (exp_neg_mem_Icc ht)).le)
  rw [Real.dist_eq] at hβP ⊢
  have key : weighted ρ β h / laplace ρ β - ∫ t, h (Real.exp (-t)) ∂ν =
      (weighted ρ β h / laplace ρ β - weighted ρ β (fun u => p.eval u) / laplace ρ β) +
      (weighted ρ β (fun u => p.eval u) / laplace ρ β - ∫ t, p.eval (Real.exp (-t)) ∂ν) +
      (∫ t, p.eval (Real.exp (-t)) ∂ν - ∫ t, h (Real.exp (-t)) ∂ν) := by ring
  rw [key]
  refine (abs_add_three _ _ _).trans_lt ?_
  linarith

end

end Lightlike.Karamata
