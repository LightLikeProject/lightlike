import Mathlib
import Lightlike.CausalSets.PoissonProcessCounts.Poisson2

/-!
# Independence of Poisson counts on disjoint sets (via characteristic functions)

For the Poisson process `poissonProcess lam ν` and disjoint measurable `A`, `B` the joint
characteristic function of `(N_A, N_B)` is
`E exp (i (u N_A + v N_B)) = exp (lam ν(A) (e^{iu} - 1)) · exp (lam ν(B) (e^{iv} - 1))`.
It is computed by conditioning on the Poisson number of points (the sample is an i.i.d. product, so
`E ∏ f (x i) = (∫ f dν)^n`) and mixing `c^n` over `Po(lam)`. A product of characteristic functions
means independence (Mathlib `indepFun_iff_charFun_prod`).

## Main results

* `integral_sample_prod_range`: `E ∏_{i<n} f (x i) = (∫ f dν)^n`.
* `integral_poissonMeasure_pow`: `∫ c^n d Po(lam) = exp (lam (c - 1))`.
* `integral_poissonProcess_exp_pair`: the joint exponential moment above.
* `charFun_map_poissonProcess_ptCount`: the law of `N_A` has the characteristic function of
  `Po(lam ν(A))`.
* `indepFun_poissonProcess_ptCount`: `N_A` and `N_B` are independent for disjoint `A`, `B`.

## References

* G. Last, M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press (2017).
-/

open MeasureTheory ProbabilityTheory NNReal Complex

namespace Lightlike.Rows.G2_063

variable {α : Type*} [MeasurableSpace α]

/-- A function of one coordinate of the sample integrates to the `ν`-integral. -/
lemma integral_sample_eval (ν : Measure α) [IsProbabilityMeasure ν] {f : α → ℂ}
    (hf : Measurable f) (i : ℕ) :
    ∫ x, f (x i) ∂sample ν = ∫ a, f a ∂ν := by
  have e : (sample ν).map (fun x : ℕ → α => x i) = ν :=
    Measure.infinitePi_map_eval (fun _ : ℕ => ν) i
  have h2 := integral_map (f := f) (measurable_pi_apply i).aemeasurable
    hf.aestronglyMeasurable (μ := sample ν)
  rw [e] at h2
  exact h2.symm

/-- **Product of i.i.d. coordinates**: `E ∏_{i<n} f(x i) = (∫ f dν)^n`. -/
lemma integral_sample_prod_range (ν : Measure α) [IsProbabilityMeasure ν] {f : α → ℂ}
    (hf : Measurable f) (n : ℕ) :
    ∫ x, ∏ i ∈ Finset.range n, f (x i) ∂sample ν = (∫ a, f a ∂ν) ^ n := by
  have hind : iIndepFun (fun (i : Fin n) (x : ℕ → α) => x i.val) (sample ν) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (a : α) => a)
      (fun _ => measurable_id)).precomp Fin.val_injective
  simp_rw [Finset.prod_range (fun i => f _)]
  rw [iIndepFun.integral_fun_prod_comp (f := fun _ : Fin n => f) hind
    (fun i => (measurable_pi_apply _).aemeasurable) (fun _ => hf.aestronglyMeasurable)]
  simp_rw [integral_sample_eval ν hf]
  simp

/-- **Poisson mixing of powers**: `∫ c^n d Po(lam) = exp (lam (c - 1))`. -/
lemma integral_poissonMeasure_pow (lam : ℝ≥0) (c : ℂ) :
    ∫ n, c ^ n ∂poissonMeasure lam = cexp (lam * (c - 1)) := by
  rw [integral_poissonMeasure]
  calc ∑' a : ℕ, (Real.exp (-lam) * (lam : ℝ) ^ a / a.factorial) • c ^ a
      = ∑' a : ℕ, (Real.exp (-lam) : ℂ) * (((lam : ℂ) * c) ^ a / a.factorial) := by
        congr with a
        rw [Complex.real_smul]
        push_cast
        rw [mul_pow]
        ring
    _ = (Real.exp (-lam) : ℂ) * ∑' a : ℕ, (((lam : ℂ) * c) ^ a / a.factorial) := tsum_mul_left
    _ = (Real.exp (-lam) : ℂ) * cexp ((lam : ℂ) * c) := by
        rw [(NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * c)).tsum_eq, exp_eq_exp_ℂ]
    _ = cexp (lam * (c - 1)) := by
        rw [ofReal_exp, ← Complex.exp_add]
        push_cast
        ring_nf

/-- The one-point exponential moment of the pair of indicators `(1_A, 1_B)` for disjoint sets:
`∫ exp (i (u 1_A + v 1_B)) dν = 1 + ν(A) (e^{iu} - 1) + ν(B) (e^{iv} - 1)`. -/
lemma integral_exp_indicator_pair (ν : Measure α) [IsProbabilityMeasure ν] {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) (u v : ℝ) :
    ∫ a, cexp (((u * A.indicator (1 : α → ℝ) a + v * B.indicator (1 : α → ℝ) a : ℝ) : ℂ) * I) ∂ν =
      1 + (ν.real A : ℂ) * (cexp (u * I) - 1) + (ν.real B : ℂ) * (cexp (v * I) - 1) := by
  have hpt : ∀ a, cexp (((u * A.indicator (1 : α → ℝ) a + v * B.indicator (1 : α → ℝ) a : ℝ) : ℂ)
      * I) = 1 + A.indicator (fun _ => cexp (u * I) - 1) a +
        B.indicator (fun _ => cexp (v * I) - 1) a := by
    intro a
    by_cases h1 : a ∈ A
    · have h2 : a ∉ B := fun h => Set.disjoint_left.1 hAB h1 h
      simp [h1, h2]
    · by_cases h2 : a ∈ B
      · simp [h1, h2]
      · simp [h1, h2]
  simp_rw [hpt]
  have iA : Integrable (A.indicator fun _ : α => cexp (u * I) - 1) ν :=
    (integrable_const _).indicator hA
  have iB : Integrable (B.indicator fun _ : α => cexp (v * I) - 1) ν :=
    (integrable_const _).indicator hB
  have iAB : Integrable (fun a => (1 : ℂ) + A.indicator (fun _ : α => cexp (u * I) - 1) a) ν :=
    (integrable_const (1 : ℂ)).add iA
  rw [integral_add iAB iB, integral_add (integrable_const (1 : ℂ)) iA,
    integral_indicator_const _ hA, integral_indicator_const _ hB]
  simp [Complex.real_smul]

omit [MeasurableSpace α] in
lemma ptCount_real_eq_sum (A : Set α) (n : ℕ) (x : ℕ → α) :
    (ptCount A n x : ℝ) = ∑ i ∈ Finset.range n, A.indicator (1 : α → ℝ) (x i) := by
  classical
  simp only [ptCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x i ∈ A <;> simp [h, Set.indicator]

/-- **Joint exponential moment of two counts of the Poisson process** (disjoint sets):
`E exp (i (u N_A + v N_B)) = exp (lam ν(A) (e^{iu} - 1) + lam ν(B) (e^{iv} - 1))`. -/
theorem integral_poissonProcess_exp_pair (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) (u v : ℝ) :
    ∫ p, cexp (((u * (ptCount A p.1 p.2 : ℝ) + v * (ptCount B p.1 p.2 : ℝ) : ℝ) : ℂ) * I)
        ∂poissonProcess lam ν =
      cexp (lam * (ν.real A * (cexp (u * I) - 1)) + lam * (ν.real B * (cexp (v * I) - 1))) := by
  set g : α → ℂ := fun a =>
    cexp (((u * A.indicator (1 : α → ℝ) a + v * B.indicator (1 : α → ℝ) a : ℝ) : ℂ) * I) with hg
  have hgm : Measurable g := by
    rw [hg]
    have h1 : Measurable fun a : α =>
        u * A.indicator (1 : α → ℝ) a + v * B.indicator (1 : α → ℝ) a :=
      (measurable_const.mul (measurable_one.indicator hA)).add
        (measurable_const.mul (measurable_one.indicator hB))
    fun_prop
  have hF : ∀ n (x : ℕ → α),
      cexp (((u * (ptCount A n x : ℝ) + v * (ptCount B n x : ℝ) : ℝ) : ℂ) * I) =
        ∏ i ∈ Finset.range n, g (x i) := by
    intro n x
    rw [hg]
    simp only
    rw [← Complex.exp_sum, ptCount_real_eq_sum A n x, ptCount_real_eq_sum B n x,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  have hFm : ∀ n, Measurable fun x : ℕ → α =>
      cexp (((u * (ptCount A n x : ℝ) + v * (ptCount B n x : ℝ) : ℝ) : ℂ) * I) := by
    intro n
    have h1 : Measurable fun x : ℕ → α =>
        u * (ptCount A n x : ℝ) + v * (ptCount B n x : ℝ) :=
      (measurable_const.mul (measurable_ptCount_real A hA n)).add
        (measurable_const.mul (measurable_ptCount_real B hB n))
    fun_prop
  have hm : Measurable fun p : ℕ × (ℕ → α) =>
      cexp (((u * (ptCount A p.1 p.2 : ℝ) + v * (ptCount B p.1 p.2 : ℝ) : ℝ) : ℂ) * I) :=
    measurable_from_prod_countable_right (f := fun p : ℕ × (ℕ → α) =>
      cexp (((u * (ptCount A p.1 p.2 : ℝ) + v * (ptCount B p.1 p.2 : ℝ) : ℝ) : ℂ) * I)) hFm
  have hint : Integrable (fun p : ℕ × (ℕ → α) =>
      cexp (((u * (ptCount A p.1 p.2 : ℝ) + v * (ptCount B p.1 p.2 : ℝ) : ℝ) : ℂ) * I))
      (poissonProcess lam ν) :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => (Complex.norm_exp_ofReal_mul_I _).le)
  rw [poissonProcess, integral_prod _ hint]
  simp_rw [hF, integral_sample_prod_range ν hgm, hg, integral_exp_indicator_pair ν hA hB hAB u v,
    integral_poissonMeasure_pow]
  congr 1
  ring

lemma measurable_poissonProcess_ptCount {A : Set α} (hA : MeasurableSet A) :
    Measurable fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ) :=
  measurable_from_prod_countable_right (f := fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ))
    fun n => measurable_ptCount_real A hA n

/-- The characteristic function of a Poisson count: that of `Po(lam ν(A))`. -/
theorem charFun_map_poissonProcess_ptCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) (s : ℝ) :
    charFun ((poissonProcess lam ν).map fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ)) s =
      cexp (lam * (ν.real A * (cexp (s * I) - 1))) := by
  have h := integral_poissonProcess_exp_pair lam ν hA MeasurableSet.empty
    (Set.disjoint_empty A) s 0
  simp only [zero_mul, add_zero, measureReal_empty, Complex.ofReal_zero, zero_mul,
    mul_zero, Complex.exp_zero] at h
  rw [charFun_apply, integral_map (measurable_poissonProcess_ptCount hA).aemeasurable
    (by fun_prop)]
  simpa [mul_comm] using h

/-- **Independence of Poisson counts on disjoint sets**: for disjoint measurable `A`, `B`, the counts
`N_A` and `N_B` of the Poisson process are independent random variables. -/
theorem indepFun_poissonProcess_ptCount (lam : ℝ≥0) (ν : Measure α) [IsProbabilityMeasure ν]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : Disjoint A B) :
    IndepFun (fun p : ℕ × (ℕ → α) => (ptCount A p.1 p.2 : ℝ))
      (fun p : ℕ × (ℕ → α) => (ptCount B p.1 p.2 : ℝ)) (poissonProcess lam ν) := by
  rw [indepFun_iff_charFun_prod (measurable_poissonProcess_ptCount hA).aemeasurable
    (measurable_poissonProcess_ptCount hB).aemeasurable]
  intro t
  have hm : Measurable fun p : ℕ × (ℕ → α) => WithLp.toLp 2
      ((ptCount A p.1 p.2 : ℝ), (ptCount B p.1 p.2 : ℝ)) :=
    (WithLp.prod_continuous_toLp 2 ℝ ℝ).measurable.comp
      ((measurable_poissonProcess_ptCount hA).prodMk (measurable_poissonProcess_ptCount hB))
  rw [charFun_map_poissonProcess_ptCount lam ν hA, charFun_map_poissonProcess_ptCount lam ν hB,
    charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  have h := integral_poissonProcess_exp_pair lam ν hA hB hAB t.ofLp.1 t.ofLp.2
  rw [← Complex.exp_add, ← h]
  congr 1

end Lightlike.Rows.G2_063
