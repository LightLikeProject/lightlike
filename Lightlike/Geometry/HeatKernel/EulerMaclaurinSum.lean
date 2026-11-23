import Lightlike.Geometry.HeatKernel.EulerMaclaurin

/-!
# Euler–Maclaurin summation to order six (finite sums)

Summing `integral_unit_interval_six` over the intervals `[j, j+1]`, `j < N`, gives the Euler–Maclaurin
formula for the partial sum `∑_{j<N} g j` of a smooth function, with the boundary terms at `0` and `N`
and the Bernoulli remainder `(1/720) ∑_{j<N} I₆(g(· + j))`.

## Main results

* `Lightlike.HeatKernel.integral_eq_sum_six`: the finite-`N` formula.
* `Lightlike.HeatKernel.abs_bernoulliInt_six_le`: `|I₆(g(· + j))| ≤ M ∫_j^{j+1} |g⁽⁶⁾|`.
-/

open intervalIntegral

noncomputable section

namespace Lightlike.HeatKernel

/-- Shifts of a smooth function stay smooth in the sense used by the Bernoulli lemmas. -/
theorem shift_smooth (g : ℝ → ℝ) (hg : ∀ k, Differentiable ℝ (iteratedDeriv k g)) (c : ℝ) :
    ∀ k, Differentiable ℝ (iteratedDeriv k (fun x => g (x + c))) := by
  intro k
  rw [iteratedDeriv_comp_add_const]
  exact (hg k).comp (differentiable_id.add_const c)

/-- **Euler–Maclaurin summation, order six, finite `N`.**
`∫₀^N g = ∑_{j<N} g j + (g N - g 0)/2 - (g'(N) - g'(0))/12 + (g'''(N) - g'''(0))/720
  - B₆ (g⁽⁵⁾(N) - g⁽⁵⁾(0))/720 + (1/720) ∑_{j<N} I₆(g(· + j))`. -/
theorem integral_eq_sum_six (g : ℝ → ℝ) (hg : ∀ k, Differentiable ℝ (iteratedDeriv k g)) (N : ℕ) :
    ∫ x in (0 : ℝ)..N, g x =
      (∑ j ∈ Finset.range N, g j) + (g N - g 0) / 2
        - (iteratedDeriv 1 g N - iteratedDeriv 1 g 0) / 12
        + (iteratedDeriv 3 g N - iteratedDeriv 3 g 0) / 720
        - bernoulliFun 6 0 * (iteratedDeriv 5 g N - iteratedDeriv 5 g 0) / 720
        + (∑ j ∈ Finset.range N, bernoulliInt (fun x => g (x + j)) 6) / 720 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hint : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
      fun a b => ((hg 0).continuous).intervalIntegrable a b
    have hsplit : ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), g x =
        (∫ x in (0 : ℝ)..N, g x) + ∫ x in (N : ℝ)..((N + 1 : ℕ) : ℝ), g x :=
      (integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
    have hshift : ∫ x in (N : ℝ)..((N + 1 : ℕ) : ℝ), g x =
        ∫ x in (0 : ℝ)..1, g (x + N) := by
      rw [intervalIntegral.integral_comp_add_right (fun x => g x) (N : ℝ)]
      congr 1 <;> push_cast <;> ring
    have hu := integral_unit_interval_six (fun x => g (x + N)) (shift_smooth g hg N)
    simp only [iteratedDeriv_comp_add_const] at hu
    rw [hsplit, hshift, hu, ih]
    simp only [Finset.sum_range_succ, zero_add]
    push_cast
    have e1 : (1 : ℝ) + N = N + 1 := by ring
    rw [e1]
    ring

/-- Bound on the Bernoulli remainder of a unit interval: with `M` bounding `|B₆|` on `[0,1]`,
`|I₆(g(· + j))| ≤ M ∫_j^{j+1} |g⁽⁶⁾|`. -/
theorem abs_bernoulliInt_six_le (g : ℝ → ℝ) (hg : ∀ k, Differentiable ℝ (iteratedDeriv k g))
    (M : ℝ) (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun 6 x| ≤ M) (j : ℕ) :
    |bernoulliInt (fun x => g (x + j)) 6| ≤ M * ∫ x in (j : ℝ)..(j + 1 : ℝ), |iteratedDeriv 6 g x| := by
  unfold bernoulliInt
  rw [iteratedDeriv_comp_add_const]
  have hc : Continuous (iteratedDeriv 6 g) := (hg 6).continuous
  have h1 : |∫ x in (0 : ℝ)..1, bernoulliFun 6 x * iteratedDeriv 6 g (x + j)| ≤
      ∫ x in (0 : ℝ)..1, |bernoulliFun 6 x * iteratedDeriv 6 g (x + j)| :=
    abs_integral_le_integral_abs zero_le_one
  have h2 : ∫ x in (0 : ℝ)..1, |bernoulliFun 6 x * iteratedDeriv 6 g (x + j)| ≤
      ∫ x in (0 : ℝ)..1, M * |iteratedDeriv 6 g (x + j)| := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (((continuous_bernoulliFun 6).mul (hc.comp (continuous_id.add continuous_const))).abs
        ).intervalIntegrable _ _
    · exact ((continuous_const.mul (hc.comp (continuous_id.add continuous_const)).abs)
        ).intervalIntegrable _ _
    · intro x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hM x hx) (abs_nonneg _)
  have h3 : ∫ x in (0 : ℝ)..1, M * |iteratedDeriv 6 g (x + j)| =
      M * ∫ x in (j : ℝ)..(j + 1 : ℝ), |iteratedDeriv 6 g x| := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_comp_add_right (fun x => |iteratedDeriv 6 g x|) (j : ℝ)]
    rw [zero_add, add_comm (1 : ℝ) (j : ℝ)]
  linarith

/-- **Euler–Maclaurin with error bound for a convergent sum.** Let `g` be smooth, integrable on
`(0, ∞)`, with `g, g', g''', g⁽⁵⁾ → 0` at `+∞` and `g⁽⁶⁾` integrable on `(0, ∞)`, and suppose
`∑ g j = S`. If `M` bounds `|B₆|` on `[0,1]`, then
`|S - (∫₀^∞ g + g 0/2 - g'(0)/12 + g'''(0)/720 - B₆ g⁽⁵⁾(0)/720)| ≤ (M/720) ∫₀^∞ |g⁽⁶⁾|`. -/
theorem abs_sum_sub_le (g : ℝ → ℝ) (hg : ∀ k, Differentiable ℝ (iteratedDeriv k g))
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (h0 : Filter.Tendsto g Filter.atTop (nhds 0))
    (h1 : Filter.Tendsto (iteratedDeriv 1 g) Filter.atTop (nhds 0))
    (h3 : Filter.Tendsto (iteratedDeriv 3 g) Filter.atTop (nhds 0))
    (h5 : Filter.Tendsto (iteratedDeriv 5 g) Filter.atTop (nhds 0))
    (h6 : MeasureTheory.IntegrableOn (iteratedDeriv 6 g) (Set.Ioi 0))
    (S : ℝ) (hS : Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, g j) Filter.atTop (nhds S))
    (M : ℝ) (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |bernoulliFun 6 x| ≤ M) :
    |S - ((∫ x in Set.Ioi (0 : ℝ), g x) + g 0 / 2 - iteratedDeriv 1 g 0 / 12
        + iteratedDeriv 3 g 0 / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g 0 / 720)| ≤
      M / 720 * ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 g x| := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  set J : ℝ := ∫ x in Set.Ioi (0 : ℝ), |iteratedDeriv 6 g x| with hJ
  have hnat : Filter.Tendsto (fun N : ℕ => (N : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hI : Filter.Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..N, g x) Filter.atTop
      (nhds (∫ x in Set.Ioi (0 : ℝ), g x)) :=
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0 hint Filter.tendsto_id).comp hnat
  -- bound on the remainder sum
  have hc6 : Continuous (iteratedDeriv 6 g) := (hg 6).continuous
  have hR : ∀ N : ℕ, |∑ j ∈ Finset.range N, bernoulliInt (fun x => g (x + j)) 6| ≤ M * J := by
    intro N
    have hab : ∀ j : ℕ, |bernoulliInt (fun x => g (x + j)) 6| ≤
        M * ∫ x in (j : ℝ)..(j + 1 : ℝ), |iteratedDeriv 6 g x| := abs_bernoulliInt_six_le g hg M hM
    calc |∑ j ∈ Finset.range N, bernoulliInt (fun x => g (x + j)) 6|
        ≤ ∑ j ∈ Finset.range N, |bernoulliInt (fun x => g (x + j)) 6| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, M * ∫ x in (j : ℝ)..(j + 1 : ℝ), |iteratedDeriv 6 g x| :=
          Finset.sum_le_sum fun j _ => hab j
      _ = M * ∫ x in (0 : ℝ)..N, |iteratedDeriv 6 g x| := by
          rw [← Finset.mul_sum]
          congr 1
          have := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ))
            (f := fun x => |iteratedDeriv 6 g x|) (μ := MeasureTheory.volume) (n := N)
            (fun j _ => (hc6.abs).intervalIntegrable _ _)
          simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at this
          exact this
      _ ≤ M * J := by
          apply mul_le_mul_of_nonneg_left _ hM0
          rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
          exact MeasureTheory.setIntegral_mono_set h6.abs
            (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (Filter.Eventually.of_forall (Set.Ioc_subset_Ioi_self))
  -- limit of the tail terms
  have ht : Filter.Tendsto (fun N : ℕ => |(g N) / 2 - iteratedDeriv 1 g N / 12
      + iteratedDeriv 3 g N / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g N / 720|)
      Filter.atTop (nhds 0) := by
    have := ((((h0.comp hnat).div_const 2).sub ((h1.comp hnat).div_const 12)).add
      ((h3.comp hnat).div_const 720)).sub (((h5.comp hnat).const_mul (bernoulliFun 6 0)).div_const 720)
    simp only [Function.comp, zero_div, add_zero, mul_zero, sub_self] at this
    simpa using this.abs
  have hbound : ∀ N : ℕ, |(∑ j ∈ Finset.range N, g j) -
      ((∫ x in (0 : ℝ)..N, g x) + g 0 / 2 - iteratedDeriv 1 g 0 / 12
        + iteratedDeriv 3 g 0 / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g 0 / 720)| ≤
      |(g N) / 2 - iteratedDeriv 1 g N / 12
      + iteratedDeriv 3 g N / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g N / 720| + M / 720 * J := by
    intro N
    have hE := integral_eq_sum_six g hg N
    have hRN := hR N
    set R := ∑ j ∈ Finset.range N, bernoulliInt (fun x => g (x + j)) 6
    have : (∑ j ∈ Finset.range N, g j) -
      ((∫ x in (0 : ℝ)..N, g x) + g 0 / 2 - iteratedDeriv 1 g 0 / 12
        + iteratedDeriv 3 g 0 / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g 0 / 720) =
        -((g N) / 2 - iteratedDeriv 1 g N / 12
      + iteratedDeriv 3 g N / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g N / 720) - R / 720 := by
      linarith
    rw [this]
    calc _ ≤ |-((g N) / 2 - iteratedDeriv 1 g N / 12
      + iteratedDeriv 3 g N / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g N / 720)| + |R / 720| := by
            have := abs_sub (-((g N) / 2 - iteratedDeriv 1 g N / 12
      + iteratedDeriv 3 g N / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g N / 720)) (R / 720)
            exact this
      _ ≤ _ := by
            rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 720)]
            have : |R| / 720 ≤ M / 720 * J := by
              rw [div_mul_eq_mul_div]
              exact div_le_div_of_nonneg_right hRN (by norm_num)
            linarith
  have hlim : Filter.Tendsto (fun N : ℕ => |(∑ j ∈ Finset.range N, g j) -
      ((∫ x in (0 : ℝ)..N, g x) + g 0 / 2 - iteratedDeriv 1 g 0 / 12
        + iteratedDeriv 3 g 0 / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g 0 / 720)|)
      Filter.atTop (nhds |S - ((∫ x in Set.Ioi (0 : ℝ), g x) + g 0 / 2 - iteratedDeriv 1 g 0 / 12
        + iteratedDeriv 3 g 0 / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g 0 / 720)|) := by
    refine (hS.sub ?_).abs
    exact (((hI.add_const (g 0 / 2)).sub_const (iteratedDeriv 1 g 0 / 12)).add_const
      (iteratedDeriv 3 g 0 / 720)).sub_const (bernoulliFun 6 0 * iteratedDeriv 5 g 0 / 720)
  have hub : Filter.Tendsto (fun N : ℕ => |(g N) / 2 - iteratedDeriv 1 g N / 12
      + iteratedDeriv 3 g N / 720 - bernoulliFun 6 0 * iteratedDeriv 5 g N / 720| + M / 720 * J)
      Filter.atTop (nhds (0 + M / 720 * J)) := ht.add_const _
  have := le_of_tendsto_of_tendsto hlim hub (Filter.Eventually.of_forall hbound)
  rwa [zero_add] at this

end Lightlike.HeatKernel
