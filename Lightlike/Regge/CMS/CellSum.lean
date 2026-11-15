import Mathlib

/-!
# A Riemann sum over cells that cover a region three times (RC6b, step 11)

The deficit of a vertex is a multiple of the area of its star, and every triangle lies in the stars
of its three vertices. So if the stars (as measurable cells `S i` around vertices `p i`) cover a
region `Ω` three times, except in a thin boundary layer `B` where they cover at most three times,
a vertex sum of a Lipschitz density weighted by the cell areas approximates the integral over `Ω`.

## Main results

* `cover_integral_approx`: `|∑ i, ∫_{S i} φ - 3 ∫_Ω φ| ≤ 3 Φ |B|` for `|φ| ≤ Φ` on `K`.
* `cell_sum_approx`: `|(1/3) ∑ i, φ (p i) |S i| - ∫_Ω φ| ≤ 2 L h |K| + Φ |B|` for a Lipschitz `φ`.
-/

open MeasureTheory Set

namespace Lightlike.CMS

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- **The cells cover the region three times, up to a boundary layer.** The cells cover every
point at most three times, exactly three times in `Ω` away from `B`, and nothing outside `K`. -/
theorem cover_integral_approx {V : Finset ι} {S : ι → Set E} {Ω K B : Set E} {φ : E → ℝ}
    {Φ : ℝ} (hK : IsCompact K) (hφ : ContinuousOn φ K) (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ x ∈ K, |φ x| ≤ Φ)
    (hSm : ∀ i ∈ V, MeasurableSet (S i)) (hSK : ∀ i ∈ V, S i ⊆ K) (hΩm : MeasurableSet Ω)
    (hΩ : Ω ⊆ K) (hBm : MeasurableSet B) (hBK : B ⊆ K)
    (hle : ∀ᵐ x ∂μ, ∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x ≤ 3)
    (hout : ∀ᵐ x ∂μ, x ∉ B →
      ∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x = 3 * Ω.indicator (fun _ => (1 : ℝ)) x) :
    |∑ i ∈ V, ∫ x in S i, φ x ∂μ - 3 * ∫ x in Ω, φ x ∂μ| ≤ 3 * Φ * μ.real B := by
  have hint : IntegrableOn φ K μ := hφ.integrableOn_compact hK
  have hBfin : μ B < ⊤ := lt_of_le_of_lt (measure_mono hBK) hK.measure_lt_top
  have hSi : ∀ i ∈ V, Integrable ((S i).indicator φ) μ := fun i hi =>
    (integrable_indicator_iff (hSm i hi)).mpr (hint.mono_set (hSK i hi))
  have hΩi : Integrable (Ω.indicator φ) μ :=
    (integrable_indicator_iff hΩm).mpr (hint.mono_set hΩ)
  have h1 : ∑ i ∈ V, ∫ x in S i, φ x ∂μ = ∫ x, ∑ i ∈ V, (S i).indicator φ x ∂μ := by
    rw [integral_finsetSum _ hSi]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_indicator (hSm i hi)]
  have h2 : 3 * ∫ x in Ω, φ x ∂μ = ∫ x, 3 * Ω.indicator φ x ∂μ := by
    rw [integral_const_mul, integral_indicator hΩm]
  rw [h1, h2, ← integral_sub (integrable_finsetSum _ hSi) (hΩi.const_mul 3), ← Real.norm_eq_abs]
  have hg : Integrable (B.indicator (fun _ => 3 * Φ)) μ :=
    (integrable_indicator_iff hBm).mpr (integrableOn_const hBfin.ne)
  have e : ∫ x, B.indicator (fun _ => 3 * Φ) x ∂μ = 3 * Φ * μ.real B := by
    rw [integral_indicator_const _ hBm, smul_eq_mul, mul_comm]
  rw [← e]
  refine norm_integral_le_of_norm_le hg ?_
  filter_upwards [hle, hout] with x hx hox
  have hS : ∀ i ∈ V, (S i).indicator φ x = φ x * (S i).indicator (fun _ => (1 : ℝ)) x := by
    intro i _
    by_cases hxi : x ∈ S i <;> simp [hxi]
  have hΩ' : Ω.indicator φ x = φ x * Ω.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hxi : x ∈ Ω <;> simp [hxi]
  have eF : ∑ i ∈ V, (S i).indicator φ x - 3 * Ω.indicator φ x =
      φ x * (∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x - 3 * Ω.indicator (fun _ => (1 : ℝ)) x) := by
    rw [Finset.sum_congr rfl hS, ← Finset.mul_sum, hΩ']; ring
  rw [eF, Real.norm_eq_abs, abs_mul]
  by_cases hxB : x ∈ B
  · rw [Set.indicator_of_mem hxB]
    have hn0 : 0 ≤ ∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x :=
      Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hΩ3 : 0 ≤ 3 * Ω.indicator (fun _ => (1 : ℝ)) x ∧ 3 * Ω.indicator (fun _ => (1 : ℝ)) x ≤ 3 := by
      by_cases hxΩ : x ∈ Ω <;> simp [hxΩ]
    have hφx := hΦ x (hBK hxB)
    have habs : |∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x -
        3 * Ω.indicator (fun _ => (1 : ℝ)) x| ≤ 3 := by
      rw [abs_le]; constructor <;> linarith [hΩ3.1, hΩ3.2]
    calc |φ x| * _ ≤ Φ * 3 := by gcongr
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hxB, hox hxB]; simp
    
/-- **Riemann sum over the cells.** For a Lipschitz `φ` on `K`, cells `S i ⊆ K` of diameter `h`
around points `p i ∈ K` that cover `Ω` three times away from the layer `B`:
`|(1/3) ∑ φ(p i) |S i| - ∫_Ω φ| ≤ 2 L h |K| + Φ |B|`. -/
theorem cell_sum_approx {V : Finset ι} {S : ι → Set E} {p : ι → E} {Ω K B : Set E} {φ : E → ℝ}
    {L : NNReal} {h Φ : ℝ} (hh : 0 ≤ h) (hΦ0 : 0 ≤ Φ) (hΦ : ∀ x ∈ K, |φ x| ≤ Φ)
    (hK : IsCompact K) (hφ : LipschitzOnWith L φ K)
    (hSm : ∀ i ∈ V, MeasurableSet (S i)) (hSK : ∀ i ∈ V, S i ⊆ K) (hp : ∀ i ∈ V, p i ∈ K)
    (hSb : ∀ i ∈ V, ∀ x ∈ S i, dist x (p i) ≤ h) (hΩm : MeasurableSet Ω) (hΩ : Ω ⊆ K)
    (hBm : MeasurableSet B) (hBK : B ⊆ K)
    (hle : ∀ᵐ x ∂μ, ∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x ≤ 3)
    (hout : ∀ᵐ x ∂μ, x ∉ B →
      ∑ i ∈ V, (S i).indicator (fun _ => (1 : ℝ)) x = 3 * Ω.indicator (fun _ => (1 : ℝ)) x) :
    |(1 / 3) * ∑ i ∈ V, φ (p i) * μ.real (S i) - ∫ x in Ω, φ x ∂μ| ≤
      2 * L * h * μ.real K + Φ * μ.real B := by
  have hfin : μ K < ⊤ := hK.measure_lt_top
  have hφc : ContinuousOn φ K := hφ.continuousOn
  have hint : IntegrableOn φ K μ := hφ.continuousOn.integrableOn_compact hK
  have hmeas1 := cover_integral_approx (μ := μ) (φ := fun _ => (1 : ℝ)) (Φ := 1) hK
    continuousOn_const zero_le_one (fun _ _ => by simp) hSm hSK hΩm hΩ hBm hBK hle hout
  have hmeas1' : |∑ i ∈ V, μ.real (S i) - 3 * μ.real Ω| ≤ 3 * 1 * μ.real B := by
    simpa [Measure.real] using hmeas1
  have hmain := cover_integral_approx (μ := μ) hK hφc hΦ0 hΦ hSm hSK hΩm hΩ hBm hBK hle hout
  have hΩK : μ.real Ω ≤ μ.real K := measureReal_mono hΩ hfin.ne
  have hBK' : μ.real B ≤ μ.real K := measureReal_mono hBK hfin.ne
  have hsumS : ∑ i ∈ V, μ.real (S i) ≤ 6 * μ.real K := by
    have := (abs_le.mp hmeas1').2
    linarith
  have hper : ∀ i ∈ V, |φ (p i) * μ.real (S i) - ∫ x in S i, φ x ∂μ| ≤ L * h * μ.real (S i) := by
    intro i hi
    have hSfin : μ (S i) < ⊤ := lt_of_le_of_lt (measure_mono (hSK i hi)) hfin
    have hI : IntegrableOn φ (S i) μ := hint.mono_set (hSK i hi)
    have e : φ (p i) * μ.real (S i) - ∫ x in S i, φ x ∂μ = ∫ x in S i, (φ (p i) - φ x) ∂μ := by
      rw [integral_sub (integrableOn_const hSfin.ne) hI]
      simp [mul_comm, Measure.real]
    rw [e, ← Real.norm_eq_abs]
    refine (norm_setIntegral_le_of_norm_le_const (C := L * h) hSfin ?_).trans (le_of_eq (by ring))
    intro x hx
    rw [Real.norm_eq_abs, abs_sub_comm]
    have := hφ.dist_le_mul x (hSK i hi hx) (p i) (hp i hi)
    rw [Real.dist_eq] at this
    refine this.trans ?_
    have := hSb i hi x hx
    have hL : (0 : ℝ) ≤ L := L.2
    calc (L : ℝ) * dist x (p i) ≤ L * h := by gcongr
      _ = _ := rfl
  have hsum : |∑ i ∈ V, (φ (p i) * μ.real (S i) - ∫ x in S i, φ x ∂μ)| ≤
      ∑ i ∈ V, L * h * μ.real (S i) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hper)
  rw [← Finset.mul_sum] at hsum
  have hL : (0 : ℝ) ≤ L := L.2
  have hLh : (L : ℝ) * h * ∑ i ∈ V, μ.real (S i) ≤ L * h * (6 * μ.real K) := by gcongr
  have e : (1 / 3) * ∑ i ∈ V, φ (p i) * μ.real (S i) - ∫ x in Ω, φ x ∂μ =
      (1 / 3) * ∑ i ∈ V, (φ (p i) * μ.real (S i) - ∫ x in S i, φ x ∂μ) +
        (1 / 3) * (∑ i ∈ V, ∫ x in S i, φ x ∂μ - 3 * ∫ x in Ω, φ x ∂μ) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
  have hb : |∑ i ∈ V, ∫ x in S i, φ x ∂μ - 3 * ∫ x in Ω, φ x ∂μ| ≤ 3 * Φ * μ.real B := by
    refine hmain
  nlinarith [hsum, hLh, hb]

end Lightlike.CMS
