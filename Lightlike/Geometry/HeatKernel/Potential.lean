import Mathlib
import Lightlike.Geometry.HeatKernel.Expansion
import Lightlike.Geometry.HeatKernel.Consistency
import Lightlike.Geometry.HeatKernel.Sphere3Expansion

/-!
# Heat-trace expansion with a constant potential `E`

Pass 4 of row G1-018. For the Laplace-type operator `D = -(Δ + E)` with a constant scalar potential
`E = c`, `e^{-tD} = e^{tc} e^{tΔ}`, so the heat trace is `e^{tc}` times the trace of `e^{tΔ}`.
The Seeley–DeWitt coefficient is then `a₁ = (4π)^{-n/2} V (6E + R)/6`, the "6E" of
Vassilevich (key `vassilevich-2003`, eq. (4.27)).

## Main results

* `exp_mul_taylor_isBigO`: `e^{ct} = Σ_{j<M} c^j t^j / j! + O(t^M)`.
* `hasHeatExpansionTo_monomial_exp`: the expansion of `t^{i-n/2} e^{ct}`.
* `HasHeatExpansionTo.mul_exp`, `HasHeatExpansion.mul_exp`: `K e^{ct}` has Cauchy-product coefficients.
* `heatCoeffsE`, `heatCoeffsE_eq_mulExpCoeffs`: the coefficients `a₀,a₁,a₂` with potential `E`.
* `hasHeatExpansionTo_torusTrace_exp`, `..._sphereTrace_exp`, `..._sphere3Trace_exp`: examples.
* `heatCoeffsE_one_unique`: `a₁ = (4π)^{-n/2} V (6E+R)/6` is forced.
-/

open Filter Topology Asymptotics Real

noncomputable section

namespace Lightlike.HeatKernel

/-- **Taylor remainder of `e^{ct}`.** For `M > 0`,
`e^{ct} - Σ_{j<M} c^j/j! t^j = O(t^M)` as `t → 0⁺`. -/
theorem exp_mul_taylor_isBigO (c : ℝ) {M : ℕ} (hM : 0 < M) :
    (fun t : ℝ => Real.exp (c * t) - ∑ j ∈ Finset.range M, c ^ j / (j.factorial : ℝ) * t ^ j)
      =O[𝓝[>] (0 : ℝ)] fun t => t ^ M := by
  refine IsBigO.of_bound (|c| ^ M * (((M.succ : ℕ) : ℝ) / ((M.factorial : ℕ) * (M : ℕ)))) ?_
  have hδ : (0 : ℝ) < 1 / (|c| + 1) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  have ht0 : 0 < t := ht.1
  have hct : |c * t| ≤ 1 := by
    rw [abs_mul, abs_of_pos ht0]
    have h1 : t * (|c| + 1) < 1 := by
      have := ht.2
      rw [lt_div_iff₀ (by positivity)] at this
      exact this
    nlinarith [abs_nonneg c]
  have hb := Real.exp_bound hct hM
  have hs : ∑ m ∈ Finset.range M, (c * t) ^ m / (m.factorial : ℝ) =
      ∑ j ∈ Finset.range M, c ^ j / (j.factorial : ℝ) * t ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  rw [hs, abs_mul, abs_of_pos ht0, mul_pow] at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos ht0 M)]
  calc _ ≤ |c| ^ M * t ^ M * (((M.succ : ℕ) : ℝ) / ((M.factorial : ℕ) * (M : ℕ))) := hb
    _ = _ := by ring

/-- **Expansion of a shifted exponential.** For `M > 0`, the function `t^{i - n/2} e^{ct}` has the
expansion to order `i + M` with coefficients `c^{k-i}/(k-i)!` for `k ≥ i` (and `0` for `k < i`). -/
theorem hasHeatExpansionTo_monomial_exp (n i : ℕ) (c : ℝ) {M : ℕ} (hM : 0 < M) :
    HasHeatExpansionTo n (i + M) (fun t => t ^ ((i : ℝ) - n / 2) * Real.exp (c * t))
      (fun k => if i ≤ k then c ^ (k - i) / ((k - i).factorial : ℝ) else 0) := by
  unfold HasHeatExpansionTo
  have h := (isBigO_refl (fun t : ℝ => t ^ ((i : ℝ) - n / 2)) (𝓝[>] (0 : ℝ))).mul
    (exp_mul_taylor_isBigO c hM)
  refine h.congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [Finset.sum_range_add]
    have h0 : ∑ k ∈ Finset.range i, (if i ≤ k then c ^ (k - i) / ((k - i).factorial : ℝ) else 0) *
        t ^ ((k : ℝ) - n / 2) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk' : ¬ i ≤ k := by simpa using hk
      simp [hk']
    rw [h0, zero_add, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left]
    have : t ^ (((i + j : ℕ) : ℝ) - n / 2) = t ^ ((i : ℝ) - n / 2) * t ^ j := by
      rw [← Real.rpow_natCast t j, ← Real.rpow_add ht]
      congr 1; push_cast; ring
    rw [this]; ring
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    show t ^ ((i : ℝ) - n / 2) * t ^ M = t ^ (((i + M : ℕ) : ℝ) - n / 2)
    rw [← Real.rpow_natCast t M, ← Real.rpow_add ht]
    congr 1; push_cast; ring

/-- Coefficients of `K(t) e^{ct}` when `K` has coefficients `a`: the Cauchy product with `e^{ct}`,
`b k = Σ_{i ≤ k} a i * c^{k-i}/(k-i)!`. -/
def mulExpCoeffs (c : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), a i * (c ^ (k - i) / ((k - i).factorial : ℝ))

/-- Reindexing of the double sum used for the Cauchy product. -/
theorem sum_mul_ite_swap (n N : ℕ) (c : ℝ) (a : ℕ → ℝ) (t : ℝ) :
    ∑ i ∈ Finset.range N, a i * ∑ k ∈ Finset.range N,
        (if i ≤ k then c ^ (k - i) / ((k - i).factorial : ℝ) else 0) * t ^ ((k : ℝ) - n / 2)
      = ∑ k ∈ Finset.range N, mulExpCoeffs c a k * t ^ ((k : ℝ) - n / 2) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < N := by simpa using hk
  have hfil : Finset.range (k + 1) = (Finset.range N).filter (fun i => i ≤ k) := by
    ext i; simp only [Finset.mem_range, Finset.mem_filter]; omega
  unfold mulExpCoeffs
  rw [Finset.sum_mul, hfil, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- **Multiplying an expansion by `e^{ct}`.** If `K ∼ Σ a_k t^{k-n/2}` then
`K e^{ct} ∼ Σ b_k t^{k-n/2}` with `b` the Cauchy product `mulExpCoeffs c a`. -/
theorem HasHeatExpansionTo.mul_exp {n N : ℕ} {K : ℝ → ℝ} {a : ℕ → ℝ} (c : ℝ)
    (hK : HasHeatExpansionTo n N K a) :
    HasHeatExpansionTo n N (fun t => K t * Real.exp (c * t)) (mulExpCoeffs c a) := by
  unfold HasHeatExpansionTo at hK ⊢
  have hbd : (fun t : ℝ => Real.exp (c * t)) =O[𝓝[>] (0 : ℝ)] (1 : ℝ → ℝ) := by
    have h : Tendsto (fun t : ℝ => Real.exp (c * t)) (𝓝 0) (𝓝 (Real.exp (c * 0))) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0
    exact (h.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  have h1 := hK.mul hbd
  have h2 : (fun t : ℝ => ∑ i ∈ Finset.range N, a i *
      (t ^ ((i : ℝ) - n / 2) * Real.exp (c * t) - ∑ k ∈ Finset.range N,
        (if i ≤ k then c ^ (k - i) / ((k - i).factorial : ℝ) else 0) * t ^ ((k : ℝ) - n / 2)))
      =O[𝓝[>] (0 : ℝ)] fun t => t ^ ((N : ℝ) - n / 2) := by
    refine IsBigO.fun_sum fun i hi => ?_
    have hiN : i < N := by simpa using hi
    have := hasHeatExpansionTo_monomial_exp n i c (M := N - i) (by omega)
    rw [Nat.add_sub_cancel' hiN.le] at this
    exact this.const_mul_left (a i)
  refine ((h1.congr_right (fun t => by simp)).add h2).congr_left ?_
  intro t
  simp only [mul_sub, Finset.sum_sub_distrib, sum_mul_ite_swap]
  rw [sub_mul, Finset.sum_mul]
  have : ∑ i ∈ Finset.range N, a i * (t ^ ((i : ℝ) - n / 2) * Real.exp (c * t)) =
      ∑ i ∈ Finset.range N, a i * t ^ ((i : ℝ) - n / 2) * Real.exp (c * t) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

/-- Full-order version of `HasHeatExpansionTo.mul_exp`. -/
theorem HasHeatExpansion.mul_exp {n : ℕ} {K : ℝ → ℝ} {a : ℕ → ℝ} (c : ℝ)
    (hK : HasHeatExpansion n K a) :
    HasHeatExpansion n (fun t => K t * Real.exp (c * t)) (mulExpCoeffs c a) :=
  fun N => (hK.to N).mul_exp c

/-- Seeley–DeWitt coefficients `a₀, a₁, a₂` (others `0`) of `D = -(Δ + E)` with constant potential `E`
on a closed `n`-manifold of volume `V`, constant scalar curvature `R`, `|Ric|² = ric`,
`|Riem|² = riem`: `a₁ = (4π)^{-n/2} V (6E + R)/6`, `a₂ = (4π)^{-n/2} V (180E² + 60RE + 5R² - 2ric +
2riem)/360` (the "6E" of `vassilevich-2003`, eq. (4.27)). -/
def heatCoeffsE (n : ℕ) (V R ric riem E : ℝ) : ℕ → ℝ
  | 0 => (4 * π) ^ (-((n : ℝ) / 2)) * V
  | 1 => (4 * π) ^ (-((n : ℝ) / 2)) * V * (6 * E + R) / 6
  | 2 => (4 * π) ^ (-((n : ℝ) / 2)) * V *
      (180 * E ^ 2 + 60 * R * E + 5 * R ^ 2 - 2 * ric + 2 * riem) / 360
  | _ => 0

/-- `heatCoeffsE` is the Cauchy product of `heatCoeffs` with `e^{Et}`, up to `a₂`. -/
theorem heatCoeffsE_eq_mulExpCoeffs (n : ℕ) (V R ric riem E : ℝ) {k : ℕ} (hk : k < 3) :
    mulExpCoeffs E (heatCoeffs n V R ric riem) k = heatCoeffsE n V R ric riem E k := by
  interval_cases k
  · simp [mulExpCoeffs, heatCoeffs, heatCoeffsE]
  · simp [mulExpCoeffs, heatCoeffs, heatCoeffsE, Finset.sum_range_succ]
    ring
  · simp [mulExpCoeffs, heatCoeffs, heatCoeffsE, Finset.sum_range_succ]
    ring

/-- With `E = 0`, `heatCoeffsE` is `heatCoeffs`. -/
theorem heatCoeffsE_zero (n : ℕ) (V R ric riem : ℝ) {k : ℕ} (hk : k < 3) :
    heatCoeffsE n V R ric riem 0 k = heatCoeffs n V R ric riem k := by
  interval_cases k <;> simp [heatCoeffsE, heatCoeffs]

/-- **Potential shift.** If `K` has the Seeley–DeWitt expansion of `-Δ` to order `3`, then
`K(t) e^{Et}` (the heat trace of `-(Δ + E)`) has the expansion with `heatCoeffsE`. -/
theorem HasHeatExpansionTo.heatCoeffsE {n : ℕ} {K : ℝ → ℝ} {V R ric riem : ℝ}
    (hK : HasHeatExpansionTo n 3 K (heatCoeffs n V R ric riem)) (E : ℝ) :
    HasHeatExpansionTo n 3 (fun t => K t * Real.exp (E * t)) (heatCoeffsE n V R ric riem E) :=
  (hK.mul_exp E).congr_coeff fun _ hk => heatCoeffsE_eq_mulExpCoeffs n V R ric riem E hk

/-- **Torus with potential.** `e^{Et} Σ_{k∈ℤⁿ} e^{-t|k|²}` has the expansion of `-(Δ + E)` on the flat
torus: `a₁ = (4π)^{-n/2} V E` (here `R = 0`). -/
theorem hasHeatExpansionTo_torusTrace_exp (n : ℕ) (E : ℝ) :
    HasHeatExpansionTo n 3 (fun t => torusTrace n t * Real.exp (E * t))
      (heatCoeffsE n ((2 * π) ^ n) 0 0 0 E) :=
  ((hasHeatExpansion_torusTrace_geom n).to 3).heatCoeffsE E

/-- **`S²` with potential.** `e^{Et} Σ (2l+1) e^{-t l(l+1)}` has the expansion of `-(Δ + E)` on the unit
`S²` (`V = 4π`, `R = 2`): `a₁ = (6E + 2)/6`. -/
theorem hasHeatExpansionTo_sphereTrace_exp (E : ℝ) :
    HasHeatExpansionTo 2 3 (fun t => sphereTrace t * Real.exp (E * t))
      (heatCoeffsE 2 (4 * π) 2 2 4 E) :=
  hasHeatExpansionTo_sphereTrace_geom.heatCoeffsE E

/-- **`S³` with potential.** The same for the round unit `S³` (`V = 2π²`, `R = 6`). -/
theorem hasHeatExpansionTo_sphere3Trace_exp (E : ℝ) :
    HasHeatExpansionTo 3 3 (fun t => sphere3Trace t * Real.exp (E * t))
      (heatCoeffsE 3 (2 * π ^ 2) 6 12 12 E) :=
  hasHeatExpansionTo_sphere3Trace_geom.heatCoeffsE E

/-- **`a₁` with potential is geometric.** Any coefficient sequence of an expansion of `K e^{Et}` to
order `≥ 2` that also has the geometric `heatCoeffsE` expansion has `a 1 = (4π)^{-n/2} V (6E+R)/6`. -/
theorem heatCoeffsE_one_unique {n m : ℕ} (hm : 2 ≤ m) {K : ℝ → ℝ} {a : ℕ → ℝ}
    {V R ric riem E : ℝ} (ha : HasHeatExpansionTo n m K a)
    (hg : HasHeatExpansionTo n m K (heatCoeffsE n V R ric riem E)) :
    a 1 = (4 * π) ^ (-((n : ℝ) / 2)) * V * (6 * E + R) / 6 :=
  ha.coeff_unique hg 1 (by omega)

end Lightlike.HeatKernel
