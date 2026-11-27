import Mathlib
import Lightlike.Geometry.HeatKernel.IsChartParametrix
import Lightlike.Geometry.HeatKernel.ChartParametrixDelta

/-!
# The delta property of the chart parametrix in the base point

For the chart parametrix `H(t, p, y)` (`Lightlike.IsChartParametrix`), integration in the base point `p` against a
continuous `F` supported near the centre also tends to the value at the other point:
`∫ H(t, p, y) F(p) dp → F(y)/√det g(y)` as `t → 0⁺`, uniformly for `y` near the centre.

The comparison `Lightlike.IsChartParametrix.exists_frozen_cmp` with the frozen Gaussian of `g(p)` (the second-slot
argument of `Lightlike.exists_chart_parametrix_delta`, stated for the bundle) is combined with the comparison of the
frozen Gaussians of `g(p)` and `g(y)` (`Lightlike.gauss_sub_gauss_le`, from the Lipschitz bound of `g`), and the
integrated comparison `Lightlike.delta_of_pointwise` is applied in the variable `p`.
-/

open Set Filter Metric MeasureTheory Real Matrix
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Two frozen Gaussians**: if `a, b ≥ c‖z‖²` and `|a − b| ≤ C₁‖z‖³` for `‖z‖ < r`, then
`|e^{-a/4t} − e^{-b/4t}| ≤ K √t e^{-c‖z‖²/8t}` for `t ∈ (0, 1]`. -/
theorem gauss_sub_gauss_le {t c r C₁ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hc : 0 < c) (hr : 0 < r) (hC₁ : 0 ≤ C₁)
    {z : Fin n → ℝ} {a b : ℝ} (ha : c * ‖z‖ ^ 2 ≤ a) (hb : c * ‖z‖ ^ 2 ≤ b)
    (hab : ‖z‖ < r → |a - b| ≤ C₁ * ‖z‖ ^ 3) :
    |Real.exp (-a / (4 * t)) - Real.exp (-b / (4 * t))| ≤
      (C₁ * 2 * √(4 / c) ^ 3 + 64 / (r ^ 2 * c)) * √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := by
  by_cases hz : ‖z‖ < r
  · have h := cutoffGauss_sub_frozen_le (θv := 1) (Uv := 1) (C₂ := 0) ht ht1 hc hr hC₁ le_rfl (by simp)
      (fun _ => rfl) (fun h => absurd h (not_le.2 hz)) (fun _ => ha) hb hab (fun _ => by simp)
    simpa using h
  · push Not at hz
    have hfar := exp_neg_le_of_far ht ht1 hc hr hz
    have hae : Real.exp (-a / (4 * t)) ≤ Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := by
      apply Real.exp_le_exp.2; rw [neg_div, neg_le_neg_iff]; gcongr
    have hbe : Real.exp (-b / (4 * t)) ≤ Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := by
      apply Real.exp_le_exp.2; rw [neg_div, neg_le_neg_iff]; gcongr
    have hE0 : 0 ≤ √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := by positivity
    have h1 : |Real.exp (-a / (4 * t)) - Real.exp (-b / (4 * t))| ≤ Real.exp (-(c * ‖z‖ ^ 2 / (4 * t))) := by
      rw [abs_le]; constructor <;> linarith [Real.exp_pos (-a / (4 * t)), Real.exp_pos (-b / (4 * t))]
    have h2 : 32 / (r ^ 2 * c) ≤ C₁ * 2 * √(4 / c) ^ 3 + 64 / (r ^ 2 * c) := by
      have : 0 ≤ C₁ * 2 * √(4 / c) ^ 3 := by positivity
      have : 32 / (r ^ 2 * c) ≤ 64 / (r ^ 2 * c) := by gcongr; norm_num
      linarith
    calc _ ≤ _ := h1
      _ ≤ 32 / (r ^ 2 * c) * √t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2) := hfar
      _ = 32 / (r ^ 2 * c) * (√t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2)) := by ring
      _ ≤ (C₁ * 2 * √(4 / c) ^ 3 + 64 / (r ^ 2 * c)) * (√t * Real.exp (-(c * ‖z‖ ^ 2 / (4 * t)) / 2)) :=
          mul_le_mul_of_nonneg_right h2 hE0
      _ = _ := by ring

/-- **The comparison of the chart parametrix with the frozen Gaussian of `g(p)`**, near the centre: radius `rb`,
constants `K`, `c'`, the uniform lower bound `l` of `g` there. -/
theorem IsChartParametrix.exists_frozen_cmp {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) :
    ∃ rb K c' l : ℝ, 0 < rb ∧ rb ≤ r ∧ 0 ≤ K ∧ 0 < c' ∧ 0 < l ∧ (∀ p, ‖p - x‖ < rb → p ∈ U) ∧
      (∀ p, ‖p - x‖ < rb → ∀ w, l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (g p *ᵥ w)) ∧
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < rb → ∀ y, |H t p y -
        (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t))| ≤
        (4 * π * t) ^ (-(n : ℝ) / 2) * (K * √t * Real.exp (-(c' * ‖y - p‖ ^ 2 / (4 * t)) / 2)) := by
  have hr := h.r_pos
  have hu0 := h.u_zero_diag
  have hΩo := h.isOpen
  have hxΩ := h.center_mem
  have hmem := h.mem_of_lt
  have hΩU := h.snd_mem
  have hVs := h.V_smooth
  have hus := h.u_smooth
  have hVd := h.V_diag
  have hσV := h.σ_eq
  have hθ1 := h.θ_one
  have hθ0 := h.θ_zero
  have hθr := h.θ_mem
  have hH := h.H_eq
  obtain ⟨c, hc, hσlow⟩ := h.σ_lower
  obtain ⟨A, hA⟩ := h.ansatz_le
  have hx : x ∈ U := hΩU _ hxΩ
  -- the Taylor bound of the world function
  obtain ⟨rT, C₁, hrT, hC₁, hT⟩ := exists_abs_pairing_sub_le hg.coord.toLightlike hΩo hVs hx hxΩ
    (fun p hp => (hVd p hp).1) (fun p hp => (hVd p hp).2)
  -- `u₀` is Lipschitz near `(x, x)`
  obtain ⟨KL, tL, htL, hlip⟩ :=
    (((hus 0).contDiffAt (hΩo.mem_nhds hxΩ)).of_le (by exact_mod_cast le_top) :
      ContDiffAt ℝ 1 (u 0) (x, x)).exists_lipschitzOnWith
  obtain ⟨ρL, hρL, hρLt⟩ := Metric.mem_nhds_iff.1 htL
  -- the higher coefficients are bounded near `(x, x)`
  obtain ⟨ρΩ, hρΩ, hρΩs⟩ := Metric.isOpen_iff.1 hΩo _ hxΩ
  have hKΩ : closedBall ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) (ρΩ / 2) ⊆ Ω :=
    (closedBall_subset_ball (by linarith)).trans hρΩs
  have hcs : ContinuousOn (fun q => ∑ k ∈ Finset.range N, |u (k + 1) q|) Ω :=
    continuousOn_finsetSum _ fun k _ => (hus (k + 1)).continuousOn.abs
  obtain ⟨M, hM⟩ := (isCompact_closedBall ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) (ρΩ / 2)).exists_bound_of_continuousOn
    (hcs.mono hKΩ)
  -- the uniform lower bound of the metric
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.isOpen_iff.1 hg.coord.isOpen x hx
  have hKU : closedBall x (ε₀ / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hε₀U
  obtain ⟨l, rw, hl, hrw, hlow⟩ := Upstream.GeodesicExpansion.IsRiemMetric.normSq_lower
    (U := ⟨U, hg.coord.isOpen⟩) hg (isCompact_closedBall x (ε₀ / 2)) hKU
  -- the radii
  set R := min (min rT ρL) (min (ρΩ / 2) (ε₀ / 2)) with hR
  have hR0 : 0 < R := lt_min (lt_min hrT hρL) (lt_min (by linarith) (by linarith))
  have hRT : R ≤ rT := (min_le_left _ _).trans (min_le_left _ _)
  have hRL : R ≤ ρL := (min_le_left _ _).trans (min_le_right _ _)
  have hRΩ : R ≤ ρΩ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hRε : R ≤ ε₀ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set rb := min (R / 2) r with hrb
  have hrb0 : 0 < rb := lt_min (by linarith) hr
  have hrbr : rb ≤ r := min_le_right _ _
  have hrbR : rb ≤ R / 2 := min_le_left _ _
  set c' := min c l with hc'
  have hc'0 : 0 < c' := lt_min hc hl
  set C₂ := (KL : ℝ) + |M| with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set K := ((1 + C₂ * (rb + 1)) * C₁ * 2 * √(4 / c') ^ 3 + C₂ * (√(4 / c') + 1) + 64 / (rb ^ 2 * c')) +
    (|A| + 1) * (32 / (rb ^ 2 * c')) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the metric lower bound for all vectors
  have hlowall : ∀ p, ‖p - x‖ < rb → ∀ w, l * ‖w‖ ^ 2 ≤ w ⬝ᵥ (g p *ᵥ w) := fun p hp =>
    quad_lower_of_ball hrw (hlow p (by rw [mem_closedBall, dist_eq_norm]; linarith))
  have hpU : ∀ p, ‖p - x‖ < rb → p ∈ U := fun p hp =>
    hΩU (p, p) (hmem p p (lt_of_lt_of_le hp hrbr) (by simpa using hr))
  -- the pointwise comparison
  have hcmp : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p ∈ {p : Fin n → ℝ | ‖p - x‖ < rb}, ∀ y, |H t p y -
      (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t))| ≤
      (4 * π * t) ^ (-(n : ℝ) / 2) * (K * √t * Real.exp (-(c' * ‖y - p‖ ^ 2 / (4 * t)) / 2)) := by
    intro t ht p hp y
    have hp : ‖p - x‖ < rb := hp
    have hpr : ‖p - x‖ < r := lt_of_lt_of_le hp hrbr
    have ht0 : 0 < t := ht.1
    have hyx : ‖y - p‖ < rb → ‖y - x‖ < R := fun hz => by
      have := norm_sub_le_norm_sub_add_norm_sub y p x
      linarith
    have hσ : ‖y - p‖ < r → c' * ‖y - p‖ ^ 2 ≤ σ (p, y) := fun hz =>
      le_trans (by gcongr; exact min_le_left _ _) (hσlow p y hpr hz)
    have hq : c' * ‖y - p‖ ^ 2 ≤ (y - p) ⬝ᵥ (g p *ᵥ (y - p)) :=
      le_trans (by gcongr; exact min_le_right _ _) (hlowall p hp (y - p))
    have hσq : ‖y - p‖ < rb → |σ (p, y) - (y - p) ⬝ᵥ (g p *ᵥ (y - p))| ≤ C₁ * ‖y - p‖ ^ 3 := fun hz => by
      rw [hσV (p, y) (hmem p y hpr (lt_of_lt_of_le hz hrbr)), ← Geodesic.pairing_eq_dotProduct]
      exact hT p y (by linarith) (by linarith [hyx hz])
    have hU : ‖y - p‖ < rb → |truncAnsatz (fun k y => u k (p, y)) N t y - 1| ≤ C₂ * (‖y - p‖ + t) := by
      intro hz
      have hyR := hyx hz
      have hpyB : (p, y) ∈ ball ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) R := by
        rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]; exact max_lt (by linarith) hyR
      have hppB : (p, p) ∈ ball ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) R := by
        rw [mem_ball, Prod.dist_eq, dist_eq_norm, max_self]; linarith
      have h1 : |u 0 (p, y) - 1| ≤ KL * ‖y - p‖ := by
        rw [← hu0 p hpr, ← Real.dist_eq]
        have := hlip.dist_le_mul (p, y) (hρLt (ball_subset_ball hRL hpyB)) (p, p)
          (hρLt (ball_subset_ball hRL hppB))
        refine this.trans (le_of_eq ?_)
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        exact congrArg _ (dist_eq_norm y p)
      have h2 : |∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)| ≤ t * |M| := by
        have hb := hM (p, y) (ball_subset_closedBall (ball_subset_ball hRΩ hpyB))
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at hb
        calc |∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)|
            ≤ ∑ k ∈ Finset.range N, |t ^ (k + 1) * u (k + 1) (p, y)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range N, t * |u (k + 1) (p, y)| := by
              refine Finset.sum_le_sum fun k _ => ?_
              rw [abs_mul, abs_of_nonneg (pow_nonneg ht0.le _)]
              exact mul_le_mul_of_nonneg_right (pow_le_of_le_one ht0.le ht.2 (Nat.succ_ne_zero k))
                (abs_nonneg _)
          _ = t * ∑ k ∈ Finset.range N, |u (k + 1) (p, y)| := by rw [Finset.mul_sum]
          _ ≤ t * |M| := mul_le_mul_of_nonneg_left (hb.trans (le_abs_self _)) ht0.le
      have hsplit : truncAnsatz (fun k y => u k (p, y)) N t y - 1 =
          (∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)) + (u 0 (p, y) - 1) := by
        rw [truncAnsatz, Finset.sum_range_succ', pow_zero, one_mul]; ring
      rw [hsplit]
      calc _ ≤ |∑ k ∈ Finset.range N, t ^ (k + 1) * u (k + 1) (p, y)| + |u 0 (p, y) - 1| := abs_add_le _ _
        _ ≤ t * |M| + KL * ‖y - p‖ := add_le_add h2 h1
        _ ≤ C₂ * (‖y - p‖ + t) := by
            rw [hC₂]
            nlinarith [norm_nonneg (y - p), abs_nonneg M, KL.2, ht0.le]
    have hUA : ‖y - p‖ < r → |truncAnsatz (fun k y => u k (p, y)) N t y| ≤ |A| := fun hz =>
      (hA t ht p y hpr hz).trans (le_abs_self _)
    have hpt := cutoffGauss_sub_frozen_le₂ ht0 ht.2 hc'0 hrb0 hrbr hC₁ hC₂0 (abs_nonneg A) (hθr (y - p))
      (hθ1 (y - p)) (hθ0 (y - p)) hσ hq hσq hU hUA
    have hG0 : 0 < (4 * π * t) ^ (-(n : ℝ) / 2) := by positivity
    have heq : H t p y - (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t)) =
        (4 * π * t) ^ (-(n : ℝ) / 2) * (θ (y - p) * Real.exp (-σ (p, y) / (4 * t)) *
          truncAnsatz (fun k y => u k (p, y)) N t y - Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t))) := by
      rw [hH, heatGaussian, gaussFactor]; ring
    rw [heq, abs_mul, abs_of_pos hG0]
    exact mul_le_mul_of_nonneg_left hpt hG0.le
  exact ⟨rb, K, c', l, hrb0, hrbr, hK0, hc'0, hl, fun p hp => hpU p hp, hlowall, fun t ht p hp y => hcmp t ht p hp y⟩

/-- **The quadratic form of a coordinate metric is Lipschitz in the point**:
`|w·g(p)w − w·g(y)w| ≤ L‖p − y‖‖w‖²` for `p, y` near `x`. -/
theorem IsCoordMetric.exists_quad_lipschitz (hg : IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ ρ L : ℝ, 0 < ρ ∧ 0 ≤ L ∧ ∀ p y : Fin n → ℝ, ‖p - x‖ < ρ → ‖y - x‖ < ρ → ∀ w : Fin n → ℝ,
      |w ⬝ᵥ (g p *ᵥ w) - w ⬝ᵥ (g y *ᵥ w)| ≤ L * ‖p - y‖ * ‖w‖ ^ 2 := by
  have hlip : ∀ ij : Fin n × Fin n, ∃ K : NNReal, ∃ s ∈ 𝓝 x, LipschitzOnWith K (fun y => g y ij.1 ij.2) s :=
    fun ij => (((hg.smooth ij.1 ij.2).contDiffAt (hg.isOpen.mem_nhds hx)).of_le
      (by exact_mod_cast le_top) : ContDiffAt ℝ 1 (fun y => g y ij.1 ij.2) x).exists_lipschitzOnWith
  choose K s hs hK using hlip
  have hmem : (⋂ ij, s ij) ∈ 𝓝 x := Filter.iInter_mem.2 hs
  obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨ρ, ∑ ij, (K ij : ℝ), hρ, Finset.sum_nonneg fun _ _ => (K _).2, fun p y hp hy w => ?_⟩
  have hpS : ∀ ij, p ∈ s ij := fun ij => mem_iInter.1 (hρs (by rw [mem_ball, dist_eq_norm]; exact hp)) ij
  have hyS : ∀ ij, y ∈ s ij := fun ij => mem_iInter.1 (hρs (by rw [mem_ball, dist_eq_norm]; exact hy)) ij
  have hentry : ∀ i j, |g p i j - g y i j| ≤ K (i, j) * ‖p - y‖ := fun i j => by
    have := (hK (i, j)).dist_le_mul p (hpS (i, j)) y (hyS (i, j))
    rwa [Real.dist_eq, dist_eq_norm] at this
  have heq : w ⬝ᵥ (g p *ᵥ w) - w ⬝ᵥ (g y *ᵥ w) = ∑ i, ∑ j, w i * ((g p i j - g y i j) * w j) := by
    simp only [dotProduct, Matrix.mulVec, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  have hw : ∀ i, |w i| ≤ ‖w‖ := fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w i
  calc |∑ i, ∑ j, w i * ((g p i j - g y i j) * w j)|
      ≤ ∑ i, ∑ j, |w i * ((g p i j - g y i j) * w j)| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ‖w‖ * ((K (i, j) * ‖p - y‖) * ‖w‖) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_mul]
        gcongr
        · exact hw i
        · exact hentry i j
        · exact hw j
    _ = (∑ ij, (K ij : ℝ)) * ‖p - y‖ * ‖w‖ ^ 2 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
        simp only [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The world function of the chart parametrix is smooth near the diagonal. -/
theorem IsChartParametrix.σ_contDiffOn {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : IsCoordMetric g U) :
    ContDiffOn ℝ ∞ σ {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r ∧ ‖q.2 - q.1‖ < r} := by
  have hWΩ : ∀ q ∈ {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r ∧ ‖q.2 - q.1‖ < r}, q ∈ Ω :=
    fun q hq => h.mem_of_lt q.1 q.2 hq.1 hq.2
  have hW1U : ∀ q ∈ {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r ∧ ‖q.2 - q.1‖ < r}, q.1 ∈ U :=
    fun q hq => h.snd_mem (q.1, q.1) (h.mem_of_lt q.1 q.1 hq.1 (by simpa using h.r_pos))
  refine ContDiffOn.congr ?_ fun q hq => h.σ_eq q (hWΩ q hq)
  unfold Geodesic.pairing
  have hV := contDiffOn_pi.1 (h.V_smooth.mono hWΩ)
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (hV i).mul (((hg.smooth i j).comp contDiffOn_fst fun q hq => hW1U q hq).mul (hV j))

/-- **The chart parametrix is continuous in the base point** on the ball of radius `r`. -/
theorem IsChartParametrix.continuousAt_base {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : IsCoordMetric g U) (t : ℝ) (y : Fin n → ℝ) {p : Fin n → ℝ} (hp : ‖p - x‖ < r) :
    ContinuousAt (fun p => H t p y) p := by
  by_cases hsupp : y - p ∈ tsupport θ
  · have hyp : ‖y - p‖ < r := by
      have := h.θ_tsupport hsupp; rwa [mem_ball, dist_zero_right] at this
    set W := {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r ∧ ‖q.2 - q.1‖ < r} with hWdef
    have hWo : IsOpen W := (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_snd.sub continuous_fst).norm continuous_const)
    have hqW : (p, y) ∈ W := ⟨hp, hyp⟩
    have hpy : ContinuousAt (fun p' : Fin n → ℝ => (p', y)) p := continuousAt_id.prodMk continuousAt_const
    have hσc : ContinuousAt (fun p' => σ (p', y)) p :=
      ContinuousAt.comp (f := fun p' => (p', y)) ((h.σ_contDiffOn hg).continuousOn.continuousAt
        (hWo.mem_nhds hqW)) hpy
    have huc : ∀ k, ContinuousAt (fun p' => u k (p', y)) p := fun k =>
      ContinuousAt.comp (f := fun p' => (p', y)) ((h.u_smooth k).continuousOn.continuousAt
        (h.isOpen.mem_nhds (h.mem_of_lt p y hp hyp))) hpy
    have hθc : ContinuousAt (fun p' => θ (y - p')) p :=
      (h.θ_smooth.continuous.comp (continuous_const.sub continuous_id)).continuousAt
    have hfun : (fun p' => H t p' y) = fun p' => θ (y - p') * ((4 * π * t) ^ (-(n : ℝ) / 2) *
        Real.exp (-σ (p', y) / (4 * t)) * ∑ k ∈ Finset.range (N + 1), t ^ k * u k (p', y)) := by
      funext p'; rw [h.H_eq]; rfl
    rw [hfun]
    exact hθc.mul ((continuousAt_const.mul (Real.continuous_exp.continuousAt.comp (hσc.neg.div_const _))).mul
      (tendsto_finsetSum _ fun k _ => continuousAt_const.mul (huc k)))
  · have h0 : ∀ᶠ w in 𝓝 (y - p), θ w = 0 := notMem_tsupport_iff_eventuallyEq.mp hsupp
    have h1 : ∀ᶠ p' in 𝓝 p, H t p' y = 0 :=
      (((continuous_const.sub continuous_id).continuousAt (x := p)).eventually h0).mono fun p' hp' => by
        rw [h.H_eq, show θ (y - p') = 0 from hp', zero_mul]
    exact continuousAt_const.congr (h1.mono fun z hz => hz.symm)

/-- **The delta property of the chart parametrix in the base point**: for continuous `F` vanishing outside the ball of
radius `ρ` around the centre, `∫ H(t, p, y) F(p) dp → F(y)/√det g(y)` as `t → 0⁺`, uniformly for `‖y − x‖ < ρ`. -/
theorem IsChartParametrix.base_delta {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ F : (Fin n → ℝ) → ℝ, Continuous F → (∀ p, ρ ≤ ‖p - x‖ → F p = 0) →
      ∀ ε > 0, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀, ∀ y, ‖y - x‖ < ρ →
        |(∫ p, H t p y * F p) - F y / √(g y).det| ≤ ε := by
  have hgc : IsCoordMetric g U := hg.coord.toLightlike
  have hx : x ∈ U := h.snd_mem _ h.center_mem
  obtain ⟨rb, K, c', l, hrb, hrbr, hK0, hc', hl, hpU, hlow, hcmp⟩ := h.exists_frozen_cmp hg
  obtain ⟨ρg, L, hρg, hL0, hLip⟩ := hgc.exists_quad_lipschitz hx
  set R := min rb ρg with hR
  have hR0 : 0 < R := lt_min hrb hρg
  have hRrb : R ≤ rb := min_le_left _ _
  have hRg : R ≤ ρg := min_le_right _ _
  set ρ := R / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  -- a cutoff: `1` on the closed ball of radius `ρ`, supported in the ball of radius `R`
  obtain ⟨χ, hχ, hχs, W, hWo, hKW, hχ1, hχr⟩ := exists_cutoff_of_isOpen (isOpen_ball (x := x) (ε := R))
    (isCompact_closedBall x ρ) (closedBall_subset_ball (by linarith))
  refine ⟨ρ, hρ0, by linarith, fun F hFc hF0 => ?_⟩
  have hχ1' : ∀ p, ‖p - x‖ ≤ ρ → χ p = 1 := fun p hp =>
    hχ1 p (hKW (by rw [mem_closedBall, dist_eq_norm]; exact hp))
  have hχsupp : ∀ p ∈ tsupport χ, ‖p - x‖ < R := fun p hp => by
    have := hχs hp; rwa [mem_ball, dist_eq_norm] at this
  -- `F` is bounded and uniformly continuous
  have hFcs : HasCompactSupport F := HasCompactSupport.intro (isCompact_closedBall x ρ) fun p hp => hF0 p (by
    rw [mem_closedBall, dist_eq_norm, not_le] at hp; exact hp.le)
  obtain ⟨B, hB⟩ := hFc.bounded_above_of_compact_support hFcs
  have hFu : UniformContinuous F := hFcs.uniformContinuous_of_continuous hFc
  -- the comparison family
  set c'' := min c' l with hc''
  have hc''0 : 0 < c'' := lt_min hc' hl
  set K' := K + (L * 2 * √(4 / l) ^ 3 + 64 / (1 ^ 2 * l)) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  set Hf : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun t y p => χ p * H t p y +
    (1 - χ p) * ((4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((p - y) ⬝ᵥ (g y *ᵥ (p - y))) / (4 * t))) with hHf
  have hS : ∀ y ∈ {y : Fin n → ℝ | ‖y - x‖ < ρ}, ‖y - x‖ < rb := fun y hy => by
    have : ‖y - x‖ < ρ := hy; linarith
  have hcmp' : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y ∈ {y : Fin n → ℝ | ‖y - x‖ < ρ}, ∀ p, |Hf t y p -
      (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((p - y) ⬝ᵥ (g y *ᵥ (p - y))) / (4 * t))| ≤
      (4 * π * t) ^ (-(n : ℝ) / 2) * (K' * √t * Real.exp (-(c'' * ‖p - y‖ ^ 2 / (4 * t)) / 2)) := by
    intro t ht y hy p
    have hy' : ‖y - x‖ < ρ := hy
    have ht0 : 0 < t := ht.1
    have hG0 : 0 < (4 * π * t) ^ (-(n : ℝ) / 2) := by positivity
    set ky := (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((p - y) ⬝ᵥ (g y *ᵥ (p - y))) / (4 * t)) with hky
    have heq : Hf t y p - ky = χ p * (H t p y - ky) := by simp only [hHf, hky]; ring
    rw [heq, abs_mul]
    have hRHS0 : 0 ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * (K' * √t * Real.exp (-(c'' * ‖p - y‖ ^ 2 / (4 * t)) / 2)) := by
      positivity
    by_cases hpR : ‖p - x‖ < R
    · have hχb : |χ p| ≤ 1 := by rw [abs_of_nonneg (hχr p).1]; exact (hχr p).2
      set kp := (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((y - p) ⬝ᵥ (g p *ᵥ (y - p))) / (4 * t)) with hkp
      have h1 := hcmp t ht p (lt_of_lt_of_le hpR hRrb) y
      -- the two frozen Gaussians
      have hba : (p - y) ⬝ᵥ (g y *ᵥ (p - y)) = (y - p) ⬝ᵥ (g y *ᵥ (y - p)) := by
        rw [show p - y = -(y - p) by abel, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
      have hnorm : ‖p - y‖ = ‖y - p‖ := norm_sub_rev p y
      have h2 := gauss_sub_gauss_le (n := n) (z := y - p) ht0 ht.2 hl one_pos hL0
        (a := (y - p) ⬝ᵥ (g p *ᵥ (y - p))) (b := (p - y) ⬝ᵥ (g y *ᵥ (p - y)))
        (hlow p (lt_of_lt_of_le hpR hRrb) (y - p))
        (by rw [hba]; exact hlow y (hS y hy) (y - p))
        (fun _ => by
          rw [hba]
          have := hLip p y (lt_of_lt_of_le hpR hRg) (by linarith) (y - p)
          calc _ ≤ L * ‖p - y‖ * ‖y - p‖ ^ 2 := this
            _ = L * ‖y - p‖ ^ 3 := by rw [hnorm]; ring)
      have hkk : |kp - ky| ≤ (4 * π * t) ^ (-(n : ℝ) / 2) * ((L * 2 * √(4 / l) ^ 3 + 64 / (1 ^ 2 * l)) * √t *
          Real.exp (-(l * ‖y - p‖ ^ 2 / (4 * t)) / 2)) := by
        rw [hkp, hky, ← mul_sub, abs_mul, abs_of_pos hG0]
        exact mul_le_mul_of_nonneg_left h2 hG0.le
      have he1 : Real.exp (-(c' * ‖y - p‖ ^ 2 / (4 * t)) / 2) ≤ Real.exp (-(c'' * ‖p - y‖ ^ 2 / (4 * t)) / 2) := by
        apply Real.exp_le_exp.2; rw [hnorm]
        have : c'' * ‖y - p‖ ^ 2 / (4 * t) ≤ c' * ‖y - p‖ ^ 2 / (4 * t) := by gcongr; exact min_le_left _ _
        linarith
      have he2 : Real.exp (-(l * ‖y - p‖ ^ 2 / (4 * t)) / 2) ≤ Real.exp (-(c'' * ‖p - y‖ ^ 2 / (4 * t)) / 2) := by
        apply Real.exp_le_exp.2; rw [hnorm]
        have : c'' * ‖y - p‖ ^ 2 / (4 * t) ≤ l * ‖y - p‖ ^ 2 / (4 * t) := by gcongr; exact min_le_right _ _
        linarith
      have hst := Real.sqrt_nonneg t
      have hc1 : 0 ≤ L * 2 * √(4 / l) ^ 3 + 64 / (1 ^ 2 * l) := by positivity
      calc |χ p| * |H t p y - ky| ≤ 1 * (|H t p y - kp| + |kp - ky|) :=
            mul_le_mul hχb (abs_sub_le _ _ _) (abs_nonneg _) zero_le_one
        _ ≤ 1 * ((4 * π * t) ^ (-(n : ℝ) / 2) * (K * √t * Real.exp (-(c'' * ‖p - y‖ ^ 2 / (4 * t)) / 2)) +
              (4 * π * t) ^ (-(n : ℝ) / 2) * ((L * 2 * √(4 / l) ^ 3 + 64 / (1 ^ 2 * l)) * √t *
                Real.exp (-(c'' * ‖p - y‖ ^ 2 / (4 * t)) / 2))) := by
            gcongr
            · exact h1.trans (by gcongr)
            · exact hkk.trans (by gcongr)
        _ = _ := by rw [hK']; ring
    · push Not at hpR
      have hχp : χ p = 0 := image_eq_zero_of_notMem_tsupport fun hs => by linarith [hχsupp p hs]
      rw [hχp, abs_zero, zero_mul]
      exact hRHS0
  have hcont : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y ∈ {y : Fin n → ℝ | ‖y - x‖ < ρ}, Continuous (Hf t y) := by
    intro t _ y _
    have hk : Continuous fun p : Fin n → ℝ =>
        (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-((p - y) ⬝ᵥ (g y *ᵥ (p - y))) / (4 * t)) :=
      continuous_const.mul (Real.continuous_exp.comp ((((continuous_id.sub continuous_const).dotProduct
        (continuous_const.matrix_mulVec (continuous_id.sub continuous_const))).neg).div_const _))
    have hχH : Continuous fun p => χ p * H t p y := by
      refine continuous_iff_continuousAt.2 fun p => ?_
      by_cases hs : p ∈ tsupport χ
      · exact hχ.continuous.continuousAt.mul
          (h.continuousAt_base hgc t y (lt_of_lt_of_le (hχsupp p hs) (hRrb.trans hrbr)))
      · have h0 : ∀ᶠ p' in 𝓝 p, χ p' = 0 := notMem_tsupport_iff_eventuallyEq.mp hs
        have h1 : ∀ᶠ p' in 𝓝 p, χ p' * H t p' y = 0 := h0.mono fun p' hp' => by rw [hp', zero_mul]
        exact continuousAt_const.congr (h1.mono fun z hz => hz.symm)
    exact hχH.add ((continuous_const.sub hχ.continuous).mul hk)
  have hd := delta_of_pointwise (S := {y : Fin n → ℝ | ‖y - x‖ < ρ}) (G := g) (Hf := Hf)
    (fun y hy => hg.posDef y (hpU y (hS y hy))) hl (fun y hy => hlow y (hS y hy)) hK'0 hc''0 hcmp' hcont
    (fun p => by simpa [Real.norm_eq_abs] using hB p) hFu
  intro ε hε
  obtain ⟨t₀, ht₀, ht⟩ := hd ε hε
  refine ⟨t₀, ht₀, fun t htt y hy => ?_⟩
  have hint : (∫ p, H t p y * F p) = ∫ p, Hf t y p * F p := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    by_cases hFp : F p = 0
    · simp [hFp]
    · have hpρ : ‖p - x‖ ≤ ρ := by
        by_contra hc; exact hFp (hF0 p (le_of_lt (not_le.1 hc)))
      simp only [hHf, hχ1' p hpρ, one_mul, sub_self, zero_mul, add_zero]
  rw [hint]
  exact ht t htt y hy

end Lightlike
