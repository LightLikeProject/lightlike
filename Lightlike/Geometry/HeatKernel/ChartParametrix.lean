import Mathlib
import Lightlike.Geometry.HeatKernel.CutoffAnsatz
import Lightlike.Geometry.HeatKernel.HeatCoeffs
import Lightlike.Geometry.HeatKernel.WorldFunctionBounds
import Lightlike.Asymptotics.ExpDecay
import Lightlike.Asymptotics.GaussianIntegralPi

/-!
# The parametrix in a chart

`exists_chart_parametrix`: for a Riemannian coordinate metric, near any point `x` and for every order `N`, the cut-off
parametrix `H(t, p, y) = θ(y − p) (4πt)^{-n/2} e^{-σ(p, y)/4t} Σ_{k≤N} tᵏ u_k(p, y)` (coefficients of
`Lightlike.exists_heatCoeffs`, `θ = 1` for `|y − p| < r/2`, `θ = 0` for `|y − p| ≥ r`) has the diagonal
`(4πt)^{-n/2} Σ tᵏ u_k(p, p)` with `u₀(p, p) = 1`, the Gaussian bound
`|H| ≤ C t^{-n/2} e^{-a|y − p|²/t}` and hence `∫ |H(t, p, y)| dy ≤ C` (`integral_exp_neg_mul_sum_sq_sub`), and heat error `|(∂ₜ + Δ_y) H| ≤ C t^{N − n/2}` uniformly for
`t ∈ (0, 1]`, `|p − x| < r` and all `y`. Near the diagonal only `t^N Δu_N` remains (`heatOperator_cutoff_ansatz`);
on `r/2 ≤ |y − p| < r` the Gaussian lower bound `σ ≥ c|y − p|²` (`exists_pairing_lower`) and
`exists_exp_neg_div_le_rpow` make the cutoff terms `O(t^∞)`; beyond, `H` vanishes. The real-number estimates are
`chart_near_bound`, `chart_far_bound`.

Helpers:

* `Upstream.GeodesicExpansion.IsCoordMetric.toLightlike`: the coordinate-metric predicate of the Upstream geodesic
  expansion layer gives the library's `Lightlike.IsCoordMetric` (the two have the same fields; a bridge, so that the
  Riemannian lower bounds of that layer apply to the heat-kernel coefficients).
* `IsCoordMetric.continuousOn_coordGradPair_param`: `(p, y) ↦ g⁻¹(dA(p, ·), dB(p, ·))(y)` is continuous for `A, B`
  smooth on an open set.
-/

open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Bridge**: the Upstream coordinate-metric predicate gives the library's one. -/
theorem _root_.Lightlike.Upstream.GeodesicExpansion.IsCoordMetric.toLightlike
    (hg : Upstream.GeodesicExpansion.IsCoordMetric g U) : IsCoordMetric g U :=
  ⟨hg.isOpen, hg.symm, hg.isUnit_det, hg.smooth⟩

/-- The pairing of the differentials in the second variable is jointly continuous. -/
theorem IsCoordMetric.continuousOn_coordGradPair_param (hg : IsCoordMetric g U)
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hΩ : IsOpen Ω) (hΩU : ∀ q ∈ Ω, q.2 ∈ U)
    {A B : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} (hA : ContDiffOn ℝ ∞ A Ω) (hB : ContDiffOn ℝ ∞ B Ω) :
    ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      coordGradPair g (fun y => A (q.1, y)) (fun y => B (q.1, y)) q.2) Ω := by
  have heq : ∀ q ∈ Ω, coordGradPair g (fun y => A (q.1, y)) (fun y => B (q.1, y)) q.2 =
      ∑ i, ∑ j, (g q.2)⁻¹ i j * pdY i A q * pdY j B q := by
    intro q hq
    unfold coordGradPair
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [pd_eq_pdY hΩ hA hq i, pd_eq_pdY hΩ hB hq j]
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  exact (((hg.contDiffOn_inv i j).continuousOn.comp continuousOn_snd fun q hq => hΩU q hq).mul
    (contDiffOn_pdY hΩ hA i).continuousOn).mul (contDiffOn_pdY hΩ hB j).continuousOn

/-- `Δ(c f) = c Δf`. -/
theorem IsCoordMetric.coordLaplacian_const_mul (hg : IsCoordMetric g U) (c : ℝ) {F : (Fin n → ℝ) → ℝ}
    (hF : ContDiffOn ℝ ∞ F U) {y : Fin n → ℝ} (hy : y ∈ U) :
    coordLaplacian g (fun z => c * F z) y = c * coordLaplacian g F y := by
  have h := hg.coordLaplacian_sum_smul (Finset.univ : Finset Unit) (fun _ => c) (F := fun _ => F) (fun _ => hF) hy
  simpa using h

/-- `|Σ_{k≤N} tᵏ a_k| ≤ Σ_{k≤N} |a_k|` for `t ∈ [0, 1]`. -/
theorem abs_sum_pow_mul_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (N : ℕ) (a : ℕ → ℝ) :
    |∑ k ∈ Finset.range (N + 1), t ^ k * a k| ≤ ∑ k ∈ Finset.range (N + 1), |a k| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 k)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ht0 ht1)

/-- `(4πt)^{-n/2} = (4π)^{-n/2} t^{-n/2}`. -/
theorem fourPi_rpow_split {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2) = (4 * Real.pi) ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2) :=
  Real.mul_rpow (by positivity) ht.le


/-- The estimate near the diagonal, as a statement about real numbers. -/
theorem chart_near_bound {G e θv tN L A1 A6 : ℝ} (hG : 0 < G) (he0 : 0 ≤ e) (he1 : e ≤ 1) (htN : 0 ≤ tN)
    (b1 : |L| ≤ |A1|) (b6 : |θv| ≤ |A6|) :
    |θv * (G * e * (tN * L)) + 0| ≤ G * (|A6| * |A1|) * tN := by
  rw [add_zero, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hG, abs_of_nonneg he0, abs_of_nonneg htN]
  calc |θv| * (G * e * (tN * |L|)) ≤ |A6| * (G * 1 * (tN * |A1|)) := by gcongr
    _ = G * (|A6| * |A1|) * tN := by ring

/-- The estimate away from the diagonal, as a statement about real numbers. -/
theorem chart_far_bound {G e θv tN L Ut Lθ P Q t A1 A2 A3 A4 A5 A6 C1 : ℝ} (hG : 0 < G) (he0 : 0 ≤ e)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (htN0 : 0 ≤ tN) (htN1 : tN ≤ 1) (hC1 : 0 ≤ C1) (hedec : e ≤ C1 * (tN * t))
    (b1 : |L| ≤ |A1|) (b2 : |Ut| ≤ |A2|) (b3 : |Lθ| ≤ |A3|) (b4 : |P| ≤ |A4|) (b5 : |Q| ≤ |A5|)
    (b6 : |θv| ≤ |A6|) :
    |θv * (G * e * (tN * L)) + G * (e * Ut * Lθ - 2 * (e * (P - Ut * Q / (4 * t))))| ≤
      G * ((|A6| * |A1| + |A2| * |A3| + 2 * |A4| + |A2| * |A5|) * C1) * tN := by
  have hexpr : θv * (G * e * (tN * L)) + G * (e * Ut * Lθ - 2 * (e * (P - Ut * Q / (4 * t)))) =
      G * e * (θv * tN * L + Ut * Lθ - 2 * P + Ut * Q / (2 * t)) := by
    field_simp; ring
  rw [hexpr]
  set M := |A6| * |A1| + |A2| * |A3| + 2 * |A4| + |A2| * |A5| with hM
  have hbr : |θv * tN * L + Ut * Lθ - 2 * P + Ut * Q / (2 * t)| ≤ M / t := by
    have e1 : |θv * tN * L| ≤ |A6| * |A1| := by
      rw [abs_mul, abs_mul, abs_of_nonneg htN0]
      calc |θv| * tN * |L| ≤ |A6| * 1 * |A1| := by gcongr
        _ = |A6| * |A1| := by ring
    have e2 : |Ut * Lθ| ≤ |A2| * |A3| := by rw [abs_mul]; gcongr
    have e3 : |2 * P| ≤ 2 * |A4| := by rw [abs_mul, abs_two]; gcongr
    have e4 : |Ut * Q / (2 * t)| ≤ |A2| * |A5| / t := by
      rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      calc |Ut| * |Q| / (2 * t) ≤ |A2| * |A5| / (2 * t) := by gcongr
        _ ≤ |A2| * |A5| / t := div_le_div_of_nonneg_left (by positivity) ht0 (by linarith)
    have hsum : |θv * tN * L + Ut * Lθ - 2 * P + Ut * Q / (2 * t)| ≤
        |A6| * |A1| + |A2| * |A3| + 2 * |A4| + |A2| * |A5| / t := by
      have h1 := abs_add_le (θv * tN * L + Ut * Lθ - 2 * P) (Ut * Q / (2 * t))
      have h2 := abs_add_le (θv * tN * L + Ut * Lθ) (-(2 * P))
      rw [abs_neg, ← sub_eq_add_neg] at h2
      have h3 := abs_add_le (θv * tN * L) (Ut * Lθ)
      linarith
    have h0 : 0 ≤ |A6| * |A1| + |A2| * |A3| + 2 * |A4| := by positivity
    have hle : |A6| * |A1| + |A2| * |A3| + 2 * |A4| ≤ (|A6| * |A1| + |A2| * |A3| + 2 * |A4|) / t := by
      rw [le_div_iff₀ ht0]; nlinarith
    calc _ ≤ _ := hsum
      _ ≤ (|A6| * |A1| + |A2| * |A3| + 2 * |A4|) / t + |A2| * |A5| / t := by linarith
      _ = M / t := by rw [hM]; ring
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  calc |G * e * (θv * tN * L + Ut * Lθ - 2 * P + Ut * Q / (2 * t))|
      = G * e * |θv * tN * L + Ut * Lθ - 2 * P + Ut * Q / (2 * t)| := by
        rw [abs_mul, abs_mul, abs_of_pos hG, abs_of_nonneg he0]
    _ ≤ G * (C1 * (tN * t)) * (M / t) := by gcongr
    _ = G * (M * C1) * tN := by field_simp

/-- **The properties of the parametrix of order `N` in a chart**, near `x`. -/
structure IsChartParametrix (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (N : ℕ) (r : ℝ) (u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ)
    (H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ) (Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))) (θ : (Fin n → ℝ) → ℝ)
    (σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)) : Prop where
  r_pos : 0 < r
  u_zero_diag : ∀ p, ‖p - x‖ < r → u 0 (p, p) = 1
  diag_eq : ∀ t > 0, ∀ p, ‖p - x‖ < r →
    H t p p = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ∑ k ∈ Finset.range (N + 1), t ^ k * u k (p, p)
  gauss_le : ∃ C a : ℝ, 0 < a ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y,
    |H t p y| ≤ C * t ^ (-(n : ℝ) / 2) * Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t)
  integral_abs_le : ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∫ y, |H t p y| ≤ C
  isOpen : IsOpen Ω
  center_mem : (x, x) ∈ Ω
  mem_of_lt : ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → (p, y) ∈ Ω
  snd_mem : ∀ q ∈ Ω, q.2 ∈ U
  V_smooth : ContDiffOn ℝ ∞ V Ω
  u_smooth : ∀ k, ContDiffOn ℝ ∞ (u k) Ω
  V_diag : ∀ p, (p, p) ∈ Ω → V (p, p) = 0 ∧
    HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p
  σ_eq : ∀ q ∈ Ω, σ q = Geodesic.pairing g q.1 (V q) (V q)
  θ_one : ∀ z, ‖z‖ < r / 2 → θ z = 1
  θ_zero : ∀ z, r ≤ ‖z‖ → θ z = 0
  θ_mem : ∀ z, θ z ∈ Icc (0 : ℝ) 1
  θ_smooth : ContDiff ℝ ∞ θ
  θ_tsupport : tsupport θ ⊆ ball 0 r
  θ_eventually_one : ∀ z, ‖z‖ < r / 2 → θ =ᶠ[𝓝 z] fun _ => 1
  H_cont : ∀ t p, ‖p - x‖ < r → Continuous (H t p)
  heatError_eq : ∀ t > 0, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → ∃ D, HasDerivAt (fun s => H s p y) D t ∧
    D + coordLaplacian g (H t p) y =
      θ (y - p) * (heatGaussian n (σ (p, y)) t * (t ^ N * coordLaplacian g (fun z => u N (p, z)) y)) +
        (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (gaussFactor t (σ (p, y)) * truncAnsatz (fun k y => u k (p, y)) N t y *
          coordLaplacian g (fun z => θ (z - p)) y - 2 * (gaussFactor t (σ (p, y)) *
            ((∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y) -
              truncAnsatz (fun k y => u k (p, y)) N t y *
                coordGradPair g (fun z => θ (z - p)) (fun z => σ (p, z)) y / (4 * t))))
  σ_lower : ∃ c : ℝ, 0 < c ∧ ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → c * ‖y - p‖ ^ 2 ≤ σ (p, y)
  ansatz_le : ∃ A : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r →
    |truncAnsatz (fun k y => u k (p, y)) N t y| ≤ A
  H_eq : ∀ t p y, H t p y = θ (y - p) * (heatGaussian n (σ (p, y)) t * truncAnsatz (fun k y => u k (p, y)) N t y)
  heatError_le : ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y, ∃ D, HasDerivAt (fun s => H s p y) D t ∧
    |D + coordLaplacian g (H t p) y| ≤ C * t ^ ((N : ℝ) - n / 2)

set_option maxHeartbeats 1200000 in
/-- **The parametrix in a chart, at every order with the same coefficients**: near `x` there are `r > 0`, coefficients
`u_k(p, y)`, a domain `Ω`, a cutoff `θ`, the world function `σ = g_p(V, V)`, and for every order `N` a cut-off
parametrix `H` with all the properties of `Lightlike.IsChartParametrix`. Only `H` depends on `N`. -/
theorem exists_chart_parametrix_uniform {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ r u Ω θ σ V, ∀ N : ℕ, ∃ H, IsChartParametrix g U x N r u H Ω θ σ V := by
  have hg' : IsCoordMetric g U := hg.coord.toLightlike
  obtain ⟨Ω, σ, u, hΩo, hxΩ, hΩU, hσs, hus, heik, ⟨V, hVs, hVd, hσV⟩, hdiag, htr⟩ := exists_heatCoeffs hg' hx
  obtain ⟨r₀, c, hr₀, hc, hlow⟩ := exists_pairing_lower hg hΩo hVs hx hxΩ (fun p hp => (hVd p hp).1)
    (fun p hp => (hVd p hp).2)
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩo _ hxΩ
  set r := min r₀ ρ / 3 with hrdef
  have hr : 0 < r := by positivity
  have h3r : 3 * r = min r₀ ρ := by rw [hrdef]; ring
  have hr3 : 3 * r ≤ r₀ ∧ 3 * r ≤ ρ := ⟨h3r ▸ min_le_left r₀ ρ, h3r ▸ min_le_right r₀ ρ⟩
  -- the cutoff in `y − p`
  obtain ⟨θ, hθ, hθs, W₀, hW₀o, hKW₀, hθ1, hθr⟩ := exists_cutoff_of_isOpen (E := Fin n → ℝ)
    (isOpen_ball (x := (0 : Fin n → ℝ)) (ε := r)) (isCompact_closedBall (0 : Fin n → ℝ) (r / 2))
    (closedBall_subset_ball (by linarith : r / 2 < r))
  refine ⟨r, u, Ω, θ, σ, V, fun N => ?_⟩
  set H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun t p y =>
    θ (y - p) * (heatGaussian n (σ (p, y)) t * truncAnsatz (fun k y => u k (p, y)) N t y) with hHdef
  -- the compact set of the estimates
  set Kc := closedBall ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) (2 * r) with hKc
  have hKcΩ : Kc ⊆ Ω := (closedBall_subset_ball (by linarith [hr3.2])).trans hρΩ
  have hKcc : IsCompact Kc := isCompact_closedBall _ _
  have hmemK : ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → (p, y) ∈ Kc := by
    intro p y hp hy
    rw [hKc, mem_closedBall, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    refine max_le (by linarith) ?_
    have := norm_sub_le_norm_sub_add_norm_sub y p x
    linarith
  have hσnn : ∀ q ∈ Kc, c * ‖q.2 - q.1‖ ^ 2 ≤ σ q := by
    intro q hq
    have hq' := mem_closedBall.1 hq
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hq'
    have h1 : ‖q.1 - x‖ < r₀ := by linarith [le_max_left ‖q.1 - x‖ ‖q.2 - x‖]
    have h2 : ‖q.2 - x‖ < r₀ := by linarith [le_max_right ‖q.1 - x‖ ‖q.2 - x‖]
    rw [hσV q (hKcΩ hq)]
    exact hlow q.1 q.2 h1 h2
  -- continuous coefficients and their bounds on `Kc`
  have hθp : ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) => θ (q.2 - q.1)) :=
    hθ.comp (contDiff_snd.sub contDiff_fst)
  have hc1 := (hg'.contDiffOn_coordLaplacian_param hΩo hΩU (hus N)).continuousOn
  have hc2 : ContinuousOn (fun q => ∑ k ∈ Finset.range (N + 1), |u k q|) Ω :=
    continuousOn_finsetSum _ fun k _ => (hus k).continuousOn.abs
  have hc3 := (hg'.contDiffOn_coordLaplacian_param hΩo hΩU hθp.contDiffOn).continuousOn
  have hc4 : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) => ∑ k ∈ Finset.range (N + 1),
      |coordGradPair g (fun y => θ (y - q.1)) (fun y => u k (q.1, y)) q.2|) Ω :=
    continuousOn_finsetSum _ fun k _ =>
      (hg'.continuousOn_coordGradPair_param hΩo hΩU (A := fun q => θ (q.2 - q.1)) hθp.contDiffOn (hus k)).abs
  have hc5 := hg'.continuousOn_coordGradPair_param hΩo hΩU (A := fun q => θ (q.2 - q.1)) hθp.contDiffOn hσs
  obtain ⟨A1, hA1⟩ := hKcc.exists_bound_of_continuousOn (hc1.mono hKcΩ)
  obtain ⟨A2, hA2⟩ := hKcc.exists_bound_of_continuousOn (hc2.mono hKcΩ)
  obtain ⟨A3, hA3⟩ := hKcc.exists_bound_of_continuousOn (hc3.mono hKcΩ)
  obtain ⟨A4, hA4⟩ := hKcc.exists_bound_of_continuousOn (hc4.mono hKcΩ)
  obtain ⟨A5, hA5⟩ := hKcc.exists_bound_of_continuousOn (hc5.mono hKcΩ)
  obtain ⟨A6, hA6⟩ := hKcc.exists_bound_of_continuousOn (hθp.continuous.continuousOn (s := Kc))
  -- the Gaussian decay away from the diagonal
  set c' := c * (r / 2) ^ 2 / 4 with hc'
  have hc'pos : 0 < c' := by positivity
  obtain ⟨C1, hC1, hdec⟩ := exists_exp_neg_div_le_rpow hc'pos ((N : ℝ) + 1)
  set M := |A6| * |A1| + |A2| * |A3| + 2 * |A4| + |A2| * |A5| with hM
  set C := (4 * Real.pi) ^ (-(n : ℝ) / 2) * (|A6| * |A1| + M * C1) with hCdef
  -- the Gaussian bound with its exponential factor
  set a := c / (4 * ((n : ℝ) + 1)) with ha
  have hapos : 0 < a := by positivity
  set CG := (4 * Real.pi) ^ (-(n : ℝ) / 2) * (|A6| * |A2|) with hCG
  have hCG0 : 0 ≤ CG := by positivity
  have hGauss : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y,
      |H t p y| ≤ CG * t ^ (-(n : ℝ) / 2) * Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t) := by
    intro t ht p hp y
    have ht0 : 0 < t := ht.1
    have hexp0 : 0 < Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t) := Real.exp_pos _
    by_cases hyp : ‖y - p‖ < r
    · have hqK := hmemK p y hp hyp
      have hσq : c * ‖y - p‖ ^ 2 ≤ σ (p, y) := hσnn (p, y) hqK
      have hsum : ∑ i, (y i - p i) ^ 2 ≤ ((n : ℝ) + 1) * ‖y - p‖ ^ 2 := by
        have h1 : ∀ i, (y i - p i) ^ 2 ≤ ‖y - p‖ ^ 2 := fun i => by
          have := norm_le_pi_norm (y - p) i
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        calc ∑ i, (y i - p i) ^ 2 ≤ ∑ _i : Fin n, ‖y - p‖ ^ 2 := Finset.sum_le_sum fun i _ => h1 i
          _ = (n : ℝ) * ‖y - p‖ ^ 2 := by simp
          _ ≤ ((n : ℝ) + 1) * ‖y - p‖ ^ 2 := by nlinarith [sq_nonneg ‖y - p‖]
      have he : gaussFactor t (σ (p, y)) ≤ Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t) := by
        rw [gaussFactor]
        apply Real.exp_le_exp.2
        rw [div_le_div_iff₀ (by positivity) ht0]
        have h1 : a * ∑ i, (y i - p i) ^ 2 ≤ c * ‖y - p‖ ^ 2 / 4 := by
          rw [ha]
          calc c / (4 * ((n : ℝ) + 1)) * ∑ i, (y i - p i) ^ 2
              ≤ c / (4 * ((n : ℝ) + 1)) * (((n : ℝ) + 1) * ‖y - p‖ ^ 2) := by gcongr
            _ = c * ‖y - p‖ ^ 2 / 4 := by field_simp
        nlinarith
      have he0 : 0 ≤ gaussFactor t (σ (p, y)) := (Real.exp_pos _).le
      have b2 : |truncAnsatz (fun k y => u k (p, y)) N t y| ≤ |A2| := by
        have := hA2 _ hqK
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at this
        exact (abs_sum_pow_mul_le ht0.le ht.2 N _).trans (this.trans (le_abs_self _))
      have b6 : |θ (y - p)| ≤ |A6| := (hA6 _ hqK).trans (le_abs_self _)
      show |θ (y - p) * ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * gaussFactor t (σ (p, y)) *
        truncAnsatz (fun k y => u k (p, y)) N t y)| ≤ _
      rw [fourPi_rpow_split ht0 n, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (4 * Real.pi) ^ (-(n : ℝ) / 2)),
        abs_of_pos (Real.rpow_pos_of_pos ht0 _), abs_of_nonneg he0]
      calc |θ (y - p)| * ((4 * Real.pi) ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2) * gaussFactor t (σ (p, y)) *
            |truncAnsatz (fun k y => u k (p, y)) N t y|)
          ≤ |A6| * ((4 * Real.pi) ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2) *
              Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t) * |A2|) := by
            gcongr
        _ = CG * t ^ (-(n : ℝ) / 2) * Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t) := by rw [hCG]; ring
    · have hθ0 : θ (y - p) = 0 := by
        by_contra hne
        exact hyp (by
          have := hθs (subset_tsupport θ hne)
          rwa [mem_ball, dist_zero_right] at this)
      show |θ (y - p) * _| ≤ _
      rw [hθ0, zero_mul, abs_zero]
      positivity
  -- continuity of `H(t, p, ·)`: the cutoff vanishes near every point outside the slice of `Ω`
  have hHc : ∀ t p, ‖p - x‖ < r → Continuous (H t p) := by
    intro t p hp
    refine continuous_iff_continuousAt.2 fun y => ?_
    by_cases hsupp : y - p ∈ tsupport θ
    · have hyp : ‖y - p‖ < r := by
        have := hθs hsupp; rwa [mem_ball, dist_zero_right] at this
      have hqΩ := hKcΩ (hmemK p y hp hyp)
      have hpy : ContinuousAt (fun z : Fin n → ℝ => (p, z)) y := continuousAt_const.prodMk continuousAt_id
      have hσc : ContinuousAt (fun z => σ (p, z)) y :=
        ContinuousAt.comp (f := fun z => (p, z)) (hσs.continuousOn.continuousAt (hΩo.mem_nhds hqΩ)) hpy
      have huc : ∀ k, ContinuousAt (fun z => u k (p, z)) y := fun k =>
        ContinuousAt.comp (f := fun z => (p, z)) ((hus k).continuousOn.continuousAt (hΩo.mem_nhds hqΩ)) hpy
      have hθc : ContinuousAt (fun z => θ (z - p)) y :=
        (hθ.continuous.comp (continuous_id.sub continuous_const)).continuousAt
      simp only [hHdef, heatGaussian, gaussFactor, truncAnsatz]
      exact hθc.mul ((continuousAt_const.mul (Real.continuous_exp.continuousAt.comp (hσc.neg.div_const _))).mul
        (tendsto_finsetSum _ fun k _ => continuousAt_const.mul (huc k)))
    · have h0 : ∀ᶠ w in 𝓝 (y - p), θ w = 0 := notMem_tsupport_iff_eventuallyEq.mp hsupp
      have h1 : ∀ᶠ z in 𝓝 y, H t p z = 0 :=
        (((continuous_id.sub continuous_const).continuousAt (x := y)).eventually h0).mono fun z hz => by
          show θ (z - p) * _ = 0
          rw [show θ (z - p) = 0 from hz, zero_mul]
      exact continuousAt_const.congr (h1.mono fun z hz => hz.symm)
  -- the heat error, expanded
  have hform : ∀ t > 0, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → ∃ D, HasDerivAt (fun s => H s p y) D t ∧
      D + coordLaplacian g (H t p) y =
        θ (y - p) * (heatGaussian n (σ (p, y)) t * (t ^ N * coordLaplacian g (fun z => u N (p, z)) y)) +
            (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (gaussFactor t (σ (p, y)) * truncAnsatz (fun k y => u k (p, y)) N t y *
              coordLaplacian g (fun z => θ (z - p)) y - 2 * (gaussFactor t (σ (p, y)) *
                ((∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y) -
                  truncAnsatz (fun k y => u k (p, y)) N t y *
                    coordGradPair g (fun z => θ (z - p)) (fun z => σ (p, z)) y / (4 * t)))) := by
    intro t ht0 p y hp hyp
    have hqΩ := hKcΩ (hmemK p y hp hyp)
    set U' := {z | (p, z) ∈ Ω} with hU'
    have hU'o : IsOpen U' := isOpen_slice hΩo p
    have hgU' : IsCoordMetric g U' := hg'.mono hU'o fun z hz => hΩU _ hz
    have hσp : ContDiffOn ℝ ∞ (fun z => σ (p, z)) U' :=
      hσs.comp (contDiffOn_const.prodMk contDiffOn_id) fun z hz => hz
    have hup : ∀ k, ContDiffOn ℝ ∞ (fun z => u k (p, z)) U' := fun k =>
      (hus k).comp (contDiffOn_const.prodMk contDiffOn_id) fun z hz => hz
    have heikp : ∀ z ∈ U', coordGradPair g (fun z => σ (p, z)) (fun z => σ (p, z)) z = 4 * σ (p, z) :=
      fun z hz => heik (p, z) hz
    have hθp' : ContDiff ℝ ∞ (fun z => θ (z - p)) := hθ.comp (contDiff_id.sub contDiff_const)
    obtain ⟨D, hD, hDeq⟩ := heatOperator_cutoff_ansatz hgU' hσp hup heikp (htr p N) hθp' ht0 hqΩ
    refine ⟨D, hD, ?_⟩
    have hΦ : ContDiffOn ℝ ∞ (fun z => θ (z - p) * (gaussFactor t (σ (p, z)) *
        truncAnsatz (fun k y => u k (p, y)) N t z)) U' :=
      hθp'.contDiffOn.mul (((contDiff_gaussFactor t).comp_contDiffOn hσp).mul
        (ContDiffOn.sum fun k _ => contDiffOn_const.mul (hup k)))
    have hHt : H t p = fun z => (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (θ (z - p) * (gaussFactor t (σ (p, z)) *
        truncAnsatz (fun k y => u k (p, y)) N t z)) := by
      funext z; simp only [hHdef, heatGaussian]; ring
    rw [hHt, hgU'.coordLaplacian_const_mul _ hΦ hqΩ, hDeq]
    have hσd : DifferentiableAt ℝ (fun z => σ (p, z)) y :=
      (hσp.contDiffAt (hU'o.mem_nhds hqΩ)).differentiableAt (by simp)
    have hUd : DifferentiableAt ℝ (fun z => truncAnsatz (fun k y => u k (p, y)) N t z) y :=
      ((ContDiffOn.sum fun k _ => contDiffOn_const.mul (hup k)).contDiffAt
        (hU'o.mem_nhds hqΩ)).differentiableAt (by simp)
    have hgpU : coordGradPair g (fun z => θ (z - p)) (fun z => truncAnsatz (fun k y => u k (p, y)) N t z) y =
        ∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y :=
      hgU'.coordGradPair_sum_smul_right _ (fun k => t ^ k) hup hqΩ
    rw [coordGradPair_gauss_mul hσd hUd t, hgpU]
  refine ⟨H, ⟨hr, fun p hp => (hdiag p ?_).2, fun t ht p hp => ?_,
    ⟨CG, a, hapos, hGauss⟩, ⟨CG * (Real.pi / a) ^ ((n : ℝ) / 2), fun t ht p hp => ?_⟩,
    hΩo, hxΩ, fun p y hp hy => hKcΩ (hmemK p y hp hy), hΩU, hVs, hus, hVd, hσV,
    fun z hz => hθ1 z (hKW₀ (by rw [mem_closedBall, dist_zero_right]; exact hz.le)),
    fun z hz => image_eq_zero_of_notMem_tsupport fun h => by
      have := hθs h; rw [mem_ball, dist_zero_right] at this; linarith,
    hθr, hθ, hθs, fun z hz => by
      have hev : ∀ᶠ w in 𝓝 z, ‖w‖ < r / 2 := (isOpen_lt continuous_norm continuous_const).mem_nhds hz
      filter_upwards [hev] with w hw using hθ1 w (hKW₀ (by rw [mem_closedBall, dist_zero_right]; exact hw.le)),
    hHc, hform, ⟨c, hc, fun p y hp hy => hσnn (p, y) (hmemK p y hp hy)⟩,
    ⟨|A2|, fun t ht p y hp hy => by
      have := hA2 _ (hmemK p y hp hy)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at this
      exact (abs_sum_pow_mul_le ht.1.le ht.2 N _).trans (this.trans (le_abs_self _))⟩,
    fun t p y => rfl, ⟨C, fun t ht p hp y => ?_⟩⟩⟩
  · exact hKcΩ (hmemK p p hp (by simpa using hr))
  · have hpp := hKcΩ (hmemK p p hp (by simpa using hr))
    simp only [hHdef, sub_self, hθ1 0 (hKW₀ (mem_closedBall_self (by linarith))), one_mul, heatGaussian,
      (hdiag p hpp).1, gaussFactor, neg_zero, zero_div, Real.exp_zero, mul_one, truncAnsatz]
  · -- the integral bound
    have ht0 : 0 < t := ht.1
    have hb : 0 < a / t := div_pos hapos ht0
    have hint := (integrable_exp_neg_mul_sum_sq_sub n hb p).const_mul (CG * t ^ (-(n : ℝ) / 2))
    calc ∫ y, |H t p y| ≤ ∫ y : Fin n → ℝ, CG * t ^ (-(n : ℝ) / 2) * Real.exp (-(a / t) * ∑ i, (y i - p i) ^ 2) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hint
            (Eventually.of_forall fun y => ?_)
          have h := hGauss t ht p hp y
          have he : -a * (∑ i, (y i - p i) ^ 2) / t = -(a / t) * ∑ i, (y i - p i) ^ 2 := by ring
          rwa [he] at h
      _ = CG * t ^ (-(n : ℝ) / 2) * (Real.pi / (a / t)) ^ ((n : ℝ) / 2) := by
          rw [integral_const_mul, integral_exp_neg_mul_sum_sq_sub n hb p]
      _ = CG * (Real.pi / a) ^ ((n : ℝ) / 2) := by
          rw [show Real.pi / (a / t) = Real.pi / a * t by field_simp, Real.mul_rpow (by positivity) ht0.le,
            show -(n : ℝ) / 2 = -((n : ℝ) / 2) by ring, Real.rpow_neg ht0.le]
          field_simp
  · have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hCnn : 0 ≤ C := by rw [hCdef]; positivity
    have hpow_nn : 0 ≤ t ^ ((N : ℝ) - n / 2) := (Real.rpow_pos_of_pos ht0 _).le
    by_cases hsupp : y - p ∈ tsupport θ
    · -- near the diagonal: the cut-off ansatz on the slice
      have hyp : ‖y - p‖ < r := by
        have := hθs hsupp; rwa [mem_ball, dist_zero_right] at this
      have hqK := hmemK p y hp hyp
      have hqΩ := hKcΩ hqK
      set U' := {z | (p, z) ∈ Ω} with hU'
      have hU'o : IsOpen U' := isOpen_slice hΩo p
      have hgU' : IsCoordMetric g U' := hg'.mono hU'o fun z hz => hΩU _ hz
      have hσp : ContDiffOn ℝ ∞ (fun z => σ (p, z)) U' :=
        hσs.comp (contDiffOn_const.prodMk contDiffOn_id) fun z hz => hz
      have hup : ∀ k, ContDiffOn ℝ ∞ (fun z => u k (p, z)) U' := fun k =>
        (hus k).comp (contDiffOn_const.prodMk contDiffOn_id) fun z hz => hz
      have heikp : ∀ z ∈ U', coordGradPair g (fun z => σ (p, z)) (fun z => σ (p, z)) z = 4 * σ (p, z) :=
        fun z hz => heik (p, z) hz
      have hθp' : ContDiff ℝ ∞ (fun z => θ (z - p)) := hθ.comp (contDiff_id.sub contDiff_const)
      obtain ⟨D, hD, hDeq⟩ := heatOperator_cutoff_ansatz hgU' hσp hup heikp (htr p N) hθp' ht0 hqΩ
      refine ⟨D, hD, ?_⟩
      -- the Laplacian of `H t p` is `(4πt)^{-n/2}` times that of the cut-off ansatz
      have hΦ : ContDiffOn ℝ ∞ (fun z => θ (z - p) * (gaussFactor t (σ (p, z)) *
          truncAnsatz (fun k y => u k (p, y)) N t z)) U' :=
        hθp'.contDiffOn.mul (((contDiff_gaussFactor t).comp_contDiffOn hσp).mul
          (ContDiffOn.sum fun k _ => contDiffOn_const.mul (hup k)))
      have hHt : H t p = fun z => (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (θ (z - p) * (gaussFactor t (σ (p, z)) *
          truncAnsatz (fun k y => u k (p, y)) N t z)) := by
        funext z; simp only [hHdef, heatGaussian]; ring
      rw [hHt, hgU'.coordLaplacian_const_mul _ hΦ hqΩ, hDeq]
      -- expand the cross term
      have hσd : DifferentiableAt ℝ (fun z => σ (p, z)) y :=
        (hσp.contDiffAt (hU'o.mem_nhds hqΩ)).differentiableAt (by simp)
      have hUd : DifferentiableAt ℝ (fun z => truncAnsatz (fun k y => u k (p, y)) N t z) y :=
        ((ContDiffOn.sum fun k _ => contDiffOn_const.mul (hup k)).contDiffAt
          (hU'o.mem_nhds hqΩ)).differentiableAt (by simp)
      rw [coordGradPair_gauss_mul hσd hUd t]
      have hgpU : coordGradPair g (fun z => θ (z - p)) (fun z => truncAnsatz (fun k y => u k (p, y)) N t z) y =
          ∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y :=
        hgU'.coordGradPair_sum_smul_right _ (fun k => t ^ k) hup hqΩ
      rw [hgpU]
      set e := gaussFactor t (σ (p, y)) with he
      set Ut := truncAnsatz (fun k y => u k (p, y)) N t y with hUt
      set G := (4 * Real.pi * t) ^ (-(n : ℝ) / 2) with hG
      have hGpos : 0 < G := by rw [hG]; positivity
      have he0 : 0 ≤ e := (Real.exp_pos _).le
      have hσq : c * ‖y - p‖ ^ 2 ≤ σ (p, y) := hσnn (p, y) hqK
      have he1 : e ≤ 1 := by
        rw [he, gaussFactor, Real.exp_le_one_iff]
        have : 0 ≤ σ (p, y) := le_trans (by positivity) hσq
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      -- the bounds of the coefficients at `(p, y)`
      have b1 : |coordLaplacian g (fun z => u N (p, z)) y| ≤ |A1| := (hA1 _ hqK).trans (le_abs_self _)
      have b2 : |Ut| ≤ |A2| := by
        have := hA2 _ hqK
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at this
        exact (abs_sum_pow_mul_le ht0.le ht1 N _).trans (this.trans (le_abs_self _))
      have b3 : |coordLaplacian g (fun z => θ (z - p)) y| ≤ |A3| := (hA3 _ hqK).trans (le_abs_self _)
      have b4 : |∑ k ∈ Finset.range (N + 1), t ^ k *
          coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y| ≤ |A4| := by
        have := hA4 _ hqK
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)] at this
        exact (abs_sum_pow_mul_le ht0.le ht1 N _).trans (this.trans (le_abs_self _))
      have b5 : |coordGradPair g (fun z => θ (z - p)) (fun z => σ (p, z)) y| ≤ |A5| :=
        (hA5 _ hqK).trans (le_abs_self _)
      have b6 : |θ (y - p)| ≤ |A6| := (hA6 _ hqK).trans (le_abs_self _)
      have hGsplit : G = (4 * Real.pi) ^ (-(n : ℝ) / 2) * t ^ (-(n : ℝ) / 2) := fourPi_rpow_split ht0 n
      have htpow : t ^ ((N : ℝ) - n / 2) = t ^ N * t ^ (-(n : ℝ) / 2) := by
        rw [sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_natCast, neg_div]
      have hfour : 0 < (4 * Real.pi) ^ (-(n : ℝ) / 2) := by positivity
      have htn : 0 < t ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos ht0 _
      by_cases hnear : ‖y - p‖ < r / 2
      · -- the cutoff is `1` near `y`: only the truncated error remains
        have h1 : (fun z => θ (z - p)) =ᶠ[𝓝 y] fun _ => 1 := by
          have hmem : y - p ∈ W₀ := hKW₀ (by rw [mem_closedBall, dist_zero_right]; exact hnear.le)
          have hev : ∀ᶠ z in 𝓝 y, z - p ∈ W₀ :=
            (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (hW₀o.mem_nhds hmem)
          filter_upwards [hev] with z hz using hθ1 _ hz
        obtain ⟨hz1, -⟩ := cutoff_terms_eq_zero_of_eventuallyEq_one (g := g)
          (Φ := fun z => truncAnsatz (fun k y => u k (p, y)) N t z) h1
        have hz2 : ∀ k, coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y = 0 := fun k =>
          (cutoff_terms_eq_zero_of_eventuallyEq_one (g := g) (Φ := fun z => u k (p, z)) h1).2
        have hz3 : coordGradPair g (fun z => θ (z - p)) (fun z => σ (p, z)) y = 0 :=
          (cutoff_terms_eq_zero_of_eventuallyEq_one (g := g) (Φ := fun z => σ (p, z)) h1).2
        rw [hz1, hz3]
        simp only [hz2, mul_zero, Finset.sum_const_zero, zero_div, sub_zero]
        rw [show heatGaussian n (σ (p, y)) t = G * e from rfl]
        have hnb := chart_near_bound (θv := θ (y - p)) hGpos he0 he1 (pow_nonneg ht0.le N) b1 b6
        calc _ ≤ G * (|A6| * |A1|) * t ^ N := hnb
          _ = (4 * Real.pi) ^ (-(n : ℝ) / 2) * (|A6| * |A1|) * t ^ ((N : ℝ) - n / 2) := by
              rw [hGsplit, htpow]; ring
          _ ≤ C * t ^ ((N : ℝ) - n / 2) := by
              gcongr
              rw [hCdef]
              have : 0 ≤ M * C1 := by rw [hM]; positivity
              nlinarith
      · -- away from the diagonal: the Gaussian factor is smaller than every power of `t`
        push Not at hnear
        have hsq : (r / 2) ^ 2 ≤ ‖y - p‖ ^ 2 := pow_le_pow_left₀ (by positivity) hnear 2
        have hσfar : 4 * c' ≤ σ (p, y) := by
          have h1 : 4 * c' = c * (r / 2) ^ 2 := by rw [hc']; ring
          rw [h1]
          exact (mul_le_mul_of_nonneg_left hsq hc.le).trans hσq
        have hexp : -σ (p, y) / (4 * t) ≤ -c' / t := by
          rw [div_le_div_iff₀ (by positivity) ht0]
          nlinarith
        have hedec : e ≤ C1 * (t ^ N * t) := by
          have h1 : e ≤ Real.exp (-c' / t) := by
            rw [he, gaussFactor]; exact Real.exp_le_exp.2 hexp
          have h2 := hdec t ht
          rw [Real.rpow_add ht0, Real.rpow_natCast, Real.rpow_one] at h2
          exact h1.trans h2
        rw [show heatGaussian n (σ (p, y)) t = G * e from rfl]
        have hfb := chart_far_bound (θv := θ (y - p)) hGpos he0 ht0 ht1 (pow_nonneg ht0.le N)
          (pow_le_one₀ ht0.le ht1) hC1 hedec b1 b2 b3 b4 b5 b6
        calc _ ≤ _ := hfb
          _ = (4 * Real.pi) ^ (-(n : ℝ) / 2) * (M * C1) * t ^ ((N : ℝ) - n / 2) := by
              rw [hGsplit, htpow, hM]; ring
          _ ≤ C * t ^ ((N : ℝ) - n / 2) := by
              gcongr
              rw [hCdef]
              have : 0 ≤ |A6| * |A1| := by positivity
              nlinarith
    · -- away from the support of the cutoff: `H` vanishes near `y`
      have hz : ∀ᶠ z in 𝓝 y, θ (z - p) = 0 := by
        have h0 : ∀ᶠ w in 𝓝 (y - p), θ w = 0 := notMem_tsupport_iff_eventuallyEq.mp hsupp
        exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds h0
      have hHz : H t p =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hz] with z hz
        show θ (z - p) * _ = 0
        rw [hz, zero_mul]
      have hθy : θ (y - p) = 0 := image_eq_zero_of_notMem_tsupport hsupp
      refine ⟨0, ?_, ?_⟩
      · have : (fun s => H s p y) = fun _ => 0 := funext fun s => by
          show θ (y - p) * _ = 0
          rw [hθy, zero_mul]
        rw [this]; exact hasDerivAt_const t 0
      · have hL : coordLaplacian g (H t p) y = 0 := by
          unfold coordLaplacian
          have hflux : ∀ i, coordFlux g (H t p) i =ᶠ[𝓝 y] fun _ => 0 := fun i => by
            filter_upwards [hHz.eventuallyEq_nhds] with z hz'
            simp [coordFlux, pd_congr hz', pd_const]
          simp [pd_congr (hflux _), pd_const]
        rw [hL, zero_add, abs_zero]
        exact mul_nonneg hCnn hpow_nn

/-- **The parametrix in a chart and its heat error.** For a Riemannian coordinate metric on `U`, `x ∈ U` and an order
`N`, there are `r > 0`, coefficients `u_k(p, y)` with `u₀(p, p) = 1`, and a cut-off parametrix
`H(t, p, y) = θ(y − p) (4πt)^{-n/2} e^{-σ(p, y)/4t} Σ_{k≤N} tᵏ u_k(p, y)` with the diagonal
`H(t, p, p) = (4πt)^{-n/2} Σ_{k≤N} tᵏ u_k(p, p)`, whose heat error in the second variable is `O(t^{N − n/2})` uniformly
for `t ∈ (0, 1]`, `‖p − x‖ < r` and all `y`. -/
theorem exists_chart_parametrix {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) (N : ℕ) :
    ∃ (r : ℝ) (u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ), 0 < r ∧
      (∀ p, ‖p - x‖ < r → u 0 (p, p) = 1) ∧
      (∀ t > 0, ∀ p, ‖p - x‖ < r →
        H t p p = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * ∑ k ∈ Finset.range (N + 1), t ^ k * u k (p, p)) ∧
      (∃ C a : ℝ, 0 < a ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y,
        |H t p y| ≤ C * t ^ (-(n : ℝ) / 2) * Real.exp (-a * (∑ i, (y i - p i) ^ 2) / t)) ∧
      (∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∫ y, |H t p y| ≤ C) ∧
      -- the structure of `H`, for the delta property
      (∃ (Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))) (θ : (Fin n → ℝ) → ℝ)
          (σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ) (V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)),
        IsOpen Ω ∧ (x, x) ∈ Ω ∧ (∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → (p, y) ∈ Ω) ∧
        (∀ q ∈ Ω, q.2 ∈ U) ∧ ContDiffOn ℝ ∞ V Ω ∧ (∀ k, ContDiffOn ℝ ∞ (u k) Ω) ∧
        (∀ p, (p, p) ∈ Ω → V (p, p) = 0 ∧
          HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) ∧
        (∀ q ∈ Ω, σ q = Geodesic.pairing g q.1 (V q) (V q)) ∧
        (∀ z, ‖z‖ < r / 2 → θ z = 1) ∧ (∀ z, r ≤ ‖z‖ → θ z = 0) ∧ (∀ z, θ z ∈ Icc (0 : ℝ) 1) ∧
        ContDiff ℝ ∞ θ ∧ tsupport θ ⊆ ball 0 r ∧ (∀ t p, ‖p - x‖ < r → Continuous (H t p)) ∧
        (∀ t > 0, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → ∃ D, HasDerivAt (fun s => H s p y) D t ∧
          D + coordLaplacian g (H t p) y =
            θ (y - p) * (heatGaussian n (σ (p, y)) t * (t ^ N * coordLaplacian g (fun z => u N (p, z)) y)) +
            (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (gaussFactor t (σ (p, y)) * truncAnsatz (fun k y => u k (p, y)) N t y *
              coordLaplacian g (fun z => θ (z - p)) y - 2 * (gaussFactor t (σ (p, y)) *
                ((∑ k ∈ Finset.range (N + 1), t ^ k * coordGradPair g (fun z => θ (z - p)) (fun z => u k (p, z)) y) -
                  truncAnsatz (fun k y => u k (p, y)) N t y *
                    coordGradPair g (fun z => θ (z - p)) (fun z => σ (p, z)) y / (4 * t))))) ∧
        (∃ c : ℝ, 0 < c ∧ ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r → c * ‖y - p‖ ^ 2 ≤ σ (p, y)) ∧
        (∃ A : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - p‖ < r →
          |truncAnsatz (fun k y => u k (p, y)) N t y| ≤ A) ∧
        ∀ t p y, H t p y = θ (y - p) * (heatGaussian n (σ (p, y)) t * truncAnsatz (fun k y => u k (p, y)) N t y)) ∧
      ∃ C : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ p, ‖p - x‖ < r → ∀ y, ∃ D, HasDerivAt (fun s => H s p y) D t ∧
        |D + coordLaplacian g (H t p) y| ≤ C * t ^ ((N : ℝ) - n / 2) := by
  obtain ⟨r, u, Ω, θ, σ, V, h⟩ := exists_chart_parametrix_uniform hg hx
  obtain ⟨H, hH⟩ := h N
  exact ⟨r, u, H, hH.r_pos, hH.u_zero_diag, hH.diag_eq, hH.gauss_le, hH.integral_abs_le,
    ⟨Ω, θ, σ, V, hH.isOpen, hH.center_mem, hH.mem_of_lt, hH.snd_mem, hH.V_smooth, hH.u_smooth, hH.V_diag,
      hH.σ_eq, hH.θ_one, hH.θ_zero, hH.θ_mem, hH.θ_smooth, hH.θ_tsupport, hH.H_cont, hH.heatError_eq,
      hH.σ_lower, hH.ansatz_le, hH.H_eq⟩, hH.heatError_le⟩

end Lightlike
