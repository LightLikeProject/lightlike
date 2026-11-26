import Lightlike.Spacetime.PenroseSingularity.SecondVariation

/-!
# A short chart segment in a timelike direction (G1-012, step D4)

If `q s - x s = s² d s` with `d s` tending to a future timelike vector `d₀` as `s → 0` and `x s → x₀`, then for
small `s > 0` the straight segment from `x s` to `q s` has everywhere a future timelike velocity, in the sense of a
continuous future reference field.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The pairing of continuous families is continuous. -/
theorem continuousAt_gpairAt_fun {α : Type*} [TopologicalSpace α] (hg : Lightlike.IsCoordMetric g U)
    {y u v : α → Fin n → ℝ} {a₀ : α} (hy : y a₀ ∈ U) (hyc : ContinuousAt y a₀) (huc : ContinuousAt u a₀)
    (hvc : ContinuousAt v a₀) : ContinuousAt (fun a => gpairAt g (y a) (u a) (v a)) a₀ := by
  unfold gpairAt
  refine tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => ?_
  have hgab : ContinuousAt (fun x : α => g (y x) a b) a₀ :=
    ContinuousAt.comp (g := fun z => g z a b) ((hg.smooth a b).continuousOn.continuousAt
      (hg.isOpen.mem_nhds hy)) hyc
  have hu : ContinuousAt (fun x : α => u x a) a₀ := (continuous_apply a).continuousAt.comp huc
  have hv : ContinuousAt (fun x : α => v x b) a₀ := (continuous_apply b).continuousAt.comp hvc
  exact (hgab.mul hu).mul hv

/-- The set of `(y, v)` with `y ∈ U` and `v` future timelike (for the reference `Xc`) is a neighbourhood of a point
of it. -/
theorem future_timelike_nhds (hg : Lightlike.IsCoordMetric g U) {x₀ d₀ : Fin n → ℝ}
    {Xc : (Fin n → ℝ) → Fin n → ℝ} (hx0 : x₀ ∈ U) (hX : ContinuousAt Xc x₀)
    (hneg : gpairAt g x₀ d₀ d₀ < 0) (hfut : gpairAt g x₀ d₀ (Xc x₀) < 0) :
    {p : (Fin n → ℝ) × (Fin n → ℝ) | p.1 ∈ U ∧ gpairAt g p.1 p.2 p.2 < 0 ∧
      gpairAt g p.1 p.2 (Xc p.1) < 0} ∈ 𝓝 (x₀, d₀) := by
  have hF1 : ContinuousAt (fun p : (Fin n → ℝ) × (Fin n → ℝ) => gpairAt g p.1 p.2 p.2) (x₀, d₀) :=
    continuousAt_gpairAt_fun hg hx0 continuousAt_fst continuousAt_snd continuousAt_snd
  have hF2 : ContinuousAt (fun p : (Fin n → ℝ) × (Fin n → ℝ) => gpairAt g p.1 p.2 (Xc p.1)) (x₀, d₀) :=
    continuousAt_gpairAt_fun hg hx0 continuousAt_fst continuousAt_snd (hX.comp continuousAt_fst)
  have e1 : ∀ᶠ p in 𝓝 (x₀, d₀), p.1 ∈ U :=
    continuousAt_fst.preimage_mem_nhds (hg.isOpen.mem_nhds hx0)
  have e2 : ∀ᶠ p in 𝓝 (x₀, d₀), gpairAt g p.1 p.2 p.2 < 0 := hF1.eventually (gt_mem_nhds hneg)
  have e3 : ∀ᶠ p in 𝓝 (x₀, d₀), gpairAt g p.1 p.2 (Xc p.1) < 0 := hF2.eventually (gt_mem_nhds hfut)
  exact e1.and (e2.and e3)

/-- **The chart segment from `x s` to `x s + s² d s` is future timelike for small `s`.** The reference field `Xc`
is a continuous chart expression of the time orientation. -/
theorem segment_future_timelike (hg : Lightlike.IsCoordMetric g U) {x : ℝ → Fin n → ℝ} {d : ℝ → Fin n → ℝ}
    {Xc : (Fin n → ℝ) → Fin n → ℝ} (hx0 : x 0 ∈ U) (hxc : ContinuousAt x 0) (hdc : ContinuousAt d 0)
    (hX : ContinuousAt Xc (x 0)) (hneg : gpairAt g (x 0) (d 0) (d 0) < 0)
    (hfut : gpairAt g (x 0) (d 0) (Xc (x 0)) < 0) :
    ∃ δ > 0, ∀ s, |s| < δ → ∀ r ∈ Icc (0 : ℝ) 1,
      x s + r • (s ^ 2 • d s) ∈ U ∧ gpairAt g (x s + r • (s ^ 2 • d s)) (d s) (d s) < 0 ∧
        gpairAt g (x s + r • (s ^ 2 • d s)) (d s) (Xc (x s + r • (s ^ 2 • d s))) < 0 := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (future_timelike_nhds hg hx0 hX hneg hfut)
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), dist (x s) (x 0) < ρ / 2 :=
    hxc.eventually (Metric.ball_mem_nhds _ (by linarith))
  have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), dist (d s) (d 0) < ρ := hdc.eventually (Metric.ball_mem_nhds _ hρ)
  have h3 : ∀ᶠ s in 𝓝 (0 : ℝ), s ^ 2 * (‖d 0‖ + ρ) < ρ / 2 := by
    have hc : ContinuousAt (fun s : ℝ => s ^ 2 * (‖d 0‖ + ρ)) 0 := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simp; linarith))
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.1 (h1.and (h2.and h3))
  refine ⟨δ, hδ, fun s hs r hr => ?_⟩
  have hs' : dist s 0 < δ := by simpa [Real.dist_eq] using hs
  obtain ⟨e1, e2, e3⟩ := hδs hs'
  have hdn : ‖d s‖ ≤ ‖d 0‖ + ρ := by
    have h : ‖d s‖ ≤ ‖d 0‖ + ‖d s - d 0‖ := by
      have := norm_le_norm_add_norm_sub' (d s) (d 0)
      linarith
    have h' : ‖d s - d 0‖ < ρ := by simpa [dist_eq_norm] using e2
    linarith
  have hshift : ‖r • (s ^ 2 • d s)‖ < ρ / 2 := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr.1, abs_of_nonneg (sq_nonneg s)]
    calc r * (s ^ 2 * ‖d s‖) ≤ 1 * (s ^ 2 * ‖d s‖) :=
          mul_le_mul_of_nonneg_right hr.2 (mul_nonneg (sq_nonneg s) (norm_nonneg _))
      _ ≤ s ^ 2 * (‖d 0‖ + ρ) := by rw [one_mul]; exact mul_le_mul_of_nonneg_left hdn (sq_nonneg s)
      _ < ρ / 2 := e3
  have hmem : (x s + r • (s ^ 2 • d s), d s) ∈ Metric.ball (x 0, d 0) ρ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    refine max_lt ?_ e2
    have h : dist (x s + r • (s ^ 2 • d s)) (x 0) ≤ dist (x s) (x 0) + ‖r • (s ^ 2 • d s)‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖x s + r • (s ^ 2 • d s) - x 0‖ = ‖(x s - x 0) + r • (s ^ 2 • d s)‖ := by congr 1; abel
        _ ≤ ‖x s - x 0‖ + ‖r • (s ^ 2 • d s)‖ := norm_add_le _ _
    linarith
  exact hball hmem

end Lightlike.Penrose
