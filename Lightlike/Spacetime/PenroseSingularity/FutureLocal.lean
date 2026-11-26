import Lightlike.Spacetime.PenroseSingularity.ChartSegment

/-!
# Future direction is an open condition near a point (G1-012, step D4)

If the velocity `Y s t` of a family of chart curves pairs negatively with a continuous future reference field at
`(0, t₀)`, it does so for all small `s` and all `t` near `t₀`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Future direction near `(0, t₀)`.** -/
theorem future_local (hg : Lightlike.IsCoordMetric g U) {c Y : ℝ → ℝ → Fin n → ℝ} {t₀ : ℝ}
    {Xc : (Fin n → ℝ) → Fin n → ℝ}
    (hc : ContinuousAt (fun p : ℝ × ℝ => c p.1 p.2) (0, t₀))
    (hY : ContinuousAt (fun p : ℝ × ℝ => Y p.1 p.2) (0, t₀)) (hx : c 0 t₀ ∈ U)
    (hX : ContinuousAt Xc (c 0 t₀))
    (hneg : gpairAt g (c 0 t₀) (Y 0 t₀) (Xc (c 0 t₀)) < 0) :
    ∃ δ > 0, ∃ ε > 0, ∀ t, |t - t₀| < ε → ∀ s, |s| < δ →
      gpairAt g (c s t) (Y s t) (Xc (c s t)) < 0 := by
  have hF : ContinuousAt (fun p : ℝ × ℝ => gpairAt g (c p.1 p.2) (Y p.1 p.2) (Xc (c p.1 p.2))) (0, t₀) :=
    continuousAt_gpairAt_fun (y := fun p : ℝ × ℝ => c p.1 p.2) (u := fun p : ℝ × ℝ => Y p.1 p.2)
      (v := fun p : ℝ × ℝ => Xc (c p.1 p.2)) (a₀ := ((0 : ℝ), t₀)) hg hx hc hY
      (ContinuousAt.comp (g := Xc) (f := fun p : ℝ × ℝ => c p.1 p.2) hX hc)
  have hev := hF.eventually (gt_mem_nhds hneg)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r, hr, r, hr, fun t ht s hs => ?_⟩
  have hd : dist ((s, t) : ℝ × ℝ) ((0 : ℝ), t₀) < r := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_lt (by simpa using hs) ht
  exact hball hd

end Lightlike.Penrose
