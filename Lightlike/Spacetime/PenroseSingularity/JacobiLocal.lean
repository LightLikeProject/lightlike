import Lightlike.Spacetime.ConjugatePoints.JacobiVariation

/-!
# Jacobi fields from a locally defined variation (G1-012, step D3b wiring)

`exists_isJacobiOn_of_variation` needs a globally `C³` variation. For a variation `H` that is `C³` only
on an open set `W ⊇ {(t₀, 0)}`, a bump function cuts it off, and the Jacobi equation holds on a small
interval around `t₀`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- `IsJacobiOn` depends only on the germs of the fields at the points of `I`. -/
theorem IsJacobiOn.congr_eventually {γ w J P γ' w' J' : ℝ → Fin n → ℝ} {I : Set ℝ}
    (h : IsJacobiOn g γ w J P I) (hγ : ∀ t ∈ I, γ' =ᶠ[𝓝 t] γ) (hw : ∀ t ∈ I, w' =ᶠ[𝓝 t] w)
    (hJ : ∀ t ∈ I, J' =ᶠ[𝓝 t] J) : IsJacobiOn g γ' w' J' P I := by
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_⟩, fun t ht => ?_, fun t ht => ?_⟩
  · have := h.geodesic.pos t ht
    rw [(hw t ht).self_of_nhds]
    exact this.congr_of_eventuallyEq (hγ t ht)
  · have := h.geodesic.vel t ht
    rw [(hγ t ht).self_of_nhds, (hw t ht).self_of_nhds]
    exact this.congr_of_eventuallyEq (hw t ht)
  · have := h.deriv_field t ht
    rw [(hγ t ht).self_of_nhds, (hw t ht).self_of_nhds, (hJ t ht).self_of_nhds]
    exact this.congr_of_eventuallyEq (hJ t ht)
  · have := h.deriv_cov t ht
    rw [(hγ t ht).self_of_nhds, (hw t ht).self_of_nhds, (hJ t ht).self_of_nhds]
    exact this

/-- **Local Jacobi fields from a local variation.** -/
theorem exists_isJacobiOn_local (hg : Lightlike.IsCoordMetric g U) {H : ℝ × ℝ → Fin n → ℝ}
    {W : Set (ℝ × ℝ)} (hW : IsOpen W) (hH : ContDiffOn ℝ 3 H W) {t₀ : ℝ} (ht₀ : (t₀, (0 : ℝ)) ∈ W)
    (hU : ∀ p ∈ W, H p ∈ U)
    (hgeo : ∀ p ∈ W, IsGeodesicOn g (fun t => H (t, p.2)) (fun t => fderiv ℝ H (t, p.2) (1, 0))
      {t | (t, p.2) ∈ W}) :
    ∃ δ > 0, ∃ P, IsJacobiOn g (fun t => H (t, 0)) (fun t => fderiv ℝ H (t, 0) (1, 0))
      (fun t => fderiv ℝ H (t, 0) (0, 1)) P (Ioo (t₀ - δ) (t₀ + δ)) := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW _ ht₀
  set c : ℝ × ℝ := (t₀, 0) with hc
  let bmp : ContDiffBump c := ⟨r / 4, r / 2, by linarith, by linarith⟩
  have hsupp : tsupport bmp ⊆ W := by
    rw [bmp.tsupport_eq]
    intro p hp
    exact hball (by rw [Metric.mem_ball]; have := Metric.mem_closedBall.1 hp; simp only [bmp] at this; linarith)
  set H' : ℝ × ℝ → Fin n → ℝ := fun p => bmp p • H p with hH'
  have hH'c : ContDiff ℝ 3 H' := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ W
    · exact (bmp.contDiff.contDiffAt).smul (hH.contDiffAt (hW.mem_nhds hp))
    · have hp' : p ∉ tsupport bmp := fun h => hp (hsupp h)
      have : H' =ᶠ[𝓝 p] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport bmp).isOpen_compl.mem_nhds hp'] with q hq
        simp [hH', image_eq_zero_of_notMem_tsupport hq]
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hone : ∀ p ∈ Metric.ball c (r / 4), bmp p = 1 := fun p hp =>
    bmp.one_of_mem_closedBall (by simpa [bmp] using (Metric.ball_subset_closedBall hp))
  have hH'eq : ∀ p ∈ Metric.ball c (r / 4), H' =ᶠ[𝓝 p] H := fun p hp => by
    filter_upwards [Metric.isOpen_ball.mem_nhds hp] with q hq
    simp [hH', hone q hq]
  have hfd : ∀ p ∈ Metric.ball c (r / 4), fderiv ℝ H' p = fderiv ℝ H p := fun p hp =>
    (hH'eq p hp).fderiv_eq
  set δ : ℝ := r / 8 with hδ
  have hδpos : 0 < δ := by positivity
  have hin : ∀ t s : ℝ, |t - t₀| < δ → |s| < δ → ((t, s) : ℝ × ℝ) ∈ Metric.ball c (r / 4) := by
    intro t s ht hs
    rw [Metric.mem_ball, hc, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    refine max_lt ?_ ?_ <;> simp [hδ] at * <;> linarith
  have hIT : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), |t - t₀| < δ := fun t ht => by
    rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
  have hdH' : ∀ p, DifferentiableAt ℝ H' p := fun p => (hH'c.differentiable (by norm_num)) p
  have hq : ∀ t s : ℝ, HasDerivAt (fun t : ℝ => ((t, s) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) t := fun t s => by
    simpa using (hasDerivAt_id t).prodMk (hasDerivAt_const t s)
  have hgeo' : ∀ᶠ s in 𝓝 (0 : ℝ), IsGeodesicOn g (fun t => H' (t, s))
      (fun t => fderiv ℝ H' (t, s) (1, 0)) (Ioo (t₀ - δ) (t₀ + δ)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδpos] with s hs
    have hsabs : |s| < δ := abs_lt.2 ⟨hs.1, hs.2⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · exact (hdH' (t, s)).hasFDerivAt.comp_hasDerivAt t (hq t s)
    · have hp := hin t s (hIT t ht) hsabs
      have hpW : ((t, s) : ℝ × ℝ) ∈ W := hball (lt_of_lt_of_le (by simpa [Metric.mem_ball] using hp)
        (by linarith : r / 4 ≤ r) |> fun h => by simpa [Metric.mem_ball] using h)
      have hv := (hgeo ((t, s)) hpW).vel t (by simpa using hpW)
      have hev : (fun t' : ℝ => fderiv ℝ H (t', s) (1, 0)) =ᶠ[𝓝 t]
          (fun t' : ℝ => fderiv ℝ H' (t', s) (1, 0)) := by
        have hcont : Continuous fun t' : ℝ => ((t', s) : ℝ × ℝ) := by fun_prop
        filter_upwards [hcont.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)] with t' ht'
        rw [hfd _ ht']
      have hHe : H' (t, s) = H (t, s) := (hH'eq _ hp).self_of_nhds
      rw [hHe, hfd _ hp]
      exact hv.congr_of_eventuallyEq hev.symm
  have hU' : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), H' (t, 0) ∈ U := by
    intro t ht
    have hp := hin t 0 (hIT t ht) (by simpa using hδpos)
    have hpW : ((t, 0) : ℝ × ℝ) ∈ W := hball (lt_of_lt_of_le (by simpa [Metric.mem_ball] using hp)
      (by linarith : r / 4 ≤ r) |> fun h => by simpa [Metric.mem_ball] using h)
    rw [(hH'eq _ hp).self_of_nhds]
    exact hU _ hpW
  obtain ⟨P, hP⟩ := exists_isJacobiOn_of_variation hg hH'c hU' hgeo'
  refine ⟨δ, hδpos, P, ?_⟩
  refine hP.congr_eventually (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · have hp := hin t 0 (hIT t ht) (by simpa using hδpos)
    have hcont : Continuous fun t' : ℝ => ((t', 0) : ℝ × ℝ) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)] with t' ht'
    simp [hH', hone _ ht']
  · have hp := hin t 0 (hIT t ht) (by simpa using hδpos)
    have hcont : Continuous fun t' : ℝ => ((t', 0) : ℝ × ℝ) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)] with t' ht'
    rw [hfd _ ht']
  · have hp := hin t 0 (hIT t ht) (by simpa using hδpos)
    have hcont : Continuous fun t' : ℝ => ((t', 0) : ℝ × ℝ) := by fun_prop
    filter_upwards [hcont.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)] with t' ht'
    rw [hfd _ ht']

end Lightlike.Geodesic
