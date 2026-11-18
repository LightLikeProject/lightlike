import Lightlike.Spacetime.CausalLadder.ChartModel
import Lightlike.Spacetime.CausalLadder.ChartCurve
import Lightlike.Spacetime.CausalLadder.BoundarylessChart
import Lightlike.Spacetime.Causal.CurveMargin
import Lightlike.Spacetime.Causal.Relations

/-!
# Every neighbourhood of a point meets its chronological future

In a manifold without boundary, every neighbourhood `V` of `p` contains a point of `I⁺(p)`. The chart at
`p` has the vector `X p` (transported by the trivialization) as a timelike direction at `p`, hence, by
the continuity of the metric and of the time orientation, at every point near `p`. The curve
`t ↦ (extChartAt I p).symm (φ p + t · X)` is therefore a `C¹` future timelike curve from `p` for small `t`,
and its points are close to `p`.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Every neighbourhood of `p` contains a point of the chronological future of `p`.** -/
theorem exists_mem_chronFuture_near [BoundarylessManifold I M] (p : M) {V : Set M} (hV : V ∈ 𝓝 p) :
    ∃ q ∈ V, q ∈ chronFuture T p := by
  obtain ⟨ξ, A, B, hA, hB, h0, hmodel⟩ := exists_chart_model T p
  set φ := extChartAt I p with hφ
  have hbase : (tTriv I M p).baseSet ∈ 𝓝 p :=
    (tTriv I M p).open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p)
  have hp : p ∈ (tTriv I M p).baseSet := mem_baseSet_trivializationAt E (fun x : M ↦ TangentSpace I x) p
  set w0 : E := (tTriv I M p ⟨p, T.X p⟩).2 with hw0
  set c0 : Fin n → ℝ := fun i => ξ.repr w0 i with hc0
  obtain ⟨hq0, hl0⟩ := hmodel p hp (T.X p)
  have hQ : quadForm (A p) c0 < 0 := by rw [← hq0]; exact T.timelike p
  have hL : linForm (B p) c0 < 0 := by rw [← hl0]; exact T.timelike p
  have hcQ : Continuous (fun a : Fin n → Fin n → ℝ => quadForm a c0) := by unfold quadForm; fun_prop
  have hcL : Continuous (fun b : Fin n → ℝ => linForm b c0) := by unfold linForm; fun_prop
  have hW : ∀ᶠ q in 𝓝 p, quadForm (A q) c0 < 0 ∧ linForm (B q) c0 < 0 :=
    ((hcQ.continuousAt.comp hA).eventually (Iio_mem_nhds hQ)).and
      ((hcL.continuousAt.comp hB).eventually (Iio_mem_nhds hL))
  have hN : {q | quadForm (A q) c0 < 0 ∧ linForm (B q) c0 < 0} ∩ V ∩ (tTriv I M p).baseSet ∈ 𝓝 p :=
    inter_mem (inter_mem hW hV) hbase
  -- the chart curve
  have hsymm : ContinuousAt φ.symm (φ p) := continuousAt_extChartAt_symm p
  have hu : Continuous (fun t : ℝ => φ p + t • w0) := by fun_prop
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), φ p + t • w0 ∈ φ.target ∧
      φ.symm (φ p + t • w0) ∈ {q | quadForm (A q) c0 < 0 ∧ linForm (B q) c0 < 0} ∩ V ∩
        (tTriv I M p).baseSet := by
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), φ p + t • w0 ∈ φ.target := by
      have : Tendsto (fun t : ℝ => φ p + t • w0) (𝓝 0) (𝓝 (φ p)) := by
        simpa using hu.tendsto 0
      exact this.eventually (extChartAt_target_mem_nhds_of_boundaryless p)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), φ.symm (φ p + t • w0) ∈ {q | quadForm (A q) c0 < 0 ∧ linForm (B q) c0 < 0} ∩ V ∩
        (tTriv I M p).baseSet := by
      have hlim : Tendsto (fun t : ℝ => φ.symm (φ p + t • w0)) (𝓝 0) (𝓝 (φ.symm (φ p))) :=
        hsymm.tendsto.comp (by simpa using hu.tendsto 0)
      rw [φ.left_inv (mem_extChartAt_source p)] at hlim
      exact hlim.eventually hN
    exact h1.and h2
  obtain ⟨ρ, hρ, hρev⟩ := Metric.eventually_nhds_iff.1 hev
  set δ : ℝ := ρ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hmem : ∀ t ∈ Icc 0 δ, φ p + t • w0 ∈ φ.target ∧
      φ.symm (φ p + t • w0) ∈ {q | quadForm (A q) c0 < 0 ∧ linForm (B q) c0 < 0} ∩ V ∩
        (tTriv I M p).baseSet := fun t ht =>
    hρev (by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith [ht.2])
  set c : ℝ → M := fun t => φ.symm (φ p + t • w0) with hc
  have hcsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc 0 δ) := by
    have hs : ContMDiffOn 𝓘(ℝ, E) I ∞ φ.symm φ.target := contMDiffOn_extChartAt_symm p
    have hu' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => φ p + t • w0) :=
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
    have := hs.comp hu'.contMDiffOn (fun t ht => (hmem t ht).1)
    exact this.of_le (by exact_mod_cast le_top)
  have hvel : ∀ t ∈ Icc 0 δ, T.IsFutureTimelike (velocity I c (Icc 0 δ) t) := by
    intro t ht
    have hd : HasDerivWithinAt (fun t : ℝ => φ p + t • w0) w0 (Icc 0 δ) t := by
      have := ((hasDerivAt_id t).smul_const w0).const_add (φ p)
      simpa using this.hasDerivWithinAt
    obtain ⟨-, hv⟩ := mdifferentiableWithinAt_chart_symm (I := I) p (uniqueDiffOn_Icc hδpos t ht) ht hd
      (fun t' ht' => (hmem t' ht').1)
    obtain ⟨hm1, hm2⟩ := hmodel (c t) (hmem t ht).2.2 (velocity I c (Icc 0 δ) t)
    have hv' : (tTriv I M p ⟨c t, velocity I c (Icc 0 δ) t⟩).2 = w0 := hv
    rw [hv'] at hm1 hm2
    obtain ⟨hn1, hn2⟩ := (hmem t ht).2.1.1
    exact ⟨by rw [hm1]; exact hn1, by rw [hm2]; exact hn2⟩
  have hcurve := isFutureTimelikeCurve_of_contMDiffOn T hδpos hcsm hvel
  refine ⟨c δ, (hmem δ ⟨hδpos.le, le_rfl⟩).2.1.2, c, 0, δ, hδpos, hcurve, ?_, rfl⟩
  show φ.symm (φ p + (0 : ℝ) • w0) = p
  rw [zero_smul, add_zero]
  exact φ.left_inv (mem_extChartAt_source p)

end Lightlike.Causal
