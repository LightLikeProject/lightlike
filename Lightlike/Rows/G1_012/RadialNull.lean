import Lightlike.Rows.G1_012.LocalGenerators
import Lightlike.Rows.G1_012.NullGeodChart

/-!
# Radial null segments of a time ball are future null geodesics of `M` (G1-012)

In the future time ball at `p` (chart coordinates of the chart at `x`), a nonzero null vector `w` with
`x⁰(w) > 0` gives the radial segment `s ↦ ψ.symm (φ (s • w))`, `s ∈ [0, 1]`, which is a future null
geodesic of `M` (`radial_isFutureNullGeodesicOn`): the chart geodesic of the normal chart
(`IsNormalChart.geodesic`), read in the chart at `x`, is a null geodesic curve
(`isNullGeodesicOn_of_chart`).
-/

open Bundle Manifold Set Filter Topology MeasureTheory Metric Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- **A radial null segment of a future time ball is a future null geodesic of `M`.** -/
theorem radial_isFutureNullGeodesicOn (T : Causal.TimeOrientation g) (x : M) {p : Fin n → ℝ}
    {ρ r : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {N : (Fin n → ℝ) → Fin n → ℝ}
    (hTB : Lightlike.Geodesic.IsTimeBall (g.coordMetric x)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target p ρ φ (timeCoord T x p) r N)
    (hfutN : ∀ v ∈ ball (0 : Fin n → ℝ) r, Lightlike.Geodesic.pairing (g.coordMetric x) (φ v) (N v)
      (timeCoord T x (φ v)) < 0)
    {w : Fin n → ℝ} (hw : w ∈ ball (0 : Fin n → ℝ) r) (hw0 : w ≠ 0)
    (hσ : Lightlike.Geodesic.pairing (g.coordMetric x) p w w = 0)
    (hx0 : Lightlike.Geodesic.pairing (g.coordMetric x) p (timeCoord T x p) w < 0) :
    IsFutureNullGeodesicOn T (fun s : ℝ => (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (φ (s • w)))
      (Icc 0 1) := by
  have hL := g.isLorentzianCoordMetric_coordMetric x
  have hg := hL.1
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  have hwρ : w ∈ ball (0 : Fin n → ℝ) ρ := hTB.mem_ball hw
  -- a slightly longer vector still in the normal ball
  obtain ⟨lam, hlam1, hlamw⟩ : ∃ lam : ℝ, 1 < lam ∧ lam • w ∈ ball (0 : Fin n → ℝ) ρ := by
    have hopen : IsOpen ((fun t : ℝ => t • w) ⁻¹' ball (0 : Fin n → ℝ) ρ) :=
      isOpen_ball.preimage (by fun_prop)
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 hopen 1 (by simpa using hwρ)
    refine ⟨1 + δ / 2, by linarith, hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_nonneg (by linarith)]; linarith
  have hlam0 : 0 < lam := by linarith
  -- the chart geodesic and its rescaling
  obtain ⟨γ', w', -, -, -, hgeo', hγ'⟩ := hTB.chart.geodesic (lam • w) hlamw
  have hgeoS := hgeo'.scale lam⁻¹
  set O : Set ℝ := Ioo (-lam) lam with hO
  have hOo : IsOpen O := isOpen_Ioo
  have hIO : Icc (0 : ℝ) 1 ⊆ O := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsw : ∀ s ∈ O, s • w ∈ ball (0 : Fin n → ℝ) ρ := by
    intro s hs
    have hs' : |s| < lam := abs_lt.2 hs
    rw [mem_ball_zero_iff] at hlamw ⊢
    rw [norm_smul, Real.norm_eq_abs]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0] at hlamw
    calc |s| * ‖w‖ ≤ lam * ‖w‖ := by gcongr
      _ < ρ := hlamw
  set c : ℝ → Fin n → ℝ := fun s => φ (s • w) with hc
  set c' : ℝ → Fin n → ℝ := fun s => fderiv ℝ φ (s • w) w with hc'
  have hφd : ∀ s ∈ O, HasDerivAt c (c' s) s := by
    intro s hs
    have hsrc : s • w ∈ φ.source := by rw [hTB.chart.source_eq]; exact hsw s hs
    have hdφ : HasFDerivAt φ (fderiv ℝ φ (s • w)) (s • w) :=
      ((hTB.chart.contDiffOn.contDiffAt (φ.open_source.mem_nhds hsrc)).differentiableAt
        (by simp)).hasFDerivAt
    have hin : HasDerivAt (fun s : ℝ => s • w) w s := by
      simpa using (hasDerivAt_id s).smul_const w
    exact hdφ.comp_hasDerivAt s hin
  have hctarget : ∀ s ∈ O, c s ∈ ψ.target := fun s hs =>
    hTB.chart.target_subset (φ.map_source (by rw [hTB.chart.source_eq]; exact hsw s hs))
  have hmemS : ∀ s ∈ O, s ∈ (fun t : ℝ => lam⁻¹ * t) ⁻¹' Ioo (-1 : ℝ) 2 := by
    intro s hs
    have hs' : |s| < lam := abs_lt.2 hs
    have h1 : |lam⁻¹ * s| < 1 := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hlam0), inv_mul_lt_iff₀ hlam0]; linarith
    have := abs_lt.1 h1
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hcγ : ∀ s ∈ O, γ' (lam⁻¹ * s) = c s := by
    intro s hs
    have hs' : |s| < lam := abs_lt.2 hs
    have h1 : |lam⁻¹ * s| ≤ 1 := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hlam0), inv_mul_le_iff₀ hlam0]; linarith
    have := abs_le.1 h1
    rw [hγ' _ ⟨this.1, this.2⟩]
    simp only [hc, smul_smul]
    have : lam⁻¹ * s * lam = s := by field_simp
    rw [this]
  set w'' : ℝ → Fin n → ℝ := fun s => lam⁻¹ • w' (lam⁻¹ * s) with hw''
  have hpos'' : ∀ s ∈ O, HasDerivAt c (w'' s) s := by
    intro s hs
    refine (hgeoS.pos s (hmemS s hs)).congr_of_eventuallyEq ?_
    filter_upwards [hOo.mem_nhds hs] with s' hs'
    exact (hcγ s' hs').symm
  have hw''eq : ∀ s ∈ O, w'' s = c' s := fun s hs => (hpos'' s hs).unique (hφd s hs)
  have hgeoC : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x) c w'' O := by
    refine ⟨hpos'', fun s hs => ?_⟩
    have h2 := hgeoS.vel s (hmemS s hs)
    rw [hcγ s hs] at h2
    exact h2
  have hcM : ∀ s ∈ O, ψ (ψ.symm (c s)) = c s := fun s hs => ψ.right_inv (hctarget s hs)
  have hgeoM : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric x)
      (fun s => ψ (ψ.symm (c s))) w'' O := by
    refine ⟨fun s hs => ?_, fun s hs => ?_⟩
    · refine (hgeoC.pos s hs).congr_of_eventuallyEq ?_
      filter_upwards [hOo.mem_nhds hs] with s' hs' using hcM s' hs'
    · have := hgeoC.vel s hs
      rw [← hcM s hs] at this
      exact this
  have hNull : IsNullGeodesicOn g (fun s => ψ.symm (c s)) O := by
    refine isNullGeodesicOn_of_chart g x hOo (fun s hs => ψ.map_target (hctarget s hs))
      (fun s hs => ?_) (fun s hs => ?_) hgeoM
    · rw [hw''eq s hs]
      intro h0
      have := hTB.chart.fderiv_symm_apply (hsw s hs) w
      have h0' : fderiv ℝ φ (s • w) w = 0 := h0
      rw [h0', map_zero] at this
      exact hw0 this.symm
    · rw [hcM s hs, hw''eq s hs, ← pairing_eq_bil]
      rw [show c s = φ (s • w) from rfl]
      exact (radial_pairing hg hTB.chart (hsw s hs)).trans hσ
  refine ⟨hNull.mono hIO, fun s hs => ?_⟩
  set C : ℝ → M := fun s => ψ.symm (c s) with hC
  have hCvel : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x
      ⟨C s, Causal.velocity 𝓘(ℝ, Fin n → ℝ) C (Icc 0 1) s⟩).2 = c' s :=
    (Causal.mdifferentiableWithinAt_chart_symm (I := 𝓘(ℝ, Fin n → ℝ)) x
      (uniqueDiffOn_Icc zero_lt_one s hs) hs (hφd s (hIO hs)).hasDerivWithinAt
      (fun s hs => hctarget s (hIO hs))).2
  have hCsrc : C s ∈ ψ.source := ψ.map_target (hctarget s (hIO hs))
  have hψC : ψ (C s) = c s := ψ.right_inv (hctarget s (hIO hs))
  have hvq := eq_symmL_of_tTriv x (C s) (mem_baseSet_of_mem_source _ _ hCsrc) _ hCvel
  have hXC := timeOrientation_eq_symmL T x (C s) hCsrc
  rw [hψC] at hXC
  show g.g (C s) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) C (Icc 0 1) s) (T.X (C s)) < 0
  rw [hvq, hXC, metric_eq_bil_at g.toNondegMetric x (C s) hCsrc, hψC]
  have hy : c s ∈ ψ.target := hctarget s (hIO hs)
  have hLf := Lightlike.Geodesic.isLorentzianForm_matForm hL hy
  have hq : ∀ a b, Lightlike.Geodesic.pairing (g.coordMetric x) (c s) a b =
      matForm (g.coordMetric x (c s)) a b := fun a b =>
    Lightlike.Geodesic.pairing_eq_matForm _ _ a b
  have hmemr : s • w ∈ ball (0 : Fin n → ℝ) r := by
    have hw' := mem_ball_zero_iff.1 hw
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [norm_nonneg w, hs.2, hs.1]
  have hσs : Lightlike.Geodesic.pairing (g.coordMetric x) (c s) (c' s) (c' s) = 0 :=
    (radial_pairing hg hTB.chart (hsw s (hIO hs))).trans hσ
  have hc'ne : c' s ≠ 0 := by
    intro h0
    have := hTB.chart.fderiv_symm_apply (hsw s (hIO hs)) w
    have h0' : fderiv ℝ φ (s • w) w = 0 := h0
    rw [h0', map_zero] at this
    exact hw0 this.symm
  have hdual : Lightlike.Geodesic.pairing (g.coordMetric x) (c s) (N (s • w)) (c' s) < 0 := by
    rw [hTB.dual _ hmemr]; exact hx0
  have := hLf.neg_of_neg_pair_causal (X := timeCoord T x (c s)) (N := N (s • w)) (u := c' s)
    (by rw [← hq]; exact timeCoord_timelike T x hy) (by rw [← hq]; exact hTB.timelike _ hmemr)
    (by rw [← hq]; exact hfutN _ hmemr) (by rw [← hq]; exact hσs.le) hc'ne
    (by rw [← hq, Lightlike.Geodesic.pairing_comm hg hy]; exact hdual)
  rw [← Lightlike.Geodesic.pairing_eq_matForm] at this
  rw [pairing_eq_bil] at this
  exact this

end Lightlike.Penrose
