import Lightlike.GR.KruskalManifoldCurvature
import Lightlike.Spacetime.ExtensionChart

/-!
# No extension of the Kruskal manifold reaches the singularity

Gap row G1-020, toward maximality. Let `(M', g')` be any Lorentzian manifold and `ι` a smooth isometric map of the
Kruskal manifold `kruskalCOpen` (the whole manifold `{X² - T² > -1} × S²`, `kruskalManifoldMetric`) into it; in
particular any extension in the sense of `IsLorentzianExtension`. Then a sequence of points of the Kruskal
manifold with `X² - T² → -1`, that is `r → 0`, has no limit in `M'`
(`not_tendsto_of_isometric_kruskal`, `IsLorentzianExtension.not_tendsto_kruskal`): in the chart of `M'` at a
would-be limit point the map `ι` is a chart change (`isChartChange_extChartMap`), the Kretschmann scalar of `g'`
is continuous there and equals `48 M²/r⁶` along the sequence.

So the boundary of the Kruskal manifold in any extension contains no limit of points approaching the
singularity. This is the curvature half of maximality; the other half (points escaping to infinity at bounded
`r` have no limit either) uses the geodesics; the full statement is `kruskal_isInextendible`.
-/

open Matrix Real Set Filter Topology Manifold TopologicalSpace
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- **The curvature is unbounded near `r = 0` on the whole Kruskal manifold.** -/
theorem kretschmann_kruskalC_unbounded (hM : 0 < M) (B : ℝ) :
    ∃ δ > 0, ∀ z ∈ kruskalC, sC z < -1 + δ → B < kretschmann (kruskalCMetric M) z := by
  set ε : ℝ := min 1 (48 * M ^ 2 / (|B| + 1)) with hε
  have hB1 : 0 < |B| + 1 := by positivity
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ 48 * M ^ 2 / (|B| + 1) := min_le_right _ _
  have hmono := kF_strictMonoOn M hM
  have hδ : 0 < kF M ε + 1 := by
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hε0.le) hε0
    rw [kF_zero M hM.ne'] at this
    linarith
  refine ⟨kF M ε + 1, hδ, fun z hz hlt => ?_⟩
  have hr := krC_pos M hM hz
  have hrε : krC M z < ε := by
    have h1 : kF M (krC M z) < kF M ε := by
      unfold krC
      rw [kF_kG M hM hz.2]
      linarith
    exact (hmono.lt_iff_lt (mem_Ici.2 hr.le) (mem_Ici.2 hε0.le)).1 h1
  rw [kretschmann_kruskalC M hM hz]
  have h6 : krC M z ^ 6 < ε := by
    have h1 : krC M z ^ 6 ≤ krC M z := by
      have hle : krC M z ≤ 1 := by linarith
      calc krC M z ^ 6 = krC M z * krC M z ^ 5 := by ring
        _ ≤ krC M z * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hle) hr.le
        _ = krC M z := mul_one _
    linarith
  have h7 : krC M z ^ 6 * (|B| + 1) < 48 * M ^ 2 := by
    have h8 : ε * (|B| + 1) ≤ 48 * M ^ 2 := by rwa [le_div_iff₀ hB1] at hε2
    nlinarith [pow_pos hr 6]
  have h9 : |B| + 1 < 48 * M ^ 2 / krC M z ^ 6 := by
    rw [lt_div_iff₀ (pow_pos hr 6)]
    linarith
  linarith [le_abs_self B]

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace (Fin 4 → ℝ) M']
  [IsManifold 𝓘(ℝ, Fin 4 → ℝ) ∞ M']

/-- **No isometric image of the Kruskal manifold contains a limit of points approaching the singularity.** -/
theorem not_tendsto_of_isometric_kruskal (hM : 0 < M) (g' : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M' 4)
    (ι : kruskalCOpen → M') (hι : ContMDiff 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 4 → ℝ) ∞ ι)
    (hiso : ∀ (x : kruskalCOpen) (v w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x),
      g'.g (ι x) (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 4 → ℝ) ι x v)
        (mfderiv 𝓘(ℝ, Fin 4 → ℝ) 𝓘(ℝ, Fin 4 → ℝ) ι x w) = (kruskalManifoldMetric M hM).g x v w)
    {z : ℕ → kruskalCOpen} (hlim : Tendsto (fun k => sC (z k).1) atTop (𝓝 (-1))) (p : M') :
    ¬ Tendsto (fun k => ι (z k)) atTop (𝓝 p) := by
  intro hconv
  have hL := kruskalC_isLorentzian M hM
  have hch := isChartChange_extChartMap kruskalCOpen ι p (kruskalCMetric M) hL g' hι hiso
  have hg'c := g'.isCoordMetric_coordMetric p
  -- the Kretschmann scalar of `g'` in the chart at `p`, along the sequence
  have hK : ∀ y ∈ extChartDom kruskalCOpen ι p,
      kretschmann (g'.coordMetric p) (extChartMap kruskalCOpen ι p y) =
        kretschmann (kruskalCMetric M) y := fun y hy => by
    rw [← kretschmann_pullback hg'c hch hy,
      kretschmann_congr_on hch.isOpen
        (fun y' hy' => pullback_coordMetric_extChartMap kruskalCOpen ι p (kruskalCMetric M) hL g' hι hiso hy')
        hy]
  -- eventually the sequence is in the chart
  have hsrc : ∀ᶠ k in atTop, ι (z k) ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p).source :=
    hconv.eventually ((isOpen_extChartAt_source (I := 𝓘(ℝ, Fin 4 → ℝ)) p).mem_nhds
      (mem_extChartAt_source (I := 𝓘(ℝ, Fin 4 → ℝ)) p))
  have hchart : Tendsto (fun k => extChartAt 𝓘(ℝ, Fin 4 → ℝ) p (ι (z k))) atTop
      (𝓝 (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p p)) :=
    (continuousAt_extChartAt (I := 𝓘(ℝ, Fin 4 → ℝ)) p).tendsto.comp hconv
  have hcont : ContinuousAt (kretschmann (g'.coordMetric p)) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p p) :=
    (continuousOn_kretschmann hg'c).continuousAt
      ((isOpen_extChartAt_target p).mem_nhds (mem_extChartAt_target (I := 𝓘(ℝ, Fin 4 → ℝ)) p))
  have hlimK := hcont.tendsto.comp hchart
  obtain ⟨δ, hδ, hbig⟩ := kretschmann_kruskalC_unbounded M hM
    (kretschmann (g'.coordMetric p) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p p) + 1)
  have hev1 : ∀ᶠ k in atTop, sC (z k).1 < -1 + δ := hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ k in atTop, kretschmann (g'.coordMetric p) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p (ι (z k))) <
      kretschmann (g'.coordMetric p) (extChartAt 𝓘(ℝ, Fin 4 → ℝ) p p) + 1 :=
    hlimK.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k, hk0, hk1, hk2⟩ := (hsrc.and (hev1.and hev2)).exists
  have hmem : (z k).1 ∈ extChartDom kruskalCOpen ι p := ⟨(z k).2, hk0⟩
  have h1 := hK _ hmem
  rw [extChartMap_apply kruskalCOpen ι p (z k)] at h1
  have h2 := hbig (z k).1 (z k).2 hk1
  rw [← h1] at h2
  linarith

/-- **In every extension of the Kruskal manifold, a sequence approaching the singularity has no limit.** -/
theorem IsLorentzianExtension.not_tendsto_kruskal (hM : 0 < M)
    {g' : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) M' 4} {ι : kruskalCOpen → M'}
    (hext : IsLorentzianExtension (kruskalManifoldMetric M hM) g' ι) {z : ℕ → kruskalCOpen}
    (hlim : Tendsto (fun k => sC (z k).1) atTop (𝓝 (-1))) (p : M') :
    ¬ Tendsto (fun k => ι (z k)) atTop (𝓝 p) :=
  not_tendsto_of_isometric_kruskal M hM g' ι hext.contMDiff hext.isometric hlim p

end Lightlike
