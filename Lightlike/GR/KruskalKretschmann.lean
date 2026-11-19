import Lightlike.GR.KruskalRegions
import Lightlike.GR.SchwarzschildKretschmann
import Lightlike.Spacetime.SchwarzschildManifold

/-!
# The curvature singularity of the Kruskal–Szekeres extension

Gap row G1-020, toward maximality. The Kretschmann scalar is chart-independent (`kretschmann_pullback`), so its
Schwarzschild value `48 M²/r⁶` (`kretschmann_sch`) holds

* in ingoing Eddington–Finkelstein coordinates for every `r > 0`, across the horizon (`kretschmann_ef`), and
* in Kruskal–Szekeres coordinates on the whole domain `X² - T² > -1` (`kretschmann_kruskal`), with
  `r = kr M z` the radius function.

It is unbounded near `X² - T² = -1` (`kretschmann_kruskal_unbounded`). Consequently
(`not_tendsto_of_isometric_chart`): for every coordinate metric `g'` on an open set `U'` and every chart change
`φ` of the Kruskal domain into `U'` under which `g'` pulls back to the Kruskal metric, a sequence of points with
`X² - T² → -1` (that is `r → 0`) has no limit in `U'`. So no extension of the Kruskal manifold, in any
coordinates, contains a point of the boundary `r = 0`: the Kruskal extension cannot be extended through its
singularity.

Source read: S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7, printed
pages 171-172 ("If any of these scalars ... go to infinity as we approach some point, we will regard that point
as a singularity of the curvature"; eq. (7.30), "This is enough to convince us that `r = 0` represents an honest
singularity"). The value in (7.30) is `12 G²M²/r⁶`; the computation gives `48 M²/r⁶` (see the header of the
Schwarzschild computation).

**Not proved here**: maximality in full (inextendibility as a Lorentzian manifold). That needs, besides this
statement, that every other way of leaving the Kruskal domain takes infinite affine length (the completeness of
the geodesics that do not run into `r = 0`), and the notion of an extension of a manifold; neither is in the
library.
-/

open Matrix Real Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

section Congr

variable {n : ℕ} {g₁ g₂ : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- Two metrics that agree on an open set have the same Kretschmann scalar there. -/
theorem kretschmann_congr_on (hU : IsOpen U) (h : ∀ y ∈ U, g₁ y = g₂ y) {y : Fin n → ℝ} (hy : y ∈ U) :
    kretschmann g₁ y = kretschmann g₂ y := by
  have hR : ∀ c d, riemMat g₁ c d y = riemMat g₂ c d y := fun c d => by
    ext a b
    exact riemann_congr_on hU h hy a b c d
  have hT : kretMat g₁ y = kretMat g₂ y := by
    ext p q
    simp only [kretMat, hR, h y hy]
  simp only [kretschmann, hT, h y hy]

end Congr

/-- Two functions that are continuous at `z` and agree at the points `z + t e`, `t ≠ 0` small, agree at `z`. -/
lemma eq_of_continuousAt_of_eventually_line {f h : (Fin 4 → ℝ) → ℝ} {z : Fin 4 → ℝ} (e : Fin 4 → ℝ)
    (hf : ContinuousAt f z) (hh : ContinuousAt h z)
    (heq : ∀ᶠ t in 𝓝[≠] (0 : ℝ), f (z + t • e) = h (z + t • e)) : f z = h z := by
  set c : ℝ → Fin 4 → ℝ := fun t => z + t • e with hc
  have hcc : Continuous c := continuous_const.add (continuous_id.smul continuous_const)
  have hc0 : c 0 = z := by simp [hc]
  have h0 := hcc.tendsto 0
  rw [hc0] at h0
  have hlimf : Tendsto (fun t => f (c t)) (𝓝[≠] 0) (𝓝 (f z)) :=
    (hf.tendsto.comp h0).mono_left nhdsWithin_le_nhds
  have hlimh : Tendsto (fun t => h (c t)) (𝓝[≠] 0) (𝓝 (h z)) :=
    (hh.tendsto.comp h0).mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hlimf (hlimh.congr' (heq.mono fun t ht => ht.symm))

variable (M : ℝ)

/-! ### Eddington–Finkelstein coordinates -/

/-- The Kretschmann scalar of the Eddington–Finkelstein metric off the horizon. -/
theorem kretschmann_ef_region {S : Set ℝ} (hS : IsOpen S) (hpos : ∀ r ∈ S, 0 < r)
    (hh : ∀ r ∈ S, r ≠ 2 * M) {rs : ℝ → ℝ}
    (hrs : ∀ r ∈ S, HasDerivAt rs (1 - 2 * M / r)⁻¹ r) (hsm : ContDiffOn ℝ ∞ rs S)
    {y : Fin 4 → ℝ} (hy : y ∈ efRegion S) : kretschmann (efMetric M) y = 48 * M ^ 2 / y 1 ^ 6 := by
  have hCM := isCoordMetric_sch_region M hS hpos hh
  have hφ := isChartChange_efChange M hS hrs hsm
  have hcongr : ∀ z ∈ efRegion S, efMetric M z = pullback (schMetric M) (efChange rs) z :=
    fun z hz => (pullback_sch_ef M (hpos _ hz.1).ne' (sub_ne_zero.2 (hh _ hz.1)) (hrs _ hz.1)).symm
  have hreg : efChange rs y ∈ schRegion M :=
    ⟨by simpa [efChange] using hpos _ hy.1,
     by simpa [efChange] using sub_ne_zero.2 (hh _ hy.1),
     by simpa [efChange] using (sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2).ne'⟩
  rw [kretschmann_congr_on (isOpen_efRegion hS) hcongr hy, kretschmann_pullback hCM hφ hy,
    kretschmann_sch M hreg]
  rfl

/-- **The Kretschmann scalar of the Eddington–Finkelstein metric is `48 M²/r⁶` for every `r > 0`**, across the
horizon. -/
theorem kretschmann_ef (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ efU) :
    kretschmann (efMetric M) y = 48 * M ^ 2 / y 1 ^ 6 := by
  obtain ⟨hr, hθ, hθ'⟩ := hy
  have hext : ∀ {w : Fin 4 → ℝ}, 2 * M < w 1 → 0 < w 2 → w 2 < π →
      kretschmann (efMetric M) w = 48 * M ^ 2 / w 1 ^ 6 := fun {w} h1 h2 h3 =>
    kretschmann_ef_region M (S := Ioi (2 * M)) isOpen_Ioi
      (fun r hr => by have : 2 * M < r := hr; linarith) (fun r hr => ne_of_gt hr)
      (fun r hr => hasDerivAt_tortoiseExt M hM hr) (contDiffOn_tortoiseExt M hM) ⟨h1, h2, h3⟩
  have hint : ∀ {w : Fin 4 → ℝ}, 0 < w 1 → w 1 < 2 * M → 0 < w 2 → w 2 < π →
      kretschmann (efMetric M) w = 48 * M ^ 2 / w 1 ^ 6 := fun {w} h0 h1 h2 h3 =>
    kretschmann_ef_region M (S := Ioo 0 (2 * M)) isOpen_Ioo (fun r hr => hr.1)
      (fun r hr => ne_of_lt hr.2) (fun r hr => hasDerivAt_tortoiseInt M hM hr.1 hr.2)
      (contDiffOn_tortoiseInt M hM) ⟨⟨h0, h1⟩, h2, h3⟩
  rcases lt_trichotomy (y 1) (2 * M) with h | h | h
  · exact hint hr h hθ hθ'
  · have hmem : y ∈ efU := ⟨hr, hθ, hθ'⟩
    have hf : ContinuousAt (kretschmann (efMetric M)) y :=
      (continuousOn_kretschmann (isCoordMetric_ef M)).continuousAt (isOpen_efU.mem_nhds hmem)
    have hh : ContinuousAt (fun w : Fin 4 → ℝ => 48 * M ^ 2 / w 1 ^ 6) y :=
      ContinuousAt.div continuousAt_const ((continuous_apply 1).continuousAt.pow 6)
        (pow_ne_zero 6 hr.ne')
    refine eq_of_continuousAt_of_eventually_line (Pi.single 1 1) hf hh ?_
    have hcc : Continuous fun t : ℝ => y + t • (Pi.single 1 1 : Fin 4 → ℝ) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hU : ∀ᶠ t in 𝓝 (0 : ℝ), y + t • (Pi.single 1 1 : Fin 4 → ℝ) ∈ efU :=
      hcc.continuousAt.preimage_mem_nhds (by simpa using isOpen_efU.mem_nhds hmem)
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with t ht ht0
    have h1 : (y + t • (Pi.single 1 1 : Fin 4 → ℝ)) 1 = 2 * M + t := by simp [h, Pi.single_apply]
    rcases lt_or_gt_of_ne (show t ≠ 0 from ht0) with hlt | hgt
    · exact hint ht.1 (by rw [h1]; linarith) ht.2.1 ht.2.2
    · exact hext (by rw [h1]; linarith) ht.2.1 ht.2.2
  · exact hext h hθ hθ'

/-! ### Kruskal–Szekeres coordinates -/

/-- The Kretschmann scalar at the image of the Kruskal change. -/
theorem kretschmann_kruskal_of_mem_image (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ efU) :
    kretschmann (kruskalMetric M) (kruskalChange M y) =
      48 * M ^ 2 / kr M (kruskalChange M y) ^ 6 := by
  rw [← kretschmann_pullback (isCoordMetric_kruskal M hM) (isChartChange_kruskalChange M hM) hy,
    kretschmann_congr_on isOpen_efU (fun y' hy' => pullback_kruskal_ef M hM hy') hy,
    kretschmann_ef M hM hy, kr_kruskalChange M hM hy]

/-- The Kretschmann scalar is invariant under the reflection `(T, X) ↦ (-T, -X)`. -/
theorem kretschmann_kruskal_neg (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalU) :
    kretschmann (kruskalMetric M) (kruskalNeg z) = kretschmann (kruskalMetric M) z := by
  rw [← kretschmann_pullback (isCoordMetric_kruskal M hM) isChartChange_kruskalNeg hz,
    kretschmann_congr_on isOpen_kruskalU (fun y _ => pullback_kruskalNeg M y) hz]

/-- The Kretschmann scalar off `T + X = 0`. -/
theorem kretschmann_kruskal_of_ne (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalU)
    (hV : z 0 + z 1 ≠ 0) : kretschmann (kruskalMetric M) z = 48 * M ^ 2 / kr M z ^ 6 := by
  rcases lt_or_gt_of_ne hV with h | h
  · have hzn : kruskalNeg z ∈ kruskalU := kruskalNeg_mem hz
    obtain ⟨y, hy, hyz⟩ := exists_kruskalChange_eq M hM hzn (by simp [kruskalNeg]; linarith)
    have h1 := kretschmann_kruskal_of_mem_image M hM hy
    rw [hyz, kretschmann_kruskal_neg M hM hz, kr_neg] at h1
    exact h1
  · obtain ⟨y, hy, hyz⟩ := exists_kruskalChange_eq M hM hz h
    have := kretschmann_kruskal_of_mem_image M hM hy
    rwa [hyz] at this

/-- **The Kretschmann scalar of the Kruskal–Szekeres metric is `48 M²/r⁶` on the whole domain**
`X² - T² > -1`, including the horizons. -/
theorem kretschmann_kruskal (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalU) :
    kretschmann (kruskalMetric M) z = 48 * M ^ 2 / kr M z ^ 6 := by
  by_cases hV : z 0 + z 1 = 0
  · have hf : ContinuousAt (kretschmann (kruskalMetric M)) z :=
      (continuousOn_kretschmann (isCoordMetric_kruskal M hM)).continuousAt
        (isOpen_kruskalU.mem_nhds hz)
    have hh : ContinuousAt (fun w : Fin 4 → ℝ => 48 * M ^ 2 / kr M w ^ 6) z :=
      ContinuousAt.div continuousAt_const ((contDiffAt_kr M hM hz).continuousAt.pow 6)
        (pow_ne_zero 6 (kr_pos M hM hz).ne')
    refine eq_of_continuousAt_of_eventually_line (Pi.single 0 1) hf hh ?_
    have hcc : Continuous fun t : ℝ => z + t • (Pi.single 0 1 : Fin 4 → ℝ) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hU : ∀ᶠ t in 𝓝 (0 : ℝ), z + t • (Pi.single 0 1 : Fin 4 → ℝ) ∈ kruskalU :=
      hcc.continuousAt.preimage_mem_nhds (by simpa using isOpen_kruskalU.mem_nhds hz)
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with t ht ht0
    refine kretschmann_kruskal_of_ne M hM ht ?_
    have h0 : (z + t • (Pi.single 0 1 : Fin 4 → ℝ)) 0 = z 0 + t := by simp
    have h1 : (z + t • (Pi.single 0 1 : Fin 4 → ℝ)) 1 = z 1 := by simp [Pi.single_apply]
    rw [h0, h1]
    have : t ≠ 0 := ht0
    intro h; apply this; linarith
  · exact kretschmann_kruskal_of_ne M hM hz hV

/-- **The curvature is unbounded near `r = 0`**: for every bound `B` there is `δ > 0` such that the Kretschmann
scalar exceeds `B` at every point of the Kruskal domain with `X² - T² < -1 + δ`. -/
theorem kretschmann_kruskal_unbounded (hM : 0 < M) (B : ℝ) :
    ∃ δ > 0, ∀ z ∈ kruskalU, z 1 ^ 2 - z 0 ^ 2 < -1 + δ → B < kretschmann (kruskalMetric M) z := by
  -- a radius `ε ≤ 1` with `48 M²/ε⁶ > B`
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
  have hr := kr_pos M hM hz
  have hrε : kr M z < ε := by
    have h1 : kF M (kr M z) < kF M ε := by
      unfold kr
      rw [kF_kG M hM hz.1]
      linarith
    exact (hmono.lt_iff_lt (mem_Ici.2 hr.le) (mem_Ici.2 hε0.le)).1 h1
  rw [kretschmann_kruskal M hM hz]
  have h6 : kr M z ^ 6 < ε := by
    have h1 : kr M z ^ 6 ≤ kr M z := by
      have hle : kr M z ≤ 1 := by linarith
      calc kr M z ^ 6 = kr M z * kr M z ^ 5 := by ring
        _ ≤ kr M z * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hle) hr.le
        _ = kr M z := mul_one _
    linarith
  have h7 : kr M z ^ 6 * (|B| + 1) < 48 * M ^ 2 := by
    have h8 : ε * (|B| + 1) ≤ 48 * M ^ 2 := by
      rwa [le_div_iff₀ hB1] at hε2
    nlinarith [pow_pos hr 6]
  have h9 : |B| + 1 < 48 * M ^ 2 / kr M z ^ 6 := by
    rw [lt_div_iff₀ (pow_pos hr 6)]
    linarith
  linarith [le_abs_self B]

/-- **No extension through the singularity.** Let `g'` be a coordinate metric on an open set `U'` and `φ` a
chart change of the Kruskal domain into `U'` under which `g'` pulls back to the Kruskal metric. Then a sequence
of points of the Kruskal domain with `X² - T² → -1` (`r → 0`) has no limit in `U'` under `φ`: the Kretschmann
scalar of `g'` is continuous on `U'` and equals `48 M²/r⁶` along the sequence. -/
theorem not_tendsto_of_isometric_chart (hM : 0 < M) {g' : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {U' : Set (Fin 4 → ℝ)} (hg' : IsCoordMetric g' U') {φ : (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    (hφ : IsChartChange φ kruskalU U') (hiso : ∀ z ∈ kruskalU, pullback g' φ z = kruskalMetric M z)
    {z : ℕ → Fin 4 → ℝ} (hz : ∀ k, z k ∈ kruskalU)
    (hlim : Tendsto (fun k => z k 1 ^ 2 - z k 0 ^ 2) atTop (𝓝 (-1))) {p : Fin 4 → ℝ} (hp : p ∈ U') :
    ¬ Tendsto (fun k => φ (z k)) atTop (𝓝 p) := by
  intro hconv
  have hK : ∀ k, kretschmann g' (φ (z k)) = kretschmann (kruskalMetric M) (z k) := fun k => by
    rw [← kretschmann_pullback hg' hφ (hz k), kretschmann_congr_on isOpen_kruskalU hiso (hz k)]
  have hcont : ContinuousAt (kretschmann g') p :=
    (continuousOn_kretschmann hg').continuousAt (hg'.isOpen.mem_nhds hp)
  have hlimK : Tendsto (fun k => kretschmann g' (φ (z k))) atTop (𝓝 (kretschmann g' p)) :=
    hcont.tendsto.comp hconv
  obtain ⟨δ, hδ, hbig⟩ := kretschmann_kruskal_unbounded M hM (kretschmann g' p + 1)
  have hev1 : ∀ᶠ k in atTop, z k 1 ^ 2 - z k 0 ^ 2 < -1 + δ :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ k in atTop, kretschmann g' (φ (z k)) < kretschmann g' p + 1 :=
    hlimK.eventually (gt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  have := hbig (z k) (hz k) hk1
  rw [← hK k] at this
  linarith

end Lightlike
