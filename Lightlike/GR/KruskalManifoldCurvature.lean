import Lightlike.GR.KruskalSpherical
import Lightlike.GR.KruskalKretschmann
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Vacuum equations and the curvature invariant on the whole Kruskal manifold

Gap row G1-020. Every point of the global chart `kruskalC` off the rotation axis is in the image of the spherical
chart (`exists_kruskalSph_eq`), where the metric pulls back to the Kruskal metric; the axis is reached by
continuity. Hence, on the whole Kruskal manifold `{X² - T² > -1} × S²`:

* `kruskalC_isVacuumSolution`: the Kruskal metric solves the vacuum Einstein equations;
* `kretschmann_kruskalC`: the Kretschmann scalar is `48 M²/r⁶`, `r = krC M z`.
-/

open Matrix Real Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- **Every point off the rotation axis is in the image of the spherical chart.** -/
lemma exists_kruskalSph_eq {z : Fin 4 → ℝ} (hz : z ∈ kruskalC) (hax : 0 < z 1 ^ 2 + z 2 ^ 2) :
    ∃ y ∈ kruskalU, kruskalSph y = z := by
  have hq : 0 < rhoSq z := hz.1
  have hqdef : rhoSq z = z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 := rfl
  set ρ := √(rhoSq z) with hρdef
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hq
  have hρ2 : ρ ^ 2 = rhoSq z := Real.sq_sqrt hq.le
  -- the horizontal radius
  set w : ℂ := ⟨z 1, z 2⟩ with hw
  have hσ2 : ‖w‖ ^ 2 = z 1 ^ 2 + z 2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]; ring
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hσ2
    linarith
  have hσ0 : 0 < ‖w‖ := norm_pos_iff.2 hw0
  -- the polar angle
  have hlt : (z 3 / ρ) ^ 2 < 1 := by
    rw [div_pow, div_lt_one (by positivity), hρ2, hqdef]
    linarith
  have habs := abs_lt.1 (sq_lt_one_iff_abs_lt_one _ |>.1 hlt)
  have hcos : cos (arccos (z 3 / ρ)) = z 3 / ρ := cos_arccos habs.1.le habs.2.le
  have hsin : sin (arccos (z 3 / ρ)) = ‖w‖ / ρ := by
    rw [sin_arccos]
    have h1 : 1 - (z 3 / ρ) ^ 2 = (‖w‖ / ρ) ^ 2 := by
      rw [div_pow, div_pow, hσ2, hρ2, hqdef]
      field_simp
      ring
    rw [h1, Real.sqrt_sq (div_pos hσ0 hρ0).le]
  have hcφ : cos (Complex.arg w) = z 1 / ‖w‖ := Complex.cos_arg hw0
  have hsφ : sin (Complex.arg w) = z 2 / ‖w‖ := Complex.sin_arg w
  have hexp : exp (log ρ) = ρ := exp_log hρ0
  refine ⟨![z 0, log ρ, arccos (z 3 / ρ), Complex.arg w], ⟨?_, ?_, ?_⟩, ?_⟩
  · show -1 < log ρ ^ 2 - z 0 ^ 2
    have h2 : log ρ = 1 / 2 * log (rhoSq z) := by
      rw [hρdef, Real.log_sqrt hq.le]; ring
    rw [h2]
    exact hz.2
  · show 0 < arccos (z 3 / ρ)
    exact arccos_pos.2 habs.2
  · show arccos (z 3 / ρ) < π
    exact arccos_lt_pi.2 habs.1
  · ext i
    fin_cases i
    · rfl
    · show exp (log ρ) * (sin (arccos (z 3 / ρ)) * cos (Complex.arg w)) = z 1
      rw [hexp, hsin, hcφ]
      field_simp
    · show exp (log ρ) * (sin (arccos (z 3 / ρ)) * sin (Complex.arg w)) = z 2
      rw [hexp, hsin, hsφ]
      field_simp
    · show exp (log ρ) * cos (arccos (z 3 / ρ)) = z 3
      rw [hexp, hcos]
      field_simp

/-- Points near an axis point, moved in the direction `x¹`, are off the axis. -/
lemma off_axis_of_line {z : Fin 4 → ℝ} (h1 : z 1 = 0) (h2 : z 2 = 0) {t : ℝ} (ht : t ≠ 0) :
    0 < (z + t • (Pi.single 1 1 : Fin 4 → ℝ)) 1 ^ 2 + (z + t • (Pi.single 1 1 : Fin 4 → ℝ)) 2 ^ 2 := by
  have e1 : (z + t • (Pi.single 1 1 : Fin 4 → ℝ)) 1 = t := by simp [h1]
  have e2 : (z + t • (Pi.single 1 1 : Fin 4 → ℝ)) 2 = 0 := by simp [h2]
  rw [e1, e2]
  positivity

/-- The Ricci tensor vanishes at the points off the axis. -/
theorem ricci_kruskalC_off_axis (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalC)
    (hax : 0 < z 1 ^ 2 + z 2 ^ 2) (b d : Fin 4) : ricci (kruskalCMetric M) b d z = 0 := by
  obtain ⟨y, hy, rfl⟩ := exists_kruskalSph_eq hz hax
  exact ricci_eq_zero_of_pullback (isCoordMetric_kruskalC M hM) (isChartChange_kruskalSph M hM) hy
    (fun b d => by
      rw [ricci_congr_on isOpen_kruskalU (fun y' _ => pullback_kruskalC_sph M y') hy]
      exact ricci_kruskal_eq_zero M hM hy b d) b d

/-- **The Ricci tensor vanishes on the whole Kruskal manifold.** -/
theorem ricci_kruskalC_eq_zero (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalC) (b d : Fin 4) :
    ricci (kruskalCMetric M) b d z = 0 := by
  by_cases hax : 0 < z 1 ^ 2 + z 2 ^ 2
  · exact ricci_kruskalC_off_axis M hM hz hax b d
  · have h1 : z 1 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
    have h2 : z 2 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
    have hf : ContinuousAt (ricci (kruskalCMetric M) b d) z :=
      (continuousOn_ricci (isCoordMetric_kruskalC M hM) b d).continuousAt
        (isOpen_kruskalC.mem_nhds hz)
    refine eq_of_continuousAt_of_eventually_line (h := fun _ => 0) (Pi.single 1 1) hf
      continuousAt_const ?_
    have hcc : Continuous fun t : ℝ => z + t • (Pi.single 1 1 : Fin 4 → ℝ) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hU : ∀ᶠ t in 𝓝 (0 : ℝ), z + t • (Pi.single 1 1 : Fin 4 → ℝ) ∈ kruskalC :=
      hcc.continuousAt.preimage_mem_nhds (by simpa using isOpen_kruskalC.mem_nhds hz)
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with t ht ht0
    exact ricci_kruskalC_off_axis M hM ht (off_axis_of_line h1 h2 ht0) b d

/-- **The Kruskal–Szekeres spacetime solves the vacuum Einstein equations on the whole manifold**
`{X² - T² > -1} × S²`. -/
theorem kruskalC_isVacuumSolution (hM : 0 < M) : IsVacuumSolution 0 (kruskalCMetric M) kruskalC :=
  ⟨isCoordMetric_kruskalC M hM, fun y hy μ ν => by
    simp [einsteinTensor, scalarCurvature, ricci_kruskalC_eq_zero M hM hy]⟩

/-- The Kretschmann scalar at the points off the axis. -/
theorem kretschmann_kruskalC_off_axis (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalC)
    (hax : 0 < z 1 ^ 2 + z 2 ^ 2) : kretschmann (kruskalCMetric M) z = 48 * M ^ 2 / krC M z ^ 6 := by
  obtain ⟨y, hy, rfl⟩ := exists_kruskalSph_eq hz hax
  rw [← kretschmann_pullback (isCoordMetric_kruskalC M hM) (isChartChange_kruskalSph M hM) hy,
    kretschmann_congr_on isOpen_kruskalU (fun y' _ => pullback_kruskalC_sph M y') hy,
    kretschmann_kruskal M hM hy, krC_kruskalSph]

/-- **The Kretschmann scalar is `48 M²/r⁶` on the whole Kruskal manifold.** -/
theorem kretschmann_kruskalC (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalC) :
    kretschmann (kruskalCMetric M) z = 48 * M ^ 2 / krC M z ^ 6 := by
  by_cases hax : 0 < z 1 ^ 2 + z 2 ^ 2
  · exact kretschmann_kruskalC_off_axis M hM hz hax
  · have h1 : z 1 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
    have h2 : z 2 = 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 2)]
    have hf : ContinuousAt (kretschmann (kruskalCMetric M)) z :=
      (continuousOn_kretschmann (isCoordMetric_kruskalC M hM)).continuousAt
        (isOpen_kruskalC.mem_nhds hz)
    have hh : ContinuousAt (fun w : Fin 4 → ℝ => 48 * M ^ 2 / krC M w ^ 6) z :=
      ContinuousAt.div continuousAt_const
        (((contDiffOn_krC M hM).continuousOn.continuousAt (isOpen_kruskalC.mem_nhds hz)).pow 6)
        (pow_ne_zero 6 (krC_pos M hM hz).ne')
    refine eq_of_continuousAt_of_eventually_line (Pi.single 1 1) hf hh ?_
    have hcc : Continuous fun t : ℝ => z + t • (Pi.single 1 1 : Fin 4 → ℝ) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hU : ∀ᶠ t in 𝓝 (0 : ℝ), z + t • (Pi.single 1 1 : Fin 4 → ℝ) ∈ kruskalC :=
      hcc.continuousAt.preimage_mem_nhds (by simpa using isOpen_kruskalC.mem_nhds hz)
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with t ht ht0
    exact kretschmann_kruskalC_off_axis M hM ht (off_axis_of_line h1 h2 ht0)

end Lightlike
