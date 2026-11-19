import Lightlike.GR.StaticSphericalRicci
import Lightlike.GR.Einstein

/-!
# Schwarzschild-anti-de Sitter solves the vacuum equations with `Λ = -3/L²`

`ds² = -f dt² + dr²/f + r² dΩ²` with `f(r) = 1 - 2M/r + r²/L²` (`sadsF`, `sadsMetric = ssMetric (sadsF M L)`) on
`r > 0`, `f ≠ 0`, `0 < θ < π` has Ricci tensor `-(3/L²) g` (`ricci_sads`) and scalar curvature `-12/L²`, hence
`G + Λ g = 0` with `Λ = -3/L²` (`sads_isVacuumSolution`); for `L → ∞` formally Schwarzschild. It is not a solution with
`Λ = 0` for `M`, `L` finite (`sads_not_vacuumSolution_zero`: the Ricci tensor is `-(3/L²) g ≠ 0`).

Built on the general static spherical Ricci tensor of `StaticSphericalRicci` (`ricci_ss_ij`).

Gap row G3-022. Compared with D. Harlow, *Jerusalem Lectures on Black Holes and Quantum Information*, arXiv:1409.1231
(pdftotext), section 6.4, eqs. (6.30)-(6.32), p. 79: \"the AdS_{d+1} version of the Schwarzschild geometry, which is the unique spherically
symmetric solution of Einstein's equation with negative vacuum energy\", `ds² = -f dt² + dr²/f + r² dΩ²_{d-1}`,
`f = r² + 1 - α/r^{d-2}` (`r_ads = 1`), `α = 16πGM/((d-1)Ω_{d-1})`. For `d = 3` and `r_ads = L` general this is `sadsF` with `α = 2M`
(`M` here is the Schwarzschild mass parameter). The source states uniqueness and the form of `f`; the Lean statement is that this metric
solves `G + Λ g = 0` (not uniqueness). See `docs/notes/g3-022-ads-source.md`.
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

lemma isOpen_ssU {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ioi 0)) : IsOpen (ssU f) := by
  have hc : ContinuousOn (fun y : Fin 4 → ℝ => f (y 1)) {y | 0 < y 1} :=
    hf.comp (continuous_apply 1).continuousOn (fun y hy => hy)
  have h1 : IsOpen {y : Fin 4 → ℝ | 0 < y 1 ∧ f (y 1) ≠ 0} :=
    hc.isOpen_inter_preimage (isOpen_lt continuous_const (continuous_apply 1)) isOpen_ne
  have h2 := h1.inter ((isOpen_lt (continuous_const : Continuous fun _ : Fin 4 → ℝ => (0 : ℝ))
    (continuous_apply 2)).inter (isOpen_lt (continuous_apply 2) (continuous_const : Continuous fun _ : Fin 4 → ℝ => π)))
  convert h2 using 1
  ext y
  simp [ssU, and_assoc]

/-- The static spherical metric is a coordinate metric on `ssU f` for `f` smooth on `r > 0`. -/
theorem isCoordMetric_ss {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Set.Ioi 0)) : IsCoordMetric (ssMetric f) (ssU f) := by
  have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 1) (ssU f) :=
    (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
  have hθ : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 2 := by fun_prop
  have hfs : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => f (y 1)) (ssU f) :=
    hf.comp hr (fun y hy => hy.1)
  refine isCoordMetric_diagonal (fun y => ![-f (y 1), 1 / f (y 1), y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2])
    (isOpen_ssU hf.continuousOn) (fun i => ?_) (fun y hy i => ?_)
  · fin_cases i
    · exact hfs.neg
    · exact contDiffOn_const.div hfs (fun y hy => hy.2.1)
    · exact hr.pow 2
    · exact (hr.pow 2).mul ((Real.contDiff_sin.comp hθ).pow 2).contDiffOn
  · have hr0 : y 1 ≠ 0 := hy.1.ne'
    have hs := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
    fin_cases i <;> simp [hr0, hy.2.1, hs]

/-- `f(r) = 1 - 2M/r + r²/L²`. -/
def sadsF (M L : ℝ) (r : ℝ) : ℝ := 1 - 2 * M / r + r ^ 2 / L ^ 2

lemma sadsF_hasDeriv (M L : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (sadsF M L) (2 * M / r ^ 2 + 2 * r / L ^ 2) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * M / r) (-(2 * M / r ^ 2)) r := by
    have := (hasDerivAt_const r (2 * M)).div (hasDerivAt_id' r) hr.ne'
    refine this.congr_deriv ?_
    field_simp; ring
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2 / L ^ 2) (2 * r / L ^ 2) r := by
    have := (hasDerivAt_pow 2 r).div_const (L ^ 2)
    refine this.congr_deriv ?_
    simp
  have := ((hasDerivAt_const r (1 : ℝ)).sub h1).add h2
  refine this.congr_deriv ?_
  ring

lemma sadsF1_hasDeriv (M L : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r : ℝ => 2 * M / r ^ 2 + 2 * r / L ^ 2) (-(4 * M / r ^ 3) + 2 / L ^ 2) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * M / r ^ 2) (-(4 * M / r ^ 3)) r := by
    have := (hasDerivAt_const r (2 * M)).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr.ne')
    refine this.congr_deriv ?_
    field_simp; ring
  have h2 : HasDerivAt (fun r : ℝ => 2 * r / L ^ 2) (2 / L ^ 2) r := by
    have := ((hasDerivAt_id' r).const_mul 2).div_const (L ^ 2)
    simpa using this
  exact h1.add h2

lemma sadsF_contDiffOn (M L : ℝ) : ContDiffOn ℝ ∞ (sadsF M L) (Set.Ioi 0) := by
  unfold sadsF
  exact (contDiffOn_const.sub (contDiffOn_const.div contDiffOn_id (fun r hr => (Set.mem_Ioi.1 hr).ne'))).add
    ((contDiffOn_id.pow 2).div_const _)

/-- Schwarzschild-AdS in coordinates `(t, r, θ, φ)`. -/
abbrev sadsMetric (M L : ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := ssMetric (sadsF M L)

/-- **The Ricci tensor of Schwarzschild-AdS is `-(3/L²) g`.** -/
theorem ricci_sads (M L : ℝ) (hL : L ≠ 0) {y : Fin 4 → ℝ} (hy : y ∈ ssU (sadsF M L)) (σ ν : Fin 4) :
    ricci (sadsMetric M L) σ ν y = -(3 / L ^ 2) * sadsMetric M L y σ ν := by
  have hA : ∀ r, 0 < r → HasDerivAt (sadsF M L) (2 * M / r ^ 2 + 2 * r / L ^ 2) r :=
    fun r hr => sadsF_hasDeriv M L hr
  have hB : ∀ r, 0 < r → HasDerivAt (fun r : ℝ => 2 * M / r ^ 2 + 2 * r / L ^ 2)
      (-(4 * M / r ^ 3) + 2 / L ^ 2) r := fun r hr => sadsF1_hasDeriv M L hr
  have hg := isCoordMetric_ss (sadsF_contDiffOn M L)
  have hU := isOpen_ssU (sadsF_contDiffOn M L).continuousOn
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : sadsF M L (y 1) ≠ 0 := hy.2.1
  fin_cases σ <;> fin_cases ν
  · have := ricci_ss_00 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 0 0 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 0 0
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_01 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 0 1 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 0 1
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_02 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 0 2 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 0 2
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_03 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 0 3 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 0 3
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_10 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 1 0 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 1 0
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_11 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 1 1 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 1 1
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_12 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 1 2 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 1 2
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_13 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 1 3 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 1 3
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_20 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 2 0 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 2 0
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_21 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 2 1 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 2 1
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_22 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 2 2 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 2 2
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_23 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 2 3 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 2 3
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_30 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 3 0 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 3 0
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_31 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 3 1 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 3 1
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_32 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 3 2 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 3 2
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring
  · have := ricci_ss_33 _ _ _ hA hB hy hU hg
    show ricci (ssMetric (sadsF M L)) 3 3 y = -(3 / L ^ 2) * ssMetric (sadsF M L) y 3 3
    rw [this]
    simp [ssMetric, sadsF, Matrix.diagonal_apply]
    try field_simp
    try ring

/-- The scalar curvature of Schwarzschild-AdS is `-12/L²`. -/
theorem scalarCurvature_sads (M L : ℝ) (hL : L ≠ 0) {y : Fin 4 → ℝ} (hy : y ∈ ssU (sadsF M L)) :
    scalarCurvature (sadsMetric M L) y = -(12 / L ^ 2) := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : sadsF M L (y 1) ≠ 0 := hy.2.1
  have hs : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  have hinv := ssMetric_inv (sadsF M L) hy
  unfold scalarCurvature
  simp only [sadsMetric, hinv, ricci_sads M L hL hy, Fin.sum_univ_four]
  simp [ssMetric, Matrix.diagonal_apply]
  field_simp
  ring

/-- **Schwarzschild-AdS solves the vacuum Einstein equations with `Λ = -3/L²`**: `G + Λ g = 0`. -/
theorem sads_isVacuumSolution (M L : ℝ) (hL : L ≠ 0) :
    IsVacuumSolution (-(3 / L ^ 2)) (sadsMetric M L) (ssU (sadsF M L)) :=
  ⟨isCoordMetric_ss (sadsF_contDiffOn M L), fun y hy μ ν => by
    simp only [einsteinTensor, scalarCurvature_sads M L hL hy, ricci_sads M L hL hy]
    ring⟩

/-- **Wrong-model control.** Schwarzschild-AdS is not a vacuum solution with `Λ = 0`. -/
theorem sads_not_vacuumSolution_zero (M L : ℝ) (hL : L ≠ 0) (hne : (ssU (sadsF M L)).Nonempty) :
    ¬ IsVacuumSolution 0 (sadsMetric M L) (ssU (sadsF M L)) := by
  intro h
  obtain ⟨y, hy⟩ := hne
  have := h.2 y hy 2 2
  simp only [einsteinTensor, scalarCurvature_sads M L hL hy, ricci_sads M L hL hy] at this
  simp [sadsMetric, ssMetric] at this
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hL2 : L ≠ 0 := hL
  field_simp at this
  have : 0 < y 1 ^ 2 := by positivity
  linarith

end Lightlike
