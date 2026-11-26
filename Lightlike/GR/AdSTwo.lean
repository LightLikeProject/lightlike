import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Spacetime.Causal.TimeOrientation
import Lightlike.Spacetime.Causal.Ladder
import Lightlike.Spacetime.Causal.OpenSegment
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Anti-de Sitter space in two dimensions as a manifold, and its time orientation

Global `AdS₂` of radius `1` in the conformal coordinates `(t, ρ)`: the strip `-π/2 < ρ < π/2`, `t ∈ ℝ`, an open subset of
`ℝ²`, with the metric `(1/cos²ρ)(-dt² + dρ²)` (the metric of `adsGlobal` with `r = tan ρ`, `AdSConformal.lean`, in
dimension two). `adsTwoMetric` is the Lorentzian metric of the manifold `adsTwoOpen` (`openMetric`) and `adsTwoOrientation`
the time orientation `∂_t`.
-/

open Matrix Real Set Filter Topology Manifold Bundle
open scoped ContDiff

noncomputable section

namespace Lightlike

/-- The strip `-π/2 < ρ < π/2` of the conformal coordinates `(t, ρ)`. -/
def adsTwoU : Set (Fin 2 → ℝ) := {y | -(π / 2) < y 1 ∧ y 1 < π / 2}

theorem isOpen_adsTwoU : IsOpen adsTwoU :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter (isOpen_lt (continuous_apply 1) continuous_const)

lemma cos_pos_of_mem_adsTwoU {y : Fin 2 → ℝ} (hy : y ∈ adsTwoU) : 0 < cos (y 1) :=
  cos_pos_of_mem_Ioo ⟨hy.1, hy.2⟩

/-- The metric `(1/cos²ρ) diag(-1, 1)` of `AdS₂`. -/
def adsTwoCMetric (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal ![-(1 / cos (y 1) ^ 2), 1 / cos (y 1) ^ 2]

lemma contDiffOn_adsTwoFactor : ContDiffOn ℝ ∞ (fun y : Fin 2 → ℝ => 1 / cos (y 1) ^ 2) adsTwoU := by
  refine contDiffOn_const.div ?_ fun y hy => pow_ne_zero 2 (cos_pos_of_mem_adsTwoU hy).ne'
  exact (Real.contDiff_cos.comp (by fun_prop : ContDiff ℝ ∞ fun y : Fin 2 → ℝ => y 1)).pow 2 |>.contDiffOn

theorem isCoordMetric_adsTwo : IsCoordMetric adsTwoCMetric adsTwoU := by
  refine isCoordMetric_diagonal _ isOpen_adsTwoU (fun i => ?_) fun x hx i => ?_
  · fin_cases i
    · simpa using contDiffOn_adsTwoFactor.neg
    · simpa using contDiffOn_adsTwoFactor
  · have := cos_pos_of_mem_adsTwoU hx
    fin_cases i <;> simp <;> positivity

theorem adsTwo_isLorentzian : IsLorentzianCoordMetric adsTwoCMetric adsTwoU :=
  ⟨isCoordMetric_adsTwo, fun y hy => by
    have hc := cos_pos_of_mem_adsTwoU hy
    refine ⟨diagonal ![1 / cos (y 1), 1 / cos (y 1)], ?_, ?_⟩
    · rw [Matrix.det_diagonal]
      exact (Finset.prod_ne_zero_iff.mpr fun i _ => by fin_cases i <;> simp <;> positivity).isUnit
    · ext i j
      simp only [adsTwoCMetric, eta, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, etaDiag,
        Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> simp <;> field_simp⟩

/-- Global `AdS₂` as an open subset of `ℝ²`. -/
def adsTwoOpen : TopologicalSpace.Opens (Fin 2 → ℝ) := ⟨adsTwoU, isOpen_adsTwoU⟩

/-- **Global anti-de Sitter space in two dimensions**: the Lorentzian metric `(1/cos²ρ)(-dt² + dρ²)` on the strip. -/
def adsTwoMetric : LorentzianMetric 𝓘(ℝ, Fin 2 → ℝ) adsTwoOpen 2 :=
  openMetric adsTwoOpen adsTwoCMetric adsTwo_isLorentzian

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 200000 in
/-- **The time orientation `∂_t` of `AdS₂`.** -/
def adsTwoOrientation : Causal.TimeOrientation adsTwoMetric where
  X _ := Pi.single 0 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    have e : ∀ y : adsTwoOpen, ((trivializationAt (Fin 2 → ℝ) (TangentSpace 𝓘(ℝ, Fin 2 → ℝ)) x)
        ⟨y, (Pi.single 0 1 : Fin 2 → ℝ)⟩).2 = Pi.single 0 1 := fun y => by
      have hb : y ∈ (trivializationAt (Fin 2 → ℝ) (TangentSpace 𝓘(ℝ, Fin 2 → ℝ)) x).baseSet := by
        simp [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
      have h1 : (trivializationAt (Fin 2 → ℝ) (TangentSpace 𝓘(ℝ, Fin 2 → ℝ)) x).continuousLinearMapAt ℝ y
          (Pi.single 0 1 : Fin 2 → ℝ) =
          ((trivializationAt (Fin 2 → ℝ) (TangentSpace 𝓘(ℝ, Fin 2 → ℝ)) x)
            ⟨y, (Pi.single 0 1 : Fin 2 → ℝ)⟩).2 := by
        rw [Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hb]
      rw [opens_continuousLinearMapAt] at h1
      exact h1.symm
    simp only [e]
    exact contMDiffAt_const
  timelike x := by
    have hc := cos_pos_of_mem_adsTwoU x.2
    show matForm (adsTwoCMetric x.1) (Pi.single 0 1) (Pi.single 0 1) < 0
    rw [matForm_apply]
    simp [adsTwoCMetric, Fin.sum_univ_two]
    positivity

/-- The `AdS₂` metric on a vector with components `(a, b)` at a point of the strip is `(b² - a²) / cos² ρ`. -/
lemma adsTwoCMetric_form (y : Fin 2 → ℝ) (v w : Fin 2 → ℝ) :
    matForm (adsTwoCMetric y) v w = (1 / cos (y 1) ^ 2) * (-(v 0 * w 0) + v 1 * w 1) := by
  rw [matForm_apply]
  simp [adsTwoCMetric, Fin.sum_univ_two]
  ring

/-- A segment of the strip whose direction `(a, b)` has `|b| < a` is a future-directed timelike segment. -/
theorem adsTwo_segment_chron {p v : Fin 2 → ℝ} (hp : p ∈ adsTwoU) (hq : p + v ∈ adsTwoU)
    (hv : |v 1| < v 0) :
    (⟨p + v, hq⟩ : adsTwoOpen) ∈ Causal.chronFuture adsTwoOrientation ⟨p, hp⟩ := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, p + t • v ∈ adsTwoU := fun t ht => by
    obtain ⟨h1, h2⟩ := hp
    obtain ⟨h3, h4⟩ := hq
    simp only [Pi.add_apply] at h3 h4
    show -(π / 2) < p 1 + t * v 1 ∧ p 1 + t * v 1 < π / 2
    have a1 := mul_nonneg (sub_nonneg.2 ht.2) (show 0 ≤ p 1 + π / 2 by linarith)
    have a2 := mul_nonneg ht.1 (show 0 ≤ p 1 + v 1 + π / 2 by linarith)
    have b1 := mul_nonneg (sub_nonneg.2 ht.2) (show 0 ≤ π / 2 - p 1 by linarith)
    have b2 := mul_nonneg ht.1 (show 0 ≤ π / 2 - (p 1 + v 1) by linarith)
    constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
  refine Causal.mem_chronFuture_of_segment hseg adsTwoOrientation fun t ht => ?_
  have hc := cos_pos_of_mem_adsTwoU (hseg t ht)
  have hv0 : 0 < v 0 := lt_of_le_of_lt (abs_nonneg _) hv
  have hb : v 1 ^ 2 < v 0 ^ 2 := by simpa using sq_lt_sq.2 (by rwa [abs_of_pos hv0])
  have hX : adsTwoOrientation.X (Causal.segCurve adsTwoOpen p v hseg t) = Pi.single 0 1 := rfl
  rw [hX, adsTwoCMetric_form, adsTwoCMetric_form]
  have hpos : 0 < 1 / cos ((p + t • v) 1) ^ 2 := by positivity
  constructor
  · nlinarith [mul_pos hpos (sub_pos.2 hb)]
  · have h00 : (Pi.single 0 1 : Fin 2 → ℝ) 0 = 1 := by simp
    have h10 : (Pi.single 0 1 : Fin 2 → ℝ) 1 = 0 := by simp
    rw [h00, h10]
    nlinarith [mul_pos hpos hv0]

lemma mem_adsTwoU_of_abs_lt {a b : ℝ} (h : |b| < π / 2) : (![a, b] : Fin 2 → ℝ) ∈ adsTwoU := by
  obtain ⟨h1, h2⟩ := abs_lt.1 h
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- **`AdS₂` is not globally hyperbolic**: the causal diamond `J⁺(0, 0) ∩ J⁻(4, 0)` contains the point `(2, ρ)` for every
`|ρ| < π/2` (it is reached from `(0, 0)` by the segment of direction `(2, ρ)` and reaches `(4, 0)` by the segment of
direction `(2, -ρ)`, both timelike since `|ρ| < 2`, as the cones of `(1/cos²ρ)(-dt² + dρ²)` are those of Minkowski space),
so the continuous function `ρ` has no maximum on it, though a compact set has one and `ρ < π/2` on the strip. -/
theorem adsTwo_not_globallyHyperbolic : ¬ Causal.IsGloballyHyperbolic adsTwoOrientation := by
  intro hGH
  have h0 : (![0, 0] : Fin 2 → ℝ) ∈ adsTwoU := mem_adsTwoU_of_abs_lt (by simp [Real.pi_pos])
  set x : adsTwoOpen := ⟨![0, 0], h0⟩ with hx
  have h4 : (![4, 0] : Fin 2 → ℝ) ∈ adsTwoU := mem_adsTwoU_of_abs_lt (by simp [Real.pi_pos])
  set y : adsTwoOpen := ⟨![4, 0], h4⟩ with hy
  have hK := hGH.2 x y
  -- the point (2, ρ) is in the diamond
  have hmem : ∀ ρ : ℝ, |ρ| < π / 2 → ∃ q : adsTwoOpen, q ∈ Causal.causalFuture adsTwoOrientation x ∩
      Causal.causalPast adsTwoOrientation y ∧ (q : Fin 2 → ℝ) 1 = ρ := by
    intro ρ hρ
    have hρ2 : |ρ| < 2 := lt_trans hρ (by linarith [Real.pi_lt_four])
    have hq0 : (![0, 0] + ![2, ρ] : Fin 2 → ℝ) ∈ adsTwoU := by
      have : (![0, 0] + ![2, ρ] : Fin 2 → ℝ) = ![2, ρ] := by ext i; fin_cases i <;> simp
      rw [this]; exact mem_adsTwoU_of_abs_lt hρ
    have hq1 : (![0, 0] + ![2, ρ] + ![2, -ρ] : Fin 2 → ℝ) ∈ adsTwoU := by
      have : (![0, 0] + ![2, ρ] + ![2, -ρ] : Fin 2 → ℝ) = ![4, 0] := by ext i; fin_cases i <;> simp <;> norm_num
      rw [this]; exact h4
    have c1 := adsTwo_segment_chron (p := ![0, 0]) (v := ![2, ρ]) h0 hq0 (by simpa using hρ2)
    have c2 := adsTwo_segment_chron (p := ![0, 0] + ![2, ρ]) (v := ![2, -ρ]) hq0 hq1
      (by simpa [abs_neg] using hρ2)
    have ey : (⟨![0, 0] + ![2, ρ] + ![2, -ρ], hq1⟩ : adsTwoOpen) = y := Subtype.ext (by
      simp only [hy]; ext i; fin_cases i <;> simp <;> norm_num)
    rw [ey] at c2
    refine ⟨⟨![0, 0] + ![2, ρ], hq0⟩, ⟨Causal.chron_subset_causal _ _ c1, Causal.chron_subset_causal _ _ c2⟩, ?_⟩
    simp
  obtain ⟨q₀, hq₀, -⟩ := hmem 0 (by simp [Real.pi_pos])
  obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn ⟨q₀, hq₀⟩
    (f := fun q : adsTwoOpen => (q : Fin 2 → ℝ) 1)
    (by exact (continuous_apply 1).comp continuous_subtype_val |>.continuousOn)
  have hlt : (m : Fin 2 → ℝ) 1 < π / 2 := m.2.2
  obtain ⟨q, hq, hqρ⟩ := hmem (((m : Fin 2 → ℝ) 1 + π / 2) / 2) (by
    rw [abs_lt]; constructor
    · have := m.2.1; linarith [Real.pi_pos]
    · linarith)
  have h2 : (q : Fin 2 → ℝ) 1 ≤ (m : Fin 2 → ℝ) 1 := hmax hq
  rw [hqρ] at h2
  linarith

end Lightlike
