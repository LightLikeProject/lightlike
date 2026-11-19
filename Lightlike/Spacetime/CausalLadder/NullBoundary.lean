import Mathlib

/-!
# The boundary of a set with a cone property is Lebesgue-null

Let `K` be the open cone `{D | ∃ s ∈ (0, s₀), ‖D - s V‖ < s ε}` around a vector `V ≠ 0` in `ℝⁿ`
(`ε < ‖V‖`). Let `A` be a set such that, in an open set `Ω`, `a ∈ A` and `a - b ∈ K` give `b ∈ A`
(a past set for the cone `K`). Then `frontier A ∩ Ω` is Lebesgue-null.

At a point `b` of the frontier no point of `b + K` is in the closure of `A`, since otherwise a whole
neighbourhood of `b` would lie in `A`. So the density of the frontier at `b` is at most `1 - θ` with
`θ > 0` the proportion of a small ball occupied by the cone, while by Lebesgue's density theorem it is
`1` at almost every point of the frontier. This is the local step of the null horismos of task
`T-GE2-P11` (Hawking–Ellis: the boundary of a past set is a Lipschitz hypersurface).

Supporting lemma for the causal ladder; no catalogue entry.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal Pointwise

namespace Lightlike

variable {n : ℕ}

/-- The open cone `{D | ∃ s ∈ (0, s₀), ‖D - s V‖ < s ε}` around `V`. -/
def openCone (V : Fin n → ℝ) (ε s₀ : ℝ) : Set (Fin n → ℝ) :=
  {D | ∃ s : ℝ, 0 < s ∧ s < s₀ ∧ ‖D - s • V‖ < s * ε}

/-- The cone is open. -/
theorem isOpen_openCone (V : Fin n → ℝ) (ε s₀ : ℝ) : IsOpen (openCone V ε s₀) := by
  have : openCone V ε s₀ = ⋃ s ∈ Ioo 0 s₀, ball (s • V) (s * ε) := by
    ext D
    simp only [openCone, mem_setOf_eq, mem_iUnion, mem_ball, dist_eq_norm, mem_Ioo]
    constructor
    · rintro ⟨s, h0, h1, h2⟩; exact ⟨s, ⟨h0, h1⟩, h2⟩
    · rintro ⟨s, ⟨h0, h1⟩, h2⟩; exact ⟨s, h0, h1, h2⟩
  rw [this]
  exact isOpen_biUnion fun s _ => isOpen_ball

/-- The untruncated cone. -/
def fullCone (V : Fin n → ℝ) (ε : ℝ) : Set (Fin n → ℝ) :=
  {D | ∃ s : ℝ, 0 < s ∧ ‖D - s • V‖ < s * ε}

theorem smul_mem_fullCone {V : Fin n → ℝ} {ε : ℝ} {D : Fin n → ℝ} (hD : D ∈ fullCone V ε) {r : ℝ}
    (hr : 0 < r) : r • D ∈ fullCone V ε := by
  obtain ⟨s, hs, h⟩ := hD
  refine ⟨r * s, mul_pos hr hs, ?_⟩
  have : r • D - (r * s) • V = r • (D - s • V) := by
    rw [smul_sub, smul_smul]
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_assoc]
  exact mul_lt_mul_of_pos_left h hr

/-- Below a radius, the truncated cone coincides with the full cone. -/
theorem openCone_inter_closedBall {V : Fin n → ℝ} {ε s₀ : ℝ} (hεV : ε < ‖V‖) {r : ℝ}
    (hr : r < s₀ * (‖V‖ - ε)) :
    openCone V ε s₀ ∩ closedBall 0 r = fullCone V ε ∩ closedBall 0 r := by
  ext D
  constructor
  · rintro ⟨⟨s, h0, h1, h2⟩, hb⟩; exact ⟨⟨s, h0, h2⟩, hb⟩
  · rintro ⟨⟨s, h0, h2⟩, hb⟩
    refine ⟨⟨s, h0, ?_, h2⟩, hb⟩
    have hD : ‖D‖ ≤ r := by simpa using hb
    have h3 : s * ‖V‖ - s * ε ≤ ‖D‖ := by
      have := norm_sub_norm_le (s • V) D
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos h0, norm_sub_rev] at this
      linarith
    have h4 : s * (‖V‖ - ε) ≤ r := by nlinarith
    have hpos : 0 < ‖V‖ - ε := by linarith
    by_contra hs
    push Not at hs
    have : s₀ * (‖V‖ - ε) ≤ s * (‖V‖ - ε) := mul_le_mul_of_nonneg_right hs hpos.le
    linarith

/-- **The cone occupies a fixed proportion of every small ball.** -/
theorem exists_cone_fraction {V : Fin n → ℝ} {ε s₀ : ℝ} (hV : V ≠ 0) (hε : 0 < ε) (hεV : ε < ‖V‖)
    (hs₀ : 0 < s₀) :
    ∃ θ : ℝ≥0∞, 0 < θ ∧ ∃ r₁ : ℝ, 0 < r₁ ∧ ∀ r : ℝ, 0 < r → r < r₁ →
      volume (openCone V ε s₀ ∩ closedBall 0 r) = θ * volume (closedBall (0 : Fin n → ℝ) r) := by
  set m1 : ℝ≥0∞ := volume (fullCone V ε ∩ closedBall 0 1) with hm1
  set v1 : ℝ≥0∞ := volume (closedBall (0 : Fin n → ℝ) 1) with hv1
  have hv0 : v1 ≠ 0 := (measure_closedBall_pos volume 0 one_pos).ne'
  have hvtop : v1 ≠ ⊤ := measure_closedBall_lt_top.ne
  have hFopen : IsOpen (fullCone V ε) := by
    have : fullCone V ε = ⋃ s ∈ Ioi (0 : ℝ), ball (s • V) (s * ε) := by
      ext D
      simp only [fullCone, mem_setOf_eq, mem_iUnion, mem_ball, dist_eq_norm, mem_Ioi]
      constructor
      · rintro ⟨s, h0, h2⟩; exact ⟨s, h0, h2⟩
      · rintro ⟨s, h0, h2⟩; exact ⟨s, h0, h2⟩
    rw [this]; exact isOpen_biUnion fun s _ => isOpen_ball
  have hm0 : m1 ≠ 0 := by
    have hne : (fullCone V ε ∩ ball 0 1).Nonempty := by
      set t : ℝ := 1 / (2 * (‖V‖ + 1)) with ht
      have htpos : 0 < t := by positivity
      refine ⟨t • V, ⟨t, htpos, ?_⟩, ?_⟩
      · simp [mul_pos htpos hε]
      · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]
        have : 0 < ‖V‖ + 1 := by positivity
        rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
        nlinarith [norm_nonneg V]
    have hpos : 0 < volume (fullCone V ε ∩ ball 0 1) :=
      (hFopen.inter isOpen_ball).measure_pos volume hne
    exact (hpos.trans_le (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))).ne'
  refine ⟨m1 / v1, ENNReal.div_pos hm0 hvtop, s₀ * (‖V‖ - ε), by nlinarith, fun r hr hrr => ?_⟩
  rw [openCone_inter_closedBall hεV hrr]
  have hset : fullCone V ε ∩ closedBall 0 r = r • (fullCone V ε ∩ closedBall 0 1) := by
    ext D
    constructor
    · rintro ⟨hD, hb⟩
      refine ⟨r⁻¹ • D, ⟨smul_mem_fullCone hD (inv_pos.2 hr), ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
        have : ‖D‖ ≤ r := by simpa using hb
        calc r⁻¹ * ‖D‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left this (inv_nonneg.2 hr.le)
          _ = 1 := inv_mul_cancel₀ hr.ne'
      · simp [smul_smul, hr.ne']
    · rintro ⟨D', ⟨hD', hb'⟩, rfl⟩
      refine ⟨smul_mem_fullCone hD' hr, ?_⟩
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have : ‖D'‖ ≤ 1 := by simpa using hb'
      nlinarith
  have hball : closedBall (0 : Fin n → ℝ) r = r • closedBall 0 1 := by
    rw [smul_closedBall _ _ zero_le_one]; simp [abs_of_pos hr]
  rw [hset, hball, Measure.addHaar_smul, Measure.addHaar_smul]
  rw [← hm1, ← hv1]
  set c : ℝ≥0∞ := ENNReal.ofReal |r ^ Module.finrank ℝ (Fin n → ℝ)| with hc
  calc c * m1 = c * (m1 / v1 * v1) := by rw [ENNReal.div_mul_cancel hv0 hvtop]
    _ = m1 / v1 * (c * v1) := by ring

/-- At a frontier point `b` of a past set no point of `b + K` lies in the closure of `A`. -/
theorem not_mem_closure_of_cone {V : Fin n → ℝ} {ε s₀ : ℝ} {Ω A : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω)
    (hP : ∀ a ∈ A, a ∈ Ω → ∀ b ∈ Ω, a - b ∈ openCone V ε s₀ → b ∈ A)
    {b : Fin n → ℝ} (hb : b ∈ frontier A) (hbΩ : b ∈ Ω) {c : Fin n → ℝ}
    (hc : c - b ∈ openCone V ε s₀) (hcΩ : c ∈ Ω) : c ∉ closure A := by
  intro hcl
  -- an open neighbourhood of `(c, b)` on which `a - b'` stays in the cone
  have hopen : IsOpen {p : (Fin n → ℝ) × (Fin n → ℝ) | p.1 - p.2 ∈ openCone V ε s₀} :=
    (isOpen_openCone V ε s₀).preimage (continuous_fst.sub continuous_snd)
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.1 (hopen.mem_nhds (show (c, b) ∈ _ from hc))
  obtain ⟨a, ⟨haU, haΩ⟩, haA⟩ := mem_closure_iff_nhds.1 hcl (U ∩ Ω) (inter_mem hU (hΩ.mem_nhds hcΩ))
  have hsub : W ∩ Ω ⊆ A := fun b' hb' =>
    hP a haA haΩ b' hb'.2 (hUW (show (a, b') ∈ U ×ˢ W from ⟨haU, hb'.1⟩))
  have : b ∈ interior A := mem_interior_iff_mem_nhds.2 (mem_of_superset (inter_mem hW (hΩ.mem_nhds hbΩ)) hsub)
  exact hb.2 this

/-- **The frontier of a past set for a cone is Lebesgue-null.** See the module docstring. -/
theorem volume_frontier_inter_eq_zero {V : Fin n → ℝ} {ε s₀ : ℝ} (hV : V ≠ 0) (hε : 0 < ε)
    (hεV : ε < ‖V‖) (hs₀ : 0 < s₀) {Ω A : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (hP : ∀ a ∈ A, a ∈ Ω → ∀ b ∈ Ω, a - b ∈ openCone V ε s₀ → b ∈ A) :
    volume (frontier A ∩ Ω) = 0 := by
  set Z := frontier A ∩ Ω with hZ
  have hZmeas : MeasurableSet Z := isClosed_frontier.measurableSet.inter hΩ.measurableSet
  obtain ⟨θ, hθ, r₁, hr₁, hfrac⟩ := exists_cone_fraction hV hε hεV hs₀
  have hdens := IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div
    (volume : Measure (Fin n → ℝ)) Z 1
  have hfalse : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)).restrict Z, False := by
    filter_upwards [hdens, ae_restrict_mem hZmeas] with x hx hxZ
    have hlim := hx (ι := ℝ) (l := 𝓝[>] 0) (fun _ => x) id tendsto_id
      (by filter_upwards [self_mem_nhdsWithin] with r hr
          simpa using (mem_Ioi.1 hr).le)
    obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ x hxZ.2
    -- for small `r` the density ratio plus `θ` is at most `1`
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        volume (Z ∩ closedBall x r) / volume (closedBall x r) + θ ≤ 1 := by
      have hsmall : Ioo (0 : ℝ) (min r₁ ρ) ∈ 𝓝[>] (0 : ℝ) :=
        Ioo_mem_nhdsGT (lt_min hr₁ hρ)
      filter_upwards [hsmall] with r hr
      have hr0 : 0 < r := hr.1
      have hrr₁ : r < r₁ := hr.2.trans_le (min_le_left _ _)
      have hrρ : r < ρ := hr.2.trans_le (min_le_right _ _)
      set B := closedBall x r with hB
      set T : Set (Fin n → ℝ) := (fun p => p - x) ⁻¹' (openCone V ε s₀ ∩ closedBall 0 r) with hT
      have hTmeas : MeasurableSet T :=
        ((isOpen_openCone V ε s₀).measurableSet.inter measurableSet_closedBall).preimage
          (measurable_id.sub_const x)
      have hTB : T ⊆ B := fun p hp => by
        have := hp.2
        simpa [hB, mem_closedBall, dist_eq_norm] using this
      have hdisj : Disjoint (Z ∩ B) T := by
        rw [Set.disjoint_left]
        rintro p ⟨hpZ, hpB⟩ hpT
        have hpΩ : p ∈ Ω := hρΩ (by
          have : dist p x ≤ r := by simpa [hB] using hpB
          exact lt_of_le_of_lt this hrρ)
        have hcone : p - x ∈ openCone V ε s₀ := hpT.1
        exact not_mem_closure_of_cone hΩ hP hxZ.1 hxZ.2 hcone hpΩ (frontier_subset_closure hpZ.1)
      have hvolT : volume T = θ * volume B := by
        have h1 : volume T = volume (openCone V ε s₀ ∩ closedBall 0 r) := by
          have : T = (fun p => p + (-x)) ⁻¹' (openCone V ε s₀ ∩ closedBall 0 r) := by
            ext p; simp [hT, sub_eq_add_neg]
          rw [this, measure_preimage_add_right]
        rw [h1, hfrac r hr0 hrr₁, hB]
        congr 1
        exact (Measure.addHaar_closedBall_center volume x r).symm
      have hsum : volume (Z ∩ B) + θ * volume B ≤ volume B := by
        rw [← hvolT, ← measure_union hdisj hTmeas]
        exact measure_mono (union_subset inter_subset_right hTB)
      have hb0 : volume B ≠ 0 := (measure_closedBall_pos volume x hr0).ne'
      have hbtop : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
      have : (volume (Z ∩ B) + θ * volume B) / volume B ≤ 1 := by
        rw [ENNReal.div_le_iff hb0 hbtop, one_mul]; exact hsum
      rwa [ENNReal.add_div, ENNReal.mul_div_cancel_right hb0 hbtop] at this
    have hle : 1 + θ ≤ 1 :=
      le_of_tendsto (hlim.add_const θ) hbound
    exact absurd hle (not_le.2 (ENNReal.lt_add_right ENNReal.one_ne_top hθ.ne'))
  have : ((volume : Measure (Fin n → ℝ)).restrict Z) univ = 0 := by
    have := (ae_iff.1 hfalse)
    simpa using this
  simpa [Measure.restrict_apply_univ] using this

end Lightlike
