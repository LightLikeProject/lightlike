import Lightlike.PL.IndexTheta

/-!
# Checks of the θ configuration

The unit circle split into its upper and lower halves at `1` and `-1`, with the centre `0` as the point `Ω`, is a θ
configuration (`circleTheta`): this shows that the hypotheses of `Theta.lemma_9_14` are satisfiable. Wrong-model check:
with `Ω = 2` the segment from `-1` to `Ω` crosses the circle at `1`, so it meets the curve at a point other than `-1`,
and the field `segQ` of the structure fails.
-/

open Complex unitInterval Real Set

namespace Lightlike.PL

lemma expPi_eq_iff (a b : ℝ) :
    exp ((π : ℂ) * Complex.I * (a : ℂ)) = exp ((π : ℂ) * Complex.I * (b : ℂ)) ↔ ∃ m : ℤ, a = b + 2 * m := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h : (π : ℂ) * Complex.I * ((a : ℂ) - b - 2 * m) = 0 := by linear_combination hm
    have hne : (π : ℂ) * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := (mul_eq_zero.1 h).resolve_left hne
    have h2 : (a : ℂ) = b + 2 * m := by linear_combination this
    exact_mod_cast h2
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]; push_cast; ring

lemma norm_expPi (t : ℝ) : ‖exp ((π : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  have : (π : ℂ) * Complex.I * (t : ℂ) = ((π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

/-- The upper half of the unit circle from `1` to `-1`. -/
noncomputable def upperArc : Path (1 : ℂ) (-1) where
  toFun t := exp ((π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
  source' := by simp
  target' := by simp
  continuous_toFun := by fun_prop

/-- The lower half of the unit circle from `-1` to `1`. -/
noncomputable def lowerArc : Path (-1 : ℂ) 1 where
  toFun t := exp ((π : ℂ) * Complex.I * ((1 + (t : ℝ) : ℝ) : ℂ))
  source' := by simp
  target' := by
    have : (π : ℂ) * Complex.I * ((1 + ((1 : I) : ℝ) : ℝ) : ℂ) = 2 * π * Complex.I := by
      rw [show ((1 : I) : ℝ) = 1 from rfl]; push_cast; ring
    simp only [this, Complex.exp_two_pi_mul_I]
  continuous_toFun := by fun_prop

lemma upperArc_injective : Function.Injective upperArc := by
  intro s t h
  obtain ⟨m, hm⟩ := (expPi_eq_iff s t).1 h
  have h1 := s.2; have h2 := t.2
  have h3 : (m : ℝ) < 1 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
  have h4 : (-1 : ℝ) < m := by nlinarith [h1.1, h1.2, h2.1, h2.2]
  have h5 : m = 0 := by
    have : m < 1 := by exact_mod_cast h3
    have : -1 < m := by exact_mod_cast h4
    omega
  exact Subtype.ext (by rw [hm, h5]; simp)

lemma lowerArc_injective : Function.Injective lowerArc := by
  intro s t h
  obtain ⟨m, hm⟩ := (expPi_eq_iff (1 + s) (1 + t)).1 h
  have h1 := s.2; have h2 := t.2
  have h3 : (m : ℝ) < 1 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
  have h4 : (-1 : ℝ) < m := by nlinarith [h1.1, h1.2, h2.1, h2.2]
  have h5 : m = 0 := by
    have : m < 1 := by exact_mod_cast h3
    have : -1 < m := by exact_mod_cast h4
    omega
  exact Subtype.ext (by rw [h5] at hm; simpa using hm)

lemma upper_one : upperArc 1 = -1 := upperArc.target
lemma upper_zero : upperArc 0 = 1 := upperArc.source
lemma lower_zero : lowerArc 0 = -1 := lowerArc.source
lemma lower_one : lowerArc 1 = 1 := lowerArc.target

lemma arcs_disj : range upperArc ∩ range lowerArc = ({1, -1} : Set ℂ) := by
  ext z
  constructor
  · rintro ⟨⟨s, rfl⟩, ⟨t, ht⟩⟩
    obtain ⟨m, hm⟩ := (expPi_eq_iff s (1 + t)).1 ht.symm
    have h1 := s.2; have h2 := t.2
    have h3 : (m : ℝ) < 1 := by nlinarith [h1.1, h1.2, h2.1, h2.2]
    have h4 : (-2 : ℝ) < m := by nlinarith [h1.1, h1.2, h2.1, h2.2]
    have h5 : m = 0 ∨ m = -1 := by
      have : m < 1 := by exact_mod_cast h3
      have : -2 < m := by exact_mod_cast h4
      omega
    rcases h5 with h5 | h5
    · rw [h5] at hm
      have hs1 : (s : ℝ) = 1 := by simp at hm; linarith [h1.2, h2.1]
      have : s = 1 := Subtype.ext hs1
      right; simp [this]
    · rw [h5] at hm
      have hs0 : (s : ℝ) = 0 := by simp at hm; linarith [h1.1, h2.2]
      have : s = 0 := Subtype.ext hs0
      left; rw [this, upper_zero]
  · rintro (rfl | rfl)
    · exact ⟨⟨0, upper_zero⟩, ⟨1, lower_one⟩⟩
    · exact ⟨⟨1, upper_one⟩, ⟨0, lower_zero⟩⟩

lemma norm_of_mem_circle {z : ℂ} (hz : z ∈ range upperArc ∪ range lowerArc) : ‖z‖ = 1 := by
  rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact norm_expPi _
  · exact norm_expPi _

lemma seg_one_zero : segment ℝ (1 : ℂ) 0 ∩ (range upperArc ∪ range lowerArc) = {1} := by
  ext z
  constructor
  · rintro ⟨⟨a, b, ha, hb, hab, rfl⟩, hz⟩
    have hn := norm_of_mem_circle hz
    simp only [smul_zero, add_zero, Complex.real_smul, mul_one] at hn ⊢
    rw [Complex.norm_real, Real.norm_of_nonneg ha] at hn
    simp [hn]
  · rintro rfl
    exact ⟨left_mem_segment ℝ _ _, Or.inl ⟨0, upper_zero⟩⟩

lemma seg_neg_one_zero : segment ℝ (-1 : ℂ) 0 ∩ (range upperArc ∪ range lowerArc) = {-1} := by
  ext z
  constructor
  · rintro ⟨⟨a, b, ha, hb, hab, rfl⟩, hz⟩
    have hn := norm_of_mem_circle hz
    simp only [smul_zero, add_zero, Complex.real_smul] at hn ⊢
    have : ‖(a : ℂ) * (-1)‖ = a := by simp [Real.norm_of_nonneg ha]
    rw [this] at hn
    simp [hn]
  · rintro rfl
    exact ⟨left_mem_segment ℝ _ _, Or.inl ⟨1, upper_one⟩⟩

/-- A concrete θ configuration: the unit circle split into its upper and lower halves at `1` and `-1`, with the
centre `0` as the point `Ω` (the segments from `1` and `-1` to the centre meet the circle only at their ends). -/
noncomputable def circleTheta : Theta where
  P := 1
  Q := -1
  Ω := 0
  γ₁ := upperArc
  γ₂ := lowerArc
  inj₁ := upperArc_injective
  inj₂ := lowerArc_injective
  disj := arcs_disj
  segP := seg_one_zero
  segQ := seg_neg_one_zero
  hΩ := fun h => by
    have := norm_of_mem_circle h
    simp at this

/-- Wrong model: moving `Ω` to `2` makes the segment from `-1` to `Ω` cross the circle at `1`, so it meets the curve
at a point other than `-1`, and the field `segQ` fails. -/
example : segment ℝ (-1 : ℂ) 2 ∩ (range upperArc ∪ range lowerArc) ≠ {-1} := by
  intro h
  have h1 : (1 : ℂ) ∈ segment ℝ (-1 : ℂ) 2 ∩ (range upperArc ∪ range lowerArc) :=
    ⟨⟨1 / 3, 2 / 3, by norm_num, by norm_num, by norm_num, by simp [Complex.real_smul]; norm_num⟩,
      Or.inl ⟨0, upper_zero⟩⟩
  rw [h] at h1
  simp at h1
  norm_num at h1

/-- The curve of the concrete configuration is the unit circle. -/
example : circleTheta.curve = range upperArc ∪ range lowerArc := rfl

end Lightlike.PL
