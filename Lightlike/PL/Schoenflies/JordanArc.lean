import Mathlib
import Lightlike.PL.JordanCurve

/-!
# Long arcs of a Jordan curve

Row G3-188 (PL5), step 2 of the pass-4 plan.  `exists_arc_complement`: for a Jordan curve `f` and `ε > 0`
there is `δ > 0` such that for every parameter `t₀` the curve has a compact connected piece `B` (an arc)
that misses the points of the curve within `δ` of `f t₀` and contains every point of the curve at distance
`≥ ε` from `f t₀`.
-/

namespace Lightlike.PL.Schoenflies

open Set Metric

lemma circle_dist_eq (a b : Circle) : dist a b = ‖(a : ℂ) - b‖ := by
  rw [← dist_eq_norm]; rfl

/-- The chord `‖exp φ − 1‖` is at most `|φ|`. -/
lemma dist_mul_exp_le (t₀ : Circle) (φ : ℝ) : dist (t₀ * Circle.exp φ) t₀ ≤ |φ| := by
  rw [circle_dist_eq]
  have h : ((t₀ * Circle.exp φ : Circle) : ℂ) - (t₀ : ℂ) = (t₀ : ℂ) * (Complex.exp (Complex.I * φ) - 1) := by
    simp only [Circle.coe_mul, Circle.coe_exp]; rw [mul_comm Complex.I]; ring
  rw [h, norm_mul, Circle.norm_coe, one_mul]
  simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ))

/-- Away from a multiple of `2π` the chord is bounded below. -/
lemma exists_chord_lower {w : ℝ} (hw : 0 < w) (hw2 : w ≤ Real.pi) :
    ∃ c : ℝ, 0 < c ∧ ∀ (t₀ : Circle) (φ : ℝ), w ≤ φ → φ ≤ 2 * Real.pi - w →
      c ≤ dist (t₀ * Circle.exp φ) t₀ := by
  have hK : IsCompact (Icc w (2 * Real.pi - w)) := isCompact_Icc
  have hne : (Icc w (2 * Real.pi - w)).Nonempty := ⟨w, le_rfl, by linarith⟩
  obtain ⟨φ₀, hφ₀, hmin⟩ := hK.exists_isMinOn hne
    (f := fun φ => dist (Circle.exp φ) 1) (by fun_prop)
  refine ⟨dist (Circle.exp φ₀) 1, ?_, ?_⟩
  · rw [dist_pos]
    intro h1
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 h1
    have h2 : 0 < (n : ℝ) * (2 * Real.pi) := by rw [← hn]; linarith [hφ₀.1]
    have h3 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by rw [← hn]; linarith [hφ₀.2]
    have hpi := Real.pi_pos
    have h4 : (0 : ℝ) < n := by nlinarith
    have h5 : (n : ℝ) < 1 := by nlinarith
    have h6 : 0 < n := by exact_mod_cast h4
    have h7 : n < 1 := by exact_mod_cast h5
    omega
  · intro t₀ φ h1 h2
    have := hmin (show φ ∈ Icc w (2 * Real.pi - w) from ⟨h1, h2⟩)
    simp only [mem_ofPred_eq] at this
    calc dist (Circle.exp φ₀) 1 ≤ dist (Circle.exp φ) 1 := this
      _ = dist (t₀ * Circle.exp φ) t₀ := by
        rw [circle_dist_eq, circle_dist_eq]
        simp only [Circle.coe_mul, Circle.coe_one]
        have e : (t₀ : ℂ) * (Circle.exp φ : ℂ) - (t₀ : ℂ) = (t₀ : ℂ) * ((Circle.exp φ : ℂ) - 1) := by ring
        rw [e, norm_mul, Circle.norm_coe, one_mul]

/-- Points of the circle far apart are mapped to points far apart, by an injective continuous map. -/
lemma exists_sep {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f) {c : ℝ}
    (hc0 : 0 < c) : ∃ m : ℝ, 0 < m ∧ ∀ s t : Circle, c ≤ dist s t → m ≤ dist (f s) (f t) := by
  have hS : IsCompact {p : Circle × Circle | c ≤ dist p.1 p.2} :=
    (isClosed_le continuous_const (by fun_prop)).isCompact
  by_cases hne : {p : Circle × Circle | c ≤ dist p.1 p.2}.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne (f := fun p => dist (f p.1) (f p.2)) (by fun_prop)
    refine ⟨dist (f p.1) (f p.2), ?_, fun s t hst => hmin (show (s, t) ∈ _ from hst)⟩
    rw [dist_pos]
    intro h
    have := hi h
    have h2 : c ≤ dist p.1 p.2 := hp
    rw [this, dist_self] at h2
    linarith
  · refine ⟨1, one_pos, fun s t hst => ?_⟩
    exact absurd ⟨(s, t), hst⟩ hne

theorem exists_arc_complement {f : Circle → ℝ × ℝ} (hc : Continuous f) (hi : Function.Injective f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t₀ : Circle, ∃ B : Set (ℝ × ℝ), IsCompact B ∧ IsConnected B ∧ B ⊆ range f ∧
      (∀ z ∈ range f, dist z (f t₀) < δ → z ∉ B) ∧ (∀ z ∈ range f, z ∉ B → dist z (f t₀) < ε) := by
  obtain ⟨w', hw', hu⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  have hpi := Real.pi_pos
  set w : ℝ := min (w' / 2) (Real.pi / 2) with hw
  have hw0 : 0 < w := lt_min (half_pos hw') (half_pos hpi)
  have hwpi : w ≤ Real.pi / 2 := min_le_right _ _
  have hww' : w ≤ w' / 2 := min_le_left _ _
  obtain ⟨c, hc0, hcl⟩ := exists_chord_lower hw0 (by linarith)
  obtain ⟨m, hm0, hm⟩ := exists_sep hc hi hc0
  refine ⟨m, hm0, fun t₀ => ?_⟩
  set h : ℝ → ℝ × ℝ := fun φ => f (t₀ * Circle.exp φ) with hh
  have hhc : Continuous h := by rw [hh]; fun_prop
  refine ⟨h '' Icc w (2 * Real.pi - w), isCompact_Icc.image hhc,
    (isConnected_Icc (by linarith)).image h hhc.continuousOn, ?_, ?_, ?_⟩
  · rintro _ ⟨φ, -, rfl⟩; exact ⟨_, rfl⟩
  · rintro z ⟨t, rfl⟩ hz ⟨φ, ⟨h1, h2⟩, hφ⟩
    have ht : t₀ * Circle.exp φ = t := hi hφ
    have := hm t t₀ (by rw [← ht]; exact hcl t₀ φ h1 h2)
    linarith
  · rintro z ⟨t, rfl⟩ hz
    -- write `t = t₀ * exp φ` with `φ ∈ [-w, 2π - w)`
    set ψ := Complex.arg ((t₀⁻¹ * t : Circle) : ℂ) with hψ
    set φ := toIcoMod Real.two_pi_pos (-w) ψ with hφ
    have hmem : φ ∈ Ico (-w) (-w + 2 * Real.pi) := toIcoMod_mem_Ico Real.two_pi_pos _ _
    have hexp : Circle.exp φ = t₀⁻¹ * t := by
      have : φ = ψ - toIcoDiv Real.two_pi_pos (-w) ψ • (2 * Real.pi) := rfl
      rw [this, Circle.periodic_exp.sub_zsmul_eq, hψ, Circle.exp_arg]
    have ht : t = t₀ * Circle.exp φ := by rw [hexp]; group
    have hφw : φ < w := by
      by_contra hge
      apply hz
      refine ⟨φ, ⟨not_lt.1 hge, by linarith [hmem.2]⟩, ?_⟩
      rw [hh]; simp only []; rw [← ht]
    have habs : |φ| ≤ w := abs_le.2 ⟨by linarith [hmem.1], hφw.le⟩
    have hd : dist t t₀ < w' := by
      rw [ht]; exact lt_of_le_of_lt ((dist_mul_exp_le t₀ φ).trans habs) (by linarith)
    exact hu hd

end Lightlike.PL.Schoenflies
