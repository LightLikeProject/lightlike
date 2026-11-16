import Lightlike.PL.ArcApprox

/-!
# Trimming an arc outside two balls

A continuous arc from `pa` to `pb` has a subarc that starts on the sphere of radius `r` around `pa`,
ends on the sphere of radius `r` around `pb`, and stays outside the open balls of radius `r` around
the two points, provided the two balls are disjoint.

## Main results

* `exists_trim`: the subarc, as a pair of parameters `s < t`.
-/

open Set

namespace Lightlike.PL

/-- **The subarc between the last visit of the first ball and the first visit of the second.** -/
theorem exists_trim {γ : ℝ → ℝ × ℝ} (hγ : ContinuousOn γ (Icc 0 1)) {pa pb : ℝ × ℝ} {r : ℝ}
    (h0 : γ 0 = pa) (h1 : γ 1 = pb) (hr : 0 < r) (hab : 2 * r < dist pa pb) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧ dist (γ s) pa = r ∧ dist (γ t) pb = r ∧
      ∀ u ∈ Icc s t, r ≤ dist (γ u) pa ∧ r ≤ dist (γ u) pb := by
  have hda : ContinuousOn (fun t => dist (γ t) pa) (Icc 0 1) := (by fun_prop : Continuous fun p : ℝ × ℝ => dist p pa).comp_continuousOn hγ
  have hdb : ContinuousOn (fun t => dist (γ t) pb) (Icc 0 1) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ => dist p pb).comp_continuousOn hγ
  -- the first visit of the closed ball around `pb`
  set T : Set ℝ := Icc 0 1 ∩ (fun t => dist (γ t) pb) ⁻¹' Iic r with hT
  have hTclosed : IsClosed T := hdb.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset hTclosed inter_subset_left
  have hT1 : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by simp [h1, hr.le]⟩
  set t₁ := sInf T with ht₁
  have ht₁T : t₁ ∈ T := hTc.sInf_mem ⟨1, hT1⟩
  have ht₁le : ∀ u ∈ T, t₁ ≤ u := fun u hu => csInf_le hTc.bddBelow hu
  -- the last visit of the closed ball around `pa` before `t₁`
  set S : Set ℝ := Icc 0 t₁ ∩ (fun t => dist (γ t) pa) ⁻¹' Iic r with hS
  have hSclosed : IsClosed S :=
    (hda.mono (Icc_subset_Icc le_rfl (ht₁T.1.2))).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed inter_subset_left
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht₁T.1.1⟩, by simp [h0, hr.le]⟩
  set s₀ := sSup S with hs₀
  have hs₀S : s₀ ∈ S := hSc.sSup_mem ⟨0, h0S⟩
  have hs₀ge : ∀ u ∈ S, u ≤ s₀ := fun u hu => le_csSup hSc.bddAbove hu
  have hdist : r < dist pa pb - r := by linarith
  have hlt : s₀ < t₁ := by
    refine lt_of_le_of_ne hs₀S.1.2 fun h => ?_
    have h1' : dist (γ s₀) pa ≤ r := hs₀S.2
    have h2' : dist (γ t₁) pb ≤ r := ht₁T.2
    rw [h] at h1'
    have := dist_triangle_left pa pb (γ t₁)
    linarith
  have hub : ∀ u, s₀ < u → u ≤ t₁ → r < dist (γ u) pa := fun u hu1 hu2 => by
    by_contra hcon
    rw [not_lt] at hcon
    have := hs₀ge u ⟨⟨(le_trans hs₀S.1.1 hu1.le), hu2⟩, hcon⟩
    linarith
  have hua : ∀ u, s₀ ≤ u → u < t₁ → r < dist (γ u) pb := fun u hu1 hu2 => by
    by_contra hcon
    rw [not_lt] at hcon
    have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨le_trans hs₀S.1.1 hu1, le_trans hu2.le ht₁T.1.2⟩
    have := ht₁le u ⟨hu01, hcon⟩
    linarith
  have hs₁ : r ≤ dist (γ s₀) pa ∧ dist (γ s₀) pa ≤ r := by
    refine ⟨?_, hs₀S.2⟩
    have hcl : s₀ ∈ closure (Ioc s₀ t₁) := by rw [closure_Ioc hlt.ne]; exact ⟨le_rfl, hlt.le⟩
    refine ContinuousWithinAt.closure_le (f := fun _ => r) (g := fun t => dist (γ t) pa) hcl
      continuousWithinAt_const ?_ fun u hu => (hub u hu.1 hu.2).le
    exact (hda.mono (Icc_subset_Icc hs₀S.1.1 ht₁T.1.2) s₀ ⟨le_rfl, hlt.le⟩).mono Ioc_subset_Icc_self
  have ht₂ : r ≤ dist (γ t₁) pb ∧ dist (γ t₁) pb ≤ r := by
    refine ⟨?_, ht₁T.2⟩
    have hcl : t₁ ∈ closure (Ico s₀ t₁) := by rw [closure_Ico hlt.ne]; exact ⟨hlt.le, le_rfl⟩
    refine ContinuousWithinAt.closure_le (f := fun _ => r) (g := fun t => dist (γ t) pb) hcl
      continuousWithinAt_const ?_ fun u hu => (hua u hu.1 hu.2).le
    exact (hdb.mono (Icc_subset_Icc hs₀S.1.1 ht₁T.1.2) t₁ ⟨hlt.le, le_rfl⟩).mono Ico_subset_Icc_self
  refine ⟨s₀, t₁, hs₀S.1.1, hlt, ht₁T.1.2, le_antisymm hs₁.2 hs₁.1, le_antisymm ht₂.2 ht₂.1, ?_⟩
  intro u hu
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hu.1 with rfl | h
    · exact hs₁.1
    · exact (hub u h hu.2).le
  · rcases eq_or_lt_of_le hu.2 with rfl | h
    · exact ht₂.1
    · exact (hua u hu.1 h).le

end Lightlike.PL
