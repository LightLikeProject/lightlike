import Lightlike.PL.WeakJordanOuter

/-!
# Joining two closed sets by an arc inside an open connected set

Two disjoint closed sets `T` and `F`, each with a point in a connected open set `U`, are joined by an
arc in `U` that meets `T` only at its first end and `F` only at its second end.

## Main results

* `isArc_image_Icc`: a restriction of an injective continuous map is an arc.
* `exists_link`: the arc (Klazar, arXiv:2604.04296, Section 2, Claim 4: "there exists an arc
  `f_{e,g}` joining a point `e ∈ T'` to a point `g ∈ f₂'` in `D` such that
  `f_{e,g}' ∩ (T ∪ f₂[I]) = ∅`", from Propositions 1.9 and 1.18).
-/

open Set

namespace Lightlike.PL

/-- A restriction of an injective continuous map to a closed interval is an arc. -/
lemma isArc_image_Icc {γ : ℝ → ℝ × ℝ} (hc : ContinuousOn γ (Icc 0 1)) (hi : InjOn γ (Icc 0 1))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    IsArc (γ '' Icc s t) (γ s) (γ t) := by
  have hm : MapsTo (fun l : ℝ => s + l * (t - s)) (Icc 0 1) (Icc s t) := fun l hl =>
    ⟨by nlinarith [hl.1], by nlinarith [hl.2]⟩
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs ht
  refine ⟨fun l => γ (s + l * (t - s)), (hc.mono hsub).comp (by fun_prop) hm, ?_, by simp, ?_, ?_⟩
  · intro a ha b hb hab
    have := hi (hsub (hm ha)) (hsub (hm hb)) hab
    have h' : a * (t - s) = b * (t - s) := by linarith
    exact mul_right_cancel₀ (by linarith) h'
  · simp
  · ext y; constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨_, hm hl, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(u - s) / (t - s), ⟨div_nonneg (by linarith [hu.1]) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]; linarith [hu.2]
      · show γ (s + (u - s) / (t - s) * (t - s)) = γ u
        rw [div_mul_cancel₀ _ (by linarith : (t - s) ≠ 0)]; simp

/-- **An arc joining two closed sets inside an open connected set.** -/
theorem exists_link {U T F : Set (ℝ × ℝ)} (hU : IsOpen U) (hc : IsPreconnected U)
    (hT : IsClosed T) (hF : IsClosed F) (hTF : Disjoint T F) {e₀ g₀ : ℝ × ℝ} (he : e₀ ∈ T)
    (hg : g₀ ∈ F) (heU : e₀ ∈ U) (hgU : g₀ ∈ U) :
    ∃ e ∈ T, ∃ g ∈ F, ∃ B : Set (ℝ × ℝ), B ⊆ U ∧ IsArc B e g ∧ B ∩ T = {e} ∧ B ∩ F = {g} := by
  obtain ⟨l, h1, h2, h3⟩ := exists_chain_in_open hU hc heU hgU
  obtain ⟨s, hs, hs1, hs2, hs3⟩ := exists_simple_sub l e₀ g₀ h1 h2
  have hne : e₀ ≠ g₀ := fun h => hTF.ne_of_mem he hg h
  have hlen : 2 ≤ s.length := two_le_length hs1 hs2 hne
  obtain ⟨γ, hγc, hγi, hγ0, hγ1, hγimg⟩ := IsArc.chain hs hs1 hs2 hlen
  have hsU : chainSet s ⊆ U := hs3.trans h3
  have hdT : ContinuousOn (fun t => γ t) (Icc 0 1) := hγc
  -- the first time on `F`
  set TF : Set ℝ := Icc 0 1 ∩ γ ⁻¹' F with hTF'
  have hTFc : IsClosed TF := hγc.preimage_isClosed_of_isClosed isClosed_Icc hF
  have hTFcpt : IsCompact TF := isCompact_Icc.of_isClosed_subset hTFc inter_subset_left
  have h1TF : (1 : ℝ) ∈ TF := ⟨⟨zero_le_one, le_rfl⟩, by simpa [hγ1] using hg⟩
  set tg := sInf TF with htg
  have htgmem : tg ∈ TF := hTFcpt.sInf_mem ⟨1, h1TF⟩
  have htgle : ∀ u ∈ TF, tg ≤ u := fun u hu => csInf_le hTFcpt.bddBelow hu
  have h0 : (0 : ℝ) ∉ TF := fun h => hTF.ne_of_mem he (by simpa [hγ0] using h.2) rfl
  have htg0 : 0 < tg := lt_of_le_of_ne htgmem.1.1 (fun h => h0 (h ▸ htgmem))
  -- the last time on `T` before it
  set ST : Set ℝ := Icc 0 tg ∩ γ ⁻¹' T with hST
  have hSTc : IsClosed ST :=
    (hγc.mono (Icc_subset_Icc le_rfl htgmem.1.2)).preimage_isClosed_of_isClosed isClosed_Icc hT
  have hSTcpt : IsCompact ST := isCompact_Icc.of_isClosed_subset hSTc inter_subset_left
  have h0ST : (0 : ℝ) ∈ ST := ⟨⟨le_rfl, htg0.le⟩, by simpa [hγ0] using he⟩
  set se := sSup ST with hse
  have hsemem : se ∈ ST := hSTcpt.sSup_mem ⟨0, h0ST⟩
  have hsege : ∀ u ∈ ST, u ≤ se := fun u hu => le_csSup hSTcpt.bddAbove hu
  have hselt : se < tg := by
    refine lt_of_le_of_ne hsemem.1.2 fun h => ?_
    have h1 : γ se ∈ T := hsemem.2
    have h2 : γ tg ∈ F := htgmem.2
    rw [h] at h1
    exact hTF.ne_of_mem h1 h2 rfl
  have hse0 : 0 ≤ se := hsemem.1.1
  have hB := isArc_image_Icc hγc hγi hse0 hselt htgmem.1.2
  refine ⟨γ se, hsemem.2, γ tg, htgmem.2, γ '' Icc se tg, ?_, hB, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hsU (hγimg ▸ ⟨u, ⟨le_trans hse0 hu.1, le_trans hu.2 htgmem.1.2⟩, rfl⟩)
  · apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨⟨se, ⟨le_rfl, hselt.le⟩, rfl⟩, hsemem.2⟩, ?_⟩
    rintro _ ⟨⟨u, hu, rfl⟩, huT⟩
    have : u ≤ se := hsege u ⟨⟨le_trans hse0 hu.1, hu.2⟩, huT⟩
    rw [le_antisymm this hu.1]
  · apply Set.eq_singleton_iff_unique_mem.2
    refine ⟨⟨⟨tg, ⟨hselt.le, le_rfl⟩, rfl⟩, htgmem.2⟩, ?_⟩
    rintro _ ⟨⟨u, hu, rfl⟩, huF⟩
    have : tg ≤ u := htgle u ⟨⟨le_trans hse0 hu.1, le_trans hu.2 htgmem.1.2⟩, huF⟩
    rw [le_antisymm hu.2 this]

end Lightlike.PL
