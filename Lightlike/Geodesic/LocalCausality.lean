import Lightlike.Geodesic.TimeBall
import Lightlike.Geodesic.ConeTrap

/-!
# Local causality in a time ball (Chruściel, Proposition 2.4.5)

Work in progress (causal stream, from fable3's plan): the uniform cone estimate on a compact set of
parameters (`exists_uniform_cone_estimate`).

Source read (pdftotext): P. T. Chruściel, *Elements of causality theory*, arXiv:1110.6706v1, section 2.4,
Proposition 2.4.5 and (2.4.6)–(2.4.7), p. 20; Lemma 2.4.8, p. 21; Lemma 2.4.9, p. 22. See
`docs/notes/local-causality-plan.md`.
-/

open Set Metric Filter Topology Matrix MeasureTheory

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ}

/-- **A uniform cone estimate.** Let `A u` be a family of matrices, continuous in `u` on a compact set `K`, and `ℓ` a
linear functional which is positive on every nonzero vector `w` with `wᵀ A(u) w ≤ 0` and `ℓ w ≥ 0`, for every `u ∈ K`.
Then there is `C` with `‖w‖ ≤ C ℓ(w)` for all such `w` and `u`. -/
theorem exists_uniform_cone_estimate {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    {A : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, ContinuousOn (fun u => A u i j) K)
    (ℓ : (Fin n → ℝ) →L[ℝ] ℝ)
    (hpos : ∀ u ∈ K, ∀ w : Fin n → ℝ, w ≠ 0 → w ⬝ᵥ (A u *ᵥ w) ≤ 0 → 0 ≤ ℓ w → 0 < ℓ w) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ K, ∀ w : Fin n → ℝ, w ⬝ᵥ (A u *ᵥ w) ≤ 0 → 0 ≤ ℓ w → ‖w‖ ≤ C * ℓ w := by
  set Q : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun p => p.2 ⬝ᵥ (A p.1 *ᵥ p.2) with hQ
  have hQc : ContinuousOn Q (K ×ˢ univ) := by
    have h1 : ∀ i j, ContinuousOn (fun p : (Fin n → ℝ) × (Fin n → ℝ) => A p.1 i j) (K ×ˢ univ) :=
      fun i j => (hA i j).comp continuousOn_fst (fun p hp => hp.1)
    simp only [hQ, dotProduct, mulVec]
    refine continuousOn_finsetSum _ fun i _ => ?_
    refine (continuous_apply i |>.comp continuous_snd).continuousOn.mul ?_
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact (h1 i j).mul (continuous_apply j |>.comp continuous_snd).continuousOn
  set S : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
    (K ×ˢ sphere (0 : Fin n → ℝ) 1) ∩ (Q ⁻¹' Iic 0 ∩ (fun p => ℓ p.2) ⁻¹' Ici 0) with hS
  have hcomp0 : IsCompact (K ×ˢ sphere (0 : Fin n → ℝ) 1) := hK.prod (isCompact_sphere 0 1)
  have hcl : IsClosed S := by
    have hQc' : ContinuousOn Q (K ×ˢ sphere (0 : Fin n → ℝ) 1) :=
      hQc.mono (prod_mono subset_rfl (subset_univ _))
    have h1 := hQc'.preimage_isClosed_of_isClosed hcomp0.isClosed (isClosed_Iic (a := (0 : ℝ)))
    have h2 : IsClosed ((fun p : (Fin n → ℝ) × (Fin n → ℝ) => ℓ p.2) ⁻¹' Ici 0) :=
      isClosed_Ici.preimage (ℓ.continuous.comp continuous_snd)
    have : S = ((K ×ˢ sphere (0 : Fin n → ℝ) 1) ∩ Q ⁻¹' Iic 0) ∩
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => ℓ p.2) ⁻¹' Ici 0 := by
      rw [hS, inter_assoc]
    rw [this]
    exact h1.inter h2
  have hcomp : IsCompact S := hcomp0.of_isClosed_subset hcl inter_subset_left
  by_cases hne : S.Nonempty
  · obtain ⟨p0, hp0, hmin⟩ := hcomp.exists_isMinOn hne (ℓ.continuous.comp continuous_snd).continuousOn
    have hp0' := hp0
    obtain ⟨⟨hu0, hw0⟩, hq0, hl0⟩ := hp0'
    have hw0ne : p0.2 ≠ 0 := by
      intro h; rw [mem_sphere_zero_iff_norm, h, norm_zero] at hw0; exact zero_ne_one hw0
    have hm : 0 < ℓ p0.2 := hpos p0.1 hu0 p0.2 hw0ne hq0 hl0
    refine ⟨1 / ℓ p0.2, by positivity, fun u hu w hw hlw => ?_⟩
    by_cases hw0 : w = 0
    · simp [hw0]
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    set w1 : Fin n → ℝ := ‖w‖⁻¹ • w with hw1
    have hmem : (u, w1) ∈ S := by
      refine ⟨⟨hu, ?_⟩, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, hw1, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
      · show w1 ⬝ᵥ (A u *ᵥ w1) ≤ 0
        rw [hw1, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hw
      · show 0 ≤ ℓ w1
        rw [hw1, map_smul, smul_eq_mul]
        positivity
    have h1 : ℓ p0.2 ≤ ℓ w1 := hmin hmem
    rw [hw1, map_smul, smul_eq_mul] at h1
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm]
    calc ‖w‖ * ℓ p0.2 ≤ ‖w‖ * (‖w‖⁻¹ * ℓ w) := mul_le_mul_of_nonneg_left h1 hwn.le
      _ = ℓ w := by field_simp
  · refine ⟨1, one_pos, fun u hu w hw hlw => ?_⟩
    by_contra hcon
    have hw0 : w ≠ 0 := by
      intro h; apply hcon; simp [h]
    have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
    apply hne
    refine ⟨(u, ‖w‖⁻¹ • w), ⟨hu, ?_⟩, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
    · show (‖w‖⁻¹ • w) ⬝ᵥ (A u *ᵥ (‖w‖⁻¹ • w)) ≤ 0
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hw
    · show 0 ≤ ℓ (‖w‖⁻¹ • w)
      rw [map_smul, smul_eq_mul]
      positivity

/-- **A Lipschitz function with almost everywhere positive derivative increases strictly** from its initial value:
`G t > G a` for `t ∈ (a, b]`. -/
theorem lt_of_ae_deriv_pos {G : ℝ → ℝ} {a b : ℝ} {K : NNReal} (hG : LipschitzOnWith K G (Icc a b))
    (hd : ∀ᵐ t, t ∈ Ioo a b → ∃ G' : ℝ, HasDerivAt G G' t ∧ 0 < G') {t : ℝ} (ht : t ∈ Ioc a b) :
    G a < G t := by
  have hmono : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' → G s ≤ G s' := by
    intro s hs s' hs' hss
    have hsub : Icc s s' ⊆ Icc a b := Icc_subset_Icc hs.1 hs'.2
    have := Lightlike.Causal.sub_le_sub_of_ae_deriv_le (f := fun _ => (0 : ℝ)) (h := G) hss
      ((LipschitzWith.const (α := ℝ) (0 : ℝ)).lipschitzOnWith) (hG.mono hsub) (by
        filter_upwards [hd] with u hu hum
        obtain ⟨G', hG', hpos⟩ := hu ⟨lt_of_le_of_lt hs.1 hum.1, lt_of_lt_of_le hum.2 hs'.2⟩
        exact ⟨differentiableAt_const _, hG'.differentiableAt, by rw [deriv_const, hG'.deriv]; exact hpos.le⟩)
    simpa using this
  have hat : a ≤ t := ht.1.le
  refine lt_of_le_of_ne (hmono a ⟨le_rfl, hat.trans ht.2⟩ t ⟨hat, ht.2⟩ hat) fun heq => ?_
  -- `G` is constant on `[a, t]`
  have hconst : ∀ s ∈ Icc a t, G s = G a := fun s hs =>
    le_antisymm (heq ▸ hmono s ⟨hs.1, hs.2.trans ht.2⟩ t ⟨hat, ht.2⟩ hs.2)
      (hmono a ⟨le_rfl, hat.trans ht.2⟩ s ⟨hs.1, hs.2.trans ht.2⟩ hs.1)
  have hpos : (volume (Ioo a t)) ≠ 0 := by
    rw [Real.volume_Ioo]; simp [ht.1]
  have hae : ∀ᵐ s ∂(volume.restrict (Ioo a t)), s ∈ Ioo a t ∧ ∃ G' : ℝ, HasDerivAt G G' s ∧ 0 < G' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hd] with s hsm hs
    exact ⟨hsm, hs ⟨hsm.1, lt_of_lt_of_le hsm.2 ht.2⟩⟩
  have hne : (volume.restrict (Ioo a t)) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact hpos
  have : (ae (volume.restrict (Ioo a t))).NeBot := ae_neBot.2 hne
  obtain ⟨s, hsm, G', hG', hG'pos⟩ := hae.exists
  have hev : G =ᶠ[𝓝 s] fun _ => G a := by
    filter_upwards [Ioo_mem_nhds hsm.1 hsm.2] with u hu
    exact hconst u (Ioo_subset_Icc_self hu)
  have h0 : HasDerivAt G 0 s := (hasDerivAt_const s (G a)).congr_of_eventuallyEq hev
  exact hG'pos.ne' (hG'.unique h0)

end Lightlike.Geodesic
