import Lightlike.Regge.Conv3.DihedralDeriv
import Lightlike.Regge.Linear.Taylor1D

/-!
# A uniform second-order Taylor bound for the dihedral angle in the squared lengths

On a compact set of admissible squared-length tuples (positive hinge, non-degenerate faces, angle
neither `0` nor `π`), the dihedral angle `dihSq` equals its first-order expansion `dihSq'` up to a
constant times the square of the perturbation, uniformly in the base point.

## Main results

* `Valid`, `isOpen_valid`: the admissible tuples form an open set.
* `contDiffAt_Dh`: the first variation `dihSq'` is `C¹` in the base lengths and the direction.
* `dihSq_taylor`: `|dihSq (L + δ) - dihSq L - dihSq' L δ| ≤ M ‖δ‖²` uniformly on compacts.
-/

open Real Set Metric

namespace Lightlike.Regge.Conv3


/-- The first variation as a function of the base lengths and the direction. -/
noncomputable def Dh (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) : ℝ :=
  dihSq' (p.1 0) (p.1 1) (p.1 2) (p.1 3) (p.1 4) (p.1 5) (p.2 0) (p.2 1) (p.2 2) (p.2 3) (p.2 4) (p.2 5)

/-- The base lengths are admissible: positive hinge, non-degenerate faces, angle not `0`, `π`. -/
def Valid (L : Fin 6 → ℝ) : Prop :=
  0 < L 0 ∧ 0 < Pp (L 0) (L 1) (L 2) ∧ 0 < Pp (L 0) (L 3) (L 4) ∧
    0 < 1 - cosSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) ^ 2

/-- The first variation `dihSq'` is continuously differentiable in the base lengths and the
direction at every admissible base point. -/
theorem contDiffAt_Dh {p : (Fin 6 → ℝ) × (Fin 6 → ℝ)} (hp : Valid p.1) : ContDiffAt ℝ 1 Dh p := by
  obtain ⟨ha, h1, h2, h3⟩ := hp
  unfold Dh dihSq' Nn' Pp' Nn Pp
  unfold cosSq Nn Pp at h3
  unfold Pp at h1 h2
  have ha' := ha.ne'
  have hpp : 0 < (p.1 1 - (p.1 1 + p.1 0 - p.1 2) ^ 2 / (4 * p.1 0)) * (p.1 3 - (p.1 3 + p.1 0 - p.1 4) ^ 2 / (4 * p.1 0)) := mul_pos h1 h2
  have hs : √(_ * _) ≠ 0 := (sqrt_pos.mpr hpp).ne'
  fun_prop (disch := first | assumption | positivity | skip)

/-- The admissible tuples form an open set. -/
theorem isOpen_valid : IsOpen {L : Fin 6 → ℝ | Valid L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  obtain ⟨ha, h1, h2, h3⟩ := hL
  have ha' : L 0 ≠ 0 := ha.ne'
  have hpp : Pp (L 0) (L 1) (L 2) * Pp (L 0) (L 3) (L 4) ≠ 0 := (mul_pos h1 h2).ne'
  have hsq : √(Pp (L 0) (L 1) (L 2) * Pp (L 0) (L 3) (L 4)) ≠ 0 := (sqrt_pos.mpr (mul_pos h1 h2)).ne'
  have k0 : ContinuousAt (fun L : Fin 6 → ℝ => L 0) L := (continuous_apply 0).continuousAt
  have k1 : ContinuousAt (fun L : Fin 6 → ℝ => L 1) L := (continuous_apply 1).continuousAt
  have k2 : ContinuousAt (fun L : Fin 6 → ℝ => L 2) L := (continuous_apply 2).continuousAt
  have k3 : ContinuousAt (fun L : Fin 6 → ℝ => L 3) L := (continuous_apply 3).continuousAt
  have k4 : ContinuousAt (fun L : Fin 6 → ℝ => L 4) L := (continuous_apply 4).continuousAt
  have k5 : ContinuousAt (fun L : Fin 6 → ℝ => L 5) L := (continuous_apply 5).continuousAt
  have c0 := k0
  have h4a : (fun L : Fin 6 → ℝ => 4 * L 0) L ≠ 0 := by simpa using ha'
  have c1 : ContinuousAt (fun L : Fin 6 → ℝ => Pp (L 0) (L 1) (L 2)) L :=
    k1.sub ((((k1.add k0).sub k2).pow 2).div (continuousAt_const.mul k0) h4a)
  have c2 : ContinuousAt (fun L : Fin 6 → ℝ => Pp (L 0) (L 3) (L 4)) L :=
    k3.sub ((((k3.add k0).sub k4).pow 2).div (continuousAt_const.mul k0) h4a)
  have hN : ContinuousAt (fun L : Fin 6 → ℝ => Nn (L 0) (L 1) (L 2) (L 3) (L 4) (L 5)) L :=
    (((k1.add k3).sub k5).div_const 2).sub
      ((((k1.add k0).sub k2).mul ((k3.add k0).sub k4)).div (continuousAt_const.mul k0) h4a)
  have c3 : ContinuousAt (fun L : Fin 6 → ℝ => 1 - cosSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) ^ 2) L :=
    continuousAt_const.sub ((hN.div (c1.mul c2).sqrt hsq).pow 2)
  have e0 := c0.eventually (lt_mem_nhds ha)
  have e1 := c1.eventually (lt_mem_nhds h1)
  have e2 := c2.eventually (lt_mem_nhds h2)
  have e3 := c3.eventually (lt_mem_nhds h3)
  exact (e0.and (e1.and (e2.and e3))).mono fun _ h => h

/-- The dihedral angle as a function of the tuple of squared lengths. -/
noncomputable def Dsq (L : Fin 6 → ℝ) : ℝ := dihSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5)

/-- `Dh` is homogeneous in the direction. -/
theorem Dh_smul (L δ : Fin 6 → ℝ) (c : ℝ) : Dh (L, c • δ) = c * Dh (L, δ) := by
  unfold Dh dihSq' Nn' Pp'
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Derivative of the dihedral angle along a line of admissible tuples. -/
theorem hasDerivAt_Dsq {L : Fin 6 → ℝ} (δ : Fin 6 → ℝ) (hL : Valid L) :
    HasDerivAt (fun ε : ℝ => Dsq (L + ε • δ)) (Dh (L, δ)) 0 := by
  obtain ⟨ha, h1, h2, h3⟩ := hL
  have hc1 : cosSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) ≠ 1 := fun h => by
    rw [h] at h3; norm_num at h3
  have hc2 : cosSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) ≠ -1 := fun h => by
    rw [h] at h3; norm_num at h3
  have := hasDerivAt_dihSq (a₁ := δ 0) (b₁ := δ 1) (c₁ := δ 2) (d₁ := δ 3) (e₁ := δ 4)
    (f₁ := δ 5) ha.ne' h1 h2 hc1 hc2
  simpa [Dsq, Dh] using this

/-- **Uniform second-order bound for the dihedral angle.** On a compact set of admissible
squared-length tuples there are `M` and `r > 0` such that
`|dihSq (L + δ) - dihSq L - dihSq' L δ| ≤ M ‖δ‖²` for every `L` in the set and `‖δ‖ ≤ r`. -/
theorem dihSq_taylor {K : Set (Fin 6 → ℝ)} (hK : IsCompact K) (hKV : ∀ L ∈ K, Valid L) :
    ∃ M r : ℝ, 0 < r ∧ ∀ L ∈ K, ∀ δ : Fin 6 → ℝ, ‖δ‖ ≤ r →
      |Dsq (L + δ) - Dsq L - Dh (L, δ)| ≤ M * ‖δ‖ ^ 2 := by
  obtain ⟨ρ, hρ, hρV⟩ := hK.exists_cthickening_subset_open isOpen_valid (fun L hL => hKV L hL)
  have hT : IsCompact (cthickening ρ K ×ˢ closedBall (0 : Fin 6 → ℝ) 1) :=
    hK.cthickening.prod (isCompact_closedBall _ _)
  have hopen : IsOpen {p : (Fin 6 → ℝ) × (Fin 6 → ℝ) | Valid p.1} :=
    isOpen_valid.preimage continuous_fst
  have hTS : cthickening ρ K ×ˢ closedBall (0 : Fin 6 → ℝ) 1 ⊆ {p | Valid p.1} :=
    fun p hp => hρV hp.1
  have hcd : ContDiffOn ℝ 1 Dh {p : (Fin 6 → ℝ) × (Fin 6 → ℝ) | Valid p.1} :=
    fun p hp => (contDiffAt_Dh hp).contDiffWithinAt
  have hcont := hcd.continuousOn_fderiv_of_isOpen hopen le_rfl
  obtain ⟨M, hM⟩ := hT.exists_bound_of_continuousOn (hcont.mono hTS)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨max M 0, min ρ 1, lt_min hρ one_pos, fun L hL δ hδ => ?_⟩
  have hδρ : ‖δ‖ ≤ ρ := hδ.trans (min_le_left _ _)
  have hδ1 : ‖δ‖ ≤ 1 := hδ.trans (min_le_right _ _)
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, L + t • δ ∈ cthickening ρ K := by
    intro t ht
    refine mem_cthickening_of_dist_le (L + t • δ) L ρ K hL ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖δ‖ ≤ 1 * ‖δ‖ := by gcongr; exact ht.2
      _ ≤ ρ := by linarith
  have hvalid : ∀ t ∈ Icc (0 : ℝ) 1, Valid (L + t • δ) := fun t ht => hρV (hmem t ht)
  by_cases hδ0 : δ = 0
  · subst hδ0
    have h0 : Dh (L, (0 : ℝ) • (0 : Fin 6 → ℝ)) = 0 * Dh (L, 0) := Dh_smul L 0 0
    simp only [zero_smul, zero_mul] at h0
    simp [h0]
  have hn : 0 < ‖δ‖ := norm_pos_iff.mpr hδ0
  set u : Fin 6 → ℝ := ‖δ‖⁻¹ • δ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hδu : δ = ‖δ‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  -- the base-point dependence of `Dh (·, u)` is Lipschitz with constant `M`
  have hdG : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => Dh (L + s • δ, u))
      (fderiv ℝ Dh (L + t • δ, u) (δ, 0)) t := by
    intro t ht
    have hp : Valid (L + t • δ) := hvalid t ht
    have hD : DifferentiableAt ℝ Dh (L + t • δ, u) :=
      (contDiffAt_Dh (p := (L + t • δ, u)) hp).differentiableAt one_ne_zero
    have hpath : HasDerivAt (fun s : ℝ => (L + s • δ, u)) (δ, (0 : Fin 6 → ℝ)) t := by
      refine HasDerivAt.prodMk ?_ (hasDerivAt_const t u)
      simpa using ((hasDerivAt_id t).smul_const δ).const_add L
    exact hD.hasFDerivAt.comp_hasDerivAt t hpath
  have hGb : ∀ t ∈ Icc (0 : ℝ) 1,
      |Dh (L + t • δ, δ) - Dh (L, δ)| ≤ max M 0 * ‖δ‖ ^ 2 * t := by
    intro t ht
    have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => Dh (L + s • δ, u))
      (f' := fun s => fderiv ℝ Dh (L + s • δ, u) (δ, 0)) (C := max M 0 * ‖δ‖) (a := 0) (b := t)
      (fun s hs => (hdG s ⟨hs.1, hs.2.trans ht.2⟩).hasDerivWithinAt) (fun s hs => by
        have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le.trans ht.2⟩
        have hpT : (L + s • δ, u) ∈ cthickening ρ K ×ˢ closedBall (0 : Fin 6 → ℝ) 1 :=
          ⟨hmem s hs', by simp [hu1]⟩
        calc ‖fderiv ℝ Dh (L + s • δ, u) (δ, 0)‖
            ≤ ‖fderiv ℝ Dh (L + s • δ, u)‖ * ‖((δ, 0) : (Fin 6 → ℝ) × (Fin 6 → ℝ))‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ max M 0 * ‖δ‖ := by
              have : ‖((δ, 0) : (Fin 6 → ℝ) × (Fin 6 → ℝ))‖ = ‖δ‖ := by simp [Prod.norm_def]
              rw [this]
              exact mul_le_mul_of_nonneg_right ((hM _ hpT).trans (le_max_left _ _)) (norm_nonneg _))
      t ⟨ht.1, le_rfl⟩
    have e1 : Dh (L + t • δ, δ) = ‖δ‖ * Dh (L + t • δ, u) := by
      have := Dh_smul (L + t • δ) u ‖δ‖
      rwa [← hδu] at this
    have e2 : Dh (L, δ) = ‖δ‖ * Dh (L, u) := by
      have := Dh_smul L u ‖δ‖
      rwa [← hδu] at this
    simp only [zero_smul, add_zero] at key
    rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos hn]
    rw [Real.norm_eq_abs, sub_zero] at key
    calc ‖δ‖ * |Dh (L + t • δ, u) - Dh (L, u)| ≤ ‖δ‖ * (max M 0 * ‖δ‖ * t) := by gcongr
      _ = _ := by ring
  -- integrate the first variation along the segment
  have hH : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun s : ℝ => Dsq (L + s • δ) - Dsq L - s * Dh (L, δ))
      (Dh (L + t • δ, δ) - Dh (L, δ)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => Dsq (L + s • δ)) (Dh (L + t • δ, δ)) t := by
      have h0 : HasDerivAt (fun ε : ℝ => Dsq (L + t • δ + ε • δ)) (Dh (L + t • δ, δ)) (t - t) := by
        rw [sub_self]; exact hasDerivAt_Dsq δ (hvalid t ht)
      have := h0.comp_sub_const t t
      convert this using 1
      funext s
      show Dsq (L + s • δ) = Dsq (L + t • δ + (s - t) • δ)
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := (h1.sub_const (Dsq L)).sub ((hasDerivAt_id t).mul_const (Dh (L, δ)))
    convert this using 1 <;> first | rfl | simp
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s : ℝ => Dsq (L + s • δ) - Dsq L - s * Dh (L, δ))
    (f' := fun t => Dh (L + t • δ, δ) - Dh (L, δ)) (C := max M 0 * ‖δ‖ ^ 2) (a := 0) (b := 1)
    (fun s hs => (hH s hs).hasDerivWithinAt) (fun s hs => by
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      rw [Real.norm_eq_abs]
      calc _ ≤ max M 0 * ‖δ‖ ^ 2 * s := hGb s hs'
        _ ≤ max M 0 * ‖δ‖ ^ 2 * 1 := by gcongr; exact hs.2.le
        _ = _ := mul_one _) 1 ⟨zero_le_one, le_rfl⟩
  simp only [zero_smul, add_zero, sub_self, zero_mul, sub_zero, one_smul, one_mul, Real.norm_eq_abs,
    mul_one, sub_zero] at key
  simpa using key

end Lightlike.Regge.Conv3
