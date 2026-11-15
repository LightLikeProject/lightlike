import Lightlike.Asymptotics.EPRL.Critical

/-!
# The exterior dihedral angle is the angle between the outward normals

For the Regge state the matrix `Q_a Q_b†` must be `cos Θ_e + i sin Θ_e (b̂_e · σ)` with `Θ_e` the
Regge angle, defined from the edge lengths by the dihedral angle formula. This file proves the
geometric input: `cos Θ_e = ⟨N_a, N_b⟩` (`cos_reggeAngle`).
-/

open Matrix Finset
open scoped RealInnerProductSpace

namespace Lightlike.Asymptotics.EPRL

/-- **Two-dimensional decomposition.** In `ℝ⁴`, let `t₁, t₂` be independent and let `N, B` be
orthogonal, `N` a unit vector and `B ≠ 0`, both orthogonal to `t₁, t₂`. Then every `V` orthogonal to
`t₁, t₂` is `(⟨V,B⟩/⟨B,B⟩) B + ⟨V,N⟩ N`. -/
lemma decomp2 {t₁ t₂ B N V : EuclideanSpace ℝ (Fin 4)} (hind : LinearIndependent ℝ ![t₁, t₂])
    (hN1 : ⟪N, t₁⟫ = 0) (hN2 : ⟪N, t₂⟫ = 0) (hB1 : ⟪B, t₁⟫ = 0) (hB2 : ⟪B, t₂⟫ = 0)
    (hV1 : ⟪V, t₁⟫ = 0) (hV2 : ⟪V, t₂⟫ = 0) (hNB : ⟪N, B⟫ = 0) (hN : ⟪N, N⟫ = 1) (hB : B ≠ 0) :
    V = (⟪V, B⟫ / ⟪B, B⟫) • B + ⟪V, N⟫ • N := by
  have hBB : ⟪B, B⟫ ≠ 0 := fun h => hB (inner_self_eq_zero.mp h)
  set Z : EuclideanSpace ℝ (Fin 4) := V - ((⟪V, B⟫ / ⟪B, B⟫) • B + ⟪V, N⟫ • N) with hZ
  suffices hZ0 : Z = 0 by
    rw [hZ, sub_eq_zero] at hZ0; exact hZ0
  by_contra hZne
  have ht1 : t₁ ≠ 0 := by
    intro h; have := hind.ne_zero 0; simp [h] at this
  set c : ℝ := ⟪t₂, t₁⟫ / ⟪t₁, t₁⟫ with hc
  set u₂ : EuclideanSpace ℝ (Fin 4) := t₂ - c • t₁ with hu₂
  have hu2ne : u₂ ≠ 0 := by
    intro h
    have := LinearIndependent.pair_iff.mp hind (-c) 1 (by rw [hu₂] at h; simpa [sub_eq_add_neg, neg_smul] using
      (by rw [add_comm]; simpa [sub_eq_add_neg, neg_smul] using h : -(c • t₁) + t₂ = 0))
    exact one_ne_zero this.2
  have h11 : ⟪t₁, t₁⟫ ≠ 0 := fun h => ht1 (inner_self_eq_zero.mp h)
  have hu21 : ⟪u₂, t₁⟫ = 0 := by
    rw [hu₂, inner_sub_left, real_inner_smul_left, hc]; field_simp; ring
  have hZ1 : ⟪Z, t₁⟫ = 0 := by
    rw [hZ, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hV1, hB1, hN1]
    simp
  have hZ2 : ⟪Z, t₂⟫ = 0 := by
    rw [hZ, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hV2, hB2, hN2]
    simp
  have hZu : ⟪Z, u₂⟫ = 0 := by
    rw [hu₂, inner_sub_right, real_inner_smul_right, hZ1, hZ2]; simp
  have hNB' : ⟪B, N⟫ = 0 := by rwa [real_inner_comm]
  have hZB : ⟪Z, B⟫ = 0 := by
    rw [hZ, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hNB]
    field_simp; ring
  have hZN : ⟪Z, N⟫ = 0 := by
    rw [hZ, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hN, hNB']
    simp
  have hu2B : ⟪u₂, B⟫ = 0 := by
    rw [hu₂, inner_sub_left, real_inner_smul_left, real_inner_comm B t₂, real_inner_comm B t₁, hB1, hB2]; simp
  have hu2N : ⟪u₂, N⟫ = 0 := by
    rw [hu₂, inner_sub_left, real_inner_smul_left, real_inner_comm N t₂, real_inner_comm N t₁, hN1, hN2]; simp
  have hNne : N ≠ 0 := fun h => by simp [h] at hN
  have hli : LinearIndependent ℝ ![t₁, u₂, B, N, Z] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i; fin_cases i <;> simp [ht1, hu2ne, hB, hNne, hZne]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
      all_goals simp
      all_goals first
        | assumption
        | (rwa [real_inner_comm])
  have := hli.fintype_card_le_finrank
  simp at this

/-- **The angle between the normals.** With `t₁, t₂` independent, `A, B` orthogonal to `t₁, t₂`
and unit vectors `N_a, N_b` orthogonal to `t₁, t₂` with `N_a ⟂ B`, `N_b ⟂ A`, `⟨N_a, A⟩ = -h_a < 0`
and `⟨N_b, B⟩ = -h_b < 0`: `⟨N_a, N_b⟩ = -⟨A, B⟩ / (‖A‖ ‖B‖)`. -/
lemma inner_normals {t₁ t₂ A B Na Nb : EuclideanSpace ℝ (Fin 4)} {ha hb : ℝ}
    (hind : LinearIndependent ℝ ![t₁, t₂])
    (hNa1 : ⟪Na, t₁⟫ = 0) (hNa2 : ⟪Na, t₂⟫ = 0) (hNb1 : ⟪Nb, t₁⟫ = 0) (hNb2 : ⟪Nb, t₂⟫ = 0)
    (hA1 : ⟪A, t₁⟫ = 0) (hA2 : ⟪A, t₂⟫ = 0) (hB1 : ⟪B, t₁⟫ = 0) (hB2 : ⟪B, t₂⟫ = 0)
    (hNa : ⟪Na, Na⟫ = 1) (hNb : ⟪Nb, Nb⟫ = 1) (hNaB : ⟪Na, B⟫ = 0) (hNbA : ⟪Nb, A⟫ = 0)
    (hNaA : ⟪Na, A⟫ = -ha) (hNbB : ⟪Nb, B⟫ = -hb) (hha : 0 < ha) (hhb : 0 < hb) :
    ⟪Na, Nb⟫ = -⟪A, B⟫ / (‖A‖ * ‖B‖) := by
  have hBne : B ≠ 0 := fun h => by simp [h] at hNbB; linarith
  have hAne : A ≠ 0 := fun h => by simp [h] at hNaA; linarith
  have hNbA' : ⟪A, Nb⟫ = 0 := by rw [real_inner_comm]; exact hNbA
  have hNaB' : ⟪B, Na⟫ = 0 := by rw [real_inner_comm]; exact hNaB
  have d1 := decomp2 hind hNa1 hNa2 hB1 hB2 hNb1 hNb2 hNaB hNa hBne
  have d2 := decomp2 hind hNa1 hNa2 hB1 hB2 hA1 hA2 hNaB hNa hBne
  have d3 := decomp2 hind hNb1 hNb2 hA1 hA2 hB1 hB2 hNbA hNb hAne
  have hAA : 0 < ⟪A, A⟫ := real_inner_self_pos.mpr hAne
  have hBB : 0 < ⟪B, B⟫ := real_inner_self_pos.mpr hBne
  have e1 : ⟪Nb, A⟫ = (⟪Nb, B⟫ / ⟪B, B⟫) * ⟪B, A⟫ + ⟪Nb, Na⟫ * ⟪Na, A⟫ := by
    have h := congrArg (fun v => ⟪v, A⟫) d1
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at h
    exact h
  have e2 : ⟪A, A⟫ = (⟪A, B⟫ / ⟪B, B⟫) * ⟪B, A⟫ + ⟪A, Na⟫ * ⟪Na, A⟫ := by
    have h := congrArg (fun v => ⟪v, A⟫) d2
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at h
    exact h
  have e3 : ⟪B, B⟫ = (⟪B, A⟫ / ⟪A, A⟫) * ⟪A, B⟫ + ⟪B, Nb⟫ * ⟪Nb, B⟫ := by
    have h := congrArg (fun v => ⟪v, B⟫) d3
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at h
    exact h
  rw [hNbA, hNbB, hNaA] at e1
  rw [real_inner_comm Na A, hNaA] at e2
  rw [real_inner_comm Nb B, hNbB] at e3
  rw [real_inner_comm A B] at e1 e2 e3
  rw [real_inner_comm Na Nb] at e1
  set ab := ⟪A, B⟫
  set c := ⟪Na, Nb⟫
  set AA := ⟪A, A⟫ with hAAd
  set BB := ⟪B, B⟫ with hBBd
  have hsA : ‖A‖ ^ 2 = AA := by rw [hAAd, real_inner_self_eq_norm_sq]
  have hsB : ‖B‖ ^ 2 = BB := by rw [hBBd, real_inner_self_eq_norm_sq]
  have hnA : 0 < ‖A‖ := norm_pos_iff.mpr hAne
  have hnB : 0 < ‖B‖ := norm_pos_iff.mpr hBne
  have hq1 : ha ^ 2 * BB = AA * BB - ab ^ 2 := by
    have e2' : AA = ab ^ 2 / BB + ha ^ 2 := by rw [e2]; ring
    have : AA * BB = ab ^ 2 + ha ^ 2 * BB := by rw [e2']; field_simp
    linarith
  have hq2 : hb ^ 2 * AA = AA * BB - ab ^ 2 := by
    have e3' : BB = ab ^ 2 / AA + hb ^ 2 := by rw [e3]; ring
    have : AA * BB = ab ^ 2 + hb ^ 2 * AA := by rw [e3']; field_simp
    linarith
  have hsq : (ha * ‖B‖) ^ 2 = (hb * ‖A‖) ^ 2 := by
    rw [mul_pow, mul_pow, hsA, hsB]; linarith
  have hh : ha * ‖B‖ = hb * ‖A‖ :=
    (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  have hc : c * ha * BB = -hb * ab := by
    have h0 : -hb / BB * ab = -hb * ab / BB := by ring
    have : c * ha = -hb * ab / BB := by linarith [e1]
    rw [this]; field_simp
  rw [eq_div_iff (by positivity)]
  have : c * ha * BB * ‖A‖ = -hb * ab * ‖A‖ := by rw [hc]
  rw [← hsB] at this
  have h2 : c * (ha * ‖B‖) * ‖B‖ * ‖A‖ = -(hb * ‖A‖) * ab := by linear_combination this
  rw [hh] at h2
  have h3 : (c * ‖A‖ * ‖B‖ + ab) * (hb * ‖A‖) = 0 := by linear_combination h2
  have h4 : hb * ‖A‖ ≠ 0 := by positivity
  have := (mul_eq_zero.mp h3).resolve_right h4
  linarith

open Lightlike.Regge4 in
/-- **The Regge angle is the angle between the outward normals:** `cos Θ_e = ⟨N_a, N_b⟩` for the
edge `e = ab`. -/
theorem cos_reggeAngle (σ : Simplex4) (e : Fin 10) :
    Real.cos (reggeAngle σ e) = ⟪outNormal σ (edgeSrc e), outNormal σ (edgeTgt e)⟫ := by
  obtain ⟨h01, h02, h12, h0s, h1s, h2s, h0t, h1t, h2t, hst⟩ := edge_distinct e
  have hℓ : ∀ a b, a ≠ b → simplexLength σ {a, b} = dist (σ.points a) (σ.points b) :=
    fun a b h => simplexLength_pair σ h
  set p := edgeTri e 0
  set q := edgeTri e 1
  set r := edgeTri e 2
  set a := edgeSrc e
  set b := edgeTgt e
  have hind := (affineIndependent_iff_linearIndependent_vsub ℝ σ.points p).mp σ.independent
  have hpair : LinearIndependent ℝ ![σ.points q - σ.points p, σ.points r - σ.points p] := by
    have := hind.comp (![⟨q, h01.symm⟩, ⟨r, h02.symm⟩] : Fin 2 → {x // x ≠ p}) (by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff])
    convert this using 1
    ext i : 1; fin_cases i <;> simp [vsub_eq_sub]
  have hG := gram_two_pos hpair
  have hG' : gram2 (simplexLength σ) p q r ≠ 0 := by
    rw [gram2_eq_inner σ.points hℓ]; exact hG.ne'
  set t₁ := σ.points q - σ.points p
  set t₂ := σ.points r - σ.points p
  set A := perp2 t₁ t₂ (σ.points a - σ.points p)
  set B := perp2 t₁ t₂ (σ.points b - σ.points p)
  have hNa1 : ⟪outNormal σ a, t₁⟫ = 0 := inner_outNormal_sub σ h1s h0s
  have hNa2 : ⟪outNormal σ a, t₂⟫ = 0 := inner_outNormal_sub σ h2s h0s
  have hNb1 : ⟪outNormal σ b, t₁⟫ = 0 := inner_outNormal_sub σ h1t h0t
  have hNb2 : ⟪outNormal σ b, t₂⟫ = 0 := inner_outNormal_sub σ h2t h0t
  have hA1 : ⟪A, t₁⟫ = 0 := inner_perp2_left hG.ne' _
  have hA2 : ⟪A, t₂⟫ = 0 := inner_perp2_right hG.ne' _
  have hB1 : ⟪B, t₁⟫ = 0 := inner_perp2_left hG.ne' _
  have hB2 : ⟪B, t₂⟫ = 0 := inner_perp2_right hG.ne' _
  have hNaB : ⟪outNormal σ a, B⟫ = 0 := by
    rw [inner_perp2_of_orth hNa1 hNa2]; exact inner_outNormal_sub σ hst.symm h0s
  have hNbA : ⟪outNormal σ b, A⟫ = 0 := by
    rw [inner_perp2_of_orth hNb1 hNb2]; exact inner_outNormal_sub σ hst h0t
  have hNaA : ⟪outNormal σ a, A⟫ = -σ.height a := by
    rw [inner_perp2_of_orth hNa1 hNa2, ← neg_sub, inner_neg_right]
    have := inner_outNormal_vsub_self σ h0s
    simp only [vsub_eq_sub] at this
    rw [this]
  have hNbB : ⟪outNormal σ b, B⟫ = -σ.height b := by
    rw [inner_perp2_of_orth hNb1 hNb2, ← neg_sub, inner_neg_right]
    have := inner_outNormal_vsub_self σ h0t
    simp only [vsub_eq_sub] at this
    rw [this]
  have key := inner_normals hpair hNa1 hNa2 hNb1 hNb2 hA1 hA2 hB1 hB2 (inner_outNormal_self σ a)
    (inner_outNormal_self σ b) hNaB hNbA hNaA hNbB (σ.height_pos a) (σ.height_pos b)
  rw [reggeAngle, Real.cos_pi_sub, dihedral4_dist σ.points hℓ hG', InnerProductGeometry.cos_angle, key]
  rw [real_inner_comm A B, mul_comm ‖A‖ ‖B‖]
  ring

open Quaternion in
/-- `sin Θ_e ≥ 0`, so `s_e = sin Θ_e`: the sine of the Regge angle is `√(1 - ⟨N_a, N_b⟩²)`. -/
lemma edgeSin_eq_sin (σ : Simplex4) (e : Fin 10) : edgeSin σ e = Real.sin (reggeAngle σ e) := by
  have hc := cos_reggeAngle σ e
  have hnn : 0 ≤ Real.sin (reggeAngle σ e) := by
    rw [reggeAngle, Real.sin_pi_sub]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  rw [edgeSin, ← hc, show 1 - Real.cos (reggeAngle σ e) ^ 2 = Real.sin (reggeAngle σ e) ^ 2 by
    linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq (reggeAngle σ e), Real.sqrt_sq hnn]

open Quaternion in
/-- **The edge rotation.** `N_a N̄_b = m_e δ(2 Θ_e) m̄_e`: the unit quaternion of the pair of
normals is the rotation by the Regge angle `Θ_e` (as `δ(2Θ) = cos Θ + sin Θ i`) about the bivector
`m_e i m̄_e`. -/
theorem normal_mul_star_normal (σ : Simplex4) (e : Fin 10) :
    normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e)) =
      liftQuat (unitBivector σ e) * phaseQuat (2 * reggeAngle σ e) *
        star (liftQuat (unitBivector σ e)) := by
  set w := normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e)) with hw
  set m := liftQuat (unitBivector σ e) with hm
  have hmn := normSq_liftQuat_bivector σ e
  have hΘ := reggeAngle σ e
  have hre : w.re = Real.cos (reggeAngle σ e) := by
    rw [hw, normalQuat, normalQuat, re_vecQuat_mul_star, cos_reggeAngle]
  have him : w.im = Real.sin (reggeAngle σ e) • bivQuat σ e := by
    rw [← edgeSin_eq_sin, bivQuat, smul_smul, mul_inv_cancel₀ (edgeSin_pos σ e).ne', one_smul]
  have hph : phaseQuat (2 * reggeAngle σ e) =
      (Real.cos (reggeAngle σ e) : ℍ) + Real.sin (reggeAngle σ e) • quatI := by
    ext <;> simp [phaseQuat, quatI]
  have hrot : m * quatI * star m = bivQuat σ e := by
    have := rotI_liftQuat_bivector σ e
    rwa [rotI] at this
  rw [hph, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hrot]
  have h1 : m * (Real.cos (reggeAngle σ e) : ℍ) * star m = (Real.cos (reggeAngle σ e) : ℍ) := by
    rw [← Quaternion.coe_commutes, mul_assoc, mul_star_of_normSq hmn, mul_one]
  rw [h1, ← hre, ← him, Quaternion.re_add_im]

end Lightlike.Asymptotics.EPRL
