import Mathlib
import Lightlike.Dirac.EigenAngular

/-!
# Regularity at the pole for the angular modes

In the stereographic chart the spinor `f = h^{1/2} g` of the sphere has the same norm as `g` seen from the
sphere frame times `h^{1/2}`.  A spinor of the sphere that extends continuously over the pole is bounded; for the
angular spinors `g = angG v n s G F` this bound forces the decay condition `n + 1 ≤ s` used in
`angular_class_complete`.  This file derives that condition (`decay_of_bounded`): boundedness of
`h^{1/2} g` plus the radial equation give `n + 1 ≤ s`, with no extra assumption.
-/

namespace Lightlike.Dirac

open Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radial equation from the two polynomial identities. -/
lemma odeOp_of_ha_hb (n s : ℕ) (G F : ℝ[X]) (lam : ℝ)
    (ha : psiPoly ((n : ℝ) + 1) (s : ℝ) G = C lam * F)
    (hb : -((1 + X) * F.derivative - C (s : ℝ) * F) = C lam * G) :
    odeOp ((n : ℝ) + 1) (s : ℝ) (lam ^ 2) G = 0 := by
  have h1 : (1 + X) * (psiPoly ((n : ℝ) + 1) (s : ℝ) G).derivative -
      C (s : ℝ) * psiPoly ((n : ℝ) + 1) (s : ℝ) G = -(C lam * (C lam * G)) := by
    rw [ha, derivative_mul, derivative_C, zero_mul, zero_add]
    linear_combination (-(C lam : ℝ[X])) * hb
  unfold odeOp
  rw [C_pow]
  linear_combination h1

/-- **Top coefficient of the radial equation**: a nonzero solution of degree `D` has level `s = D + 1`
or `s = (n + 1) + D`. -/
lemma level_of_degree (n s : ℕ) (G : ℝ[X]) (hG : G ≠ 0) (lam2 : ℝ)
    (hode : odeOp ((n : ℝ) + 1) (s : ℝ) lam2 G = 0) :
    (s : ℝ) = G.natDegree + 1 ∨ (s : ℝ) = (n : ℝ) + 1 + G.natDegree := by
  have h := congrArg (fun p => p.coeff (G.natDegree + 1)) hode
  simp only [odeOp_coeff_succ, coeff_zero] at h
  rw [coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < G.natDegree + 1 + 1),
    coeff_eq_zero_of_natDegree_lt (by omega : G.natDegree < G.natDegree + 1)] at h
  have hl : G.coeff G.natDegree ≠ 0 := by
    simpa using (Polynomial.leadingCoeff_ne_zero.mpr hG)
  have h2 : (((G.natDegree : ℝ) + 1 - s) * (((n : ℝ) + 1) + G.natDegree - s)) * G.coeff G.natDegree = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · left; linarith
    · right; linarith
  · exact absurd h3 hl

/-- **Norm lower bound**: for `v ≠ 0`, `|α| ≤ (1 + ‖γ₀‖) ‖α v + β γ₀ v‖ / ‖v‖`. -/
lemma abs_le_norm_combo (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0) (α β : ℝ) :
    |α| * ‖v‖ ≤ (1 + ‖gam ρ 0‖) * ‖α • v + β • gam ρ 0 v‖ := by
  set u := α • v + β • gam ρ 0 v with hu
  have h2 : gam ρ 0 u = α • gam ρ 0 v - β • v := by
    simp only [hu, map_add, map_smul, gam_sq]
    module
  have h3 : (α ^ 2 + β ^ 2) • v = α • u - β • gam ρ 0 u := by
    rw [h2, hu]; module
  have hM : ‖gam ρ 0 u‖ ≤ ‖gam ρ 0‖ * ‖u‖ := (gam ρ 0).le_opNorm u
  have hnorm : (α ^ 2 + β ^ 2) * ‖v‖ ≤ (|α| + |β| * ‖gam ρ 0‖) * ‖u‖ := by
    calc (α ^ 2 + β ^ 2) * ‖v‖ = ‖(α ^ 2 + β ^ 2) • v‖ := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ = ‖α • u - β • gam ρ 0 u‖ := by rw [h3]
      _ ≤ ‖α • u‖ + ‖β • gam ρ 0 u‖ := norm_sub_le _ _
      _ = |α| * ‖u‖ + |β| * ‖gam ρ 0 u‖ := by rw [norm_smul, norm_smul]; rfl
      _ ≤ |α| * ‖u‖ + |β| * (‖gam ρ 0‖ * ‖u‖) := by gcongr
      _ = (|α| + |β| * ‖gam ρ 0‖) * ‖u‖ := by ring
  by_cases h0 : α ^ 2 + β ^ 2 = 0
  · have : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
    simp only [this, abs_zero, zero_mul]
    positivity
  · have hpos : 0 < α ^ 2 + β ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    set M := ‖gam ρ 0‖
    have hM0 : 0 ≤ M := norm_nonneg _
    have hr : |α| + |β| * M ≤ (1 + M) * Real.sqrt (α ^ 2 + β ^ 2) := by
      have ha : |α| ≤ Real.sqrt (α ^ 2 + β ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg β])
      have hb : |β| ≤ Real.sqrt (α ^ 2 + β ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg α])
      nlinarith [mul_le_mul_of_nonneg_right hb hM0]
    have hs : (α ^ 2 + β ^ 2) = Real.sqrt (α ^ 2 + β ^ 2) * Real.sqrt (α ^ 2 + β ^ 2) :=
      (Real.mul_self_sqrt hpos.le).symm
    have hsp : 0 < Real.sqrt (α ^ 2 + β ^ 2) := Real.sqrt_pos.mpr hpos
    have ha : |α| ≤ Real.sqrt (α ^ 2 + β ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg β])
    have key : Real.sqrt (α ^ 2 + β ^ 2) * ‖v‖ ≤ (1 + M) * ‖u‖ := by
      have : Real.sqrt (α ^ 2 + β ^ 2) * (Real.sqrt (α ^ 2 + β ^ 2) * ‖v‖) ≤
          Real.sqrt (α ^ 2 + β ^ 2) * ((1 + M) * ‖u‖) := by
        calc _ = (α ^ 2 + β ^ 2) * ‖v‖ := by rw [← mul_assoc, ← hs]
          _ ≤ (|α| + |β| * M) * ‖u‖ := hnorm
          _ ≤ ((1 + M) * Real.sqrt (α ^ 2 + β ^ 2)) * ‖u‖ := by gcongr
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hsp
    calc |α| * ‖v‖ ≤ Real.sqrt (α ^ 2 + β ^ 2) * ‖v‖ := by gcongr
      _ ≤ _ := key

/-- A nonzero polynomial is bounded below by a multiple of its leading power for large arguments. -/
lemma poly_lower (P : ℝ[X]) (hP : P ≠ 0) :
    ∃ ε > 0, ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ t → ε * t ^ P.natDegree ≤ |P.eval t| := by
  have h := (Polynomial.isEquivalent_atTop_lead P).isBigO_symm
  obtain ⟨c, hc⟩ := h.exists_pos
  have hev := hc.2.bound
  rw [Filter.eventually_atTop] at hev
  obtain ⟨R0, hR0⟩ := hev
  have hc0 : 0 < c := hc.1
  have hl : 0 < |P.leadingCoeff| := abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
  refine ⟨|P.leadingCoeff| / c, by positivity, max R0 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht => ?_⟩
  have h1 := hR0 t (le_trans (le_max_left _ _) ht)
  have ht0 : 0 < t := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) ht
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos ht0] at h1
  rw [div_mul_eq_mul_div, div_le_iff₀ hc.1]
  nlinarith [h1]

/-- **Growth on the real axis**: if `h^{1/2} g` is bounded by `C`, then `2 deg G + n + 2 ≤ 2 s`. -/
lemma degree_le_of_bounded (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0) (n s : ℕ) (G F : ℝ[X])
    (hG : G ≠ 0) (C : ℝ)
    (hbd : ∀ y : E 2, ‖stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) • angG ρ v n s G F y‖ ≤ C) :
    2 * G.natDegree + n + 2 ≤ 2 * s := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨ε, hε, R, hR, hlow⟩ := poly_lower G hG
  set M := ‖gam ρ 0‖
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set K : ℝ := (1 + M) * C / ‖v‖
  -- for large r, the real-axis bound fails
  set r : ℝ := max (max 1 (Real.sqrt R)) (2 ^ (s + 1) * (|K| + 1) / ε + 1) with hr
  have hr1 : 1 ≤ r := le_trans (le_max_left _ _) (le_max_left _ _)
  have hrR : R ≤ r ^ 2 := by
    have h1 : Real.sqrt R ≤ r := le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 := Real.sq_sqrt hR.le
    nlinarith [Real.sqrt_nonneg R]
  have hr3 : 2 ^ (s + 1) * (|K| + 1) / ε + 1 ≤ r := le_max_right _ _
  have hr0 : 0 < r := by linarith
  have hy := hbd (r • e (0 : Fin 2))
  rw [angG_real_axis] at hy
  have hh : stereoH (r • e (0 : Fin 2)) = (1 + r ^ 2) / 2 := by simp [stereoH, e, norm_smul]
  rw [hh] at hy
  have hexp : ((((2 : ℕ) : ℝ) - 1) / 2) = 1 / 2 := by norm_num
  rw [hexp] at hy
  set α : ℝ := ((1 + r ^ 2) ^ s)⁻¹ * G.eval (r ^ 2) * r ^ (n + 1) with hα
  set β : ℝ := ((1 + r ^ 2) ^ s)⁻¹ * F.eval (r ^ 2) * r ^ n with hβ
  have hsq : 0 ≤ ((1 + r ^ 2) / 2) ^ (1 / 2 : ℝ) := by positivity
  rw [norm_smul, Real.norm_of_nonneg hsq] at hy
  have hcombo := abs_le_norm_combo ρ hv α β
  -- h^{1/2} ≥ r/2
  have hhalf : r / 2 ≤ ((1 + r ^ 2) / 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg r]
  -- |α| h^{1/2} ≤ K
  have h1 : ((1 + r ^ 2) / 2) ^ (1 / 2 : ℝ) * |α| ≤ K := by
    rw [le_div_iff₀ hvn]
    calc ((1 + r ^ 2) / 2) ^ (1 / 2 : ℝ) * |α| * ‖v‖
        ≤ ((1 + r ^ 2) / 2) ^ (1 / 2 : ℝ) * ((1 + M) * ‖α • v + β • gam ρ 0 v‖) := by
          rw [mul_assoc]; gcongr
      _ = (1 + M) * (((1 + r ^ 2) / 2) ^ (1 / 2 : ℝ) * ‖α • v + β • gam ρ 0 v‖) := by ring
      _ ≤ (1 + M) * C := by gcongr
  -- lower bound for |α|
  have hG1 : ε * (r ^ 2) ^ G.natDegree ≤ |G.eval (r ^ 2)| := hlow _ hrR
  have hpow : (1 + r ^ 2) ^ s ≤ 2 ^ s * r ^ (2 * s) := by
    rw [pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [one_le_pow₀ hr1 (n := 2)]
  have hposp : 0 < (1 + r ^ 2) ^ s := by positivity
  have hαlow : ε * r ^ (2 * G.natDegree + n + 1) / (2 ^ s * r ^ (2 * s)) ≤ |α| := by
    rw [hα, abs_mul, abs_mul, abs_inv, abs_of_pos hposp, abs_pow, abs_of_pos hr0]
    rw [div_le_iff₀ (by positivity)]
    calc ε * r ^ (2 * G.natDegree + n + 1)
        = (ε * (r ^ 2) ^ G.natDegree) * r ^ (n + 1) := by ring
      _ ≤ |G.eval (r ^ 2)| * r ^ (n + 1) := by gcongr
      _ = ((1 + r ^ 2) ^ s)⁻¹ * |G.eval (r ^ 2)| * r ^ (n + 1) * (1 + r ^ 2) ^ s := by
          field_simp
      _ ≤ _ := by gcongr
  -- combine
  have hD : 2 * s + 1 ≤ 2 * G.natDegree + n + 2 := by omega
  have hrp : r ^ (2 * s + 1) ≤ r ^ (2 * G.natDegree + n + 2) := pow_le_pow_right₀ hr1 hD
  have hrp2 : r ^ (2 * G.natDegree + n + 2) = r ^ (2 * G.natDegree + n + 1) * r := by ring
  have hden : 0 < 2 ^ s * r ^ (2 * s) := by positivity
  have h2 : (r / 2) * (ε * r ^ (2 * G.natDegree + n + 1) / (2 ^ s * r ^ (2 * s))) ≤ K := by
    calc (r / 2) * (ε * r ^ (2 * G.natDegree + n + 1) / (2 ^ s * r ^ (2 * s)))
        ≤ ((1 + r ^ 2) / 2) ^ (1 / 2 : ℝ) * |α| := by gcongr
      _ ≤ K := h1
  have h3 : ε * r / 2 ^ (s + 1) ≤ K := by
    refine le_trans ?_ h2
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : r ^ (2 * s) * r ≤ r ^ (2 * G.natDegree + n + 1) * r := by
      calc r ^ (2 * s) * r = r ^ (2 * s + 1) := by ring
        _ ≤ r ^ (2 * G.natDegree + n + 2) := hrp
        _ = _ := hrp2
    calc ε * r * (2 * (2 ^ s * r ^ (2 * s))) = (ε * 2 ^ (s + 1)) * (r ^ (2 * s) * r) := by ring
      _ ≤ (ε * 2 ^ (s + 1)) * (r ^ (2 * G.natDegree + n + 1) * r) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have h4 : ε * r ≤ 2 ^ (s + 1) * K := by
    rw [div_le_iff₀ (by positivity)] at h3; linarith
  have h5 : 2 ^ (s + 1) * (|K| + 1) / ε + 1 ≤ r := hr3
  have h6 : 2 ^ (s + 1) * (|K| + 1) / ε < r := by linarith
  rw [div_lt_iff₀ hε] at h6
  nlinarith [le_abs_self K, pow_pos (by norm_num : (0 : ℝ) < 2) (s + 1)]

/-- **The decay condition from boundedness.** If `v ≠ 0`, `G ≠ 0`, the angular spinor `g = angG v n s G F` is a
flat eigenspinor and `h^{1/2} g` is bounded (the spinor of the sphere is bounded at the pole), then
`n + 1 ≤ s`. -/
theorem decay_of_bounded (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0) (n s : ℕ) (G F : ℝ[X]) (lam : ℝ)
    (hG : G ≠ 0)
    (hflat : ∀ x : E 2, stereoH x • dirac ρ (angG ρ v n s G F) x = lam • angG ρ v n s G F x)
    (C : ℝ) (hbd : ∀ y : E 2, ‖stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) • angG ρ v n s G F y‖ ≤ C) :
    n + 1 ≤ s := by
  obtain ⟨ha, hb⟩ := angG_flat_converse ρ hv n s G F lam hflat
  have hode := odeOp_of_ha_hb n s G F lam ha hb
  have hdeg := degree_le_of_bounded ρ hv n s G F hG C hbd
  rcases level_of_degree n s G hG _ hode with h | h
  · have : s = G.natDegree + 1 := by exact_mod_cast h
    omega
  · have : s = n + 1 + G.natDegree := by exact_mod_cast h
    omega

/-- **GE5, completeness in the angular polynomial class, with the regularity at the pole.** For `v ≠ 0`, a
reduced angular spinor (`G(-1) ≠ 0`) that is a flat eigenspinor with `h^{1/2} g` bounded has eigenvalue `±s` and
radial profile a multiple of `gPoly (n+1) (s-n-1)`. -/
theorem angular_class_complete_bounded (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0) (n s : ℕ)
    (G F : ℝ[X]) (lam : ℝ) (hG : G.eval (-1) ≠ 0)
    (hflat : ∀ x : E 2, stereoH x • dirac ρ (angG ρ v n s G F) x = lam • angG ρ v n s G F x)
    (C : ℝ) (hbd : ∀ y : E 2, ‖stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) • angG ρ v n s G F y‖ ≤ C) :
    (lam = s ∨ lam = -s) ∧ G = Polynomial.C (G.coeff 0) * gPoly (n + 1) (s - (n + 1)) := by
  have hG0 : G ≠ 0 := by rintro rfl; simp at hG
  exact angular_class_complete ρ hv n s (decay_of_bounded ρ hv n s G F lam hG0 hflat C hbd) G F lam hG hflat

end Lightlike.Dirac
