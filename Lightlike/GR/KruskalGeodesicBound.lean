import Lightlike.GR.KruskalGeodesic
import Lightlike.GR.KruskalRegions
import Lightlike.Spacetime.CurveBounds

/-!
# Geodesics of the Kruskal manifold: constants of motion and the radial equation

Gap row G1-020, toward maximality. Along a geodesic of the Kruskal manifold in the global chart `(T, x)`, with
`X = log |x|`, `h = kh r`:

* the boost charge `h (T X' - X T')`, the squared angular momentum `r⁴ ω` and `g(w, w)` are constant
  (`kruskalC_hasDerivAt_boost`, `kruskalC_hasDerivAt_L2`, `kruskalC_hasDerivAt_kQ`);
* the radius obeys `r' = 2 G'(s) (X X' - T T')` (`kruskalC_hasDerivAt_r`).
-/

open Matrix Real Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

open Lightlike.Geodesic

variable {M : ℝ} {c w : ℝ → Fin 4 → ℝ} {I : Set ℝ}

/-- The quadratic form in terms of `T'`, `X'` and the angular velocity. -/
lemma kQ_eq (z v : Fin 4 → ℝ) (hρ : rhoSq z ≠ 0) :
    kQ M z v = kh M (krC M z) * (kXd z v ^ 2 - v 0 ^ 2) + krC M z ^ 2 * kOm z v := by
  simp only [kQ, kOm, kXd]
  field_simp
  ring

/-- `X = ½ log |x|²` has velocity `X' = (x·w)/|x|²`. -/
lemma kruskalC_hasDerivAt_X (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => 1 / 2 * log (rhoSq (c s))) (kXd (c t) (w t)) t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have hρ : HasDerivAt (fun s => rhoSq (c s)) (2 * xdot (c t) (w t)) t := by
    have := (((hpos 1).fun_pow 2).fun_add ((hpos 2).fun_pow 2)).fun_add ((hpos 3).fun_pow 2)
    refine this.congr_deriv ?_
    have e : (2 : ℕ) - 1 = 1 := rfl
    simp only [e, pow_one, Nat.cast_ofNat, xdot]
    ring
  refine ((hρ.log hct.1.ne').const_mul (1 / 2 : ℝ)).congr_deriv ?_
  simp only [kXd]
  ring

/-- **The radial velocity**: `r' = 2 G'(s) (X X' - T T')`. -/
lemma kruskalC_hasDerivAt_r (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => krC M (c s))
      (dkG M (krC M (c t)) * (2 * (1 / 2 * log (rhoSq (c t))) * kXd (c t) (w t) - 2 * c t 0 * w t 0)) t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have hs : HasDerivAt (fun s => sC (c s))
      (2 * (1 / 2 * log (rhoSq (c t))) * kXd (c t) (w t) - 2 * c t 0 * w t 0) t := by
    have := ((kruskalC_hasDerivAt_X hgeo ht hct).fun_pow 2).fun_sub ((hpos 0).fun_pow 2)
    refine this.congr_deriv ?_
    have e : (2 : ℕ) - 1 = 1 := rfl
    simp only [e, pow_one, Nat.cast_ofNat]
  exact (hasDerivAt_kG M hM hct.2).comp t hs

/-- **The boost charge `h (T X' - X T')` is conserved.** -/
theorem kruskalC_hasDerivAt_boost (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => c s 0 * (kh M (krC M (c s)) * kXd (c s) (w s)) -
      1 / 2 * log (rhoSq (c s)) * (kh M (krC M (c s)) * w s 0)) 0 t := by
  have hpos := hasDerivAt_pi.1 (hgeo.pos t ht)
  have h1 := ((hpos 0).mul (kruskalC_hasDerivAt_pX hM hgeo ht hct)).sub
    ((kruskalC_hasDerivAt_X hgeo ht hct).mul (kruskalC_hasDerivAt_pT hM hgeo ht hct))
  refine h1.congr_deriv ?_
  ring

/-- The squared angular momentum `r⁴ ω`. -/
def kL2 (M : ℝ) (z v : Fin 4 → ℝ) : ℝ := krC M z ^ 4 * kOm z v

/-- **The squared angular momentum is conserved.** -/
theorem kruskalC_hasDerivAt_L2 (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => kL2 M (c s) (w s)) 0 t := by
  have h1 : HasDerivAt (fun s => krC M (c s) ^ 2 / rhoSq (c s) * (c s 2 * w s 3 - c s 3 * w s 2)) 0 t := by
    simpa using kruskalC_hasDerivAt_angular hM hgeo ht hct ![0, 1, 0, 0]
  have h2 : HasDerivAt (fun s => krC M (c s) ^ 2 / rhoSq (c s) * (c s 3 * w s 1 - c s 1 * w s 3)) 0 t := by
    simpa using kruskalC_hasDerivAt_angular hM hgeo ht hct ![0, 0, 1, 0]
  have h3 : HasDerivAt (fun s => krC M (c s) ^ 2 / rhoSq (c s) * (c s 1 * w s 2 - c s 2 * w s 1)) 0 t := by
    simpa using kruskalC_hasDerivAt_angular hM hgeo ht hct ![0, 0, 0, 1]
  have hsum := ((h1.fun_pow 2).fun_add (h2.fun_pow 2)).fun_add (h3.fun_pow 2)
  have hev : ∀ᶠ s in 𝓝 t, c s ∈ kruskalC :=
    (hgeo.pos t ht).continuousAt.preimage_mem_nhds (isOpen_kruskalC.mem_nhds hct)
  have hfun : (fun s => kL2 M (c s) (w s)) =ᶠ[𝓝 t] fun s =>
      (krC M (c s) ^ 2 / rhoSq (c s) * (c s 2 * w s 3 - c s 3 * w s 2)) ^ 2 +
        (krC M (c s) ^ 2 / rhoSq (c s) * (c s 3 * w s 1 - c s 1 * w s 3)) ^ 2 +
        (krC M (c s) ^ 2 / rhoSq (c s) * (c s 1 * w s 2 - c s 2 * w s 1)) ^ 2 := by
    filter_upwards [hev] with s hs
    have hρ : rhoSq (c s) ≠ 0 := hs.1.ne'
    have hρd : rhoSq (c s) = c s 1 ^ 2 + c s 2 ^ 2 + c s 3 ^ 2 := rfl
    simp only [kL2, kOm, kXd, xdot]
    field_simp
    rw [hρd]
    ring
  refine (hsum.congr_of_eventuallyEq hfun).congr_deriv ?_
  simp

/-- **`g(w, w)` is conserved**, in the form of the quadratic form `kQ`. -/
theorem kruskalC_hasDerivAt_kQ (hM : 0 < M) (hgeo : IsGeodesicOn (kruskalCMetric M) c w I) {t : ℝ}
    (ht : t ∈ I) (hct : c t ∈ kruskalC) :
    HasDerivAt (fun s => kQ M (c s) (w s)) 0 t := by
  have h1 := hgeo.hasDerivAt_speed (isCoordMetric_kruskalC M hM) ht hct
  have hfun : (fun s => kQ M (c s) (w s)) = fun s => normSq (kruskalCMetric M) (c s) (w s) := by
    funext s
    rw [← quad_kruskalC]
    simp only [normSq, dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hfun]
  exact h1

/-! ### Pointwise algebra -/

lemma dkG_eq_kh_div (hM : 0 < M) {r : ℝ} (hr : 0 < r) : dkG M r = kh M r / (8 * M) := by
  simp only [dkG, kh]
  field_simp
  ring

lemma kh_mul_kF (hM : 0 < M) {r : ℝ} (hr : 0 < r) : kh M r * kF M r = 16 * M ^ 2 * (1 - 2 * M / r) := by
  have he : exp (-(r / (2 * M))) * exp (r / (2 * M)) = 1 := by
    rw [← Real.exp_add]; simp
  have : kh M r * kF M r = 32 * M ^ 3 / r * (r / (2 * M) - 1) * (exp (-(r / (2 * M))) * exp (r / (2 * M))) := by
    simp only [kh, kF]; ring
  rw [this, he]
  field_simp
  ring

/-- **The radial equation of the Kruskal geodesics**, pointwise:
`r'² = A²/(16M²) + (1 - 2M/r)(κ - L²/r²)`. -/
lemma radial_sq (hM : 0 < M) {r T X Td Xd om κ L2 A : ℝ} (hr : 0 < r)
    (h1 : kh M r * (Xd ^ 2 - Td ^ 2) + r ^ 2 * om = κ) (h2 : r ^ 4 * om = L2)
    (h3 : T * (kh M r * Xd) - X * (kh M r * Td) = A) (h4 : X ^ 2 - T ^ 2 = kF M r) :
    (dkG M r * (2 * X * Xd - 2 * T * Td)) ^ 2 =
      A ^ 2 / (16 * M ^ 2) + (1 - 2 * M / r) * (κ - L2 / r ^ 2) := by
  have hom : r ^ 2 * om = L2 / r ^ 2 := by
    rw [← h2]; field_simp
  have e1 : (dkG M r * (2 * X * Xd - 2 * T * Td)) ^ 2 =
      1 / (16 * M ^ 2) * ((T * (kh M r * Xd) - X * (kh M r * Td)) ^ 2 +
        kh M r * (X ^ 2 - T ^ 2) * (kh M r * (Xd ^ 2 - Td ^ 2))) := by
    rw [dkG_eq_kh_div hM hr]
    field_simp
    ring
  have h1' : kh M r * (Xd ^ 2 - Td ^ 2) = κ - L2 / r ^ 2 := by linarith
  rw [e1, h3, h4, kh_mul_kF hM hr, h1']
  field_simp

/-! ### Bounds of the coefficients on `r₀ ≤ r ≤ R` -/

lemma kh_anti (hM : 0 < M) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) : kh M R ≤ kh M r := by
  unfold kh
  have h1 : 32 * M ^ 3 / R ≤ 32 * M ^ 3 / r := div_le_div_of_nonneg_left (by positivity) hr hrR
  have h2 : exp (-(R / (2 * M))) ≤ exp (-(r / (2 * M))) := by
    apply Real.exp_le_exp.2
    have : r / (2 * M) ≤ R / (2 * M) := div_le_div_of_nonneg_right hrR (by positivity)
    linarith
  exact mul_le_mul h1 h2 (exp_pos _).le (by positivity)

lemma abs_dkG_le (hM : 0 < M) {r0 r : ℝ} (hr0 : 0 < r0) (hr : r0 ≤ r) : |dkG M r| ≤ 4 * M ^ 2 / r0 := by
  have hr' : 0 < r := hr0.trans_le hr
  have hpos : 0 ≤ dkG M r := by unfold dkG; positivity
  rw [abs_of_nonneg hpos]
  unfold dkG
  have h1 : exp (-(r / (2 * M))) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ r / (2 * M) := by positivity
    linarith)
  calc 4 * M ^ 2 * exp (-(r / (2 * M))) / r ≤ 4 * M ^ 2 * 1 / r := by gcongr
    _ ≤ 4 * M ^ 2 / r0 := by
        rw [mul_one]
        exact div_le_div_of_nonneg_left (by positivity) hr0 hr

lemma abs_dkh_le (hM : 0 < M) {r0 r : ℝ} (hr0 : 0 < r0) (hr : r0 ≤ r) :
    |dkh M r| ≤ kh M r0 * (1 / r0 + 1 / (2 * M)) := by
  have hr' : 0 < r := hr0.trans_le hr
  have hh : 0 < kh M r := kh_pos M hM hr'
  unfold dkh
  rw [abs_neg, abs_of_nonneg (by positivity)]
  have h1 : 1 / r ≤ 1 / r0 := div_le_div_of_nonneg_left zero_le_one hr0 hr
  exact mul_le_mul (kh_anti hM hr0 hr) (by linarith) (by positivity) (kh_pos M hM hr0).le

/-! ### Geodesics on `[0, b)` -/

lemma sC_eq_kF (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ kruskalC) :
    (1 / 2 * log (rhoSq z)) ^ 2 - z 0 ^ 2 = kF M (krC M z) :=
  (kF_kG M hM hz.2).symm

/-- The constants of motion on `[0, b)`. -/
lemma kruskalC_constants (hM : 0 < M) {b : ℝ} (hgeo : IsGeodesicOn (kruskalCMetric M) c w (Ico 0 b))
    (hc : ∀ t ∈ Ico 0 b, c t ∈ kruskalC) :
    ∃ κ L2 A : ℝ, ∀ t ∈ Ico 0 b,
      kh M (krC M (c t)) * (kXd (c t) (w t) ^ 2 - w t 0 ^ 2) + krC M (c t) ^ 2 * kOm (c t) (w t) = κ ∧
      krC M (c t) ^ 4 * kOm (c t) (w t) = L2 ∧
      c t 0 * (kh M (krC M (c t)) * kXd (c t) (w t)) -
        1 / 2 * log (rhoSq (c t)) * (kh M (krC M (c t)) * w t 0) = A := by
  refine ⟨kQ M (c 0) (w 0), kL2 M (c 0) (w 0), c 0 0 * (kh M (krC M (c 0)) * kXd (c 0) (w 0)) -
    1 / 2 * log (rhoSq (c 0)) * (kh M (krC M (c 0)) * w 0 0), fun t ht => ⟨?_, ?_, ?_⟩⟩
  · rw [← kQ_eq (c t) (w t) (hc t ht).1.ne']
    exact eq_zero_of_hasDerivAt_zero_Ico (f := fun s => kQ M (c s) (w s))
      (fun s hs => kruskalC_hasDerivAt_kQ hM hgeo hs (hc s hs)) ht
  · exact eq_zero_of_hasDerivAt_zero_Ico (f := fun s => kL2 M (c s) (w s))
      (fun s hs => kruskalC_hasDerivAt_L2 hM hgeo hs (hc s hs)) ht
  · exact eq_zero_of_hasDerivAt_zero_Ico
      (f := fun s => c s 0 * (kh M (krC M (c s)) * kXd (c s) (w s)) -
        1 / 2 * log (rhoSq (c s)) * (kh M (krC M (c s)) * w s 0))
      (fun s hs => kruskalC_hasDerivAt_boost hM hgeo hs (hc s hs)) ht

/-- **The radius of a geodesic on a finite interval is bounded above**, if it is bounded below. -/
theorem kruskalC_radius_bounded (hM : 0 < M) {b : ℝ} (hgeo : IsGeodesicOn (kruskalCMetric M) c w (Ico 0 b))
    (hc : ∀ t ∈ Ico 0 b, c t ∈ kruskalC) {r0 : ℝ} (hr0 : 0 < r0)
    (hr : ∀ t ∈ Ico 0 b, r0 ≤ krC M (c t)) : ∃ R : ℝ, ∀ t ∈ Ico 0 b, krC M (c t) ≤ R := by
  obtain ⟨κ, L2, A, hcon⟩ := kruskalC_constants hM hgeo hc
  set B := A ^ 2 / (16 * M ^ 2) + (1 + 2 * M / r0) * (|κ| + |L2| / r0 ^ 2) with hB
  have hbound : ∀ t ∈ Ico 0 b, |dkG M (krC M (c t)) *
      (2 * (1 / 2 * log (rhoSq (c t))) * kXd (c t) (w t) - 2 * c t 0 * w t 0)| ≤ √B := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hcon t ht
    have hrt : 0 < krC M (c t) := hr0.trans_le (hr t ht)
    apply Real.abs_le_sqrt
    rw [radial_sq hM hrt h1 h2 h3 (sC_eq_kF hM (hc t ht))]
    have e1 : |1 - 2 * M / krC M (c t)| ≤ 1 + 2 * M / r0 := by
      have h0 : 0 ≤ 2 * M / krC M (c t) := by positivity
      have h4 : 2 * M / krC M (c t) ≤ 2 * M / r0 :=
        div_le_div_of_nonneg_left (by positivity) hr0 (hr t ht)
      rw [abs_le]
      constructor <;> linarith
    have e2 : |κ - L2 / krC M (c t) ^ 2| ≤ |κ| + |L2| / r0 ^ 2 := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < krC M (c t) ^ 2)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (pow_le_pow_left₀ hr0.le (hr t ht) 2)
    have e3 : (1 - 2 * M / krC M (c t)) * (κ - L2 / krC M (c t) ^ 2) ≤
        (1 + 2 * M / r0) * (|κ| + |L2| / r0 ^ 2) := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
    rw [hB]
    linarith
  refine ⟨krC M (c 0) + √B * b, fun t ht => ?_⟩
  have h := abs_sub_le_of_hasDerivAt_Ico (f := fun s => krC M (c s))
    (fun s hs => kruskalC_hasDerivAt_r hM hgeo hs (hc s hs)) hbound ht
  have := (abs_le.1 h).2
  linarith

/-- **The velocity of a geodesic on a finite interval is bounded**, if the radius is bounded below; so is
`X = log |x|`. -/
theorem kruskalC_velocity_bounded (hM : 0 < M) {b : ℝ}
    (hgeo : IsGeodesicOn (kruskalCMetric M) c w (Ico 0 b))
    (hc : ∀ t ∈ Ico 0 b, c t ∈ kruskalC) {r0 : ℝ} (hr0 : 0 < r0)
    (hr : ∀ t ∈ Ico 0 b, r0 ≤ krC M (c t)) :
    ∃ C BX : ℝ, 0 ≤ C ∧ (∀ t ∈ Ico 0 b, ‖w t‖ ≤ C) ∧
      ∀ t ∈ Ico 0 b, |1 / 2 * log (rhoSq (c t))| ≤ BX := by
  by_cases hb : 0 < b
  swap
  · exact ⟨0, 0, le_rfl, fun t ht => absurd (ht.1.trans_lt ht.2) hb,
      fun t ht => absurd (ht.1.trans_lt ht.2) hb⟩
  obtain ⟨R, hR⟩ := kruskalC_radius_bounded hM hgeo hc hr0 hr
  obtain ⟨κ, L2, A, hcon⟩ := kruskalC_constants hM hgeo hc
  have h0I : (0 : ℝ) ∈ Ico 0 b := ⟨le_rfl, hb⟩
  have hRpos : 0 < R := hr0.trans_le ((hr 0 h0I).trans (hR 0 h0I))
  set hmin := kh M R with hhmin
  have hmin0 : 0 < hmin := kh_pos M hM hRpos
  have hrt : ∀ t ∈ Ico 0 b, 0 < krC M (c t) := fun t ht => hr0.trans_le (hr t ht)
  have hht : ∀ t ∈ Ico 0 b, hmin ≤ kh M (krC M (c t)) := fun t ht => kh_anti hM (hrt t ht) (hR t ht)
  set P := |κ| + |L2| / r0 ^ 2 with hP
  have hP0 : 0 ≤ P := by positivity
  set Ξm := kh M r0 * (1 / r0 + 1 / (2 * M)) * (P / hmin) + 2 * |L2| / r0 ^ 3 with hΞm
  have hkr0 : 0 < kh M r0 := kh_pos M hM hr0
  have hΞm0 : 0 ≤ Ξm := by positivity
  set K := 1 / hmin + 4 * M ^ 2 / r0 * Ξm with hK
  -- the angular velocity
  have hom : ∀ t ∈ Ico 0 b, kOm (c t) (w t) = L2 / krC M (c t) ^ 4 := fun t ht => by
    have := (hcon t ht).2.1
    have h4 : krC M (c t) ^ 4 ≠ 0 := pow_ne_zero 4 (hrt t ht).ne'
    rw [eq_div_iff h4]
    linarith
  have habsom : ∀ t ∈ Ico 0 b, |kOm (c t) (w t)| ≤ |L2| / r0 ^ 4 := fun t ht => by
    rw [hom t ht, abs_div, abs_of_pos (pow_pos (hrt t ht) 4)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      (pow_le_pow_left₀ hr0.le (hr t ht) 4)
  -- the common factor is bounded
  have hΞ : ∀ t ∈ Ico 0 b, |kXi M (c t) (w t)| ≤ Ξm := fun t ht => by
    obtain ⟨h1, h2, -⟩ := hcon t ht
    have hrp := hrt t ht
    have hh : 0 < kh M (krC M (c t)) := kh_pos M hM hrp
    have hD : kXd (c t) (w t) ^ 2 - w t 0 ^ 2 =
        (κ - L2 / krC M (c t) ^ 2) / kh M (krC M (c t)) := by
      rw [eq_div_iff hh.ne', ← h1, hom t ht]
      field_simp
      ring
    have e2 : |κ - L2 / krC M (c t) ^ 2| ≤ P := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < krC M (c t) ^ 2)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (pow_le_pow_left₀ hr0.le (hr t ht) 2)
    have hDb : |kXd (c t) (w t) ^ 2 - w t 0 ^ 2| ≤ P / hmin := by
      rw [hD, abs_div, abs_of_pos hh]
      exact div_le_div₀ hP0 e2 hmin0 (hht t ht)
    have hro : |2 * krC M (c t) * kOm (c t) (w t)| ≤ 2 * |L2| / r0 ^ 3 := by
      have : 2 * krC M (c t) * kOm (c t) (w t) = 2 * L2 / krC M (c t) ^ 3 := by
        rw [hom t ht]; field_simp
      rw [this, abs_div, abs_mul, abs_of_pos (pow_pos hrp 3), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hr0.le (hr t ht) 3)
    unfold kXi
    refine (abs_add_le _ _).trans (add_le_add ?_ hro)
    rw [abs_mul]
    exact mul_le_mul (abs_dkh_le hM hr0 (hr t ht)) hDb (abs_nonneg _) (by positivity)
  have hα : ∀ t ∈ Ico 0 b, |1 / kh M (krC M (c t))| ≤ K := fun t ht => by
    have hh : 0 < kh M (krC M (c t)) := kh_pos M hM (hrt t ht)
    rw [abs_of_pos (by positivity)]
    have : 1 / kh M (krC M (c t)) ≤ 1 / hmin := div_le_div_of_nonneg_left zero_le_one hmin0 (hht t ht)
    have h2 : 0 ≤ 4 * M ^ 2 / r0 * Ξm := by positivity
    rw [hK]; linarith
  have hβ : ∀ t ∈ Ico 0 b, |dkG M (krC M (c t)) * kXi M (c t) (w t)| ≤ K := fun t ht => by
    rw [abs_mul]
    have := mul_le_mul (abs_dkG_le hM hr0 (hr t ht)) (hΞ t ht) (abs_nonneg _) (by positivity)
    have h2 : 0 ≤ 1 / hmin := by positivity
    rw [hK]; linarith
  -- Grönwall for `(T, h T')` and `(X, h X')`
  have hT := fun t (ht : t ∈ Ico 0 b) => abs_le_of_linear_system_Ico
    (u := fun s => c s 0) (p := fun s => kh M (krC M (c s)) * w s 0)
    (α := fun s => 1 / kh M (krC M (c s))) (β := fun s => dkG M (krC M (c s)) * kXi M (c s) (w s))
    (fun s hs => by
      have hh : kh M (krC M (c s)) ≠ 0 := (kh_pos M hM (hrt s hs)).ne'
      refine (hasDerivAt_pi.1 (hgeo.pos s hs) 0).congr_deriv ?_
      field_simp)
    (fun s hs => (kruskalC_hasDerivAt_pT hM hgeo hs (hc s hs)).congr_deriv (by ring)) hα hβ ht
  have hX := fun t (ht : t ∈ Ico 0 b) => abs_le_of_linear_system_Ico
    (u := fun s => 1 / 2 * log (rhoSq (c s))) (p := fun s => kh M (krC M (c s)) * kXd (c s) (w s))
    (α := fun s => 1 / kh M (krC M (c s))) (β := fun s => dkG M (krC M (c s)) * kXi M (c s) (w s))
    (fun s hs => by
      have hh : kh M (krC M (c s)) ≠ 0 := (kh_pos M hM (hrt s hs)).ne'
      refine (kruskalC_hasDerivAt_X hgeo hs (hc s hs)).congr_deriv ?_
      field_simp)
    (fun s hs => (kruskalC_hasDerivAt_pX hM hgeo hs (hc s hs)).congr_deriv (by ring)) hα hβ ht
  set BT := (|c 0 0| + |kh M (krC M (c 0)) * w 0 0|) * exp (K * b) with hBT
  set BX := (|1 / 2 * log (rhoSq (c 0))| + |kh M (krC M (c 0)) * kXd (c 0) (w 0)|) * exp (K * b) with hBX
  have hBT0 : 0 ≤ BT := by positivity
  have hBX0 : 0 ≤ BX := by positivity
  have hTd : ∀ t ∈ Ico 0 b, |w t 0| ≤ BT / hmin := fun t ht => by
    have hh : 0 < kh M (krC M (c t)) := kh_pos M hM (hrt t ht)
    have h1 := (hT t ht).2
    rw [abs_mul, abs_of_pos hh] at h1
    rw [le_div_iff₀ hmin0]
    calc |w t 0| * hmin ≤ |w t 0| * kh M (krC M (c t)) :=
          mul_le_mul_of_nonneg_left (hht t ht) (abs_nonneg _)
      _ ≤ BT := by rw [mul_comm]; exact h1
  have hXd : ∀ t ∈ Ico 0 b, |kXd (c t) (w t)| ≤ BX / hmin := fun t ht => by
    have hh : 0 < kh M (krC M (c t)) := kh_pos M hM (hrt t ht)
    have h1 := (hX t ht).2
    rw [abs_mul, abs_of_pos hh] at h1
    rw [le_div_iff₀ hmin0]
    calc |kXd (c t) (w t)| * hmin ≤ |kXd (c t) (w t)| * kh M (krC M (c t)) :=
          mul_le_mul_of_nonneg_left (hht t ht) (abs_nonneg _)
      _ ≤ BX := by rw [mul_comm]; exact h1
  -- the space part of the velocity
  set W2 := exp (2 * BX) * (|L2| / r0 ^ 4 + (BX / hmin) ^ 2) with hW2
  have hW20 : 0 ≤ W2 := by positivity
  have hsp : ∀ t ∈ Ico 0 b, xdot (w t) (w t) ≤ W2 := fun t ht => by
    have hρ : 0 < rhoSq (c t) := (hc t ht).1
    have e1 : xdot (w t) (w t) = rhoSq (c t) * (kOm (c t) (w t) + kXd (c t) (w t) ^ 2) := by
      simp only [kOm]
      field_simp
      ring
    have e2 : rhoSq (c t) ≤ exp (2 * BX) := by
      have h1 := (abs_le.1 (hX t ht).1).2
      calc rhoSq (c t) = exp (2 * (1 / 2 * log (rhoSq (c t)))) := by
            rw [show 2 * (1 / 2 * log (rhoSq (c t))) = log (rhoSq (c t)) by ring, exp_log hρ]
        _ ≤ exp (2 * BX) := Real.exp_le_exp.2 (by linarith)
    have e3 : kOm (c t) (w t) + kXd (c t) (w t) ^ 2 ≤ |L2| / r0 ^ 4 + (BX / hmin) ^ 2 := by
      refine add_le_add ((le_abs_self _).trans (habsom t ht)) ?_
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hXd t ht) 2
    rw [e1, hW2]
    calc rhoSq (c t) * (kOm (c t) (w t) + kXd (c t) (w t) ^ 2)
        ≤ rhoSq (c t) * (|L2| / r0 ^ 4 + (BX / hmin) ^ 2) := mul_le_mul_of_nonneg_left e3 hρ.le
      _ ≤ exp (2 * BX) * (|L2| / r0 ^ 4 + (BX / hmin) ^ 2) :=
          mul_le_mul_of_nonneg_right e2 (by positivity)
  refine ⟨BT / hmin + √W2, BX, by positivity, fun t ht => ?_, fun t ht => (hX t ht).1⟩
  have hC0 : 0 ≤ BT / hmin + √W2 := by positivity
  rw [pi_norm_le_iff_of_nonneg hC0]
  intro i
  rw [Real.norm_eq_abs]
  have hsq : ∀ j : Fin 4, w t j ^ 2 ≤ xdot (w t) (w t) → |w t j| ≤ BT / hmin + √W2 := fun j hj => by
    have : |w t j| ≤ √W2 := Real.abs_le_sqrt (hj.trans (hsp t ht))
    have h2 : 0 ≤ BT / hmin := by positivity
    linarith
  fin_cases i
  · have := hTd t ht
    have h2 : 0 ≤ √W2 := Real.sqrt_nonneg _
    show |w t 0| ≤ _
    linarith
  · exact hsq 1 (by simp only [xdot]; nlinarith [sq_nonneg (w t 2), sq_nonneg (w t 3)])
  · exact hsq 2 (by simp only [xdot]; nlinarith [sq_nonneg (w t 1), sq_nonneg (w t 3)])
  · exact hsq 3 (by simp only [xdot]; nlinarith [sq_nonneg (w t 1), sq_nonneg (w t 2)])

end Lightlike
