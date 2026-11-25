import Mathlib
import Lightlike.Spacetime.MinkowskiCompactification

/-!
# Dilations act on the compactified Minkowski space and preserve null infinity

Row G1-016 (milestone GE7), clause "the conformal action of the isometry group on the boundary", Minkowski side.
In the null angles `U = (η + χ)/2`, `V = (η - χ)/2` of the compactification, `t = tan U + tan V`, `r = tan U - tan V`
(`compT_eq_tan_add`, `compR_eq_tan_sub`), the dilation `(t, r) ↦ (λ t, λ r)` is `tan U ↦ λ tan U`, `tan V ↦ λ tan V`.
The angle map `thetaDil λ x = arcsin (λ sin x / √(cos² x + λ² sin² x))` is `arctan (λ tan x)` on `(-π/2, π/2)`
and extends continuously by `±π/2` at the ends (`thetaDil_continuous`, `thetaDil_pi_div_two`).  Hence the dilation
extends to a continuous map of the closed region `0 ≤ χ`, `|η| + χ ≤ π` (`dilComp`), which acts on the region
as the dilation (`dilComp_compT`, `dilComp_compR`) and maps null infinity `|η| + χ = π` to itself
(`compOmega_dilComp_eq_zero_iff`).
-/

open Real Set

namespace Lightlike

/-- The angle map of a dilation by `λ`. -/
noncomputable def thetaDil (l x : ℝ) : ℝ := arcsin (l * sin x / √(cos x ^ 2 + l ^ 2 * sin x ^ 2))

lemma thetaDil_den_pos {l : ℝ} (hl : 0 < l) (x : ℝ) : 0 < cos x ^ 2 + l ^ 2 * sin x ^ 2 := by
  by_contra h
  push Not at h
  have h1 : cos x ^ 2 = 0 := by nlinarith [sq_nonneg (cos x), mul_nonneg (sq_nonneg l) (sq_nonneg (sin x))]
  have h2 : l ^ 2 * sin x ^ 2 = 0 := by nlinarith [sq_nonneg (cos x), mul_nonneg (sq_nonneg l) (sq_nonneg (sin x))]
  have hc : cos x = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
  have hs : sin x = 0 := by
    have : sin x ^ 2 = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h (pow_pos hl 2).ne'
      · exact h
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  have := sin_sq_add_cos_sq x
  rw [hc, hs] at this; norm_num at this

/-- The angle map of a dilation is continuous. -/
theorem thetaDil_continuous {l : ℝ} (hl : 0 < l) : Continuous (thetaDil l) := by
  unfold thetaDil
  refine continuous_arcsin.comp (Continuous.div (by fun_prop) (by fun_prop) fun x => ?_)
  exact (Real.sqrt_pos.2 (thetaDil_den_pos hl x)).ne'

/-- The angle map of a dilation fixes `π/2`. -/
theorem thetaDil_pi_div_two {l : ℝ} (hl : 0 < l) : thetaDil l (π / 2) = π / 2 := by
  unfold thetaDil
  have : √(cos (π / 2) ^ 2 + l ^ 2 * sin (π / 2) ^ 2) = l := by
    rw [cos_pi_div_two, sin_pi_div_two]
    simp [Real.sqrt_sq hl.le]
  rw [this, sin_pi_div_two, mul_one, div_self hl.ne', arcsin_one]

theorem thetaDil_neg_pi_div_two {l : ℝ} (hl : 0 < l) : thetaDil l (-(π / 2)) = -(π / 2) := by
  unfold thetaDil
  have : √(cos (-(π / 2)) ^ 2 + l ^ 2 * sin (-(π / 2)) ^ 2) = l := by
    rw [cos_neg, sin_neg, cos_pi_div_two, sin_pi_div_two]
    simp [Real.sqrt_sq hl.le]
  rw [this, sin_neg, sin_pi_div_two, mul_neg, mul_one, neg_div, div_self hl.ne', arcsin_neg_one]

/-- On the open interval the angle map is `arctan (λ tan x)`: `tan (thetaDil λ x) = λ tan x`. -/
theorem tan_thetaDil {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    tan (thetaDil l x) = l * tan x := by
  have hc : 0 < cos x := cos_pos_of_mem_Ioo hx
  set ρ := √(cos x ^ 2 + l ^ 2 * sin x ^ 2) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 (thetaDil_den_pos hl x)
  have hρ2 : ρ ^ 2 = cos x ^ 2 + l ^ 2 * sin x ^ 2 := Real.sq_sqrt (thetaDil_den_pos hl x).le
  have hsq : (l * sin x) ^ 2 ≤ ρ ^ 2 := by
    rw [hρ2]; nlinarith [sq_nonneg (cos x), sq_nonneg l, sq_nonneg (sin x), sin_sq_add_cos_sq x,
      mul_nonneg (sq_nonneg l) (sq_nonneg (sin x))]
  have hb := abs_le_of_sq_le_sq' hsq hρ0.le
  have hs : l * sin x / ρ ∈ Icc (-1 : ℝ) 1 :=
    ⟨by rw [le_div_iff₀ hρ0]; linarith [hb.1], (div_le_one hρ0).2 hb.2⟩
  unfold thetaDil
  rw [← hρ, tan_eq_sin_div_cos, sin_arcsin hs.1 hs.2, cos_arcsin]
  have : 1 - (l * sin x / ρ) ^ 2 = (cos x / ρ) ^ 2 := by
    field_simp; nlinarith [hρ2]
  rw [this, Real.sqrt_sq (div_pos hc hρ0).le, tan_eq_sin_div_cos]
  field_simp

theorem thetaDil_mem {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    thetaDil l x ∈ Ioo (-(π / 2)) (π / 2) := by
  have hc : 0 < cos x := cos_pos_of_mem_Ioo hx
  have hρ0 : 0 < √(cos x ^ 2 + l ^ 2 * sin x ^ 2) := Real.sqrt_pos.2 (thetaDil_den_pos hl x)
  have hρ2 : √(cos x ^ 2 + l ^ 2 * sin x ^ 2) ^ 2 = cos x ^ 2 + l ^ 2 * sin x ^ 2 :=
    Real.sq_sqrt (thetaDil_den_pos hl x).le
  have hsq : (l * sin x) ^ 2 < √(cos x ^ 2 + l ^ 2 * sin x ^ 2) ^ 2 := by
    rw [hρ2]; nlinarith [pow_pos hc 2]
  have hb := abs_lt_of_sq_lt_sq' hsq hρ0.le
  unfold thetaDil
  constructor
  · rw [neg_pi_div_two_lt_arcsin, lt_div_iff₀ hρ0]; linarith [hb.1]
  · rw [arcsin_lt_pi_div_two, div_lt_one hρ0]; exact hb.2

theorem thetaDil_mem_Icc {l : ℝ} (hl : 0 < l) (x : ℝ) : thetaDil l x ∈ Icc (-(π / 2)) (π / 2) :=
  ⟨neg_pi_div_two_le_arcsin _, arcsin_le_pi_div_two _⟩

theorem cos_thetaDil_eq_zero_iff {l : ℝ} (hl : 0 < l) {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) :
    cos (thetaDil l x) = 0 ↔ cos x = 0 := by
  rcases hx.1.eq_or_lt with h | h
  · rw [← h, thetaDil_neg_pi_div_two hl]
  rcases hx.2.eq_or_lt with h' | h'
  · rw [h', thetaDil_pi_div_two hl]
  have h1 : cos x ≠ 0 := (cos_pos_of_mem_Ioo ⟨h, h'⟩).ne'
  have h2 : cos (thetaDil l x) ≠ 0 := (cos_pos_of_mem_Ioo (thetaDil_mem hl ⟨h, h'⟩)).ne'
  exact ⟨fun hh => absurd hh h2, fun hh => absurd hh h1⟩

/-- The dilation by `λ` in the null angles: `(η, χ) ↦ (Θ U + Θ V, Θ U - Θ V)`. -/
noncomputable def dilComp (l : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2),
    thetaDil l ((p.1 + p.2) / 2) - thetaDil l ((p.1 - p.2) / 2))

/-- The dilation of the compactification is continuous on the whole plane of null angles. -/
theorem dilComp_continuous {l : ℝ} (hl : 0 < l) : Continuous (dilComp l) := by
  have := thetaDil_continuous hl
  unfold dilComp
  fun_prop

/-- **The dilation preserves the region of Minkowski space.** -/
theorem dilComp_mem {l : ℝ} (hl : 0 < l) {p : ℝ × ℝ} (hp : p ∈ compRegion) : dilComp l p ∈ compRegion := by
  obtain ⟨hχ, h⟩ := hp
  have h1 := neg_abs_le p.1
  have h2 := le_abs_self p.1
  have hU : (p.1 + p.2) / 2 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hV : (p.1 - p.2) / 2 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hU' := thetaDil_mem hl hU
  have hV' := thetaDil_mem hl hV
  have hlt : thetaDil l ((p.1 - p.2) / 2) < thetaDil l ((p.1 + p.2) / 2) := by
    by_contra hge
    push Not at hge
    have := tan_lt_tan_of_lt_of_lt_pi_div_two (x := thetaDil l ((p.1 + p.2) / 2)) (y := thetaDil l ((p.1 - p.2) / 2))
      hU'.1 hV'.2 (lt_of_le_of_ne hge (by
        intro heq
        have e1 := tan_thetaDil hl hU
        have e2 := tan_thetaDil hl hV
        rw [heq] at e1
        have : tan ((p.1 - p.2) / 2) = tan ((p.1 + p.2) / 2) := by
          have := e1.symm.trans e2; nlinarith [this]
        have := injOn_tan hV hU this
        linarith))
    rw [tan_thetaDil hl hU, tan_thetaDil hl hV] at this
    have : tan ((p.1 - p.2) / 2) < tan ((p.1 + p.2) / 2) :=
      tan_lt_tan_of_lt_of_lt_pi_div_two hV.1 hU.2 (by linarith)
    nlinarith
  refine ⟨by simp only [dilComp]; linarith, ?_⟩
  simp only [dilComp]
  rcases abs_cases (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2)) with ⟨ha, _⟩ | ⟨ha, _⟩ <;>
    rw [ha] <;> linarith [hU'.1, hU'.2, hV'.1, hV'.2]

/-- **The dilation of the compactification acts as the dilation of Minkowski space.** -/
theorem dilComp_compT {l : ℝ} (hl : 0 < l) {p : ℝ × ℝ} (hp : p ∈ compRegion) :
    compT (dilComp l p).1 (dilComp l p).2 = l * compT p.1 p.2 := by
  have hq := dilComp_mem hl hp
  obtain ⟨hχ0, hlt0⟩ := hp
  rw [compT_eq_tan_add hχ0.le hlt0, compT_eq_tan_add hq.1.le hq.2]
  have h1 := neg_abs_le p.1
  have h2 := le_abs_self p.1
  have hU : (p.1 + p.2) / 2 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hV : (p.1 - p.2) / 2 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  simp only [dilComp]
  rw [show (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2) +
      (thetaDil l ((p.1 + p.2) / 2) - thetaDil l ((p.1 - p.2) / 2))) / 2 = thetaDil l ((p.1 + p.2) / 2) by ring,
    show (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2) -
      (thetaDil l ((p.1 + p.2) / 2) - thetaDil l ((p.1 - p.2) / 2))) / 2 = thetaDil l ((p.1 - p.2) / 2) by ring,
    tan_thetaDil hl hU, tan_thetaDil hl hV]
  ring

/-- The dilation of the compactification acts as the dilation on the radius. -/
theorem dilComp_compR {l : ℝ} (hl : 0 < l) {p : ℝ × ℝ} (hp : p ∈ compRegion) :
    compR (dilComp l p).1 (dilComp l p).2 = l * compR p.1 p.2 := by
  have hq := dilComp_mem hl hp
  obtain ⟨hχ0, hlt0⟩ := hp
  rw [compR_eq_tan_sub hχ0.le hlt0, compR_eq_tan_sub hq.1.le hq.2]
  have h1 := neg_abs_le p.1
  have h2 := le_abs_self p.1
  have hU : (p.1 + p.2) / 2 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  have hV : (p.1 - p.2) / 2 ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
  simp only [dilComp]
  rw [show (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2) +
      (thetaDil l ((p.1 + p.2) / 2) - thetaDil l ((p.1 - p.2) / 2))) / 2 = thetaDil l ((p.1 + p.2) / 2) by ring,
    show (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2) -
      (thetaDil l ((p.1 + p.2) / 2) - thetaDil l ((p.1 - p.2) / 2))) / 2 = thetaDil l ((p.1 - p.2) / 2) by ring,
    tan_thetaDil hl hU, tan_thetaDil hl hV]
  ring

/-- **The dilation preserves null infinity**: on the closed region the conformal factor `ω` vanishes at the
image of `p` exactly when it vanishes at `p`. -/
theorem compOmega_dilComp_eq_zero_iff {l : ℝ} (hl : 0 < l) {p : ℝ × ℝ} (hχ : 0 ≤ p.2) (h : |p.1| + p.2 ≤ π) :
    compOmega (dilComp l p).1 (dilComp l p).2 = 0 ↔ compOmega p.1 p.2 = 0 := by
  have h1 := neg_abs_le p.1
  have h2 := le_abs_self p.1
  have hU : (p.1 + p.2) / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith⟩
  have hV : (p.1 - p.2) / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith, by linarith [pi_pos]⟩
  rw [compOmega_eq_cos_mul_cos, compOmega_eq_cos_mul_cos]
  simp only [dilComp]
  rw [show (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2) +
      (thetaDil l ((p.1 + p.2) / 2) - thetaDil l ((p.1 - p.2) / 2))) / 2 = thetaDil l ((p.1 + p.2) / 2) by ring,
    show (thetaDil l ((p.1 + p.2) / 2) + thetaDil l ((p.1 - p.2) / 2) -
      (thetaDil l ((p.1 + p.2) / 2) - thetaDil l ((p.1 - p.2) / 2))) / 2 = thetaDil l ((p.1 - p.2) / 2) by ring,
    mul_eq_zero, mul_eq_zero, cos_thetaDil_eq_zero_iff hl hU, cos_thetaDil_eq_zero_iff hl hV]

end Lightlike
