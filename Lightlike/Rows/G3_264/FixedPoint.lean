module

public import Mathlib
public import Lightlike.Rows.G3_264.Defs

/-!
# The Einstein–Hilbert ODE: algebraic reduction of the non-Gaussian fixed point

Row G3-264 (task T-AS2). With `x = 1 − 2λ` and `D(x) = 14x² − 15x + 24 > 0`, a zero `(g, λ)` of the
vector field `EH.field` with `g > 0` and `x > 0` satisfies `η = −2`, hence
`g = 12π x² / D(x)`, and then `β_λ = 2 P(x) / D(x)` with the cubic
`P(x) = 14x³ − 41x² + 59x − 24`. Conversely every such pair is a zero.

Main results
* `EH.field_eq_zero_iff`: for `g > 0`, `x > 0`, `field (g, λ) = 0 ↔ P(x) = 0 ∧ g = 12π x²/D(x)`.
* `EH.cubic_strictMono`, `EH.exists_unique_cubic_root`: `P` has exactly one real root.
-/

@[expose] public section

noncomputable section

namespace Lightlike.AsymptoticSafety.EH

open Real

/-- The cubic `P(x) = 14x³ − 41x² + 59x − 24` whose root is `x* = 1 − 2λ*`. -/
def cubic (x : ℝ) : ℝ := 14 * x ^ 3 - 41 * x ^ 2 + 59 * x - 24

/-- The quadratic `D(x) = 14x² − 15x + 24`, with `g* = 12π x²/D(x)` on `η = −2`. -/
def quad (x : ℝ) : ℝ := 14 * x ^ 2 - 15 * x + 24

lemma quad_pos (x : ℝ) : 0 < quad x := by
  unfold quad; nlinarith [sq_nonneg (x - 15 / 28)]

lemma quad2_pos (x : ℝ) : 0 < 14 * x ^ 2 - 10 * x + 18 := by
  nlinarith [sq_nonneg (x - 5 / 14)]

lemma cubic_strictMono : StrictMono cubic := by
  intro a b hab
  unfold cubic
  have h1 : 0 < b - a := sub_pos.mpr hab
  have h2 : 0 < 14 * (a ^ 2 + a * b + b ^ 2) - 41 * (a + b) + 59 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b, sq_nonneg (a + b - 41 / 28 * 2 / 2),
      sq_nonneg (a - 41 / 42), sq_nonneg (b - 41 / 42)]
  have : 14 * b ^ 3 - 41 * b ^ 2 + 59 * b - 24 - (14 * a ^ 3 - 41 * a ^ 2 + 59 * a - 24)
      = (b - a) * (14 * (a ^ 2 + a * b + b ^ 2) - 41 * (a + b) + 59) := by ring
  nlinarith [mul_pos h1 h2]

/-- `P` has a unique real root, and it lies in `(0.613, 0.614)`. -/
theorem exists_unique_cubic_root : ∃! x : ℝ, cubic x = 0 := by
  have hc : ContinuousOn cubic (Set.Icc (0.613 : ℝ) 0.614) := by
    unfold cubic; fun_prop
  have hlo : cubic 0.613 ≤ 0 := by unfold cubic; norm_num
  have hhi : 0 ≤ cubic 0.614 := by unfold cubic; norm_num
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by norm_num : (0.613 : ℝ) ≤ 0.614) hc
    ⟨hlo, hhi⟩
  exact ⟨x, hx, fun y hy => cubic_strictMono.injective (hy.trans hx.symm)⟩

lemma two_B2_sub_B1 {lam : ℝ} (hx : denom lam ≠ 0) :
    2 * B2 lam - B1 lam = quad (denom lam) / (6 * π * denom lam ^ 2) := by
  unfold B1 B2 quad
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

lemma eta_eq_neg_two_iff {g lam : ℝ} (hx : 0 < denom lam) :
    eta g lam = -2 ↔ g = 12 * π * denom lam ^ 2 / quad (denom lam) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hxne : denom lam ≠ 0 := hx.ne'
  have hq := (quad_pos (denom lam)).ne'
  constructor
  · intro h
    have hden : 1 - g * B2 lam ≠ 0 := by
      intro h0
      simp [eta, h0] at h
    have h1 : g * B1 lam = -2 * (1 - g * B2 lam) := by
      unfold eta at h
      rwa [div_eq_iff hden] at h
    have h2 : g * (2 * B2 lam - B1 lam) = 2 := by linarith
    rw [two_B2_sub_B1 hxne] at h2
    field_simp at h2
    field_simp
    linarith
  · intro h
    have hB : B2 lam = (6 - 5 * denom lam) / (12 * π * denom lam ^ 2) := by
      unfold B2; field_simp
    have h1 : 1 - g * B2 lam = (14 * denom lam ^ 2 - 10 * denom lam + 18) / quad (denom lam) := by
      rw [h, hB]
      have hQ : quad (denom lam) = 14 * denom lam ^ 2 - 15 * denom lam + 24 := rfl
      generalize quad (denom lam) = Q at *
      field_simp
      rw [hQ]
      ring
    have hpos : 1 - g * B2 lam ≠ 0 := by
      rw [h1]; exact (div_pos (quad2_pos _) (quad_pos _)).ne'
    unfold eta
    rw [div_eq_iff hpos, h1]
    have hB1 : B1 lam = (5 * denom lam - 9 - 7 * denom lam ^ 2) / (3 * π * denom lam ^ 2) := by
      unfold B1; field_simp
    rw [h, hB1]
    unfold quad
    field_simp
    ring

lemma betaLam_of_eta {g lam : ℝ} (h : eta g lam = -2) :
    betaLam g lam = -4 * lam + g / (4 * π) * (40 / (3 * denom lam) - 8) := by
  unfold betaLam
  rw [h]
  ring

/-- On the locus `η = −2`, `β_λ = 2 P(x) / D(x)`. -/
lemma betaLam_at_fixed_g {lam : ℝ} (hx : 0 < denom lam) :
    -4 * lam + (12 * π * denom lam ^ 2 / quad (denom lam)) / (4 * π)
      * (40 / (3 * denom lam) - 8) = 2 * cubic (denom lam) / quad (denom lam) := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hxne : denom lam ≠ 0 := hx.ne'
  have hq := (quad_pos (denom lam)).ne'
  have hl : -4 * lam = -2 * (1 - denom lam) := by unfold denom; ring
  rw [hl]
  generalize denom lam = y at *
  have hQ : quad y = 14 * y ^ 2 - 15 * y + 24 := rfl
  have hP : cubic y = 14 * y ^ 3 - 41 * y ^ 2 + 59 * y - 24 := rfl
  generalize quad y = Q at *
  rw [hP]
  field_simp
  rw [hQ]
  ring

/-- A zero of the Einstein–Hilbert vector field with `g > 0` and `x = 1 − 2λ > 0` is exactly a
pair with `P(x) = 0` and `g = 12π x²/D(x)`. -/
theorem field_eq_zero_iff {g lam : ℝ} (hg : 0 < g) (hx : 0 < denom lam) :
    field (g, lam) = 0 ↔ cubic (denom lam) = 0 ∧ g = 12 * π * denom lam ^ 2 / quad (denom lam) := by
  have hq := (quad_pos (denom lam)).ne'
  have hGz : betaG g lam = 0 ↔ eta g lam = -2 := by
    unfold betaG
    constructor
    · intro h
      have := (mul_eq_zero.mp h).resolve_right hg.ne'
      linarith
    · intro h; rw [h]; ring
  constructor
  · intro h
    have h1 : betaG g lam = 0 := congrArg Prod.fst h
    have h2 : betaLam g lam = 0 := congrArg Prod.snd h
    have he := hGz.mp h1
    have hgv := (eta_eq_neg_two_iff hx).mp he
    refine ⟨?_, hgv⟩
    rw [betaLam_of_eta he, hgv, betaLam_at_fixed_g hx] at h2
    field_simp at h2
    linarith
  · rintro ⟨hc, hgv⟩
    have he := (eta_eq_neg_two_iff hx).mpr hgv
    have h1 : betaG g lam = 0 := hGz.mpr he
    have h2 : betaLam g lam = 0 := by
      rw [betaLam_of_eta he, hgv, betaLam_at_fixed_g hx, hc]; simp
    exact Prod.ext h1 h2

/-- The root `x* = 1 − 2λ*` of the cubic `P`. -/
def xStar : ℝ := Classical.choose exists_unique_cubic_root

lemma cubic_xStar : cubic xStar = 0 := (Classical.choose_spec exists_unique_cubic_root).1

lemma xStar_bounds : 0.613 < xStar ∧ xStar < 0.614 := by
  have h := cubic_xStar
  constructor
  · by_contra hc
    have := cubic_strictMono.monotone (not_lt.mp hc)
    have h2 : cubic 0.613 < 0 := by unfold cubic; norm_num
    linarith
  · by_contra hc
    have := cubic_strictMono.monotone (not_lt.mp hc)
    have h2 : 0 < cubic 0.614 := by unfold cubic; norm_num
    linarith

lemma xStar_pos : 0 < xStar := by linarith [xStar_bounds.1]

/-- The non-Gaussian fixed point `g* = 12π x*²/D(x*)`. -/
def gStar : ℝ := 12 * π * xStar ^ 2 / quad xStar

/-- The non-Gaussian fixed point `λ* = (1 − x*)/2`. -/
def lamStar : ℝ := (1 - xStar) / 2

lemma denom_lamStar : denom lamStar = xStar := by unfold denom lamStar; ring

lemma gStar_pos : 0 < gStar := by
  unfold gStar
  have := xStar_pos
  have := quad_pos xStar
  positivity

/-- **Non-Gaussian fixed point of the Einstein–Hilbert ODE.** The vector field has exactly one
zero with `g > 0` and `1 − 2λ > 0`, namely `(g*, λ*)`. -/
theorem exists_unique_fixedPoint :
    ∃! p : ℝ × ℝ, 0 < p.1 ∧ 0 < denom p.2 ∧ field p = 0 := by
  refine ⟨(gStar, lamStar), ⟨gStar_pos, by rw [denom_lamStar]; exact xStar_pos, ?_⟩, ?_⟩
  · have := (field_eq_zero_iff (g := gStar) (lam := lamStar) gStar_pos
      (by rw [denom_lamStar]; exact xStar_pos)).mpr
    apply this
    rw [denom_lamStar]
    exact ⟨cubic_xStar, rfl⟩
  · rintro ⟨g, lam⟩ ⟨hg, hx, hf⟩
    obtain ⟨hc, hgv⟩ := (field_eq_zero_iff hg hx).mp hf
    have hxx : denom lam = xStar :=
      (Classical.choose_spec exists_unique_cubic_root).2 _ hc
    have hl : lam = lamStar := by
      unfold denom at hxx; unfold lamStar; linarith
    refine Prod.ext ?_ hl
    have hgv' : g = 12 * π * denom lam ^ 2 / quad (denom lam) := hgv
    show g = gStar
    rw [hgv', hxx]
    rfl

end Lightlike.AsymptoticSafety.EH
