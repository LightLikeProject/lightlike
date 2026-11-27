import Mathlib
import Lightlike.TuraevViro.QSixJGenericKL

/-!
# The generic Biedenharn–Elliott identity from the Temperley–Lieb pentagon

This file proves `GenBE θ` (`Lightlike.TV.GenBE`, the generic Biedenharn–Elliott identity at the angle
`θ`, without square roots) from the pentagon identity `TemperleyLieb.pentagon` of the recoupling
coefficients `Fc` of the Temperley–Lieb model at `q = e^{iθ}`, given that `Fc` is the Kauffman–Lins
coefficient `klCoef` on its admissible indices (`TemperleyLieb.FcEqKL ℂ`, taken as a hypothesis until
it is proved).

Part 1: the side conditions of the pentagon at `q = e^{iθ}` from `sin (nθ) ≠ 0`:
`qE_pow_ne_one` (`q^{2n} ≠ 1`), `loopVal_qE_ne_zero`, `chebD_qE_ne_zero`, `qfG_ne_zero`.
-/

open Complex Finset

namespace Lightlike.TV

open Lightlike.TemperleyLieb

/-! ## The side conditions at `q = e^{iθ}` -/

/-- `q^{2n} ≠ 1` at `q = e^{iθ}` when `sin (nθ) ≠ 0`. -/
theorem qE_pow_ne_one {θ : ℝ} {n : ℕ} (h : Real.sin (n * θ) ≠ 0) :
    ((qE θ : ℂˣ) : ℂ) ^ (2 * n) ≠ 1 := by
  rw [coe_qE, ← exp_nat_mul]
  intro h1
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h1
  apply h
  have him := congrArg Complex.im hk
  simp only [mul_im, mul_re, natCast_re, natCast_im, ofReal_re, ofReal_im, I_re, I_im, intCast_re,
    intCast_im, re_ofNat, im_ofNat] at him
  push_cast at him
  have h3 : n * θ = k * Real.pi := by linarith
  rw [h3, Real.sin_int_mul_pi]

/-- `q - q⁻¹ = 2 i sin θ` at `q = e^{iθ}`. -/
theorem qE_sub_inv (θ : ℝ) : ((qE θ : ℂˣ) : ℂ) - ((qE θ : ℂˣ) : ℂ)⁻¹ = 2 * I * (Real.sin θ : ℂ) := by
  rw [coe_qE, show (θ : ℂ) * I = ((θ : ℝ) : ℂ) * I from rfl, exp_sub_exp_neg]

theorem qE_sub_inv_ne_zero {θ : ℝ} (h : Real.sin θ ≠ 0) :
    ((qE θ : ℂˣ) : ℂ) - ((qE θ : ℂˣ) : ℂ)⁻¹ ≠ 0 := by
  rw [qE_sub_inv]
  exact mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) (ofReal_ne_zero.2 h)

/-- `[n]_θ ≠ 0` when `sin (nθ) ≠ 0` and `sin θ ≠ 0`. -/
theorem qnG_ne_zero {θ : ℝ} {n : ℕ} (h1 : Real.sin θ ≠ 0) (hn : Real.sin (n * θ) ≠ 0) :
    qnG θ n ≠ 0 :=
  div_ne_zero hn h1

/-- The quantum factorials up to `N` do not vanish when `sin (nθ) ≠ 0` for `1 ≤ n ≤ N`. -/
theorem qfG_ne_zero {θ : ℝ} {N : ℕ} (hθ : ∀ n, 1 ≤ n → n ≤ N → Real.sin (n * θ) ≠ 0)
    (h1 : Real.sin θ ≠ 0) : ∀ m, m ≤ N → qfG θ m ≠ 0 := by
  intro m hm
  induction m with
  | zero => simp [qfG]
  | succ m ih =>
    rw [qfG_succ]
    exact mul_ne_zero (ih (by omega)) (qnG_ne_zero h1 (by exact_mod_cast hθ (m + 1) (by omega) hm))

/-- The loop value `-(q + q⁻¹) = -2 cos θ` does not vanish when `sin (2θ) ≠ 0`. -/
theorem loopVal_qE_ne_zero {θ : ℝ} (h : Real.sin (2 * θ) ≠ 0) : loopVal (qE θ) ≠ 0 := by
  rw [loopVal_eq, coe_qE, ← exp_neg]
  have hc : exp (θ * I) + exp (-(θ * I)) = 2 * (Real.cos θ : ℂ) := by
    rw [ofReal_cos, cos]; ring_nf
  rw [hc, neg_ne_zero]
  refine mul_ne_zero two_ne_zero (ofReal_ne_zero.2 fun hc0 => h ?_)
  rw [Real.sin_two_mul, hc0, mul_zero]

/-- The Chebyshev values `chebD (loopVal q) n = (-1)^n [n+1]` do not vanish. -/
theorem chebD_qE_ne_zero {θ : ℝ} {n : ℕ} (h1 : Real.sin θ ≠ 0) (hn : Real.sin ((n + 1 : ℕ) * θ) ≠ 0) :
    chebD (loopVal (qE θ)) n ≠ 0 := by
  rw [chebD_eq_qb _ (qE_sub_inv_ne_zero h1), qb_qE]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ofReal_ne_zero.2 (qnG_ne_zero h1 hn))

/-! ## Symmetries of the triangle coefficients and of the q-Racah sum -/

theorem delta2G_swap12 (θ : ℝ) (x y z : ℕ) : delta2G θ x y z = delta2G θ y x z := by
  unfold delta2G
  rw [show y + x + z = x + y + z by ring]
  ring

theorem delta2G_swap23 (θ : ℝ) (x y z : ℕ) : delta2G θ x y z = delta2G θ x z y := by
  unfold delta2G
  rw [show x + z + y = x + y + z by ring]
  ring

/-- Two Racah sums on their supports agree when their bounds and summands agree. -/
theorem racahSum_congr (θ : ℝ) {F₁ F₂ F₃ F₄ B₁ B₂ B₃ G₁ G₂ G₃ G₄ C₁ C₂ C₃ : ℕ}
    (hmax : max (max G₁ G₂) (max G₃ G₄) = max (max F₁ F₂) (max F₃ F₄))
    (hmin : min C₁ (min C₂ C₃) = min B₁ (min B₂ B₃))
    (hterm : ∀ z, racahTermN θ G₁ G₂ G₃ G₄ C₁ C₂ C₃ z = racahTermN θ F₁ F₂ F₃ F₄ B₁ B₂ B₃ z) :
    ∑ z ∈ Icc (max (max G₁ G₂) (max G₃ G₄)) (min C₁ (min C₂ C₃)), racahTermN θ G₁ G₂ G₃ G₄ C₁ C₂ C₃ z =
      ∑ z ∈ Icc (max (max F₁ F₂) (max F₃ F₄)) (min B₁ (min B₂ B₃)),
        racahTermN θ F₁ F₂ F₃ F₄ B₁ B₂ B₃ z := by
  rw [hmax, hmin]
  exact sum_congr rfl fun z _ => hterm z

/-- A tetrahedral symmetry of the q-Racah sum (the second triangle coefficient of the pentagon). -/
theorem racahG_symm₂ (θ : ℝ) (a x I2 d T J2 : ℕ) :
    racahG θ d J2 x a I2 T = racahG θ a x I2 d T J2 := by
  rw [racahG_eq_Icc, racahG_eq_Icc]
  rw [show (d + J2 + x) / 2 = (d + x + J2) / 2 by ring_nf, show (d + I2 + T) / 2 = (d + T + I2) / 2 by ring_nf,
    show (a + J2 + T) / 2 = (a + T + J2) / 2 by ring_nf, show (a + I2 + x) / 2 = (a + x + I2) / 2 by ring_nf,
    show (d + J2 + a + I2) / 2 = (I2 + a + J2 + d) / 2 by ring_nf,
    show (J2 + x + I2 + T) / 2 = (x + I2 + T + J2) / 2 by ring_nf,
    show (x + d + T + a) / 2 = (a + x + d + T) / 2 by ring_nf]
  generalize (a + x + I2) / 2 = A₁, (a + T + J2) / 2 = A₂, (d + x + J2) / 2 = A₃, (d + T + I2) / 2 = A₄,
    (a + x + d + T) / 2 = B₁, (x + I2 + T + J2) / 2 = B₂, (I2 + a + J2 + d) / 2 = B₃
  exact racahSum_congr θ (by omega) (by omega) fun z => by unfold racahTermN; ring

/-- A tetrahedral symmetry of the q-Racah sum (the third triangle coefficient of the pentagon). -/
theorem racahG_symm₃ (θ : ℝ) (a b I1 c I2 x : ℕ) :
    racahG θ a I2 x c b I1 = racahG θ a b I1 c I2 x := by
  rw [racahG_eq_Icc, racahG_eq_Icc]
  rw [show (c + I2 + I1) / 2 = (c + I2 + I1) / 2 from rfl, show (c + b + x) / 2 = (c + b + x) / 2 from rfl,
    show (a + I2 + c + b) / 2 = (a + b + c + I2) / 2 by ring_nf,
    show (I2 + x + b + I1) / 2 = (b + I1 + I2 + x) / 2 by ring_nf,
    show (x + a + I1 + c) / 2 = (I1 + a + x + c) / 2 by ring_nf]
  generalize (a + b + I1) / 2 = A₁, (a + I2 + x) / 2 = A₂, (c + b + x) / 2 = A₃, (c + I2 + I1) / 2 = A₄,
    (a + b + c + I2) / 2 = B₁, (b + I1 + I2 + x) / 2 = B₂, (I1 + a + x + c) / 2 = B₃
  exact racahSum_congr θ (by omega) (by omega) fun z => by unfold racahTermN; ring

/-- A tetrahedral symmetry of the q-Racah sum (the first coefficient of the right side). -/
theorem racahG_symm₄ (θ : ℝ) (a b I1 J1 T J2 : ℕ) :
    racahG θ J1 T I1 a b J2 = racahG θ a b I1 J1 T J2 := by
  rw [racahG_eq_Icc, racahG_eq_Icc]
  rw [show (J1 + T + a + b) / 2 = (a + b + J1 + T) / 2 by ring_nf,
    show (T + I1 + b + J2) / 2 = (b + I1 + T + J2) / 2 by ring_nf,
    show (I1 + J1 + J2 + a) / 2 = (I1 + a + J2 + J1) / 2 by ring_nf]
  generalize (a + b + I1) / 2 = A₁, (a + T + J2) / 2 = A₂, (J1 + b + J2) / 2 = A₃, (J1 + T + I1) / 2 = A₄,
    (a + b + J1 + T) / 2 = B₁, (b + I1 + T + J2) / 2 = B₂, (I1 + a + J2 + J1) / 2 = B₃
  exact racahSum_congr θ (by omega) (by omega) fun z => by unfold racahTermN; ring

/-- A tetrahedral symmetry of the q-Racah sum (the second coefficient of the right side). -/
theorem racahG_symm₅ (θ : ℝ) (I1 c I2 d T J1 : ℕ) :
    racahG θ J1 T I1 I2 c d = racahG θ I1 c I2 d T J1 := by
  rw [racahG_eq_Icc, racahG_eq_Icc]
  rw [show (J1 + T + I1) / 2 = (I1 + T + J1) / 2 by ring_nf, show (J1 + c + d) / 2 = (d + c + J1) / 2 by ring_nf,
    show (I2 + T + d) / 2 = (d + T + I2) / 2 by ring_nf, show (I2 + c + I1) / 2 = (I1 + c + I2) / 2 by ring_nf,
    show (J1 + T + I2 + c) / 2 = (c + I2 + T + J1) / 2 by ring_nf,
    show (T + I1 + c + d) / 2 = (I1 + c + d + T) / 2 by ring_nf,
    show (I1 + J1 + d + I2) / 2 = (I2 + I1 + J1 + d) / 2 by ring_nf]
  generalize (I1 + c + I2) / 2 = A₁, (I1 + T + J1) / 2 = A₂, (d + c + J1) / 2 = A₃, (d + T + I2) / 2 = A₄,
    (I1 + c + d + T) / 2 = B₁, (c + I2 + T + J1) / 2 = B₂, (I2 + I1 + J1 + d) / 2 = B₃
  exact racahSum_congr θ (by omega) (by omega) fun z => by unfold racahTermN; ring

/-! ## The pentagon for the Kauffman–Lins coefficients -/

section PentagonKL

variable {k : Type*} [Field k] [CharZero k]

/-- `Fc = klCoef` given only the ranges of the second bracketing: off the ranges of the first
bracketing both vanish. -/
theorem Fc_eq_klCoef_of' (hKL : FcEqKL k) (q : kˣ) (hδ : loopVal q ≠ 0) {a b c e d f d' : ℕ}
    (hN : 1 ≤ a + b + c) (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq : ∀ n, 1 ≤ n → n ≤ a + b + c + 3 → (q : k) ^ (2 * n) ≠ 1)
    (hfb : f ≤ b) (hfc : f ≤ c) (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f) :
    Fc q a b c e d f d' = klCoef q a b c e d f d' := by
  by_cases hg : e ≤ min a b ∧ d ≤ min (a + b - 2 * e) c
  · obtain ⟨h1, h2⟩ := hg
    simp only [le_min_iff] at h1 h2
    exact Fc_eq_klCoef_of hKL q hδ hN hd hq h1.1 h1.2 hfb hfc h2.2 h2.1 hda hdf
  · have h0 : Fc q a b c e d f d' = 0 := by simp only [Fc, if_neg hg]
    have h1 : klCoef q a b c e d f d' = 0 := by
      unfold klCoef
      rw [ite_eq_right fun hA => hg ⟨hA.1, hA.2.1⟩]
    rw [h0, h1]

/-- `klCoef` vanishes off the admissible indices. -/
theorem klCoef_of_not (q : kˣ) {a b c e d f d' : ℕ} (h : ¬ KLAdm a b c e d f d') :
    klCoef q a b c e d f d' = 0 := by
  unfold klCoef; rw [ite_eq_right h]

end PentagonKL

end Lightlike.TV
