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

open Complex Finset Lightlike.Pentagon

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

omit [CharZero k] in
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
  · have h0 : Fc q a b c e d f d' = 0 := by
      unfold Fc; exact ite_eq_right hg
    have h1 : klCoef q a b c e d f d' = 0 := by
      unfold klCoef
      rw [ite_eq_right fun hA => hg ⟨hA.1, hA.2.1⟩]
    rw [h0, h1]

omit [CharZero k] in
/-- `klCoef` vanishes off the admissible indices. -/
theorem klCoef_of_not (q : kˣ) {a b c e d f d' : ℕ} (h : ¬ KLAdm a b c e d f d') :
    klCoef q a b c e d f d' = 0 := by
  unfold klCoef; rw [ite_eq_right h]

omit [CharZero k] in
/-- **The pentagon, term by term**: each product of three `Fc` of the left side of the pentagon is
the product of the three `klCoef`. -/
theorem pentagon_term_eq (hKL : FcEqKL k) (q : kˣ) (hδ : loopVal q ≠ 0)
    {a b c d j m i f h d' e₀ d₀ g₀ : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd : ∀ x, x ≤ a + b + c + d → chebD (loopVal q) x ≠ 0)
    (hq : ∀ n, 1 ≤ n → n ≤ a + b + c + d + 3 → (q : k) ^ (2 * n) ≠ 1)
    (hjc : j ≤ c) (hjd : j ≤ d) (hmb : m ≤ b) (hmz : m ≤ c + d - 2 * j) (hia : i ≤ a)
    (hiz : i ≤ b + (c + d - 2 * j) - 2 * m) :
    Fc q b c d f h j m * (Fc q a (b + c - 2 * f) d d' g₀ h i * Fc q a b c e₀ d₀ f d') =
      klCoef q b c d f h j m * (klCoef q a (b + c - 2 * f) d d' g₀ h i * klCoef q a b c e₀ d₀ f d') := by
  have e1 : Fc q b c d f h j m = klCoef q b c d f h j m :=
    Fc_eq_klCoef_of' hKL q hδ (by omega) (fun x hx => hd x (by omega))
      (fun n h1 h2 => hq n h1 (by omega)) hjc hjd hmb hmz
  rw [e1]
  by_cases g1 : KLAdm b c d f h j m
  · obtain ⟨g11, g12, -, -, g15⟩ := g1
    simp only [le_min_iff] at g11 g12
    by_cases g2 : d' ≤ min a (b + c - 2 * f) ∧ g₀ ≤ min (a + (b + c - 2 * f) - 2 * d') d
    · obtain ⟨g21, g22⟩ := g2
      simp only [le_min_iff] at g21 g22
      have e2 : Fc q a (b + c - 2 * f) d d' g₀ h i = klCoef q a (b + c - 2 * f) d d' g₀ h i :=
        Fc_eq_klCoef_of' hKL q hδ (by omega) (fun x hx => hd x (by omega))
          (fun n h1 h2 => hq n h1 (by omega)) g12.1 g12.2 hia (by omega)
      have e3 : Fc q a b c e₀ d₀ f d' = klCoef q a b c e₀ d₀ f d' :=
        Fc_eq_klCoef_of' hKL q hδ (by omega) (fun x hx => hd x (by omega))
          (fun n h1 h2 => hq n h1 (by omega)) g11.1 g11.2 g21.1 g21.2
      rw [e2, e3]
    · have h0 : Fc q a (b + c - 2 * f) d d' g₀ h i = 0 := by
        unfold Fc; exact ite_eq_right g2
      have h1 : klCoef q a (b + c - 2 * f) d d' g₀ h i = 0 :=
        klCoef_of_not q fun hA => g2 ⟨hA.1, hA.2.1⟩
      rw [h0, h1, zero_mul, zero_mul]
  · rw [klCoef_of_not q g1, zero_mul, zero_mul]

omit [CharZero k] in
/-- **The inner sums of the left side collapse**: for fixed `f`, only `h = (x + d - J₂)/2` and
`d' = (a + x - I₂)/2` contribute (`x = b + c - 2f`), by the admissibility of the outer factors. -/
theorem pentagon_inner_collapse (q : kˣ) (a b c d j m f e₀ d₀ g₀ i : ℕ) :
    ∑ h ∈ range (d + 1), ∑ d' ∈ range (a + 1),
        klCoef q b c d f h j m * (klCoef q a (b + c - 2 * f) d d' g₀ h i * klCoef q a b c e₀ d₀ f d') =
      klCoef q b c d f ((b + c - 2 * f + d - (b + (c + d - 2 * j) - 2 * m)) / 2) j m *
        (klCoef q a (b + c - 2 * f) d ((a + (b + c - 2 * f) - (a + b - 2 * e₀ + c - 2 * d₀)) / 2) g₀
            ((b + c - 2 * f + d - (b + (c + d - 2 * j) - 2 * m)) / 2) i *
          klCoef q a b c e₀ d₀ f ((a + (b + c - 2 * f) - (a + b - 2 * e₀ + c - 2 * d₀)) / 2)) := by
  set hF := (b + c - 2 * f + d - (b + (c + d - 2 * j) - 2 * m)) / 2
  set dF := (a + (b + c - 2 * f) - (a + b - 2 * e₀ + c - 2 * d₀)) / 2
  -- the `h`-sum
  have hk1 : ∀ h, h ≠ hF → klCoef q b c d f h j m = 0 := fun h hh =>
    klCoef_of_not q fun hA => hh (by obtain ⟨-, h2, -, -, h5⟩ := hA; simp only [le_min_iff] at h2; omega)
  have hk3 : ∀ d', d' ≠ dF → klCoef q a b c e₀ d₀ f d' = 0 := fun d' hd =>
    klCoef_of_not q fun hA => hd (by obtain ⟨-, -, -, h4, h5⟩ := hA; simp only [le_min_iff] at h4; omega)
  rw [sum_eq_single hF (fun h _ hh => by simp [hk1 h hh]) (fun hm => by
    have : klCoef q b c d f hF j m = 0 := klCoef_of_not q fun hA => hm (by
      obtain ⟨-, h2, -, -, -⟩ := hA; simp only [le_min_iff] at h2; simp only [mem_range]; omega)
    simp [this])]
  rw [sum_eq_single dF (fun d' _ hd => by simp [hk3 d' hd]) (fun hm => by
    have : klCoef q a b c e₀ d₀ f dF = 0 := klCoef_of_not q fun hA => hm (by
      obtain ⟨-, -, -, h4, -⟩ := hA; simp only [le_min_iff] at h4; simp only [mem_range]; omega)
    simp [this])]

omit [CharZero k] in
/-- **The right side collapses**: only `g' = (I₁ + J₁ - T)/2` contributes, `T = a + J₂ - 2i`. -/
theorem pentagon_right_collapse (q : kˣ) (a b c d j m e₀ d₀ g₀ i : ℕ) :
    ∑ g' ∈ range (c + d - 2 * j + 1),
        klCoef q a b (c + d - 2 * j) e₀ g' m i * klCoef q (a + b - 2 * e₀) c d d₀ g₀ j g' =
      klCoef q a b (c + d - 2 * j) e₀
          ((a + b - 2 * e₀ + (c + d - 2 * j) - (a + (b + (c + d - 2 * j) - 2 * m) - 2 * i)) / 2) m i *
        klCoef q (a + b - 2 * e₀) c d d₀ g₀ j
          ((a + b - 2 * e₀ + (c + d - 2 * j) - (a + (b + (c + d - 2 * j) - 2 * m) - 2 * i)) / 2) := by
  set gF := (a + b - 2 * e₀ + (c + d - 2 * j) - (a + (b + (c + d - 2 * j) - 2 * m) - 2 * i)) / 2
  have hk4 : ∀ g', g' ≠ gF → klCoef q a b (c + d - 2 * j) e₀ g' m i = 0 := fun g' hg =>
    klCoef_of_not q fun hA => hg (by obtain ⟨h1, h2, -, -, h5⟩ := hA; simp only [le_min_iff] at h1 h2; omega)
  rw [sum_eq_single gF (fun g' _ hg => by simp [hk4 g' hg]) (fun hm => by
    have : klCoef q a b (c + d - 2 * j) e₀ gF m i = 0 := klCoef_of_not q fun hA => hm (by
      obtain ⟨-, h2, -, -, -⟩ := hA; simp only [le_min_iff] at h2; simp only [mem_range]; omega)
    simp [this])]

/-- **The pentagon for `klCoef`, collapsed**: from `TemperleyLieb.pentagon` and `FcEqKL`, the sum over
`f` of the three Kauffman–Lins coefficients (with `h`, `d'` fixed by admissibility) equals the product
of the two of the right side (with `g'` fixed). -/
theorem pentagon_klCoef (hKL : FcEqKL k) (q : kˣ) (hδ : loopVal q ≠ 0) (a b c d e₀ d₀ g₀ j m i : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : ∀ x, x ≤ a + b + c + d → chebD (loopVal q) x ≠ 0)
    (hq : ∀ n, 1 ≤ n → n ≤ a + b + c + d + 3 → (q : k) ^ (2 * n) ≠ 1)
    (hjc : j ≤ c) (hjd : j ≤ d) (hmb : m ≤ b) (hmz : m ≤ c + d - 2 * j) (hia : i ≤ a)
    (hiz : i ≤ b + (c + d - 2 * j) - 2 * m) (h₀ : ValidA a b c d e₀ d₀ g₀) :
    ∑ f ∈ range (b + 1),
        klCoef q b c d f ((b + c - 2 * f + d - (b + (c + d - 2 * j) - 2 * m)) / 2) j m *
          (klCoef q a (b + c - 2 * f) d ((a + (b + c - 2 * f) - (a + b - 2 * e₀ + c - 2 * d₀)) / 2) g₀
              ((b + c - 2 * f + d - (b + (c + d - 2 * j) - 2 * m)) / 2) i *
            klCoef q a b c e₀ d₀ f ((a + (b + c - 2 * f) - (a + b - 2 * e₀ + c - 2 * d₀)) / 2)) =
      klCoef q a b (c + d - 2 * j) e₀
          ((a + b - 2 * e₀ + (c + d - 2 * j) - (a + (b + (c + d - 2 * j) - 2 * m) - 2 * i)) / 2) m i *
        klCoef q (a + b - 2 * e₀) c d d₀ g₀ j
          ((a + b - 2 * e₀ + (c + d - 2 * j) - (a + (b + (c + d - 2 * j) - 2 * m) - 2 * i)) / 2) := by
  have hq2 : ∀ x, 1 ≤ x → x ≤ a + b + c + d + 1 → (q : k) ^ (2 * x) ≠ 1 :=
    fun x h1 h2 => hq x h1 (by omega)
  have P := pentagon q hδ a b c d e₀ d₀ g₀ j m i ha hb hc hd hq2 hjc hjd hmb hmz hia hiz h₀
  -- left side: `Fc` to `klCoef`, then collapse
  have hL : ∀ f ∈ range (b + 1), ∑ h ∈ range (d + 1), ∑ d' ∈ range (a + 1),
      Fc q b c d f h j m * (Fc q a (b + c - 2 * f) d d' g₀ h i * Fc q a b c e₀ d₀ f d') =
      ∑ h ∈ range (d + 1), ∑ d' ∈ range (a + 1),
        klCoef q b c d f h j m * (klCoef q a (b + c - 2 * f) d d' g₀ h i * klCoef q a b c e₀ d₀ f d') :=
    fun f _ => sum_congr rfl fun h _ => sum_congr rfl fun d' _ =>
      pentagon_term_eq hKL q hδ ha hb hd hq hjc hjd hmb hmz hia hiz
  rw [sum_congr rfl hL] at P
  simp_rw [pentagon_inner_collapse] at P
  -- right side
  have hR : ∀ g' ∈ range (c + d - 2 * j + 1),
      Fc q a b (c + d - 2 * j) e₀ g' m i * Fc q (a + b - 2 * e₀) c d d₀ g₀ j g' =
      klCoef q a b (c + d - 2 * j) e₀ g' m i * klCoef q (a + b - 2 * e₀) c d d₀ g₀ j g' := by
    intro g' hg'
    rw [mem_range] at hg'
    have e4 : Fc q a b (c + d - 2 * j) e₀ g' m i = klCoef q a b (c + d - 2 * j) e₀ g' m i :=
      Fc_eq_klCoef_of' hKL q hδ (by omega) (fun x hx => hd x (by omega))
        (fun n h1 h2 => hq n h1 (by omega)) hmb hmz hia hiz
    rw [e4]
    obtain ⟨h01, h02, -, -⟩ := h₀
    simp only [le_min_iff] at h01 h02
    by_cases hg : g' ≤ a + b - 2 * e₀
    · rw [Fc_eq_klCoef_of' hKL q hδ (by omega) (fun x hx => hd x (by omega))
        (fun n h1 h2 => hq n h1 (by omega)) hjc hjd hg (by omega)]
    · have h4 : klCoef q a b (c + d - 2 * j) e₀ g' m i = 0 :=
        klCoef_of_not q fun hA => hg (by obtain ⟨-, h2, -, -, -⟩ := hA; simp only [le_min_iff] at h2; omega)
      rw [h4, zero_mul, zero_mul]
  rw [sum_congr rfl hR, pentagon_right_collapse] at P
  exact P

end PentagonKL

/-! ## The gauge cancels in the pentagon -/

/-- The gauge cancellation over atoms. -/
theorem gauge_alg {Pbcx Pxdj Paxi Pidt Pabi Pici Pijt Pcdj Pbjj Pajt X J1 J2 I1 I2 : ℝ}
    (h1 : Pbcx ≠ 0) (h2 : Pxdj ≠ 0) (h3 : Paxi ≠ 0) (h4 : Pidt ≠ 0) (h5 : Pabi ≠ 0) (h6 : Pici ≠ 0)
    (h7 : Pijt ≠ 0) (hX : X ≠ 0) (hJ1 : J1 ≠ 0) (hJ2 : J2 ≠ 0) (hI1 : I1 ≠ 0) (hI2 : I2 ≠ 0) :
    Pcdj * Pbjj / J1 / (Pbcx * Pxdj / X) *
        (Pxdj * Pajt / J2 / (Paxi * Pidt / I2) * (Pbcx * Paxi / X / (Pabi * Pici / I1))) =
      Pbjj * Pajt / J2 / (Pabi * Pijt / I1) * (Pcdj * Pijt / J1 / (Pici * Pidt / I2)) := by
  field_simp

/-- **The gauge cancels in the pentagon**: the product of the three gauge ratios of the left side is
the product of the two of the right side, for every middle colour `x`. -/
theorem gauge_cancel (θ : ℝ) {a b c d x I1 I2 T J1 J2 : ℕ}
    (h1 : triPi θ b c x ≠ 0) (h2 : triPi θ x d J2 ≠ 0) (h3 : triPi θ a x I2 ≠ 0)
    (h4 : triPi θ I2 d T ≠ 0) (h5 : triPi θ a b I1 ≠ 0) (h6 : triPi θ I1 c I2 ≠ 0)
    (h7 : triPi θ I1 J1 T ≠ 0) (hX : qfG θ (x + 1) ≠ 0) (hJ1 : qfG θ (J1 + 1) ≠ 0)
    (hJ2 : qfG θ (J2 + 1) ≠ 0) (hI1 : qfG θ (I1 + 1) ≠ 0) (hI2 : qfG θ (I2 + 1) ≠ 0) :
    gaugeJ θ b c d J1 J2 / gaugeI θ b c d x J2 *
        (gaugeJ θ a x d J2 T / gaugeI θ a x d I2 T * (gaugeJ θ a b c x I2 / gaugeI θ a b c I1 I2)) =
      gaugeJ θ a b J1 J2 T / gaugeI θ a b J1 I1 T * (gaugeJ θ I1 c d J1 T / gaugeI θ I1 c d I2 T) := by
  unfold gaugeI gaugeJ
  exact gauge_alg h1 h2 h3 h4 h5 h6 h7 hX hJ1 hJ2 hI1 hI2

/-! ## The Kauffman–Lins products as the terms of `GenBE` -/

theorem neg_one_pow_congr {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℝ) ^ m = (-1) ^ n := by
  rw [← Nat.mod_add_div m 2, ← Nat.mod_add_div n 2, pow_add, pow_add, pow_mul, pow_mul, h]
  norm_num

/-- **The left side of the pentagon in `klK` form is the summand of `GenBE`**, times the common
factor `(-1)^E [J₁+1] [J₂+1] Δ²(a,b,I₁) Δ²(I₁,c,I₂) Δ²(I₂,d,T)`. -/
theorem klK_left (θ : ℝ) {a b c d x I1 I2 T J1 J2 : ℕ}
    (hp1 : (b + c + x) % 2 = 0) (hp2 : (x + d + J2) % 2 = 0) (hp3 : (a + x + I2) % 2 = 0)
    (_hp4 : (I2 + d + T) % 2 = 0) (hp5 : (a + b + I1) % 2 = 0) (hp6 : (I1 + c + I2) % 2 = 0)
    (hp7 : (I1 + J1 + T) % 2 = 0) :
    klK θ b c d x J2 J1 * (klK θ a x d I2 T J2 * klK θ a b c I1 I2 x) =
      ((-1) ^ (I1 + (a + b + I1) / 2 + (I1 + J1 + T) / 2 + (I2 + (I1 + c + I2) / 2 + (I2 + d + T) / 2)) *
          (qnG θ (J1 + 1) * qnG θ (J2 + 1) * delta2G θ a b I1 * delta2G θ I1 c I2 * delta2G θ I2 d T)) *
        ((-1) ^ ((b + c + d + J2 + a + I2 + J1 + T + I1 + x) / 2) * qnG θ (x + 1) *
          (delta2G θ b c x * delta2G θ d J2 x * delta2G θ a I2 x) *
          (racahG θ b c x d J2 J1 * racahG θ d J2 x a I2 T * racahG θ a I2 x c b I1)) := by
  rw [racahG_symm₂ θ a x I2 d T J2, racahG_symm₃ θ a b I1 c I2 x, delta2G_swap23 θ a I2 x,
    delta2G_swap23 θ d J2 x, delta2G_swap12 θ d x J2]
  have hs : (-1 : ℝ) ^ (x + (b + c + x) / 2 + (x + d + J2) / 2) *
      ((-1) ^ (I2 + (a + x + I2) / 2 + (I2 + d + T) / 2) * (-1) ^ (I1 + (a + b + I1) / 2 + (I1 + c + I2) / 2)) =
      (-1) ^ (I1 + (a + b + I1) / 2 + (I1 + J1 + T) / 2 + (I2 + (I1 + c + I2) / 2 + (I2 + d + T) / 2)) *
        (-1) ^ ((b + c + d + J2 + a + I2 + J1 + T + I1 + x) / 2) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact neg_one_pow_congr (by omega)
  unfold klK
  linear_combination (qnG θ (J1 + 1) * delta2G θ b c x * delta2G θ x d J2 * racahG θ b c x d J2 J1 *
    (qnG θ (J2 + 1) * delta2G θ a x I2 * delta2G θ I2 d T * racahG θ a x I2 d T J2) *
    (qnG θ (x + 1) * delta2G θ a b I1 * delta2G θ I1 c I2 * racahG θ a b I1 c I2 x)) * hs

/-- **The right side of the pentagon in `klK` form is the right side of `GenBE`**, times the same
common factor. -/
theorem klK_right (θ : ℝ) {a b c d I1 I2 T J1 J2 : ℕ} :
    klK θ a b J1 I1 T J2 * klK θ I1 c d I2 T J1 =
      ((-1) ^ (I1 + (a + b + I1) / 2 + (I1 + J1 + T) / 2 + (I2 + (I1 + c + I2) / 2 + (I2 + d + T) / 2)) *
          (qnG θ (J1 + 1) * qnG θ (J2 + 1) * delta2G θ a b I1 * delta2G θ I1 c I2 * delta2G θ I2 d T)) *
        (delta2G θ J1 T I1 * racahG θ J1 T I1 a b J2 * racahG θ J1 T I1 I2 c d) := by
  rw [racahG_symm₄ θ a b I1 J1 T J2, racahG_symm₅ θ I1 c I2 d T J1, delta2G_swap23 θ J1 T I1,
    delta2G_swap12 θ J1 I1 T]
  unfold klK
  rw [pow_add]
  ring

/-! ## Admissibility and the triangles of the middle colour -/

/-- A triangle `(x, y, z)` in multiplied-out form: `x + y = z + 2u` with `u ≤ x`, `u ≤ y`,
`u = (x + y - z)/2`. -/
theorem tri_halves {x y z : ℕ} (h : Tri x y z) :
    x + y = z + 2 * ((x + y - z) / 2) ∧ (x + y - z) / 2 ≤ x ∧ (x + y - z) / 2 ≤ y := by
  unfold Tri at h; omega

/-- **The three admissibilities of the left side of the pentagon from the triangles of `x`**
(in multiplied-out form). -/
theorem kladm_of_tri {a b c d e f p q r' e₀ d₀ g₀ j m i fi x h dd : ℕ}
    (hx : x + 2 * fi = a + b) (hfa : fi ≤ a) (hfb : fi ≤ b)
    (hh : x + c = d + 2 * h) (hhx : h ≤ x) (hhc : h ≤ c)
    (hdd : e + x = f + 2 * dd) (hde : dd ≤ e) (hdx : dd ≤ x)
    (h1 : e + a = r' + 2 * e₀) (h1a : e₀ ≤ e) (h1b : e₀ ≤ a)
    (h2 : r' + b = f + 2 * d₀) (h2a : d₀ ≤ r') (h2b : d₀ ≤ b)
    (h3 : f + c = q + 2 * g₀) (h3a : g₀ ≤ f) (h3b : g₀ ≤ c)
    (h4 : b + c = p + 2 * j) (h4a : j ≤ b) (h4b : j ≤ c)
    (h5 : a + p = d + 2 * m) (h5a : m ≤ a) (h5b : m ≤ p)
    (h6 : e + d = q + 2 * i) (h6a : i ≤ e) (h6b : i ≤ d) :
    KLAdm a b c fi h j m ∧ KLAdm e (a + b - 2 * fi) c dd g₀ h i ∧ KLAdm e a b e₀ d₀ fi dd := by
  unfold KLAdm
  simp only [le_min_iff]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩,
    ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩ <;> omega

/-- **The triangles of `x` from the admissibilities** (the converse of `kladm_of_tri`). -/
theorem tri_of_kladm {a b c d e f p r' e₀ d₀ j m fi h dd : ℕ}
    (h1 : e + a = r' + 2 * e₀) (h2 : r' + b = f + 2 * d₀)
    (h4 : b + c = p + 2 * j) (_h4a : j ≤ b) (_h4b : j ≤ c) (h5 : a + p = d + 2 * m) (h5a : m ≤ a)
    (h5b : m ≤ p)
    (A1 : KLAdm a b c fi h j m) (A3 : KLAdm e a b e₀ d₀ fi dd) :
    Tri a b (a + b - 2 * fi) ∧ Tri c d (a + b - 2 * fi) ∧ Tri e f (a + b - 2 * fi) := by
  unfold KLAdm at A1 A3
  simp only [le_min_iff] at A1 A3
  obtain ⟨⟨a11, a12⟩, ⟨a21, a22⟩, -, -, a5⟩ := A1
  obtain ⟨⟨b11, b12⟩, ⟨b21, b22⟩, -, ⟨b41, b42⟩, b5⟩ := A3
  unfold Tri
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> omega

theorem tri_swap {x y z : ℕ} (h : Tri x y z) : Tri y x z := by unfold Tri at *; omega

theorem tri_rot {x y z : ℕ} (h : Tri x y z) : Tri y z x := by unfold Tri at *; omega

/-- The q-Racah sum vanishes when a face sum exceeds a pair sum (its support is empty). -/
theorem racahG_eq_zero_of_lt (θ : ℝ) {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}
    (h : min ((j₁ + j₂ + j₄ + j₅) / 2) (min ((j₂ + j₃ + j₅ + j₆) / 2) ((j₃ + j₁ + j₆ + j₄) / 2)) <
      max (max ((j₁ + j₂ + j₃) / 2) ((j₁ + j₅ + j₆) / 2)) (max ((j₄ + j₂ + j₆) / 2) ((j₄ + j₅ + j₃) / 2))) :
    racahG θ j₁ j₂ j₃ j₄ j₅ j₆ = 0 := by
  rw [racahG_eq_Icc, Icc_eq_empty (by omega), sum_empty]

/-- **Reindexing the sum of `GenBE`** by `x = a + b - 2f`: a function supported on the triangles
`(a, b, x)` sums over `x ≤ a + b` as over `f ≤ min a b`. -/
theorem sum_reindex {a b : ℕ} (g : ℕ → ℝ) (hg : ∀ x, g x ≠ 0 → Tri a b x) :
    ∑ fi ∈ range (a + 1), (if fi ≤ min a b then g (a + b - 2 * fi) else 0) =
      ∑ x ∈ range (a + b + 1), g x := by
  refine sum_bij_ne_zero (fun fi _ _ => a + b - 2 * fi) ?_ ?_ ?_ ?_
  · intro fi hfi hne
    simp only [mem_range] at hfi ⊢
    omega
  · intro f₁ h₁₁ h₁₂ f₂ h₂₁ h₂₂ heq
    have k1 : f₁ ≤ min a b := by by_contra hc; exact h₁₂ (by rw [ite_eq_right hc])
    have k2 : f₂ ≤ min a b := by by_contra hc; exact h₂₂ (by rw [ite_eq_right hc])
    simp only [le_min_iff] at k1 k2
    omega
  · intro x hx hgx
    have ht := hg x hgx
    unfold Tri at ht
    refine ⟨(a + b - x) / 2, by simp only [mem_range]; omega, ?_, ?_⟩
    · rw [ite_eq_left (by simp only [le_min_iff]; omega),
        show a + b - 2 * ((a + b - x) / 2) = x by omega]
      exact hgx
    · omega
  · intro fi _ hne
    have k : fi ≤ min a b := by by_contra hc; exact hne (by rw [ite_eq_right hc])
    rw [ite_eq_left k]

/-! ## The generic Biedenharn–Elliott identity, positive colours -/

/-- The admissibilities of the right side of the pentagon from the triangle `(r', p, q)`. -/
theorem kladm_right_of_tri {a b c d e f p q r' e₀ d₀ g₀ j m i gF : ℕ}
    (hg : r' + p = q + 2 * gF) (hgr : gF ≤ r') (hgp : gF ≤ p)
    (h1 : e + a = r' + 2 * e₀) (h1a : e₀ ≤ e) (h1b : e₀ ≤ a)
    (h2 : r' + b = f + 2 * d₀) (h2a : d₀ ≤ r') (h2b : d₀ ≤ b)
    (h3 : f + c = q + 2 * g₀) (h3a : g₀ ≤ f) (h3b : g₀ ≤ c)
    (h4 : b + c = p + 2 * j) (h4a : j ≤ b) (h4b : j ≤ c)
    (h5 : a + p = d + 2 * m) (h5a : m ≤ a) (h5b : m ≤ p)
    (h6 : e + d = q + 2 * i) (h6a : i ≤ e) (h6b : i ≤ d) :
    KLAdm e a p e₀ gF m i ∧ KLAdm r' b c d₀ g₀ j gF := by
  unfold KLAdm
  simp only [le_min_iff]
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩⟩ <;> omega

theorem gaugeI_ne_zero (θ : ℝ) {N a b c i D : ℕ} (hq : ∀ n, n ≤ N → qfG θ n ≠ 0)
    (h1 : triPi θ a b i ≠ 0) (h2 : triPi θ i c D ≠ 0) (hi : i + 1 ≤ N) : gaugeI θ a b c i D ≠ 0 :=
  div_ne_zero (mul_ne_zero h1 h2) (hq _ hi)

theorem gaugeJ_ne_zero (θ : ℝ) {N a b c j D : ℕ} (hq : ∀ n, n ≤ N → qfG θ n ≠ 0)
    (h1 : triPi θ b c j ≠ 0) (h2 : triPi θ a j D ≠ 0) (hj : j + 1 ≤ N) : gaugeJ θ a b c j D ≠ 0 :=
  div_ne_zero (mul_ne_zero h1 h2) (hq _ hj)

theorem delta2G_ne_zero (θ : ℝ) {N x y z : ℕ} (hq : ∀ n, n ≤ N → qfG θ n ≠ 0)
    (h : triPi θ x y z ≠ 0) (hs : (x + y + z) / 2 + 1 ≤ N) : delta2G θ x y z ≠ 0 := by
  rw [delta2G_eq_triPi]; exact div_ne_zero h (hq _ hs)

/-- The q-Racah sum of the right side of `GenBE` vanishes when `(p, q, r')` violates a triangle
inequality (its support is empty). -/
theorem racahG_eq_zero_of_tri_fail (θ : ℝ) {p q r' e a d e₀ m i : ℕ} (h1 : e + a = r' + 2 * e₀)
    (h5 : a + p = d + 2 * m) (h6 : e + d = q + 2 * i) (hpar : (p + q + r') % 2 = 0)
    (hn : r' + p < q ∨ q + r' < p ∨ p + q < r') : racahG θ p q r' e a d = 0 := by
  apply racahG_eq_zero_of_lt
  rcases hn with h | h | h
  · have k : (r' + p + d + e) / 2 < (e + q + d) / 2 := by omega
    exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
      (lt_of_lt_of_le k ((le_max_left _ _).trans (le_max_right _ _)))
  · have k : (q + r' + a + d) / 2 < (p + a + d) / 2 := by omega
    exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
      (lt_of_lt_of_le k ((le_max_right _ _).trans (le_max_left _ _)))
  · have k : (p + q + e + a) / 2 < (e + a + r') / 2 := by omega
    exact lt_of_le_of_lt (min_le_left _ _)
      (lt_of_lt_of_le k ((le_max_right _ _).trans (le_max_right _ _)))


theorem triPi_ne_zero' (θ : ℝ) {M x y z : ℕ} (hq : ∀ n, n ≤ M → qfG θ n ≠ 0) (h : x + y + z ≤ 2 * M) :
    triPi θ x y z ≠ 0 :=
  triPi_ne_zero θ hq (by omega) (by omega) (by omega)

set_option maxHeartbeats 1000000 in
/-- **One term of the left side of the pentagon at `q = e^{iθ}`** is the summand of `GenBE` at
`x = a + b - 2f`, times the gauge `G` and the common factor `C`. -/
theorem genBE_left_term (θ : ℝ) {a b c d e f p q r' e₀ d₀ g₀ j m i M : ℕ}
    (hqf : ∀ n, n ≤ M → qfG θ n ≠ 0) (hM : 2 * (a + b + c + d + e + f + p + q + r') + 4 ≤ M)
    (h1 : e + a = r' + 2 * e₀) (h1a : e₀ ≤ e) (h1b : e₀ ≤ a)
    (h2 : r' + b = f + 2 * d₀) (h2a : d₀ ≤ r') (h2b : d₀ ≤ b)
    (h3 : f + c = q + 2 * g₀) (h3a : g₀ ≤ f) (h3b : g₀ ≤ c)
    (h4 : b + c = p + 2 * j) (h4a : j ≤ b) (h4b : j ≤ c)
    (h5 : a + p = d + 2 * m) (h5a : m ≤ a) (h5b : m ≤ p)
    (h6 : e + d = q + 2 * i) (h6a : i ≤ e) (h6b : i ≤ d)
    (hI1 : e + a - 2 * e₀ = r') (hI2 : r' + b - 2 * d₀ = f) (hTq : f + c - 2 * g₀ = q)
    (hJ1 : b + c - 2 * j = p) :
    ∀ fi ∈ range (a + 1),
      klCoef (qE θ) a b c fi ((a + b - 2 * fi + c - d) / 2) j m *
        (klCoef (qE θ) e (a + b - 2 * fi) c ((e + (a + b - 2 * fi) - f) / 2) g₀
            ((a + b - 2 * fi + c - d) / 2) i *
          klCoef (qE θ) e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)) =
      (((gaugeJ θ e a p d q / gaugeI θ e a p r' q * (gaugeJ θ r' b c p q / gaugeI θ r' b c f q)) *
        ((-1 : ℝ) ^ (r' + (e + a + r') / 2 + (r' + p + q) / 2 + (f + (r' + b + f) / 2 + (f + c + q) / 2)) *
          (qnG θ (p + 1) * qnG θ (d + 1) * delta2G θ e a r' * delta2G θ r' b f * delta2G θ f c q)) *
        (if fi ≤ min a b then genBETerm θ a b c d e f p q r' (a + b - 2 * fi) else 0) : ℝ) : ℂ) := by
  have hTP : ∀ x y z : ℕ, x + y + z ≤ 2 * M → triPi θ x y z ≠ 0 := fun x y z h => triPi_ne_zero' θ hqf h
  intro fi hfi
  rw [mem_range] at hfi
  have hq1 : ∀ n, n ≤ a + b + c + 1 → qfG θ n ≠ 0 := fun n hn => hqf n (by omega)
  have hq2 : ∀ n, n ≤ e + (a + b - 2 * fi) + c + 1 → qfG θ n ≠ 0 := fun n hn => hqf n (by omega)
  have hq3 : ∀ n, n ≤ e + a + b + 1 → qfG θ n ≠ 0 := fun n hn => hqf n (by omega)
  by_cases hA : KLAdm a b c fi ((a + b - 2 * fi + c - d) / 2) j m ∧
      KLAdm e (a + b - 2 * fi) c ((e + (a + b - 2 * fi) - f) / 2) g₀ ((a + b - 2 * fi + c - d) / 2) i ∧
      KLAdm e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)
  · obtain ⟨A1, A2, A3⟩ := hA
    obtain ⟨T1, T2, T3⟩ := tri_of_kladm h1 h2 h4 h4a h4b h5 h5a h5b A1 A3
    have hfm : fi ≤ min a b := A3.2.2.1
    rw [klCoef_qE θ A1 hq1, klCoef_qE θ A2 hq2, klCoef_qE θ A3 hq3, ite_eq_left hfm]
    clear A1 A2 A3 hfm hq1 hq2 hq3
    unfold genBETerm
    rw [ite_eq_left ⟨T1, T2, T3⟩]
    unfold Tri at T1 T2 T3
    have hx1 : a + b - 2 * fi + c - 2 * ((a + b - 2 * fi + c - d) / 2) = d := by omega
    have hx2 : e + (a + b - 2 * fi) - 2 * ((e + (a + b - 2 * fi) - f) / 2) = f := by omega
    rw [hJ1, hx1, hx2, hTq, hI1, hI2, ← ofReal_mul, ← ofReal_mul, ofReal_inj]
    have hg := gauge_cancel θ (a := e) (b := a) (c := b) (d := c) (x := a + b - 2 * fi) (I1 := r') (I2 := f)
      (T := q) (J1 := p) (J2 := d) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega))
      (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega))
      (hqf _ (by omega)) (hqf _ (by omega)) (hqf _ (by omega)) (hqf _ (by omega)) (hqf _ (by omega))
    have hk := klK_left θ (a := e) (b := a) (c := b) (d := c) (x := a + b - 2 * fi) (I1 := r') (I2 := f)
      (T := q) (J1 := p) (J2 := d) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
    calc _ = (gaugeJ θ a b c p d / gaugeI θ a b c (a + b - 2 * fi) d *
            (gaugeJ θ e (a + b - 2 * fi) c d q / gaugeI θ e (a + b - 2 * fi) c f q *
              (gaugeJ θ e a b (a + b - 2 * fi) f / gaugeI θ e a b r' f))) *
          (klK θ a b c (a + b - 2 * fi) d p *
            (klK θ e (a + b - 2 * fi) c f q d * klK θ e a b r' f (a + b - 2 * fi))) := by ring
      _ = _ := by rw [hg, hk]; ring
  · have h0 : klCoef (qE θ) a b c fi ((a + b - 2 * fi + c - d) / 2) j m *
        (klCoef (qE θ) e (a + b - 2 * fi) c ((e + (a + b - 2 * fi) - f) / 2) g₀
            ((a + b - 2 * fi + c - d) / 2) i *
          klCoef (qE θ) e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)) = 0 := by
      by_cases A1 : KLAdm a b c fi ((a + b - 2 * fi + c - d) / 2) j m
      · by_cases A3 : KLAdm e a b e₀ d₀ fi ((e + (a + b - 2 * fi) - f) / 2)
        · exfalso
          obtain ⟨T1, T2, T3⟩ := tri_of_kladm h1 h2 h4 h4a h4b h5 h5a h5b A1 A3
          have hfa : fi ≤ a := A3.2.2.1.trans (min_le_left _ _)
          have hfb : fi ≤ b := A3.2.2.1.trans (min_le_right _ _)
          clear A1 A3 hq1 hq2 hq3
          unfold Tri at T1 T2 T3
          refine hA (kladm_of_tri (x := a + b - 2 * fi) (by omega) hfa hfb (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b h5 h5a h5b h6 h6a h6b)
        · rw [klCoef_of_not _ A3, mul_zero, mul_zero]
      · rw [klCoef_of_not _ A1, zero_mul]
    rw [h0]
    have hz : (if fi ≤ min a b then genBETerm θ a b c d e f p q r' (a + b - 2 * fi) else 0) = 0 := by
      split_ifs with hfm
      · unfold genBETerm
        refine ite_eq_right fun hT => hA ?_
        obtain ⟨T1, T2, T3⟩ := hT
        unfold Tri at T1 T2 T3
        simp only [le_min_iff] at hfm
        obtain ⟨hfa, hfb⟩ := hfm
        clear hq1 hq2 hq3
        exact kladm_of_tri (x := a + b - 2 * fi) (by omega) hfa hfb (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b h5 h5a h5b h6 h6a h6b
      · rfl
    rw [hz, mul_zero, ofReal_zero]

set_option maxHeartbeats 1000000 in
/-- **The generic Biedenharn–Elliott identity when the colours `e`, `a`, `b` are positive**, from the
Temperley–Lieb pentagon at `q = e^{iθ}` and `FcEqKL ℂ`. -/
theorem genBE_of_pos (hKL : FcEqKL ℂ) (θ : ℝ) {a b c d e f p q r' : ℕ}
    (hθ : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c + d + e + f + p + q + r') + 4 → Real.sin (n * θ) ≠ 0)
    (he : 1 ≤ e) (ha : 1 ≤ a) (hb : 1 ≤ b) : GenBE θ a b c d e f p q r' := by
  intro t1 t2 t3 t4 t5 t6
  obtain ⟨h1, h1a, h1b⟩ := tri_halves t5
  obtain ⟨h2, h2a, h2b⟩ := tri_halves (tri_rot (tri_rot t6))
  obtain ⟨h3, h3a, h3b⟩ := tri_halves (tri_swap t3)
  obtain ⟨h4, h4a, h4b⟩ := tri_halves (tri_swap t2)
  obtain ⟨h5, h5a, h5b⟩ := tri_halves (tri_swap (tri_rot (tri_rot t1)))
  obtain ⟨h6, h6a, h6b⟩ := tri_halves t4
  clear t1 t2 t3 t4 t5 t6
  set e₀ := (e + a - r') / 2
  set d₀ := (r' + b - f) / 2
  set g₀ := (f + c - q) / 2
  set j := (b + c - p) / 2
  set m := (a + p - d) / 2
  set i := (e + d - q) / 2
  set N := 2 * (a + b + c + d + e + f + p + q + r') + 4
  have hs1 : Real.sin θ ≠ 0 := by simpa using hθ 1 le_rfl (by omega)
  have hqf : ∀ n, n ≤ N → qfG θ n ≠ 0 := qfG_ne_zero hθ hs1
  have hI1 : e + a - 2 * e₀ = r' := by omega
  have hI2 : r' + b - 2 * d₀ = f := by omega
  have hTq : f + c - 2 * g₀ = q := by omega
  have hJ1 : b + c - 2 * j = p := by omega
  have hJ2 : a + p - 2 * m = d := by omega
  have hTi : e + d - 2 * i = q := by omega
  have P := pentagon_klCoef hKL (qE θ) (loopVal_qE_ne_zero (hθ 2 (by omega) (by omega)))
    e a b c e₀ d₀ g₀ j m i he ha hb
    (fun x hx => chebD_qE_ne_zero hs1 (hθ (x + 1) (by omega) (by omega)))
    (fun n h1 h2 => qE_pow_ne_one (hθ n h1 (by omega)))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨by simp only [le_min_iff]; omega, by simp only [le_min_iff]; omega, by omega, by omega⟩
  rw [hJ1, hJ2, hI1, hI2, hTi] at P
  have hTP : ∀ x y z : ℕ, (x + y + z) / 2 ≤ N → triPi θ x y z ≠ 0 := fun x y z h =>
    triPi_ne_zero θ hqf (by omega) (by omega) (by omega)
  have hqn : ∀ n, n + 1 ≤ N → qnG θ (n + 1) ≠ 0 := fun n hn =>
    qnG_ne_zero hs1 (by exact_mod_cast hθ (n + 1) (by omega) hn)
  set G := gaugeJ θ e a p d q / gaugeI θ e a p r' q * (gaugeJ θ r' b c p q / gaugeI θ r' b c f q) with hG
  set C := (-1 : ℝ) ^ (r' + (e + a + r') / 2 + (r' + p + q) / 2 + (f + (r' + b + f) / 2 + (f + c + q) / 2)) *
      (qnG θ (p + 1) * qnG θ (d + 1) * delta2G θ e a r' * delta2G θ r' b f * delta2G θ f c q) with hC
  have hG0 : G ≠ 0 := by
    refine mul_ne_zero (div_ne_zero ?_ ?_) (div_ne_zero ?_ ?_)
    · exact gaugeJ_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
    · exact gaugeI_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
    · exact gaugeJ_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
    · exact gaugeI_ne_zero θ hqf (hTP _ _ _ (by omega)) (hTP _ _ _ (by omega)) (by omega)
  have hC0 : C ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hqn p (by omega)) (hqn d (by omega))) ?_) ?_) ?_
    · exact delta2G_ne_zero θ hqf (hTP _ _ _ (by omega)) (by omega)
    · exact delta2G_ne_zero θ hqf (hTP _ _ _ (by omega)) (by omega)
    · exact delta2G_ne_zero θ hqf (hTP _ _ _ (by omega)) (by omega)
  -- the left side, term by term
  have hL := genBE_left_term θ hqf (le_refl _) h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b h5 h5a h5b h6 h6a h6b hI1 hI2 hTq hJ1
  -- the right side
  have hR : klCoef (qE θ) e a p e₀ ((r' + p - q) / 2) m i * klCoef (qE θ) r' b c d₀ g₀ j ((r' + p - q) / 2) =
      ((G * C * (delta2G θ p q r' * racahG θ p q r' e a d * racahG θ p q r' f b c) : ℝ) : ℂ) := by
    by_cases hpq : r' + p = q + 2 * ((r' + p - q) / 2) ∧ (r' + p - q) / 2 ≤ r' ∧ (r' + p - q) / 2 ≤ p
    · obtain ⟨A4, A5⟩ := kladm_right_of_tri hpq.1 hpq.2.1 hpq.2.2 h1 h1a h1b h2 h2a h2b h3 h3a h3b h4 h4a h4b
        h5 h5a h5b h6 h6a h6b
      have hgq : r' + p - 2 * ((r' + p - q) / 2) = q := by omega
      rw [klCoef_qE θ A4 (fun n hn => hqf n (by omega)), klCoef_qE θ A5 (fun n hn => hqf n (by omega))]
      rw [hI1, hgq, hJ2, hI2, hTq, hJ1, ← ofReal_mul, ofReal_inj]
      have hk := klK_right θ (a := e) (b := a) (c := b) (d := c) (I1 := r') (I2 := f) (T := q) (J1 := p) (J2 := d)
      calc _ = G * (klK θ e a p r' q d * klK θ r' b c f q p) := by rw [hG]; ring
        _ = _ := by rw [hk]; ring
    · have h4' : ¬ KLAdm e a p e₀ ((r' + p - q) / 2) m i := fun A4 => hpq (by
        unfold KLAdm at A4; simp only [le_min_iff] at A4; omega)
      rw [klCoef_of_not _ h4', zero_mul]
      have hpar : (p + q + r') % 2 = 0 := by omega
      have hn : r' + p < q ∨ q + r' < p ∨ p + q < r' := by omega
      have hz : racahG θ p q r' e a d = 0 := racahG_eq_zero_of_tri_fail θ h1 h5 h6 hpar hn
      rw [hz, mul_zero, zero_mul, mul_zero, ofReal_zero]
  rw [sum_congr rfl hL, hR] at P
  rw [← ofReal_sum, ofReal_inj, ← mul_sum] at P
  have P' := mul_left_cancel₀ (mul_ne_zero hG0 hC0) P
  rw [← P']
  exact (sum_reindex (genBETerm θ a b c d e f p q r') fun x hx => by
    unfold genBETerm at hx; split_ifs at hx with h; exact h.1; exact absurd rfl hx).symm

end Lightlike.TV
