import Mathlib
import Lightlike.TuraevViro.QSixJGenericKL

/-!
# The Temperley–Lieb pentagon at `q = e^{iθ}` in the quantities of `GenBE`

The pieces of the derivation of the generic Biedenharn–Elliott identity `GenBE θ` from the pentagon
identity `TemperleyLieb.pentagon` of the recoupling coefficients `Fc` of the Temperley–Lieb model at
`q = e^{iθ}`, given that `Fc` is the Kauffman–Lins coefficient `klCoef` on its admissible indices
(`TemperleyLieb.FcEqKL`); the assembly is `Lightlike.TV.genBE_of_pos` in `QSixJGenericBE`.

* the side conditions of the pentagon from `sin (nθ) ≠ 0`: `qE_pow_ne_one` (`q^{2n} ≠ 1`),
  `loopVal_qE_ne_zero`, `chebD_qE_ne_zero`, `qfG_ne_zero`;
* the tetrahedral symmetries of `racahG` and the permutations of `delta2G` used by the pentagon
  (`racahG_symm₂` … `racahG_symm₅`);
* the pentagon for `klCoef` with its sums collapsed (`pentagon_klCoef`);
* the gauge cancels (`gauge_cancel`) and the `klK` products are the terms of `GenBE` times a common
  factor (`klK_left`, `klK_right`).
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
    (hq : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * n) ≠ 1)
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
    (hq : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c + d) + 6 → (q : k) ^ (2 * n) ≠ 1)
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
    (hq : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c + d) + 6 → (q : k) ^ (2 * n) ≠ 1)
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

end Lightlike.TV
