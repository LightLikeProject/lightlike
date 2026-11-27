import Mathlib
import Lightlike.TemperleyLieb.Pentagon
import Lightlike.TemperleyLieb.KLCoef
import Lightlike.TuraevViro.QSixJGeneric

/-!
# The Kauffman–Lins nets at `q = e^{iθ}`

Preparation for the generic Biedenharn–Elliott identity `GenBE θ` (`Lightlike.TV.GenBE`), to be
derived from the pentagon identity `TemperleyLieb.pentagon` of the recoupling coefficients `Fc` of the
Temperley–Lieb model at `q = e^{iθ}`, given that `Fc` is the Kauffman–Lins coefficient `klCoef` on its
admissible indices (`TemperleyLieb.FcEqKL ℂ`).  This file writes the Kauffman–Lins nets at
`q = e^{iθ}` in the real quantities of `QSixJGeneric`:

* `Fc_eq_klCoef_of`: with `FcEqKL`, `Fc = klCoef` on every index in range (off the admissible totals
  both vanish, `TemperleyLieb.Fc_total`);
* `qb_qE`, `qfac_qE`: at `q = e^{iθ}` the quantum integers and factorials of the Temperley–Lieb model
  are `[n]_θ = sin(nθ)/sin θ` and `[n]_θ!` (`qnG`, `qfG`), with no condition on `θ`;
* `racahG_eq_Icc`: the q-Racah sum `racahG` is the sum of its summand `racahTermN` over its support;
* `tetKL_qE`, `tetPreN_eq`: the tetrahedral net is the product of the four triads `triPi` over the
  edges times `racahG θ a b i c D j`;
* `thetaKL_qE`, `deltaKL_qE`: the theta net and the loop value;
* `gaugeI`, `gaugeJ`, `klK`, `kl_alg`: the gauge form `klCoef = (gaugeJ / gaugeI) · klK` (the gauge
  ratios cancel in the pentagon), with its algebra over atoms, and `klCoef_qE`: at `q = e^{iθ}` the
  Kauffman–Lins coefficient is `(gaugeJ / gaugeI) · klK` on the admissible indices.

The dictionary between the pentagon and `GenBE` (blocks `(a,b,c,d) = (e',a',b',c')`, channels
`I1 = r'`, `I2 = f'`, total `T = q`, `J1 = p`, `J2 = d'`, summed `x = b + c - 2f`, sign
`(-1)^{s(I1,J1,T)}`) was derived and measured by the oscillatory stream (mpmath, 40 digits, worst
relative error `7.7e-40`); it is numerical evidence, not part of the proof.
-/

open Complex Finset

namespace Lightlike.TV

open Lightlike.TemperleyLieb

/-! ## `Fc` off the admissible totals -/

section Vanish

variable {k : Type*} [Field k]

/-- **`Fc = klCoef` on every index in range**, given the statement `FcEqKL` on the admissible ones:
off the admissible totals both sides vanish. -/
theorem Fc_eq_klCoef_of (hKL : FcEqKL k) (q : kˣ) (hδ : loopVal q ≠ 0) {a b c e d f d' : ℕ}
    (hN : 1 ≤ a + b + c) (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0)
    (hq : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * n) ≠ 1)
    (hea : e ≤ a) (heb : e ≤ b) (hfb : f ≤ b) (hfc : f ≤ c) (hdc : d ≤ c) (hdA : d ≤ a + b - 2 * e)
    (hda : d' ≤ a) (hdf : d' ≤ b + c - 2 * f) :
    Fc q a b c e d f d' = klCoef q a b c e d f d' := by
  by_cases hA : KLAdm a b c e d f d'
  · exact hKL q a b c e d f d' hq hA
  · have hne : a + b - 2 * e + c - 2 * d ≠ a + (b + c - 2 * f) - 2 * d' := fun h =>
      hA ⟨le_min hea heb, le_min hdA hdc, le_min hfb hfc, le_min hda hdf, h⟩
    have h0 : Fc q a b c e d f d' = 0 := by
      by_contra h
      exact hne (Fc_total q hδ a b c e d f d' hN hd hfb hfc hda hdf h)
    rw [h0]
    unfold klCoef
    rw [ite_eq_right hA]

end Vanish

/-! ## The quantum numbers at `q = e^{iθ}` -/

/-- The unit `q = e^{iθ}` of `ℂ`. -/
noncomputable def qE (θ : ℝ) : ℂˣ := Units.mk0 (exp (θ * I)) (exp_ne_zero _)

theorem coe_qE (θ : ℝ) : ((qE θ : ℂˣ) : ℂ) = exp (θ * I) := rfl

/-- `e^{iy} - e^{-iy} = 2 i sin y`. -/
theorem exp_sub_exp_neg (y : ℝ) : exp (y * I) - (exp (y * I))⁻¹ = 2 * I * (Real.sin y : ℂ) := by
  rw [← exp_neg, ofReal_sin, sin]
  ring_nf
  rw [I_sq]
  ring_nf

/-- **The quantum integer at `q = e^{iθ}`** is `[n]_θ = sin(nθ)/sin θ`. -/
theorem qb_qE (θ : ℝ) (n : ℕ) : qb (qE θ) n = (qnG θ n : ℂ) := by
  rw [qb_eq, coe_qE, ← exp_nat_mul, show (n : ℂ) * (θ * I) = ((n * θ : ℝ) : ℂ) * I by push_cast; ring,
    exp_sub_exp_neg, exp_sub_exp_neg, qnG, ofReal_div]
  by_cases hs : Real.sin θ = 0
  · simp [hs]
  · have hI : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
    rw [mul_div_mul_left _ _ hI]

/-- **The quantum factorial at `q = e^{iθ}`** is `[n]_θ!`. -/
theorem qfac_qE (θ : ℝ) (n : ℕ) : qfac (qE θ) n = (qfG θ n : ℂ) := by
  induction n with
  | zero => simp [qfac, qfG]
  | succ n ih =>
    rw [qfac, ih, qb_qE, ← ofReal_mul]
    congr 1
    simp only [qfG, prod_range_succ]

/-! ## The Racah sum on its support -/

/-- The q-Racah summand on its support `F_k ≤ z ≤ B_l`, with natural face and pair sums. -/
noncomputable def racahTermN (θ : ℝ) (F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ) : ℝ :=
  (-1) ^ z * qfG θ (z + 1) /
    (qfG θ (z - F₁) * qfG θ (z - F₂) * qfG θ (z - F₃) * qfG θ (z - F₄) *
      (qfG θ (B₁ - z) * qfG θ (B₂ - z) * qfG θ (B₃ - z)))

theorem invQFG_sub_of_le (θ : ℝ) {u v : ℕ} (h : u ≤ v) :
    invQFG θ ((v : ℤ) - u) = (qfG θ (v - u))⁻¹ := by
  rw [invQFG, ite_eq_left (by omega)]
  congr 2
  omega

theorem invQFG_sub_of_lt (θ : ℝ) {u v : ℕ} (h : v < u) : invQFG θ ((v : ℤ) - u) = 0 := by
  rw [invQFG, ite_eq_right (by omega)]

/-- The summand of `racahG` is `racahTermN` on the support and `0` off it. -/
theorem racahTermG_eq (θ : ℝ) (F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ) :
    racahTermG θ F₁ F₂ F₃ F₄ B₁ B₂ B₃ z =
      if F₁ ≤ z ∧ F₂ ≤ z ∧ F₃ ≤ z ∧ F₄ ≤ z ∧ z ≤ B₁ ∧ z ≤ B₂ ∧ z ≤ B₃ then
        racahTermN θ F₁ F₂ F₃ F₄ B₁ B₂ B₃ z else 0 := by
  unfold racahTermG
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [invQFG_sub_of_le θ h1, invQFG_sub_of_le θ h2, invQFG_sub_of_le θ h3, invQFG_sub_of_le θ h4,
      invQFG_sub_of_le θ h5, invQFG_sub_of_le θ h6, invQFG_sub_of_le θ h7, racahTermN]
    field_simp
  · simp only [not_and_or, not_le] at h
    rcases h with h | h | h | h | h | h | h
    · rw [invQFG_sub_of_lt θ h]; simp
    · rw [invQFG_sub_of_lt θ h]; simp
    · rw [invQFG_sub_of_lt θ h]; simp
    · rw [invQFG_sub_of_lt θ h]; simp
    · rw [invQFG_sub_of_lt θ h]; simp
    · rw [invQFG_sub_of_lt θ h]; simp
    · rw [invQFG_sub_of_lt θ h]; simp

/-- **The q-Racah sum on its support**: the sum of `racahTermN` over
`max F_k ≤ z ≤ min B_l`, for the face sums `α` and the pair sums `β` of `racahG`. -/
theorem racahG_eq_Icc (θ : ℝ) (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    racahG θ j₁ j₂ j₃ j₄ j₅ j₆ =
      ∑ z ∈ Icc (max (max ((j₁ + j₂ + j₃) / 2) ((j₁ + j₅ + j₆) / 2))
                  (max ((j₄ + j₂ + j₆) / 2) ((j₄ + j₅ + j₃) / 2)))
          (min ((j₁ + j₂ + j₄ + j₅) / 2) (min ((j₂ + j₃ + j₅ + j₆) / 2) ((j₃ + j₁ + j₆ + j₄) / 2))),
        racahTermN θ ((j₁ + j₂ + j₃) / 2) ((j₁ + j₅ + j₆) / 2) ((j₄ + j₂ + j₆) / 2)
          ((j₄ + j₅ + j₃) / 2) ((j₁ + j₂ + j₄ + j₅) / 2) ((j₂ + j₃ + j₅ + j₆) / 2)
          ((j₃ + j₁ + j₆ + j₄) / 2) z := by
  unfold racahG
  simp_rw [racahTermG_eq]
  rw [← sum_filter]
  refine sum_congr ?_ fun z _ => rfl
  ext z
  simp only [mem_filter, mem_range, mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨-, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6, h7⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6, h7⟩
    exact ⟨by omega, h1, h2, h3, h4, h5, h6, h7⟩

/-! ## The Kauffman–Lins nets at `q = e^{iθ}` -/

theorem racahTermN_perm (θ : ℝ) (F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ) :
    racahTermN θ F₁ F₄ F₃ F₂ B₃ B₁ B₂ z = racahTermN θ F₁ F₂ F₃ F₄ B₁ B₂ B₃ z := by
  unfold racahTermN; ring

theorem sum_racahTermN_perm (θ : ℝ) (F₁ F₂ F₃ F₄ B₁ B₂ B₃ : ℕ) :
    ∑ z ∈ Icc (max (max F₁ F₄) (max F₃ F₂)) (min B₃ (min B₁ B₂)), racahTermN θ F₁ F₄ F₃ F₂ B₃ B₁ B₂ z =
      ∑ z ∈ Icc (max (max F₁ F₂) (max F₃ F₄)) (min B₁ (min B₂ B₃)),
        racahTermN θ F₁ F₂ F₃ F₄ B₁ B₂ B₃ z :=
  sum_congr (by congr 1 <;> omega) fun z _ => racahTermN_perm θ _ _ _ _ _ _ _ z

theorem tetTerm_qE (θ : ℝ) (F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ) :
    tetTerm (qE θ) F₁ F₂ F₃ F₄ B₁ B₂ B₃ z = (racahTermN θ F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℂ) := by
  simp only [tetTerm, racahTermN, qfac_qE]
  push_cast
  ring

/-- The prefactor of the tetrahedral net, over `ℝ` at the angle `θ`. -/
noncomputable def tetPreN (θ : ℝ) (a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ : ℕ) : ℝ :=
  (qfG θ (B₁ - F₁) * qfG θ (B₁ - F₂) * qfG θ (B₁ - F₃) * qfG θ (B₁ - F₄)) *
    (qfG θ (B₂ - F₁) * qfG θ (B₂ - F₂) * qfG θ (B₂ - F₃) * qfG θ (B₂ - F₄)) *
    (qfG θ (B₃ - F₁) * qfG θ (B₃ - F₂) * qfG θ (B₃ - F₃) * qfG θ (B₃ - F₄)) /
    (qfG θ a * qfG θ b * qfG θ c * qfG θ D * qfG θ i * qfG θ j)

/-- **The tetrahedral net at `q = e^{iθ}`** is its prefactor times the q-Racah sum
`racahG θ a b i c D j`. -/
theorem tetKL_qE (θ : ℝ) (a b c D i j : ℕ) :
    tetKL (qE θ) a b c D i j =
      ((tetPreN θ a b c D i j ((a + b + i) / 2) ((i + c + D) / 2) ((b + c + j) / 2) ((a + j + D) / 2)
        ((b + D + i + j) / 2) ((a + c + i + j) / 2) ((a + b + c + D) / 2) *
        racahG θ a b i c D j : ℝ) : ℂ) := by
  have e1 : (a + D + j) / 2 = (a + j + D) / 2 := by ring_nf
  have e2 : (c + b + j) / 2 = (b + c + j) / 2 := by ring_nf
  have e3 : (c + D + i) / 2 = (i + c + D) / 2 := by ring_nf
  have e4 : (b + i + D + j) / 2 = (b + D + i + j) / 2 := by ring_nf
  have e5 : (i + a + j + c) / 2 = (a + c + i + j) / 2 := by ring_nf
  rw [racahG_eq_Icc, e1, e2, e3, e4, e5]
  rw [sum_racahTermN_perm]
  unfold tetKL
  simp only [tetPre, tetPreN, qfac_qE, tetTerm_qE]
  push_cast
  rfl

/-! ## The gauge form of `klCoef` -/

/-- The product `[s-x]! [s-y]! [s-z]!` of a triad, `s = (x+y+z)/2`. -/
noncomputable def triPi (θ : ℝ) (x y z : ℕ) : ℝ :=
  qfG θ ((x + y + z) / 2 - x) * qfG θ ((x + y + z) / 2 - y) * qfG θ ((x + y + z) / 2 - z)

/-- The gauge of the tree `(a b) c` with channel `i` and total `D`. -/
noncomputable def gaugeI (θ : ℝ) (a b c i D : ℕ) : ℝ :=
  triPi θ a b i * triPi θ i c D / qfG θ (i + 1)

/-- The gauge of the tree `a (b c)` with channel `j` and total `D`. -/
noncomputable def gaugeJ (θ : ℝ) (a b c j D : ℕ) : ℝ :=
  triPi θ b c j * triPi θ a j D / qfG θ (j + 1)

/-- The gauge-free part of the Kauffman–Lins coefficient. -/
noncomputable def klK (θ : ℝ) (a b c i D j : ℕ) : ℝ :=
  (-1) ^ (i + (a + b + i) / 2 + (i + c + D) / 2) * qnG θ (j + 1) * delta2G θ a b i *
    delta2G θ i c D * racahG θ a b i c D j

/-- The twelve indices of the prefactor of the tetrahedral net: each `B_l - F_k` is an `s - x` of
one face (natural-number arithmetic for the channels of `KLAdm`). -/
theorem tetPre_idx {a b c e d f d' i D j : ℕ} (hi : a + b - 2 * e = i) (hD : i + c - 2 * d = D)
    (hj : b + c - 2 * f = j) (h5 : D = a + j - 2 * d') (_h1a : e ≤ a) (_h1b : e ≤ b) (h2i : d ≤ i)
    (h2c : d ≤ c) (h3b : f ≤ b) (h3c : f ≤ c) (h4a : d' ≤ a) (h4j : d' ≤ j) :
    ((b + D + i + j) / 2 - (a + b + i) / 2 = (a + j + D) / 2 - a ∧
      (b + D + i + j) / 2 - (i + c + D) / 2 = (b + c + j) / 2 - c ∧
      (b + D + i + j) / 2 - (b + c + j) / 2 = (i + c + D) / 2 - c ∧
      (b + D + i + j) / 2 - (a + j + D) / 2 = (a + b + i) / 2 - a) ∧
    ((a + c + i + j) / 2 - (a + b + i) / 2 = (b + c + j) / 2 - b ∧
      (a + c + i + j) / 2 - (i + c + D) / 2 = (a + j + D) / 2 - D ∧
      (a + c + i + j) / 2 - (b + c + j) / 2 = (a + b + i) / 2 - b ∧
      (a + c + i + j) / 2 - (a + j + D) / 2 = (i + c + D) / 2 - D) ∧
    ((a + b + c + D) / 2 - (a + b + i) / 2 = (i + c + D) / 2 - i ∧
      (a + b + c + D) / 2 - (i + c + D) / 2 = (a + b + i) / 2 - i ∧
      (a + b + c + D) / 2 - (b + c + j) / 2 = (a + j + D) / 2 - j ∧
      (a + b + c + D) / 2 - (a + j + D) / 2 = (b + c + j) / 2 - j) := by
  subst hi hD hj
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The prefactor of the tetrahedral net** is the product of the four triads over the edges:
each `B_l - F_k` is an `s - x` of one face. -/
theorem tetPreN_eq (θ : ℝ) {a b c e d f d' : ℕ} (h : KLAdm a b c e d f d') :
    tetPreN θ a b c (a + b - 2 * e + c - 2 * d) (a + b - 2 * e) (b + c - 2 * f)
      ((a + b + (a + b - 2 * e)) / 2) (((a + b - 2 * e) + c + (a + b - 2 * e + c - 2 * d)) / 2)
      ((b + c + (b + c - 2 * f)) / 2) ((a + (b + c - 2 * f) + (a + b - 2 * e + c - 2 * d)) / 2)
      ((b + (a + b - 2 * e + c - 2 * d) + (a + b - 2 * e) + (b + c - 2 * f)) / 2)
      ((a + c + (a + b - 2 * e) + (b + c - 2 * f)) / 2) ((a + b + c + (a + b - 2 * e + c - 2 * d)) / 2) =
    triPi θ a b (a + b - 2 * e) * triPi θ (a + b - 2 * e) c (a + b - 2 * e + c - 2 * d) *
      triPi θ b c (b + c - 2 * f) * triPi θ a (b + c - 2 * f) (a + b - 2 * e + c - 2 * d) /
      (qfG θ a * qfG θ b * qfG θ c * qfG θ (a + b - 2 * e + c - 2 * d) * qfG θ (a + b - 2 * e) *
        qfG θ (b + c - 2 * f)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [le_min_iff] at h1 h2 h3 h4
  obtain ⟨⟨k11, k12, k13, k14⟩, ⟨k21, k22, k23, k24⟩, k31, k32, k33, k34⟩ :=
    tetPre_idx (a := a) (b := b) (c := c) (e := e) (d := d) (f := f) (d' := d') rfl rfl rfl h5
      h1.1 h1.2 h2.1 h2.2 h3.1 h3.2 h4.1 h4.2
  unfold tetPreN triPi
  rw [k11, k12, k13, k14, k21, k22, k23, k24, k31, k32, k33, k34]
  ring

theorem neg_one_pow_div (u v w : ℕ) :
    ((-1 : ℝ) ^ u) / ((-1) ^ v * (-1) ^ w) = (-1) ^ (u + v + w) := by
  have hv : ((-1 : ℝ) ^ v) * (-1) ^ v = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have hw : ((-1 : ℝ) ^ w) * (-1) ^ w = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  have hv0 : ((-1 : ℝ) ^ v) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hw0 : ((-1 : ℝ) ^ w) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_add, pow_add, div_eq_iff (mul_ne_zero hv0 hw0)]
  calc (-1 : ℝ) ^ u = (-1) ^ u * ((-1) ^ v * (-1) ^ v) * ((-1) ^ w * (-1) ^ w) := by rw [hv, hw]; ring
    _ = _ := by ring

theorem qfG_succ (θ : ℝ) (n : ℕ) : qfG θ (n + 1) = qfG θ n * qnG θ (n + 1) := by
  simp [qfG, prod_range_succ]


theorem thetaKL_qE (θ : ℝ) (x y z : ℕ) :
    thetaKL (qE θ) x y z = (((-1) ^ ((x + y + z) / 2) * qfG θ ((x + y + z) / 2 + 1) * triPi θ x y z /
      (qfG θ x * qfG θ y * qfG θ z) : ℝ) : ℂ) := by
  unfold thetaKL triPi
  simp only [qfac_qE]
  push_cast
  ring

theorem deltaKL_qE (θ : ℝ) (n : ℕ) : deltaKL (qE θ) n = (((-1) ^ n * qnG θ (n + 1) : ℝ) : ℂ) := by
  unfold deltaKL
  rw [qb_qE]
  push_cast
  ring

theorem delta2G_eq_triPi (θ : ℝ) (x y z : ℕ) :
    delta2G θ x y z = triPi θ x y z / qfG θ ((x + y + z) / 2 + 1) := rfl

/-- The algebra of `klCoef_qE`, over atoms. -/
theorem kl_alg {P₁ P₂ P₃ P₄ A B C D I J I₁ J₁ S₁ S₂ R σ σ₁ σ₂ si : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hP₁ : P₁ ≠ 0) (hP₂ : P₂ ≠ 0) (hI₁ : I₁ ≠ 0) (hJ₁ : J₁ ≠ 0) (hS₁ : S₁ ≠ 0) (hS₂ : S₂ ≠ 0)
    (hσ₁ : σ₁ ≠ 0) (hσ₂ : σ₂ ≠ 0) (hσ : si / (σ₁ * σ₂) = σ) :
    P₁ * P₂ * P₃ * P₄ / (A * B * C * D * I * J) * R * (si * I₁) /
        ((σ₁ * S₁ * P₁ / (A * B * I)) * (σ₂ * S₂ * P₂ / (I * C * D))) =
      (P₃ * P₄ / (J * J₁)) / (P₁ * P₂ / (I * I₁)) * (σ * J₁ * (P₁ / S₁) * (P₂ / S₂) * R) := by
  rw [← hσ]
  field_simp


/-- A triad product of nonvanishing quantum factorials does not vanish. -/
theorem triPi_ne_zero (θ : ℝ) {N x y z : ℕ} (hq : ∀ n, n ≤ N → qfG θ n ≠ 0)
    (hx : (x + y + z) / 2 - x ≤ N) (hy : (x + y + z) / 2 - y ≤ N) (hz : (x + y + z) / 2 - z ≤ N) :
    triPi θ x y z ≠ 0 :=
  mul_ne_zero (mul_ne_zero (hq _ hx) (hq _ hy)) (hq _ hz)

/-- **The Kauffman–Lins coefficient at `q = e^{iθ}`, real form**: the coefficient is the gauge ratio
`gaugeJ / gaugeI` times `klK`, provided the quantum factorials up to `a + b + c + 1` do not vanish. -/
theorem klCoef_qE (θ : ℝ) {a b c e d f d' : ℕ} (hA : KLAdm a b c e d f d')
    (hq : ∀ n, n ≤ a + b + c + 1 → qfG θ n ≠ 0) :
    klCoef (qE θ) a b c e d f d' =
      ((gaugeJ θ a b c (b + c - 2 * f) (a + b - 2 * e + c - 2 * d) /
          gaugeI θ a b c (a + b - 2 * e) (a + b - 2 * e + c - 2 * d) *
        klK θ a b c (a + b - 2 * e) (a + b - 2 * e + c - 2 * d) (b + c - 2 * f) : ℝ) : ℂ) := by
  unfold klCoef
  rw [ite_eq_left hA]
  rw [tetKL_qE]
  rw [tetPreN_eq θ hA]
  rw [thetaKL_qE, thetaKL_qE, deltaKL_qE]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hA
  simp only [le_min_iff] at h1 h2 h3 h4
  simp only [← ofReal_mul, ← ofReal_div]
  rw [ofReal_inj]
  unfold gaugeI gaugeJ klK
  rw [delta2G_eq_triPi, delta2G_eq_triPi, qfG_succ θ (a + b - 2 * e), qfG_succ θ (b + c - 2 * f)]
  have hi1 : a + b - 2 * e + 1 ≤ a + b + c + 1 := by omega
  have hj1 : b + c - 2 * f + 1 ≤ a + b + c + 1 := by omega
  have hqn : ∀ m, m + 1 ≤ a + b + c + 1 → qnG θ (m + 1) ≠ 0 := fun m hm h => by
    have := hq (m + 1) hm; rw [qfG_succ, h, mul_zero] at this; exact this rfl
  refine kl_alg (hq _ (by omega)) (hq _ (by omega)) (hq _ (by omega)) (hq _ (by omega))
    (hq _ (by omega)) (hq _ (by omega))
    (triPi_ne_zero θ hq (by omega) (by omega) (by omega)) (triPi_ne_zero θ hq (by omega) (by omega) (by omega))
    (hqn _ hi1) (hqn _ hj1) (hq _ (by omega)) (hq _ (by omega))
    (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)) (neg_one_pow_div _ _ _)
end Lightlike.TV
