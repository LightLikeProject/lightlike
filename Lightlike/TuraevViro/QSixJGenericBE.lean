import Mathlib
import Lightlike.TuraevViro.QSixJGenericPositive

/-!
# The generic Biedenharn–Elliott identity from the Temperley–Lieb pentagon

This file proves `GenBE θ` (`Lightlike.TV.GenBE`, the generic Biedenharn–Elliott identity at the angle
`θ`, without square roots) for every tuple of colours (`genBE_of_generic`), when `sin (nθ) ≠ 0` for
`1 ≤ n ≤ 2 S + 4` (`S` the sum of the nine colours), given the statement `TemperleyLieb.FcEqKL ℂ`
that the recoupling coefficient `Fc` of the Temperley–Lieb model is the Kauffman–Lins coefficient
`klCoef` (layer L4, taken as a hypothesis until it is proved).

* colours with `e, a, b ≥ 1`: `genBE_of_pos` (`QSixJGenericPositive`), from the pentagon;
* `e = 0`, `a = 0` or `b = 0` (the pentagon needs three nonempty blocks): the sum has one term and
  three of the five q-Racah sums have a zero edge, with the closed values `racahG_zero₁`, `₂`, `₄`,
  `₅` (`(-1)^s / Δ²` of a triangle); the identity is then a tetrahedral symmetry of `racahG`
  (`genBE_of_a_zero`, `genBE_of_b_zero`, `genBE_of_e_zero`, unconditional: no `FcEqKL`).

Non-vacuity: `sin_ne_zero_of_lt` (the angle `π/(2S + 5)` satisfies the hypothesis on `θ`); trust
check: `GenBE` at `π/21` for a tuple with `a = 0`, unconditionally.
-/

open Complex Finset Lightlike.Pentagon

namespace Lightlike.TV

open Lightlike.TemperleyLieb

/-- A q-Racah sum whose support is one point `z₀` is its summand there. -/
theorem racahG_single (θ : ℝ) {j₁ j₂ j₃ j₄ j₅ j₆ z₀ : ℕ}
    (hmax : max (max ((j₁ + j₂ + j₃) / 2) ((j₁ + j₅ + j₆) / 2))
      (max ((j₄ + j₂ + j₆) / 2) ((j₄ + j₅ + j₃) / 2)) = z₀)
    (hmin : min ((j₁ + j₂ + j₄ + j₅) / 2) (min ((j₂ + j₃ + j₅ + j₆) / 2) ((j₃ + j₁ + j₆ + j₄) / 2)) = z₀) :
    racahG θ j₁ j₂ j₃ j₄ j₅ j₆ =
      racahTermN θ ((j₁ + j₂ + j₃) / 2) ((j₁ + j₅ + j₆) / 2) ((j₄ + j₂ + j₆) / 2) ((j₄ + j₅ + j₃) / 2)
        ((j₁ + j₂ + j₄ + j₅) / 2) ((j₂ + j₃ + j₅ + j₆) / 2) ((j₃ + j₁ + j₆ + j₄) / 2) z₀ := by
  rw [racahG_eq_Icc, hmax, hmin, Icc_self, sum_singleton]

theorem qfG_zero (θ : ℝ) : qfG θ 0 = 1 := by simp [qfG]

/-- The value of a q-Racah sum with a zero edge, pattern `(0, y, y, u, v, v)`:
`(-1)^s / Δ²(u, y, v)`, `s = (u + y + v)/2`. -/
theorem racahG_zero₁ (θ : ℝ) {y u v : ℕ} (h : Tri u y v)
    (hq : ∀ n, n ≤ (u + y + v) / 2 + 1 → qfG θ n ≠ 0) :
    racahG θ 0 y y u v v = (-1) ^ ((u + y + v) / 2) / delta2G θ u y v := by
  unfold Tri at h
  rw [racahG_single θ (z₀ := (u + y + v) / 2) (by omega) (by omega)]
  unfold racahTermN delta2G
  have k1 : (u + y + v) / 2 - (0 + y + y) / 2 = (u + y + v) / 2 - y := by omega
  have k2 : (u + y + v) / 2 - (0 + v + v) / 2 = (u + y + v) / 2 - v := by omega
  have k3 : (u + y + v) / 2 - (u + y + v) / 2 = 0 := by omega
  have k4 : (u + y + v) / 2 - (u + v + y) / 2 = 0 := by omega
  have k5 : (0 + y + u + v) / 2 - (u + y + v) / 2 = 0 := by omega
  have k6 : (y + y + v + v) / 2 - (u + y + v) / 2 = (u + y + v) / 2 - u := by omega
  have k7 : (y + 0 + v + u) / 2 - (u + y + v) / 2 = 0 := by omega
  simp only [k1, k2, k3, k4, k5, k6, k7, qfG_zero, mul_one, one_mul]
  have f1 := hq ((u + y + v) / 2 - u) (by omega)
  have f2 := hq ((u + y + v) / 2 - y) (by omega)
  have f3 := hq ((u + y + v) / 2 - v) (by omega)
  have f4 := hq ((u + y + v) / 2 + 1) le_rfl
  field_simp

/-- Pattern `(x, 0, x, u, v, u)`: `(-1)^s / Δ²(x, v, u)`, `s = (x + v + u)/2`. -/
theorem racahG_zero₂ (θ : ℝ) {x u v : ℕ} (h : Tri x v u)
    (hq : ∀ n, n ≤ (x + v + u) / 2 + 1 → qfG θ n ≠ 0) :
    racahG θ x 0 x u v u = (-1) ^ ((x + v + u) / 2) / delta2G θ x v u := by
  unfold Tri at h
  rw [racahG_single θ (z₀ := (x + v + u) / 2) (by omega) (by omega)]
  unfold racahTermN delta2G
  have k1 : (x + v + u) / 2 - (x + 0 + x) / 2 = (x + v + u) / 2 - x := by omega
  have k2 : (x + v + u) / 2 - (x + v + u) / 2 = 0 := by omega
  have k3 : (x + v + u) / 2 - (u + 0 + u) / 2 = (x + v + u) / 2 - u := by omega
  have k4 : (x + v + u) / 2 - (u + v + x) / 2 = 0 := by omega
  have k5 : (x + 0 + u + v) / 2 - (x + v + u) / 2 = 0 := by omega
  have k6 : (0 + x + v + u) / 2 - (x + v + u) / 2 = 0 := by omega
  have k7 : (x + x + u + u) / 2 - (x + v + u) / 2 = (x + v + u) / 2 - v := by omega
  simp only [k1, k2, k3, k4, k5, k6, k7, qfG_zero, mul_one, one_mul]
  have f1 := hq ((x + v + u) / 2 - x) (by omega)
  have f2 := hq ((x + v + u) / 2 - v) (by omega)
  have f3 := hq ((x + v + u) / 2 - u) (by omega)
  have f4 := hq ((x + v + u) / 2 + 1) le_rfl
  field_simp

/-- Pattern `(x, y, z, 0, z, y)`: `(-1)^s / Δ²(x, y, z)`, `s = (x + y + z)/2`. -/
theorem racahG_zero₄ (θ : ℝ) {x y z : ℕ} (h : Tri x y z)
    (hq : ∀ n, n ≤ (x + y + z) / 2 + 1 → qfG θ n ≠ 0) :
    racahG θ x y z 0 z y = (-1) ^ ((x + y + z) / 2) / delta2G θ x y z := by
  unfold Tri at h
  rw [racahG_single θ (z₀ := (x + y + z) / 2) (by omega) (by omega)]
  unfold racahTermN delta2G
  have k1 : (x + y + z) / 2 - (x + y + z) / 2 = 0 := by omega
  have k2 : (x + y + z) / 2 - (x + z + y) / 2 = 0 := by omega
  have k3 : (x + y + z) / 2 - (0 + y + y) / 2 = (x + y + z) / 2 - y := by omega
  have k4 : (x + y + z) / 2 - (0 + z + z) / 2 = (x + y + z) / 2 - z := by omega
  have k5 : (x + y + 0 + z) / 2 - (x + y + z) / 2 = 0 := by omega
  have k6 : (y + z + z + y) / 2 - (x + y + z) / 2 = (x + y + z) / 2 - x := by omega
  have k7 : (z + x + y + 0) / 2 - (x + y + z) / 2 = 0 := by omega
  simp only [k1, k2, k3, k4, k5, k6, k7, qfG_zero, mul_one, one_mul]
  have f1 := hq ((x + y + z) / 2 - x) (by omega)
  have f2 := hq ((x + y + z) / 2 - y) (by omega)
  have f3 := hq ((x + y + z) / 2 - z) (by omega)
  have f4 := hq ((x + y + z) / 2 + 1) le_rfl
  field_simp

/-- Pattern `(x, y, z, z, 0, x)`: `(-1)^s / Δ²(x, y, z)`, `s = (x + y + z)/2`. -/
theorem racahG_zero₅ (θ : ℝ) {x y z : ℕ} (h : Tri x y z)
    (hq : ∀ n, n ≤ (x + y + z) / 2 + 1 → qfG θ n ≠ 0) :
    racahG θ x y z z 0 x = (-1) ^ ((x + y + z) / 2) / delta2G θ x y z := by
  unfold Tri at h
  rw [racahG_single θ (z₀ := (x + y + z) / 2) (by omega) (by omega)]
  unfold racahTermN delta2G
  have k1 : (x + y + z) / 2 - (x + y + z) / 2 = 0 := by omega
  have k2 : (x + y + z) / 2 - (x + 0 + x) / 2 = (x + y + z) / 2 - x := by omega
  have k3 : (x + y + z) / 2 - (z + y + x) / 2 = 0 := by omega
  have k4 : (x + y + z) / 2 - (z + 0 + z) / 2 = (x + y + z) / 2 - z := by omega
  have k5 : (x + y + z + 0) / 2 - (x + y + z) / 2 = 0 := by omega
  have k6 : (y + z + 0 + x) / 2 - (x + y + z) / 2 = 0 := by omega
  have k7 : (z + x + x + z) / 2 - (x + y + z) / 2 = (x + y + z) / 2 - y := by omega
  simp only [k1, k2, k3, k4, k5, k6, k7, qfG_zero, mul_one, one_mul]
  have f1 := hq ((x + y + z) / 2 - x) (by omega)
  have f2 := hq ((x + y + z) / 2 - y) (by omega)
  have f3 := hq ((x + y + z) / 2 - z) (by omega)
  have f4 := hq ((x + y + z) / 2 + 1) le_rfl
  field_simp

/-- `Δ²(0, y, y) = 1/[y+1]`. -/
theorem delta2G_zero_left (θ : ℝ) {y : ℕ} (hy : qfG θ y ≠ 0) :
    delta2G θ 0 y y = (qnG θ (y + 1))⁻¹ := by
  unfold delta2G
  rw [show (0 + y + y) / 2 = y by omega, show y - 0 = y by omega, Nat.sub_self, qfG_zero, qfG_succ]
  field_simp

/-- A tetrahedral symmetry of the q-Racah sum (the case `a = 0`). -/
theorem racahG_symm_a (θ : ℝ) (b c d e f q : ℕ) :
    racahG θ d q e f b c = racahG θ c d b e f q := by
  rw [racahG_eq_Icc, racahG_eq_Icc]
  rw [show (d + q + e) / 2 = (e + d + q) / 2 by ring_nf, show (d + b + c) / 2 = (c + d + b) / 2 by ring_nf,
    show (f + q + c) / 2 = (c + f + q) / 2 by ring_nf, show (f + b + e) / 2 = (e + f + b) / 2 by ring_nf,
    show (d + q + f + b) / 2 = (d + b + f + q) / 2 by ring_nf,
    show (q + e + b + c) / 2 = (b + c + q + e) / 2 by ring_nf,
    show (e + d + c + f) / 2 = (c + d + e + f) / 2 by ring_nf]
  generalize (c + d + b) / 2 = A₁, (c + f + q) / 2 = A₂, (e + d + q) / 2 = A₃, (e + f + b) / 2 = A₄,
    (c + d + e + f) / 2 = B₁, (d + b + f + q) / 2 = B₂, (b + c + q + e) / 2 = B₃
  exact racahSum_congr θ (by omega) (by omega) fun z => by unfold racahTermN; ring

/-- **`GenBE` when `a = 0`**: the sum has the single term `x = b`, and three of the five q-Racah sums
have a zero edge. -/
theorem genBE_of_a_zero (θ : ℝ) {b c d e f p q r' : ℕ}
    (hθ : ∀ n, 1 ≤ n → n ≤ 2 * (0 + b + c + d + e + f + p + q + r') + 4 → Real.sin (n * θ) ≠ 0) :
    GenBE θ 0 b c d e f p q r' := by
  intro t1 t2 t3 t4 t5 t6
  have hs1 : Real.sin θ ≠ 0 := by simpa using hθ 1 le_rfl (by omega)
  have hqf := qfG_ne_zero hθ hs1
  have hdp : d = p := by unfold Tri at t1; omega
  have her : e = r' := by unfold Tri at t5; omega
  subst hdp her
  -- the single term
  rw [sum_eq_single b (fun x _ hx => by
      unfold genBETerm; refine ite_eq_right fun h => hx ?_; unfold Tri at h; omega)
    (fun h => absurd (mem_range.2 (by omega)) h)]
  have hcdb : Tri c d b := by unfold Tri at t2 ⊢; omega
  have hefb : Tri e f b := by unfold Tri at t6 ⊢; omega
  unfold genBETerm
  rw [ite_eq_left ⟨by unfold Tri; omega, hcdb, hefb⟩]
  have hcbd : Tri c b d := by unfold Tri at hcdb ⊢; omega
  have hdqe : Tri d q e := by unfold Tri at t4 ⊢; omega
  rw [racahG_zero₁ θ hcbd (fun n hn => hqf n (by unfold Tri at hcbd; omega)),
    racahG_zero₅ θ hefb (fun n hn => hqf n (by unfold Tri at hefb; omega)),
    racahG_zero₅ θ hdqe (fun n hn => hqf n (by unfold Tri at hdqe; omega)),
    delta2G_zero_left θ (hqf b (by omega)), racahG_symm_a θ b c d e f q, delta2G_swap23 θ c b d]
  have hn1 : qnG θ (b + 1) ≠ 0 := qnG_ne_zero hs1 (by exact_mod_cast hθ (b + 1) (by omega) (by omega))
  have hd1 : delta2G θ c d b ≠ 0 := by
    rw [delta2G_eq_triPi]
    exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hd2 : delta2G θ e f b ≠ 0 := by
    rw [delta2G_eq_triPi]
    exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hd3 : delta2G θ d q e ≠ 0 := by
    rw [delta2G_eq_triPi]
    exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hsign : (-1 : ℝ) ^ ((0 + b + c + d + e + f + d + q + e + b) / 2) *
      ((-1) ^ ((c + b + d) / 2) * (-1) ^ ((e + f + b) / 2)) = (-1) ^ ((d + q + e) / 2) := by
    rw [← pow_add, ← pow_add]
    unfold Tri at hcdb hefb hdqe
    exact neg_one_pow_congr (by omega)
  field_simp
  linear_combination (racahG θ c d b e f q) * hsign

/-- A tetrahedral symmetry of the q-Racah sum (the case `b = 0`). -/
theorem racahG_symm_b (θ : ℝ) (a c d e f q : ℕ) :
    racahG θ c q f e a d = racahG θ c d a e f q := by
  rw [racahG_eq_Icc, racahG_eq_Icc]
  rw [show (c + q + f) / 2 = (c + f + q) / 2 by ring_nf, show (c + a + d) / 2 = (c + d + a) / 2 by ring_nf,
    show (e + q + d) / 2 = (e + d + q) / 2 by ring_nf, show (e + a + f) / 2 = (e + f + a) / 2 by ring_nf,
    show (c + q + e + a) / 2 = (a + c + q + e) / 2 by ring_nf,
    show (q + f + a + d) / 2 = (d + a + f + q) / 2 by ring_nf,
    show (f + c + d + e) / 2 = (c + d + e + f) / 2 by ring_nf]
  generalize (c + d + a) / 2 = A₁, (c + f + q) / 2 = A₂, (e + d + q) / 2 = A₃, (e + f + a) / 2 = A₄,
    (c + d + e + f) / 2 = B₁, (d + a + f + q) / 2 = B₂, (a + c + q + e) / 2 = B₃
  exact racahSum_congr θ (by omega) (by omega) fun z => by unfold racahTermN; ring

/-- A tetrahedral symmetry of the q-Racah sum (the case `e = 0`). -/
theorem racahG_symm_e (θ : ℝ) (a b c d f p : ℕ) :
    racahG θ p d a f b c = racahG θ a b f c d p := by
  rw [racahG_eq_Icc, racahG_eq_Icc]
  rw [show (p + d + a) / 2 = (a + d + p) / 2 by ring_nf, show (p + b + c) / 2 = (c + b + p) / 2 by ring_nf,
    show (f + d + c) / 2 = (c + d + f) / 2 by ring_nf, show (f + b + a) / 2 = (a + b + f) / 2 by ring_nf,
    show (p + d + f + b) / 2 = (b + f + d + p) / 2 by ring_nf,
    show (d + a + b + c) / 2 = (a + b + c + d) / 2 by ring_nf,
    show (a + p + c + f) / 2 = (f + a + p + c) / 2 by ring_nf]
  generalize (a + b + f) / 2 = A₁, (a + d + p) / 2 = A₂, (c + b + p) / 2 = A₃, (c + d + f) / 2 = A₄,
    (a + b + c + d) / 2 = B₁, (b + f + d + p) / 2 = B₂, (f + a + p + c) / 2 = B₃
  exact racahSum_congr θ (by omega) (by omega) fun z => by unfold racahTermN; ring

/-- **`GenBE` when `b = 0`**: the single term `x = a`. -/
theorem genBE_of_b_zero (θ : ℝ) {a c d e f p q r' : ℕ}
    (hθ : ∀ n, 1 ≤ n → n ≤ 2 * (a + 0 + c + d + e + f + p + q + r') + 4 → Real.sin (n * θ) ≠ 0) :
    GenBE θ a 0 c d e f p q r' := by
  intro t1 t2 t3 t4 t5 t6
  have hs1 : Real.sin θ ≠ 0 := by simpa using hθ 1 le_rfl (by omega)
  have hqf := qfG_ne_zero hθ hs1
  have hcp : c = p := by unfold Tri at t2; omega
  have hfr : f = r' := by unfold Tri at t6; omega
  subst hcp hfr
  rw [sum_eq_single a (fun x _ hx => by
      unfold genBETerm; refine ite_eq_right fun h => hx ?_; unfold Tri at h; omega)
    (fun h => absurd (mem_range.2 (by omega)) h)]
  have hcda : Tri c d a := by unfold Tri at t1 ⊢; omega
  have hefa : Tri e f a := by unfold Tri at t5 ⊢; omega
  unfold genBETerm
  rw [ite_eq_left ⟨by unfold Tri; omega, hcda, hefa⟩]
  have hadc : Tri a d c := by unfold Tri at hcda ⊢; omega
  have hcqf : Tri c q f := by unfold Tri at t3 ⊢; omega
  rw [racahG_zero₂ θ hadc (fun n hn => hqf n (by unfold Tri at hadc; omega)),
    racahG_zero₄ θ hefa (fun n hn => hqf n (by unfold Tri at hefa; omega)),
    racahG_zero₅ θ hcqf (fun n hn => hqf n (by unfold Tri at hcqf; omega)),
    delta2G_swap12 θ a 0 a, delta2G_zero_left θ (hqf a (by omega)), racahG_symm_b θ a c d e f q,
    delta2G_swap12 θ a d c, delta2G_swap23 θ d a c, delta2G_swap12 θ d c a]
  have hn1 : qnG θ (a + 1) ≠ 0 := qnG_ne_zero hs1 (by exact_mod_cast hθ (a + 1) (by omega) (by omega))
  have hd1 : delta2G θ c d a ≠ 0 := by
    rw [delta2G_eq_triPi]; exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hd2 : delta2G θ e f a ≠ 0 := by
    rw [delta2G_eq_triPi]; exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hd3 : delta2G θ c q f ≠ 0 := by
    rw [delta2G_eq_triPi]; exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hsign : (-1 : ℝ) ^ ((a + 0 + c + d + e + f + c + q + f + a) / 2) *
      ((-1) ^ ((a + d + c) / 2) * (-1) ^ ((e + f + a) / 2)) = (-1) ^ ((c + q + f) / 2) := by
    rw [← pow_add, ← pow_add]
    unfold Tri at hcda hefa hcqf
    exact neg_one_pow_congr (by omega)
  field_simp
  linear_combination (racahG θ c d a e f q) * hsign

/-- **`GenBE` when `e = 0`**: the single term `x = f`. -/
theorem genBE_of_e_zero (θ : ℝ) {a b c d f p q r' : ℕ}
    (hθ : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c + d + 0 + f + p + q + r') + 4 → Real.sin (n * θ) ≠ 0) :
    GenBE θ a b c d 0 f p q r' := by
  intro t1 t2 t3 t4 t5 t6
  have hs1 : Real.sin θ ≠ 0 := by simpa using hθ 1 le_rfl (by omega)
  have hqf := qfG_ne_zero hθ hs1
  have hdq : d = q := by unfold Tri at t4; omega
  have har : a = r' := by unfold Tri at t5; omega
  subst hdq har
  rw [sum_eq_single f (fun x _ hx => by
      unfold genBETerm; refine ite_eq_right fun h => hx ?_; unfold Tri at h; omega)
    (fun h => absurd (mem_range.2 (by unfold Tri at t6; omega)) h)]
  have habf : Tri a b f := by unfold Tri at t6 ⊢; omega
  have hcdf : Tri c d f := by unfold Tri at t3 ⊢; omega
  unfold genBETerm
  rw [ite_eq_left ⟨habf, hcdf, by unfold Tri; omega⟩]
  have hbfa : Tri b f a := by unfold Tri at habf ⊢; omega
  have hpda : Tri p d a := by unfold Tri at t1 ⊢; omega
  rw [racahG_zero₄ θ hcdf (fun n hn => hqf n (by unfold Tri at hcdf; omega)),
    racahG_zero₁ θ hbfa (fun n hn => hqf n (by unfold Tri at hbfa; omega)),
    racahG_zero₄ θ hpda (fun n hn => hqf n (by unfold Tri at hpda; omega)),
    delta2G_zero_left θ (hqf f (by omega)), racahG_symm_e θ a b c d f p,
    delta2G_swap23 θ b f a, delta2G_swap12 θ b a f]
  have hn1 : qnG θ (f + 1) ≠ 0 := qnG_ne_zero hs1 (by exact_mod_cast hθ (f + 1) (by omega) (by omega))
  have hd1 : delta2G θ a b f ≠ 0 := by
    rw [delta2G_eq_triPi]; exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hd2 : delta2G θ c d f ≠ 0 := by
    rw [delta2G_eq_triPi]; exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hd3 : delta2G θ p d a ≠ 0 := by
    rw [delta2G_eq_triPi]; exact div_ne_zero (triPi_ne_zero' θ hqf (by omega)) (hqf _ (by omega))
  have hsign : (-1 : ℝ) ^ ((a + b + c + d + 0 + f + p + d + a + f) / 2) *
      ((-1) ^ ((c + d + f) / 2) * (-1) ^ ((b + f + a) / 2)) = (-1) ^ ((p + d + a) / 2) := by
    rw [← pow_add, ← pow_add]
    unfold Tri at habf hcdf hpda
    exact neg_one_pow_congr (by omega)
  field_simp
  linear_combination (racahG θ a b f c d p) * hsign

/-- **The generic Biedenharn–Elliott identity** at the angle `θ`, for every tuple of colours, when
`sin (nθ) ≠ 0` for `1 ≤ n ≤ 2 S + 4` (`S` the sum of the nine colours), given the statement
`FcEqKL ℂ` (`Fc = klCoef`, layer L4; used only when `e, a, b ≥ 1`, through the pentagon). -/
theorem genBE_of_generic (hKL : FcEqKL ℂ) (θ : ℝ) (a b c d e f p q r' : ℕ)
    (hθ : ∀ n, 1 ≤ n → n ≤ 2 * (a + b + c + d + e + f + p + q + r') + 4 → Real.sin (n * θ) ≠ 0) :
    GenBE θ a b c d e f p q r' := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; exact genBE_of_e_zero θ hθ
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; exact genBE_of_a_zero θ hθ
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; exact genBE_of_b_zero θ hθ
  exact genBE_of_pos hKL θ hθ he ha hb

/-- Non-vacuity: the angle `π/(2S + 5)` satisfies the hypothesis of `genBE_of_generic`. -/
theorem sin_ne_zero_of_lt (S n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 2 * S + 4) :
    Real.sin (n * (Real.pi / (2 * S + 5))) ≠ 0 := by
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have hS : (0 : ℝ) < 2 * S + 5 := by positivity
    have hn : (n : ℝ) < 2 * S + 5 := by exact_mod_cast (by omega : n < 2 * S + 5)
    rw [mul_div_assoc', div_lt_iff₀ hS]
    nlinarith [Real.pi_pos]

/-- Trust check, unconditional: `GenBE` at the angle `π/9` for the tuple with `a = 0`
(`b = c = d = e = f = p = q = r' = 1`, sum `8`, so `n ≤ 20` is needed; here `2·8 + 5 = 21`). -/
example : GenBE (Real.pi / (2 * 8 + 5)) 0 1 1 1 1 1 1 1 1 :=
  genBE_of_a_zero _ fun n h1 h2 => by simpa using sin_ne_zero_of_lt 8 n h1 (by omega)

end Lightlike.TV
