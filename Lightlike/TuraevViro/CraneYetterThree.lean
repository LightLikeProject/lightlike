import Lightlike.TuraevViro.CraneYetter
import Lightlike.TuraevViro.LevelOne

/-!
# The Crane–Yetter vertex at `r = 3`

At `r = 3` (`q = e^{iπ/3}`, level `1`) the quantum numbers are `[0] = 0`, `[1] = [2] = 1`, `[3] = 0`, the colours are `0, 1`
and every Kauffman–Lins evaluation is `0` or `±1`. This file evaluates the vertex `cyVertexLoc 3` on a nonzero local
colouring, which agrees with the numerical model of the closed form.
-/

open Finset Lightlike.Pentagon

namespace Lightlike.TV

/-- `Δ₀ = 1` at `r = 3`. -/
lemma tlDelta3_zero : tlDelta 3 0 = 1 := by simp [tlDelta, qnum3_one]
/-- `Δ₁ = -1` at `r = 3`. -/
lemma tlDelta3_one : tlDelta 3 1 = -1 := by simp [tlDelta, qnum3_two]

/-- A local colouring: the triangles `034, 134, 234` and the tetrahedra omitting `0, 1, 2` have colour `1`. -/
def J1 : Finset (Fin 5) → ℕ := fun F => if F = {0, 3, 4} ∨ F = {1, 3, 4} ∨ F = {2, 3, 4} then 1 else 0

/-- The tetrahedra omitting `0, 1, 2` have colour `1`, the others `0`. -/
def I1 : Fin 5 → ℕ := ![1, 1, 1, 0, 0]

/-- The admissible triads at `r = 3`. -/
lemma qAdm3_iff {a b c : ℕ} : qAdm 3 a b c ↔ Tri a b c ∧ a + b + c ≤ 2 := by
  unfold qAdm; norm_num

/-- `Tet[1 1 1; 0 0 0] = -1` at `r = 3`. -/
lemma tlTet3_a : tlTet 3 1 1 1 0 0 0 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `Tet[1 0 1; 1 0 1] = -1` at `r = 3`. -/
lemma tlTet3_b : tlTet 3 1 0 1 1 0 1 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `Tet[0 0 1; 1 1 0] = -1` at `r = 3`. -/
lemma tlTet3_c : tlTet 3 0 0 1 1 1 0 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `θ(1, 0, 1) = -1` at `r = 3`. -/
lemma tlTheta3_a : tlTheta 3 1 0 1 = -1 := by
  norm_num [tlTheta, qAdm, Tri, qfact3]

/-- `θ(0, 1, 1) = -1` at `r = 3`. -/
lemma tlTheta3_b : tlTheta 3 0 1 1 = -1 := by
  norm_num [tlTheta, qAdm, Tri, qfact3]

/-- `R^{10}_1 = 1` at `r = 3`. -/
lemma Rbr_three_101 : Rbr 3 1 0 1 = 1 := by
  simp [Rbr]

/-- **The vertex at `r = 3` on a nonzero local colouring**: `-1`, as in the numerical model of the closed form. -/
theorem cyVertexLoc_three_J1 : cyVertexLoc 3 J1 I1 = -1 := by
  have e1 : J1 {2, 3, 4} = 1 := by decide
  have e2 : J1 {1, 2, 3} = 0 := by decide
  have e3 : J1 {0, 1, 2} = 0 := by decide
  have e4 : J1 {0, 1, 4} = 0 := by decide
  have e5 : J1 {0, 3, 4} = 1 := by decide
  have e6 : J1 {1, 2, 4} = 0 := by decide
  have e7 : J1 {1, 3, 4} = 1 := by decide
  have e8 : J1 {0, 1, 3} = 0 := by decide
  have e9 : J1 {0, 2, 3} = 0 := by decide
  have e10 : J1 {0, 2, 4} = 0 := by decide
  unfold cyVertexLoc
  simp [I1, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, Fin.prod_univ_succ, Finset.sum_range_succ, qAdm3_iff, Tri]
  rw [tlDelta3_one, Rbr_three_101, tlTet3_a, tlTet3_b, tlTet3_c, tlTheta3_a, tlTheta3_b]
  norm_num


/-- A local colouring whose vertex is `i`: the triangles `014, 023, 123, 124, 134, 234` and the tetrahedra omitting `1, 4`. -/
def J2 : Finset (Fin 5) → ℕ := fun F =>
  if F = {0, 1, 4} ∨ F = {0, 2, 3} ∨ F = {1, 2, 3} ∨ F = {1, 2, 4} ∨ F = {1, 3, 4} ∨ F = {2, 3, 4} then 1 else 0

/-- The tetrahedra omitting `1, 4` have colour `1`, the others `0`. -/
def I2 : Fin 5 → ℕ := ![0, 1, 0, 0, 1]

/-- `Tet[0 1 1; 0 1 1] = -1` at `r = 3`. -/
lemma tlTet3_d : tlTet 3 0 1 1 0 1 1 = -1 := by
  norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ]

/-- `q^{1/2}` cubed at `r = 3` is `i`. -/
lemma qHalf3_cube : qHalf 3 ^ 3 = Complex.I := by
  unfold qHalf
  rw [← Complex.exp_nat_mul]
  have : ((3 : ℕ) : ℂ) * (Complex.I * Real.pi / (2 * ((3 : ℕ) : ℂ))) = Real.pi / 2 * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_pi_div_two_mul_I]

/-- **The vertex at `r = 3` on a local colouring of value `i`** (the phase `q^{3/2}` and an odd sign), as in the numerical model
of the closed form. -/
theorem cyVertexLoc_three_J2 : cyVertexLoc 3 J2 I2 = Complex.I := by
  have e1 : J2 {2, 3, 4} = 1 := by decide
  have e2 : J2 {1, 2, 3} = 1 := by decide
  have e3 : J2 {0, 1, 2} = 0 := by decide
  have e4 : J2 {0, 1, 4} = 1 := by decide
  have e5 : J2 {0, 3, 4} = 0 := by decide
  have e6 : J2 {1, 2, 4} = 1 := by decide
  have e7 : J2 {1, 3, 4} = 1 := by decide
  have e8 : J2 {0, 1, 3} = 0 := by decide
  have e9 : J2 {0, 2, 3} = 1 := by decide
  have e10 : J2 {0, 2, 4} = 0 := by decide
  unfold cyVertexLoc
  simp [I2, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, Fin.prod_univ_succ, Finset.sum_range_succ, qAdm3_iff, Tri]
  rw [qHalf3_cube, tlDelta3_one, Rbr_three_101, tlTet3_a, tlTet3_b, tlTet3_c, tlTet3_d, tlTheta3_a,
    tlTheta3_b]
  norm_num


/-! ### The exact values of the Kauffman–Lins evaluations at `r = 3` -/

/-- The exact value of `Tet[A B E; C D F]` at `r = 3` for the colours `0, 1`, by the binary index
`idx = (((((A·2 + B)·2 + E)·2 + C)·2 + D)·2 + F`: `1` for `idx = 0`, `-1` for the seven indices `14, 21, 27, 35, 45, 54, 56`
(the colourings with four admissible triads that are not zero), `0` otherwise. -/
def tet3Z (A B E C D F : ℕ) : ℤ :=
  let idx := ((((A * 2 + B) * 2 + E) * 2 + C) * 2 + D) * 2 + F
  if idx = 0 then 1 else if idx ∈ [14, 21, 27, 35, 45, 54, 56] then -1 else 0

/-- The exact value of `θ(a, b, c)` at `r = 3` for the colours `0, 1`: `1` on `(0, 0, 0)`, `-1` if exactly two colours are
`1`, `0` otherwise. -/
def theta3Z (a b c : ℕ) : ℤ := if a = 0 ∧ b = 0 ∧ c = 0 then 1 else if a + b + c = 2 then -1 else 0

/-- **`tlTet` at `r = 3`** on the colours `0, 1` is the integer `tet3Z`. -/
lemma tlTet3_eq (A B E C D F : ℕ) (hA : A ≤ 1) (hB : B ≤ 1) (hE : E ≤ 1) (hC : C ≤ 1) (hD : D ≤ 1)
    (hF : F ≤ 1) : tlTet 3 A B E C D F = (tet3Z A B E C D F : ℝ) := by
  interval_cases A <;> interval_cases B <;> interval_cases E <;> interval_cases C <;> interval_cases D <;>
    interval_cases F <;> norm_num [tlTet, qAdm, Tri, qfact3, Fin.prod_univ_succ, tet3Z]

/-- **`tlTheta` at `r = 3`** on the colours `0, 1` is the integer `theta3Z`. -/
lemma tlTheta3_eq (a b c : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1) :
    tlTheta 3 a b c = (theta3Z a b c : ℝ) := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num [tlTheta, qAdm, Tri, qfact3, theta3Z]


/-! ### The vertex at `r = 3` on every local colouring -/

lemma theta3Z_cases (a b c : ℕ) : theta3Z a b c = 0 ∨ theta3Z a b c = 1 ∨ theta3Z a b c = -1 := by
  unfold theta3Z; split_ifs <;> simp

lemma div_cast_eq_mul (t θ : ℤ) (h : θ = 0 ∨ θ = 1 ∨ θ = -1) : (t : ℂ) / (θ : ℂ) = ((t * θ : ℤ) : ℂ) := by
  rcases h with h | h | h <;> simp [h, div_neg]

/-- The single admissible term of the sum over `x` at `r = 3`: `x = (a₀ + b₀) mod 2`. -/
lemma cy_sum3 (g : ℕ → ℂ) {a0 b0 : ℕ} (ha : a0 ≤ 1) (hb : b0 ≤ 1) :
    ∑ x ∈ range (2 * (3 - 2) + 1),
        (if qAdm 3 a0 b0 x then (tlDelta 3 x : ℂ) * Rbr 3 a0 b0 x * g x else 0) =
      (tlDelta 3 ((a0 + b0) % 2) : ℂ) * Rbr 3 a0 b0 ((a0 + b0) % 2) * g ((a0 + b0) % 2) := by
  interval_cases a0 <;> interval_cases b0 <;> simp [Finset.sum_range_succ, qAdm3_iff, Tri]

/-- `x(x + 2)` as an integer. -/
def pr3 (x : ℕ) : ℤ := ((x * (x + 2) : ℕ) : ℤ)

/-- The arrays `a`, `b`, `c` of the closed form of the vertex. -/
def cyA (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) : Fin 6 → ℕ :=
  ![J {2, 3, 4}, I 0, J {1, 2, 3}, I 4, J {0, 1, 2}, I 3]

/-- The array `b` of the closed form of the vertex. -/
def cyB (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) : Fin 6 → ℕ :=
  ![I 3, J {0, 1, 4}, I 2, J {0, 3, 4}, I 1, J {2, 3, 4}]

/-- The array `c` of the closed form of the vertex. -/
def cyC (J : Finset (Fin 5) → ℕ) (_I : Fin 5 → ℕ) : Fin 5 → ℕ :=
  ![J {1, 2, 4}, J {1, 3, 4}, J {0, 1, 3}, J {0, 2, 3}, J {0, 2, 4}]

/-- The exponent `P` of the phase `A^P`. -/
def cyP (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) : ℤ :=
  (-pr3 (I 4) + pr3 (I 3) - pr3 (I 2) - pr3 (I 0) + pr3 (J {0, 1, 3}) + pr3 (J {1, 2, 3}) + pr3 (J {1, 3, 4}) +
    pr3 (J {2, 3, 4})) / 2

/-- The exponent `s` of the sign `(-1)^s`. -/
def cyS (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) : ℤ :=
  (((J {1, 2, 3} : ℕ) + J {1, 3, 4} - I 0 : ℤ) + ((J {0, 3, 4} : ℕ) + J {0, 2, 3} - I 1 : ℤ) +
    ((J {2, 3, 4} : ℕ) + J {0, 2, 4} - I 1 : ℤ) + ((J {0, 1, 3} : ℕ) + J {0, 3, 4} - I 2 : ℤ) +
    ((J {0, 2, 4} : ℕ) + J {0, 1, 2} - I 3 : ℤ) + ((J {0, 1, 2} : ℕ) + J {0, 2, 3} - I 4 : ℤ)) / 2

/-- The integer sign of the vertex at `r = 3`. -/
def cy3Eps (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) : ℤ :=
  (-1) ^ (cyS J I).natAbs * (-1) ^ ((cyA J I 0 + cyB J I 0 - (cyA J I 0 + cyB J I 0) % 2) / 2) *
    (-1) ^ ((cyA J I 0 + cyB J I 0) % 2) *
    ∏ t : Fin 5, tet3Z (cyA J I t.castSucc) (cyA J I t.succ) ((cyA J I 0 + cyB J I 0) % 2) (cyB J I t.succ)
      (cyB J I t.castSucc) (cyC J I t) * theta3Z (cyA J I t.succ) (cyB J I t.succ) ((cyA J I 0 + cyB J I 0) % 2)

/-- The exponent of `q^{1/2}` in the phase of the vertex at `r = 3`. -/
def cy3Exp (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) : ℤ :=
  cyP J I + (pr3 ((cyA J I 0 + cyB J I 0) % 2) - pr3 (cyA J I 0) - pr3 (cyB J I 0)) / 2


/-- `(-1)^S` for an integer exponent is `(-1)^{|S|}`. -/
lemma neg_one_zpow_natAbs (S : ℤ) : (-1 : ℂ) ^ S = (-1) ^ S.natAbs := by
  rcases Int.natAbs_eq S with h | h
  · conv_lhs => rw [h]
    rw [zpow_natCast]
  · conv_lhs => rw [h]
    rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one]

/-- The braiding eigenvalue as a power of `q^{1/2}`: `R^{ab}_c = (-1)^{(a+b-c)/2} (q^{1/2})^{(c' - a' - b')/2}`. -/
lemma Rbr_eq_qHalf (r a b c : ℕ) (hr : 0 < r) (hk : (2 : ℤ) ∣ pr3 c - pr3 a - pr3 b) :
    Rbr r a b c = (-1) ^ ((a + b - c) / 2) * qHalf r ^ ((pr3 c - pr3 a - pr3 b) / 2) := by
  obtain ⟨m, hm⟩ := hk
  unfold Rbr qHalf
  rw [hm, Int.mul_ediv_cancel_left _ (by norm_num), ← Complex.exp_int_mul]
  congr 2
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have : (((c * (c + 2) : ℕ) : ℤ) - ((a * (a + 2) : ℕ) : ℤ) - ((b * (b + 2) : ℕ) : ℤ) : ℤ) = 2 * m := hm
  have h2 : ((((c * (c + 2) : ℕ) : ℤ) - ((a * (a + 2) : ℕ) : ℤ) - ((b * (b + 2) : ℕ) : ℤ) : ℤ) : ℂ) =
      ((2 * m : ℤ) : ℂ) := by rw [this]
  push_cast at h2 ⊢
  rw [h2]
  field_simp
  ring


/-- For colours `0, 1` the exponent `(x' - a' - b')` of the braiding eigenvalue is even. -/
lemma rbr_dvd {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : (2 : ℤ) ∣ pr3 ((a + b) % 2) - pr3 a - pr3 b := by
  interval_cases a <;> interval_cases b <;> decide

/-- **The vertex at `r = 3` on every local colouring with colours `0, 1`** is an integer times a power of `q^{1/2}`. -/
theorem cyVertexLoc_three (J : Finset (Fin 5) → ℕ) (I : Fin 5 → ℕ) (hJ : ∀ F, J F ≤ 1) (hI : ∀ m, I m ≤ 1) :
    cyVertexLoc 3 J I = (cy3Eps J I : ℂ) * qHalf 3 ^ cy3Exp J I := by
  have ha : ∀ i : Fin 6, cyA J I i ≤ 1 := by
    intro i; fin_cases i <;> simp [cyA, hJ, hI]
  have hb : ∀ i : Fin 6, cyB J I i ≤ 1 := by
    intro i; fin_cases i <;> simp [cyB, hJ, hI]
  have hc : ∀ i : Fin 5, cyC J I i ≤ 1 := by
    intro i; fin_cases i <;> simp [cyC, hJ, hI]
  have hx0 : (cyA J I 0 + cyB J I 0) % 2 ≤ 1 := by omega
  unfold cyVertexLoc
  dsimp only
  change (-1 : ℂ) ^ cyS J I * qHalf 3 ^ cyP J I *
      ∑ x ∈ range (2 * (3 - 2) + 1),
        (if qAdm 3 (cyA J I 0) (cyB J I 0) x then (tlDelta 3 x : ℂ) * Rbr 3 (cyA J I 0) (cyB J I 0) x *
          ∏ t : Fin 5, ((tlTet 3 (cyA J I t.castSucc) (cyA J I t.succ) x (cyB J I t.succ) (cyB J I t.castSucc)
            (cyC J I t) : ℝ) : ℂ) / (tlTheta 3 (cyA J I t.succ) (cyB J I t.succ) x : ℂ) else 0) = _
  rw [cy_sum3 _ (ha 0) (hb 0)]
  have hΔ : (tlDelta 3 ((cyA J I 0 + cyB J I 0) % 2) : ℂ) =
      (((-1 : ℤ) ^ ((cyA J I 0 + cyB J I 0) % 2) : ℤ) : ℂ) := by
    rcases (by omega : (cyA J I 0 + cyB J I 0) % 2 = 0 ∨ (cyA J I 0 + cyB J I 0) % 2 = 1) with h | h <;>
      rw [h] <;> simp [tlDelta3_zero, tlDelta3_one]
  have hR := Rbr_eq_qHalf 3 (cyA J I 0) (cyB J I 0) ((cyA J I 0 + cyB J I 0) % 2) (by norm_num)
    (rbr_dvd (ha 0) (hb 0))
  have hprod : ∏ t : Fin 5,
      ((tlTet 3 (cyA J I t.castSucc) (cyA J I t.succ) ((cyA J I 0 + cyB J I 0) % 2) (cyB J I t.succ)
        (cyB J I t.castSucc) (cyC J I t) : ℝ) : ℂ) /
        (tlTheta 3 (cyA J I t.succ) (cyB J I t.succ) ((cyA J I 0 + cyB J I 0) % 2) : ℂ) =
      ((∏ t : Fin 5, tet3Z (cyA J I t.castSucc) (cyA J I t.succ) ((cyA J I 0 + cyB J I 0) % 2)
        (cyB J I t.succ) (cyB J I t.castSucc) (cyC J I t) *
        theta3Z (cyA J I t.succ) (cyB J I t.succ) ((cyA J I 0 + cyB J I 0) % 2) : ℤ) : ℂ) := by
    rw [Int.cast_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [tlTet3_eq _ _ _ _ _ _ (ha _) (ha _) hx0 (hb _) (hb _) (hc t), tlTheta3_eq _ _ _ (ha _) (hb _) hx0]
    simp only [Complex.ofReal_intCast]
    exact div_cast_eq_mul _ _ (theta3Z_cases _ _ _)
  rw [hΔ, hR, hprod, neg_one_zpow_natAbs]
  unfold cy3Eps cy3Exp
  rw [zpow_add₀ (qHalf_ne_zero 3)]
  push_cast
  ring

end Lightlike.TV
