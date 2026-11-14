import Lightlike.Recoupling.FifteenJ

/-!
# The 4-simplex contraction is the 15j symbol of the first kind

`fifteenJSimplex_eq`: the contraction of five 4-valent intertwiners on `K₅` equals
`Π_a √(2i_a + 1)` times the 15j symbol of the first kind. The proof identifies the contraction,
term by term, with the closed Möbius ladder of `Ladder.lean` (a change of the fifteen summation
variables, each of the ten 3j symbols transposed), and then uses `fifteenJ_eq_mobius`.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.Recoupling

/-- Exact halving of an even integer. -/
lemma half_of_eq {x k : ℤ} (h : x = 2 * k) : x / 2 = k := by
  rw [h, Int.mul_ediv_cancel_left _ two_ne_zero]

/-- Exact halving of an even natural number. -/
lemma nhalf_of_eq {x k : ℕ} (h : x = 2 * k) : x / 2 = k := by
  rw [h, Nat.mul_div_cancel_left _ two_pos]

set_option maxHeartbeats 2000000 in
/-- The parity bookkeeping of `simplex_term`. -/
lemma simplex_sign_parity (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ)
    (m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 : ℤ)
    -- projection sums of the ten 3j symbols
    (s0 : m01 + m02 + μ0 = 0) (s0' : -μ0 + m03 + m04 = 0)
    (s1 : m12 + m13 + μ1 = 0) (s1' : -μ1 + m14 + -m01 = 0)
    (s2 : m23 + m24 + μ2 = 0) (s2' : -μ2 + -m02 + -m12 = 0)
    (s3 : m34 + -m03 + μ3 = 0) (s3' : -μ3 + -m13 + -m23 = 0)
    (s4 : -m04 + -m14 + μ4 = 0)
    -- parities j - m
    (k01 : ℤ) (e01 : (j01 : ℤ) - m01 = 2 * k01) (k02 : ℤ) (e02 : (j02 : ℤ) - m02 = 2 * k02)
    (k03 : ℤ) (e03 : (j03 : ℤ) - m03 = 2 * k03) (k04 : ℤ) (e04 : (j04 : ℤ) - m04 = 2 * k04)
    (k12 : ℤ) (e12 : (j12 : ℤ) - m12 = 2 * k12) (k13 : ℤ) (e13 : (j13 : ℤ) - m13 = 2 * k13)
    (k14 : ℤ) (e14 : (j14 : ℤ) - m14 = 2 * k14) (k23 : ℤ) (e23 : (j23 : ℤ) - m23 = 2 * k23)
    (k24 : ℤ) (e24 : (j24 : ℤ) - m24 = 2 * k24) (k34 : ℤ) (e34 : (j34 : ℤ) - m34 = 2 * k34)
    (n0 : ℤ) (f0 : (i0 : ℤ) - μ0 = 2 * n0) (n1 : ℤ) (f1 : (i1 : ℤ) - μ1 = 2 * n1) (n2 : ℤ) (f2 : (i2 : ℤ) - μ2 = 2 * n2)
    (n3 : ℤ) (f3 : (i3 : ℤ) - μ3 = 2 * n3) (n4 : ℤ) (f4 : (i4 : ℤ) - μ4 = 2 * n4)
    -- triads
    (Tt0 : ℕ) (t0 : j01 + j02 + i0 = 2 * Tt0) (Tt0p : ℕ) (t0' : i0 + j03 + j04 = 2 * Tt0p)
    (Tt1 : ℕ) (t1 : j12 + j13 + i1 = 2 * Tt1) (Tt1p : ℕ) (t1' : i1 + j14 + j01 = 2 * Tt1p)
    (Tt2 : ℕ) (t2 : j23 + j24 + i2 = 2 * Tt2) (Tt2p : ℕ) (t2' : i2 + j02 + j12 = 2 * Tt2p)
    (Tt3 : ℕ) (t3 : j34 + j03 + i3 = 2 * Tt3) (Tt3p : ℕ) (t3' : i3 + j13 + j23 = 2 * Tt3p)
    (Tt4 : ℕ) (t4 : j04 + j14 + i4 = 2 * Tt4) (Tt4p : ℕ) (t4' : i4 + j24 + j34 = 2 * Tt4p) :
    (((j01 : ℤ) - m01) / 2 + ((j02 : ℤ) - m02) / 2 + ((j03 : ℤ) - m03) / 2 + ((j04 : ℤ) - m04) / 2 +
      ((j12 : ℤ) - m12) / 2 + ((j13 : ℤ) - m13) / 2 + ((j14 : ℤ) - m14) / 2 +
      ((j23 : ℤ) - m23) / 2 + ((j24 : ℤ) - m24) / 2 + ((j34 : ℤ) - m34) / 2 +
      ((i0 : ℤ) - μ0) / 2 + ((i1 : ℤ) - μ1) / 2 + ((i2 : ℤ) - μ2) / 2 + ((i3 : ℤ) - μ3) / 2 +
      ((i4 : ℤ) - μ4) / 2) % 2 =
    ((j14 : ℤ) +
      (((i0 : ℤ) - -μ0) / 2 + ((j14 : ℤ) - -m14) / 2 + ((j02 : ℤ) - m02) / 2 + ((i1 : ℤ) - -μ1) / 2 +
        ((i2 : ℤ) - -μ2) / 2 + ((j13 : ℤ) - m13) / 2 + ((j24 : ℤ) - m24) / 2 + ((i3 : ℤ) - -μ3) / 2 +
        ((i4 : ℤ) - -μ4) / 2 + ((j03 : ℤ) - -m03) / 2) +
      (((j01 : ℤ) - m01) / 2 + ((j12 : ℤ) - -m12) / 2 + ((j23 : ℤ) - m23) / 2 +
        ((j34 : ℤ) - -m34) / 2 + ((j04 : ℤ) - -m04) / 2) +
      (((j01 + j02 + i0) / 2 : ℕ) + ((i1 + j14 + j01) / 2 : ℕ) + ((i2 + j02 + j12) / 2 : ℕ) +
        ((j12 + j13 + i1) / 2 : ℕ) + ((j23 + j24 + i2) / 2 : ℕ) + ((i3 + j13 + j23) / 2 : ℕ) +
        ((i4 + j24 + j34) / 2 : ℕ) + ((j34 + j03 + i3) / 2 : ℕ) + ((j04 + j14 + i4) / 2 : ℕ) +
        ((i0 + j03 + j04) / 2 : ℕ))) % 2 := by
  simp only [half_of_eq e01, half_of_eq e02, half_of_eq e03, half_of_eq (show (j03 : ℤ) - -m03 = 2 * (k03 + m03) by linear_combination e03), half_of_eq e04, half_of_eq (show (j04 : ℤ) - -m04 = 2 * (k04 + m04) by linear_combination e04), half_of_eq e12, half_of_eq (show (j12 : ℤ) - -m12 = 2 * (k12 + m12) by linear_combination e12), half_of_eq e13, half_of_eq e14, half_of_eq (show (j14 : ℤ) - -m14 = 2 * (k14 + m14) by linear_combination e14), half_of_eq e23, half_of_eq e24, half_of_eq e34, half_of_eq (show (j34 : ℤ) - -m34 = 2 * (k34 + m34) by linear_combination e34), half_of_eq f0, half_of_eq (show (i0 : ℤ) - -μ0 = 2 * (n0 + μ0) by linear_combination f0), half_of_eq f1, half_of_eq (show (i1 : ℤ) - -μ1 = 2 * (n1 + μ1) by linear_combination f1), half_of_eq f2, half_of_eq (show (i2 : ℤ) - -μ2 = 2 * (n2 + μ2) by linear_combination f2), half_of_eq f3, half_of_eq (show (i3 : ℤ) - -μ3 = 2 * (n3 + μ3) by linear_combination f3), half_of_eq f4, half_of_eq (show (i4 : ℤ) - -μ4 = 2 * (n4 + μ4) by linear_combination f4), nhalf_of_eq t0, nhalf_of_eq t0', nhalf_of_eq t1, nhalf_of_eq t1', nhalf_of_eq t2, nhalf_of_eq t2', nhalf_of_eq t3, nhalf_of_eq t3', nhalf_of_eq t4, nhalf_of_eq t4']
  have key : (↑j14 + (n0 + μ0 + (k14 + m14) + k02 + (n1 + μ1) + (n2 + μ2) + k13 + k24 + (n3 + μ3) +
      (n4 + μ4) + (k03 + m03)) + (k01 + (k12 + m12) + k23 + (k34 + m34) + (k04 + m04)) +
      ((Tt0 : ℤ) + Tt1p + Tt2p + Tt1 + Tt2 + Tt3p + Tt4p + Tt3 + Tt4 + Tt0p)) =
      (k01 + k02 + k03 + k04 + k12 + k13 + k14 + k23 + k24 + k34 + n0 + n1 + n2 + n3 + n4) +
      2 * ((i0 : ℤ) + i1 + i2 + i3 + i4 - (n0 + n1 + n2 + n3 + n4) - (k14 + k03 + k12 + k34 + k04) +
        (j14 + j03 + j12 + j34 + j04) + Tt1p + Tt2 + Tt2p + Tt1 - i1 - i2 - j12) := by
    omega
  rw [key, Int.add_mul_emod_self_left]

set_option maxHeartbeats 4000000 in
/-- **One term of the 4-simplex contraction is a term of the Möbius ladder**: the ten 3j symbols
of the five intertwiners are the ten 3j symbols of the ladder up to a transposition of columns
each, and the signs agree up to `(-1)^{j₁₄}` (doubled units). -/
lemma simplex_term (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ)
    (m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 : ℤ) :
    edgeSign j01 m01 * edgeSign j02 m02 * edgeSign j03 m03 * edgeSign j04 m04 * edgeSign j12 m12 * edgeSign j13 m13 * edgeSign j14 m14 * edgeSign j23 m23 * edgeSign j24 m24 * edgeSign j34 m34 *
      ((-1 : ℝ) ^ (((i0 : ℤ) - μ0) / 2) * threeJ j01 j02 i0 m01 m02 μ0 * threeJ i0 j03 j04 (-μ0) m03 m04) *
      ((-1 : ℝ) ^ (((i1 : ℤ) - μ1) / 2) * threeJ j12 j13 i1 m12 m13 μ1 * threeJ i1 j14 j01 (-μ1) m14 (-m01)) *
      ((-1 : ℝ) ^ (((i2 : ℤ) - μ2) / 2) * threeJ j23 j24 i2 m23 m24 μ2 * threeJ i2 j02 j12 (-μ2) (-m02) (-m12)) *
      ((-1 : ℝ) ^ (((i3 : ℤ) - μ3) / 2) * threeJ j34 j03 i3 m34 (-m03) μ3 * threeJ i3 j13 j23 (-μ3) (-m13) (-m23)) *
      ((-1 : ℝ) ^ (((i4 : ℤ) - μ4) / 2) * threeJ j04 j14 i4 (-m04) (-m14) μ4 * threeJ i4 j24 j34 (-μ4) (-m24) (-m34)) =
    (-1 : ℝ) ^ j14 * ((edgeSign i0 (-μ0) * edgeSign j14 (-m14) *
        (edgeSign j01 m01 * threeJ i0 j02 j01 μ0 m02 m01 * threeJ j14 i1 j01 m14 (-μ1) (-m01))) *
      (edgeSign j02 m02 * edgeSign i1 (-μ1) *
        (edgeSign j12 (-m12) * threeJ j02 i2 j12 (-m02) (-μ2) (-m12) * threeJ i1 j13 j12 μ1 m13 m12)) *
      (edgeSign i2 (-μ2) * edgeSign j13 m13 *
        (edgeSign j23 m23 * threeJ i2 j24 j23 μ2 m24 m23 * threeJ j13 i3 j23 (-m13) (-μ3) (-m23))) *
      (edgeSign j24 m24 * edgeSign i3 (-μ3) *
        (edgeSign j34 (-m34) * threeJ j24 i4 j34 (-m24) (-μ4) (-m34) * threeJ i3 j03 j34 μ3 (-m03) m34)) *
      (edgeSign i4 (-μ4) * edgeSign j03 (-m03) *
        (edgeSign j04 (-m04) * threeJ i4 j14 j04 μ4 (-m14) (-m04) * threeJ j03 i0 j04 m03 (-μ0) m04))) := by
  have hn : (-1 : ℝ) ≠ 0 := by norm_num
  have hL : edgeSign j01 m01 * edgeSign j02 m02 * edgeSign j03 m03 * edgeSign j04 m04 * edgeSign j12 m12 * edgeSign j13 m13 * edgeSign j14 m14 * edgeSign j23 m23 * edgeSign j24 m24 * edgeSign j34 m34 *
      ((-1 : ℝ) ^ (((i0 : ℤ) - μ0) / 2) * threeJ j01 j02 i0 m01 m02 μ0 * threeJ i0 j03 j04 (-μ0) m03 m04) *
      ((-1 : ℝ) ^ (((i1 : ℤ) - μ1) / 2) * threeJ j12 j13 i1 m12 m13 μ1 * threeJ i1 j14 j01 (-μ1) m14 (-m01)) *
      ((-1 : ℝ) ^ (((i2 : ℤ) - μ2) / 2) * threeJ j23 j24 i2 m23 m24 μ2 * threeJ i2 j02 j12 (-μ2) (-m02) (-m12)) *
      ((-1 : ℝ) ^ (((i3 : ℤ) - μ3) / 2) * threeJ j34 j03 i3 m34 (-m03) μ3 * threeJ i3 j13 j23 (-μ3) (-m13) (-m23)) *
      ((-1 : ℝ) ^ (((i4 : ℤ) - μ4) / 2) * threeJ j04 j14 i4 (-m04) (-m14) μ4 * threeJ i4 j24 j34 (-μ4) (-m24) (-m34)) = (-1 : ℝ) ^ (((j01 : ℤ) - m01) / 2 + ((j02 : ℤ) - m02) / 2 + ((j03 : ℤ) - m03) / 2 + ((j04 : ℤ) - m04) / 2 + ((j12 : ℤ) - m12) / 2 + ((j13 : ℤ) - m13) / 2 + ((j14 : ℤ) - m14) / 2 + ((j23 : ℤ) - m23) / 2 + ((j24 : ℤ) - m24) / 2 + ((j34 : ℤ) - m34) / 2 + ((i0 : ℤ) - μ0) / 2 + ((i1 : ℤ) - μ1) / 2 + ((i2 : ℤ) - μ2) / 2 + ((i3 : ℤ) - μ3) / 2 + ((i4 : ℤ) - μ4) / 2) * (threeJ j01 j02 i0 m01 m02 μ0 * threeJ i0 j03 j04 (-μ0) m03 m04 * threeJ j12 j13 i1 m12 m13 μ1 * threeJ i1 j14 j01 (-μ1) m14 (-m01) * threeJ j23 j24 i2 m23 m24 μ2 * threeJ i2 j02 j12 (-μ2) (-m02) (-m12) * threeJ j34 j03 i3 m34 (-m03) μ3 * threeJ i3 j13 j23 (-μ3) (-m13) (-m23) * threeJ j04 j14 i4 (-m04) (-m14) μ4 * threeJ i4 j24 j34 (-μ4) (-m24) (-m34)) := by
    unfold edgeSign; simp only [zpow_add₀ hn]; ring
  have hR : (-1 : ℝ) ^ j14 * ((edgeSign i0 (-μ0) * edgeSign j14 (-m14) *         (edgeSign j01 m01 * threeJ i0 j02 j01 μ0 m02 m01 * threeJ j14 i1 j01 m14 (-μ1) (-m01))) *       (edgeSign j02 m02 * edgeSign i1 (-μ1) *         (edgeSign j12 (-m12) * threeJ j02 i2 j12 (-m02) (-μ2) (-m12) * threeJ i1 j13 j12 μ1 m13 m12)) *       (edgeSign i2 (-μ2) * edgeSign j13 m13 *         (edgeSign j23 m23 * threeJ i2 j24 j23 μ2 m24 m23 * threeJ j13 i3 j23 (-m13) (-μ3) (-m23))) *       (edgeSign j24 m24 * edgeSign i3 (-μ3) *         (edgeSign j34 (-m34) * threeJ j24 i4 j34 (-m24) (-μ4) (-m34) * threeJ i3 j03 j34 μ3 (-m03) m34)) *       (edgeSign i4 (-μ4) * edgeSign j03 (-m03) *         (edgeSign j04 (-m04) * threeJ i4 j14 j04 μ4 (-m14) (-m04) * threeJ j03 i0 j04 m03 (-μ0) m04))) = (-1 : ℝ) ^ ((j14 : ℤ) + (((i0 : ℤ) - -μ0) / 2 + ((j14 : ℤ) - -m14) / 2 + ((j02 : ℤ) - m02) / 2 + ((i1 : ℤ) - -μ1) / 2 + ((i2 : ℤ) - -μ2) / 2 + ((j13 : ℤ) - m13) / 2 + ((j24 : ℤ) - m24) / 2 + ((i3 : ℤ) - -μ3) / 2 + ((i4 : ℤ) - -μ4) / 2 + ((j03 : ℤ) - -m03) / 2) + (((j01 : ℤ) - m01) / 2 + ((j12 : ℤ) - -m12) / 2 + ((j23 : ℤ) - m23) / 2 + ((j34 : ℤ) - -m34) / 2 + ((j04 : ℤ) - -m04) / 2) + (((j01 + j02 + i0) / 2 : ℕ) + ((i1 + j14 + j01) / 2 : ℕ) + ((i2 + j02 + j12) / 2 : ℕ) + ((j12 + j13 + i1) / 2 : ℕ) + ((j23 + j24 + i2) / 2 : ℕ) + ((i3 + j13 + j23) / 2 : ℕ) + ((i4 + j24 + j34) / 2 : ℕ) + ((j34 + j03 + i3) / 2 : ℕ) + ((j04 + j14 + i4) / 2 : ℕ) + ((i0 + j03 + j04) / 2 : ℕ))) * (threeJ j01 j02 i0 m01 m02 μ0 * threeJ i0 j03 j04 (-μ0) m03 m04 * threeJ j12 j13 i1 m12 m13 μ1 * threeJ i1 j14 j01 (-μ1) m14 (-m01) * threeJ j23 j24 i2 m23 m24 μ2 * threeJ i2 j02 j12 (-μ2) (-m02) (-m12) * threeJ j34 j03 i3 m34 (-m03) μ3 * threeJ i3 j13 j23 (-μ3) (-m13) (-m23) * threeJ j04 j14 i4 (-m04) (-m14) μ4 * threeJ i4 j24 j34 (-μ4) (-m24) (-m34)) := by
    rw [threeJ_swap₁₃ j01 j02 i0 m01 m02 μ0, threeJ_swap i1 j14 j01 (-μ1) m14 (-m01), threeJ_swap i2 j02 j12 (-μ2) (-m02) (-m12), threeJ_swap₁₃ j12 j13 i1 m12 m13 μ1, threeJ_swap₁₃ j23 j24 i2 m23 m24 μ2, threeJ_swap i3 j13 j23 (-μ3) (-m13) (-m23), threeJ_swap i4 j24 j34 (-μ4) (-m24) (-m34), threeJ_swap₁₃ j34 j03 i3 m34 (-m03) μ3, threeJ_swap₁₃ j04 j14 i4 (-m04) (-m14) μ4, threeJ_swap i0 j03 j04 (-μ0) m03 m04]
    unfold edgeSign; simp only [zpow_add₀ hn, zpow_natCast]; ring
  rw [hL, hR]
  by_cases hP : threeJ j01 j02 i0 m01 m02 μ0 * threeJ i0 j03 j04 (-μ0) m03 m04 *
      threeJ j12 j13 i1 m12 m13 μ1 * threeJ i1 j14 j01 (-μ1) m14 (-m01) *
      threeJ j23 j24 i2 m23 m24 μ2 * threeJ i2 j02 j12 (-μ2) (-m02) (-m12) *
      threeJ j34 j03 i3 m34 (-m03) μ3 * threeJ i3 j13 j23 (-μ3) (-m13) (-m23) *
      threeJ j04 j14 i4 (-m04) (-m14) μ4 * threeJ i4 j24 j34 (-μ4) (-m24) (-m34) = 0
  · rw [hP, mul_zero, mul_zero]
  simp only [mul_eq_zero, not_or] at hP
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hL0, hR0⟩, hL1⟩, hR1⟩, hL2⟩, hR2⟩, hL3⟩, hR3⟩, hL4⟩, hR4⟩ := hP
  obtain ⟨s0, -, -, -, -, -, -, a01, a02, b0, -, -, -, c0⟩ := adm3_of_threeJ_ne_zero hL0
  obtain ⟨s0', -, -, -, -, -, -, -, a03, a04, -, -, -, c0'⟩ := adm3_of_threeJ_ne_zero hR0
  obtain ⟨s1, -, -, -, -, -, -, a12, a13, b1, -, -, -, c1⟩ := adm3_of_threeJ_ne_zero hL1
  obtain ⟨s1', -, -, -, -, -, -, -, a14, -, -, -, -, c1'⟩ := adm3_of_threeJ_ne_zero hR1
  obtain ⟨s2, -, -, -, -, -, -, a23, a24, b2, -, -, -, c2⟩ := adm3_of_threeJ_ne_zero hL2
  obtain ⟨s2', -, -, -, -, -, -, -, -, -, -, -, -, c2'⟩ := adm3_of_threeJ_ne_zero hR2
  obtain ⟨s3, -, -, -, -, -, -, a34, -, b3, -, -, -, c3⟩ := adm3_of_threeJ_ne_zero hL3
  obtain ⟨s3', -, -, -, -, -, -, -, -, -, -, -, -, c3'⟩ := adm3_of_threeJ_ne_zero hR3
  obtain ⟨s4, -, -, -, -, -, -, -, -, b4, -, -, -, c4⟩ := adm3_of_threeJ_ne_zero hL4
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, c4'⟩ := adm3_of_threeJ_ne_zero hR4
  obtain ⟨k01, e01⟩ := Int.dvd_of_emod_eq_zero a01
  obtain ⟨k02, e02⟩ := Int.dvd_of_emod_eq_zero a02
  obtain ⟨k03, e03⟩ := Int.dvd_of_emod_eq_zero a03
  obtain ⟨k04, e04⟩ := Int.dvd_of_emod_eq_zero a04
  obtain ⟨k12, e12⟩ := Int.dvd_of_emod_eq_zero a12
  obtain ⟨k13, e13⟩ := Int.dvd_of_emod_eq_zero a13
  obtain ⟨k14, e14⟩ := Int.dvd_of_emod_eq_zero a14
  obtain ⟨k23, e23⟩ := Int.dvd_of_emod_eq_zero a23
  obtain ⟨k24, e24⟩ := Int.dvd_of_emod_eq_zero a24
  obtain ⟨k34, e34⟩ := Int.dvd_of_emod_eq_zero a34
  obtain ⟨n0, f0⟩ := Int.dvd_of_emod_eq_zero b0
  obtain ⟨n1, f1⟩ := Int.dvd_of_emod_eq_zero b1
  obtain ⟨n2, f2⟩ := Int.dvd_of_emod_eq_zero b2
  obtain ⟨n3, f3⟩ := Int.dvd_of_emod_eq_zero b3
  obtain ⟨n4, f4⟩ := Int.dvd_of_emod_eq_zero b4
  obtain ⟨T0, t0⟩ := Nat.dvd_of_mod_eq_zero c0
  obtain ⟨T0', t0'⟩ := Nat.dvd_of_mod_eq_zero c0'
  obtain ⟨T1, t1⟩ := Nat.dvd_of_mod_eq_zero c1
  obtain ⟨T1', t1'⟩ := Nat.dvd_of_mod_eq_zero c1'
  obtain ⟨T2, t2⟩ := Nat.dvd_of_mod_eq_zero c2
  obtain ⟨T2', t2'⟩ := Nat.dvd_of_mod_eq_zero c2'
  obtain ⟨T3, t3⟩ := Nat.dvd_of_mod_eq_zero c3
  obtain ⟨T3', t3'⟩ := Nat.dvd_of_mod_eq_zero c3'
  obtain ⟨T4, t4⟩ := Nat.dvd_of_mod_eq_zero c4
  obtain ⟨T4', t4'⟩ := Nat.dvd_of_mod_eq_zero c4'
  rw [neg_one_zpow_congr (simplex_sign_parity j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4
    m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 s0 s0' s1 s1' s2 s2' s3 s3' s4
    k01 e01 k02 e02 k03 e03 k04 e04 k12 e12 k13 e13 k14 e14 k23 e23 k24 e24 k34 e34
    n0 f0 n1 f1 n2 f2 n3 f3 n4 f4 T0 t0 T0' t0' T1 t1 T1' t1' T2 t2 T2' t2' T3 t3 T3' t3' T4 t4 T4' t4')]


/-- One term of the 4-simplex contraction (`fifteenJSimplex`), the normalisations `√(2i+1)` of the
intertwiners removed. -/
noncomputable def simplexTermK (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ) (m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 : ℤ) : ℝ :=
  edgeSign j01 m01 * edgeSign j02 m02 * edgeSign j03 m03 * edgeSign j04 m04 * edgeSign j12 m12 * edgeSign j13 m13 * edgeSign j14 m14 * edgeSign j23 m23 * edgeSign j24 m24 * edgeSign j34 m34 *
    ((-1 : ℝ) ^ (((i0 : ℤ) - μ0) / 2) * threeJ j01 j02 i0 m01 m02 μ0 * threeJ i0 j03 j04 (-μ0) m03 m04) *
    ((-1 : ℝ) ^ (((i1 : ℤ) - μ1) / 2) * threeJ j12 j13 i1 m12 m13 μ1 * threeJ i1 j14 j01 (-μ1) m14 (-m01)) *
    ((-1 : ℝ) ^ (((i2 : ℤ) - μ2) / 2) * threeJ j23 j24 i2 m23 m24 μ2 * threeJ i2 j02 j12 (-μ2) (-m02) (-m12)) *
    ((-1 : ℝ) ^ (((i3 : ℤ) - μ3) / 2) * threeJ j34 j03 i3 m34 (-m03) μ3 * threeJ i3 j13 j23 (-μ3) (-m13) (-m23)) *
    ((-1 : ℝ) ^ (((i4 : ℤ) - μ4) / 2) * threeJ j04 j14 i4 (-m04) (-m14) μ4 * threeJ i4 j24 j34 (-μ4) (-m24) (-m34))

/-- One term of the Möbius ladder of the 4-simplex: rails `(i₀, j₀₂, i₂, j₂₄, i₄, j₁₄)` and
`(j₁₄, i₁, j₁₃, i₃, j₀₃, i₀)`, rungs `(j₀₁, j₁₂, j₂₃, j₃₄, j₀₄)`. -/
noncomputable def simplexTermL (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ) (p0 p1 p2 p3 p4 : ℤ × ℤ) (c0 c1 c2 c3 c4 : ℤ) : ℝ :=
  (edgeSign i0 p0.1 * edgeSign j14 p0.2) *
    (edgeSign j01 c0 * threeJ i0 j02 j01 (-p0.1) p1.1 c0 * threeJ j14 i1 j01 (-p0.2) p1.2 (-c0)) *
    (edgeSign j02 p1.1 * edgeSign i1 p1.2) *
    (edgeSign j12 c1 * threeJ j02 i2 j12 (-p1.1) p2.1 c1 * threeJ i1 j13 j12 (-p1.2) p2.2 (-c1)) *
    (edgeSign i2 p2.1 * edgeSign j13 p2.2) *
    (edgeSign j23 c2 * threeJ i2 j24 j23 (-p2.1) p3.1 c2 * threeJ j13 i3 j23 (-p2.2) p3.2 (-c2)) *
    (edgeSign j24 p3.1 * edgeSign i3 p3.2) *
    (edgeSign j34 c3 * threeJ j24 i4 j34 (-p3.1) p4.1 c3 * threeJ i3 j03 j34 (-p3.2) p4.2 (-c3)) *
    (edgeSign i4 p4.1 * edgeSign j03 p4.2) *
    (edgeSign j04 c4 * threeJ i4 j14 j04 (-p4.1) p0.2 c4 * threeJ j03 i0 j04 (-p4.2) p0.1 (-c4))

/-- `simplex_term` in terms of `simplexTermK` and `simplexTermL`. -/
lemma simplexTermK_eq (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ) (m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 : ℤ) :
    simplexTermK j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 =
      (-1 : ℝ) ^ j14 * simplexTermL j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 (-μ0, -m14) (m02, -μ1) (-μ2, m13) (m24, -μ3) (-μ4, -m03)
        m01 (-m12) m23 (-m34) (-m04) := by
  unfold simplexTermK simplexTermL
  simp only [neg_neg]
  rw [simplex_term]
  ring

/-- A product of five normalised sums is a five-fold sum (the order of `simp`). -/
lemma prod_five_sums (E c0 c1 c2 c3 c4 : ℝ) (I0 I1 I2 I3 I4 : Finset ℤ)
    (X0 X1 X2 X3 X4 : ℤ → ℝ) :
    E * ((c0 * ∑ μ ∈ I0, X0 μ) * (c1 * ∑ μ ∈ I1, X1 μ) * (c2 * ∑ μ ∈ I2, X2 μ) *
      (c3 * ∑ μ ∈ I3, X3 μ) * (c4 * ∑ μ ∈ I4, X4 μ)) =
    (c0 * c1 * c2 * c3 * c4) * ∑ μ4 ∈ I4, ∑ μ3 ∈ I3, ∑ μ2 ∈ I2, ∑ μ1 ∈ I1, ∑ μ0 ∈ I0,
      E * X0 μ0 * X1 μ1 * X2 μ2 * X3 μ3 * X4 μ4 := by
  simp only [mul_sum, sum_mul]
  refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
  ring

/-- A product of five rung kernels with their rail signs is a five-fold sum. -/
lemma prod_five_rungs (e0 e1 e2 e3 e4 : ℝ) (I0 I1 I2 I3 I4 : Finset ℤ)
    (Y0 Y1 Y2 Y3 Y4 : ℤ → ℝ) :
    e0 * (∑ c ∈ I0, Y0 c) * e1 * (∑ c ∈ I1, Y1 c) * e2 * (∑ c ∈ I2, Y2 c) * e3 * (∑ c ∈ I3, Y3 c) *
      e4 * (∑ c ∈ I4, Y4 c) =
    ∑ c4 ∈ I4, ∑ c3 ∈ I3, ∑ c2 ∈ I2, ∑ c1 ∈ I1, ∑ c0 ∈ I0,
      e0 * Y0 c0 * e1 * Y1 c1 * e2 * Y2 c2 * e3 * Y3 c3 * e4 * Y4 c4 := by
  simp only [mul_sum, sum_mul]

/-- The 4-simplex contraction as a fifteen-fold sum of `simplexTermK`. -/
lemma fifteenJSimplex_expand (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ) :
    fifteenJSimplex j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 =
      (Real.sqrt ((i0 : ℝ) + 1) * Real.sqrt ((i1 : ℝ) + 1) * Real.sqrt ((i2 : ℝ) + 1) *
        Real.sqrt ((i3 : ℝ) + 1) * Real.sqrt ((i4 : ℝ) + 1)) *
      ∑ m01 ∈ Icc (-(j01 : ℤ)) j01, ∑ m02 ∈ Icc (-(j02 : ℤ)) j02, ∑ m03 ∈ Icc (-(j03 : ℤ)) j03, ∑ m04 ∈ Icc (-(j04 : ℤ)) j04, ∑ m12 ∈ Icc (-(j12 : ℤ)) j12, ∑ m13 ∈ Icc (-(j13 : ℤ)) j13, ∑ m14 ∈ Icc (-(j14 : ℤ)) j14, ∑ m23 ∈ Icc (-(j23 : ℤ)) j23, ∑ m24 ∈ Icc (-(j24 : ℤ)) j24, ∑ m34 ∈ Icc (-(j34 : ℤ)) j34, ∑ μ4 ∈ Icc (-(i4 : ℤ)) i4, ∑ μ3 ∈ Icc (-(i3 : ℤ)) i3, ∑ μ2 ∈ Icc (-(i2 : ℤ)) i2, ∑ μ1 ∈ Icc (-(i1 : ℤ)) i1, ∑ μ0 ∈ Icc (-(i0 : ℤ)) i0, 
        simplexTermK j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 := by
  unfold fifteenJSimplex
  rw [mul_sum]
  refine sum_congr rfl fun m01 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m02 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m03 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m04 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m12 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m13 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m14 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m23 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m24 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun m34 _ => ?_
  unfold fourJ
  rw [prod_five_sums]
  rfl

/-- The Möbius ladder of the 4-simplex as a fifteen-fold sum of `simplexTermL`. -/
lemma mobius_simplex_expand (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ) :
    mobius 5 (railA ![i0, j02, i2, j24, i4] ![j14, i1, j13, i3, j03])
      (railB ![i0, j02, i2, j24, i4] ![j14, i1, j13, i3, j03]) (railC ![j01, j12, j23, j34, j04]) =
    ∑ p0 ∈ pairBox i0 j14, ∑ p4 ∈ pairBox i4 j03, ∑ p3 ∈ pairBox j24 i3, ∑ p2 ∈ pairBox i2 j13,
      ∑ p1 ∈ pairBox j02 i1, ∑ c4 ∈ Icc (-(j04 : ℤ)) j04, ∑ c3 ∈ Icc (-(j34 : ℤ)) j34,
        ∑ c2 ∈ Icc (-(j23 : ℤ)) j23, ∑ c1 ∈ Icc (-(j12 : ℤ)) j12, ∑ c0 ∈ Icc (-(j01 : ℤ)) j01,
          simplexTermL j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 p0 p1 p2 p3 p4 c0 c1 c2 c3 c4 := by
  obtain ⟨A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5, C0, C1, C2, C3, C4⟩ :=
    rail_values ![i0, j02, i2, j24, i4] ![j14, i1, j13, i3, j03] ![j01, j12, j23, j34, j04]
  unfold mobius
  simp only [ladder, rung, pairDelta, ite_mul, one_mul, zero_mul, sum_ite_eq', sum_mul]
  simp only [zero_add, Nat.reduceAdd, A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5, C0, C1, C2,
    C3, C4, Matrix.cons_val]
  refine sum_congr rfl fun p0 hp0 => sum_congr rfl fun p4 _ => sum_congr rfl fun p3 _ =>
    sum_congr rfl fun p2 _ => sum_congr rfl fun p1 _ => ?_
  rw [ite_eq_left hp0]
  unfold rungKernel
  rw [prod_five_rungs]
  rfl

set_option maxHeartbeats 4000000 in
/-- The change of the fifteen summation variables between the 4-simplex contraction and its
Möbius ladder. -/
lemma sum_simplexTermK (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ) :
    ∑ m01 ∈ Icc (-(j01 : ℤ)) j01, ∑ m02 ∈ Icc (-(j02 : ℤ)) j02, ∑ m03 ∈ Icc (-(j03 : ℤ)) j03, ∑ m04 ∈ Icc (-(j04 : ℤ)) j04, ∑ m12 ∈ Icc (-(j12 : ℤ)) j12, ∑ m13 ∈ Icc (-(j13 : ℤ)) j13, ∑ m14 ∈ Icc (-(j14 : ℤ)) j14, ∑ m23 ∈ Icc (-(j23 : ℤ)) j23, ∑ m24 ∈ Icc (-(j24 : ℤ)) j24, ∑ m34 ∈ Icc (-(j34 : ℤ)) j34, ∑ μ4 ∈ Icc (-(i4 : ℤ)) i4, ∑ μ3 ∈ Icc (-(i3 : ℤ)) i3, ∑ μ2 ∈ Icc (-(i2 : ℤ)) i2, ∑ μ1 ∈ Icc (-(i1 : ℤ)) i1, ∑ μ0 ∈ Icc (-(i0 : ℤ)) i0, 
        simplexTermK j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 =
    (-1 : ℝ) ^ j14 * ∑ p0 ∈ pairBox i0 j14, ∑ p4 ∈ pairBox i4 j03, ∑ p3 ∈ pairBox j24 i3, ∑ p2 ∈ pairBox i2 j13,
      ∑ p1 ∈ pairBox j02 i1, ∑ c4 ∈ Icc (-(j04 : ℤ)) j04, ∑ c3 ∈ Icc (-(j34 : ℤ)) j34,
        ∑ c2 ∈ Icc (-(j23 : ℤ)) j23, ∑ c1 ∈ Icc (-(j12 : ℤ)) j12, ∑ c0 ∈ Icc (-(j01 : ℤ)) j01,
          simplexTermL j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 p0 p1 p2 p3 p4 c0 c1 c2 c3 c4 := by
  have hK : ∑ m01 ∈ Icc (-(j01 : ℤ)) j01, ∑ m02 ∈ Icc (-(j02 : ℤ)) j02, ∑ m03 ∈ Icc (-(j03 : ℤ)) j03, ∑ m04 ∈ Icc (-(j04 : ℤ)) j04, ∑ m12 ∈ Icc (-(j12 : ℤ)) j12, ∑ m13 ∈ Icc (-(j13 : ℤ)) j13, ∑ m14 ∈ Icc (-(j14 : ℤ)) j14, ∑ m23 ∈ Icc (-(j23 : ℤ)) j23, ∑ m24 ∈ Icc (-(j24 : ℤ)) j24, ∑ m34 ∈ Icc (-(j34 : ℤ)) j34, ∑ μ4 ∈ Icc (-(i4 : ℤ)) i4, ∑ μ3 ∈ Icc (-(i3 : ℤ)) i3, ∑ μ2 ∈ Icc (-(i2 : ℤ)) i2, ∑ μ1 ∈ Icc (-(i1 : ℤ)) i1, ∑ μ0 ∈ Icc (-(i0 : ℤ)) i0, 
        simplexTermK j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 m01 m02 m03 m04 m12 m13 m14 m23 m24 m34 μ0 μ1 μ2 μ3 μ4 =
      ∑ u ∈ Icc (-(j01 : ℤ)) j01 ×ˢ (Icc (-(j02 : ℤ)) j02 ×ˢ (Icc (-(j03 : ℤ)) j03 ×ˢ (Icc (-(j04 : ℤ)) j04 ×ˢ (Icc (-(j12 : ℤ)) j12 ×ˢ (Icc (-(j13 : ℤ)) j13 ×ˢ (Icc (-(j14 : ℤ)) j14 ×ˢ (Icc (-(j23 : ℤ)) j23 ×ˢ (Icc (-(j24 : ℤ)) j24 ×ˢ (Icc (-(j34 : ℤ)) j34 ×ˢ (Icc (-(i4 : ℤ)) i4 ×ˢ (Icc (-(i3 : ℤ)) i3 ×ˢ (Icc (-(i2 : ℤ)) i2 ×ˢ (Icc (-(i1 : ℤ)) i1 ×ˢ (Icc (-(i0 : ℤ)) i0)))))))))))))), simplexTermK j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 u.1 u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2.1 u.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.2.2.2.2.2.2.2 u.2.2.2.2.2.2.2.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.2.2.2.2.1 u.2.2.2.2.2.2.2.2.2.2.1 := by
    rw [sum_product]
    refine sum_congr rfl fun m01 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m02 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m03 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m04 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m12 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m13 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m14 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m23 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m24 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun m34 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun μ4 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun μ3 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun μ2 _ => ?_
    rw [sum_product]
  have hL : ∑ p0 ∈ pairBox i0 j14, ∑ p4 ∈ pairBox i4 j03, ∑ p3 ∈ pairBox j24 i3, ∑ p2 ∈ pairBox i2 j13,
      ∑ p1 ∈ pairBox j02 i1, ∑ c4 ∈ Icc (-(j04 : ℤ)) j04, ∑ c3 ∈ Icc (-(j34 : ℤ)) j34,
        ∑ c2 ∈ Icc (-(j23 : ℤ)) j23, ∑ c1 ∈ Icc (-(j12 : ℤ)) j12, ∑ c0 ∈ Icc (-(j01 : ℤ)) j01,
          simplexTermL j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 p0 p1 p2 p3 p4 c0 c1 c2 c3 c4 =
      ∑ w ∈ pairBox i0 j14 ×ˢ (pairBox i4 j03 ×ˢ (pairBox j24 i3 ×ˢ (pairBox i2 j13 ×ˢ (pairBox j02 i1 ×ˢ (Icc (-(j04 : ℤ)) j04 ×ˢ (Icc (-(j34 : ℤ)) j34 ×ˢ (Icc (-(j23 : ℤ)) j23 ×ˢ (Icc (-(j12 : ℤ)) j12 ×ˢ (Icc (-(j01 : ℤ)) j01))))))))), simplexTermL j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 w.1 w.2.2.2.2.1 w.2.2.2.1 w.2.2.1 w.2.1 w.2.2.2.2.2.2.2.2.2 w.2.2.2.2.2.2.2.2.1 w.2.2.2.2.2.2.2.1 w.2.2.2.2.2.2.1 w.2.2.2.2.2.1 := by
    rw [sum_product]
    refine sum_congr rfl fun p0 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun p4 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun p3 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun p2 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun p1 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun c4 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun c3 _ => ?_
    rw [sum_product]
    refine sum_congr rfl fun c2 _ => ?_
    rw [sum_product]
  rw [hK, hL, mul_sum]
  refine sum_nbij' (fun u => ((-u.2.2.2.2.2.2.2.2.2.2.2.2.2.2, -u.2.2.2.2.2.2.1), ((-u.2.2.2.2.2.2.2.2.2.2.1, -u.2.2.1), ((u.2.2.2.2.2.2.2.2.1, -u.2.2.2.2.2.2.2.2.2.2.2.1), ((-u.2.2.2.2.2.2.2.2.2.2.2.2.1, u.2.2.2.2.2.1), ((u.2.1, -u.2.2.2.2.2.2.2.2.2.2.2.2.2.1), (-u.2.2.2.1, (-u.2.2.2.2.2.2.2.2.2.1, (u.2.2.2.2.2.2.2.1, (-u.2.2.2.2.1, u.1)))))))))) (fun w => (w.2.2.2.2.2.2.2.2.2, (w.2.2.2.2.1.1, (-w.2.1.2, (-w.2.2.2.2.2.1, (-w.2.2.2.2.2.2.2.2.1, (w.2.2.2.1.2, (-w.1.2, (w.2.2.2.2.2.2.2.1, (w.2.2.1.1, (-w.2.2.2.2.2.2.1, (-w.2.1.1, (-w.2.2.1.2, (-w.2.2.2.1.1, (-w.2.2.2.2.1.2, -w.1.1)))))))))))))))
    (fun u hu => ?_) (fun w hw => ?_) (fun u _ => ?_) (fun w _ => ?_) (fun u _ => ?_)
  · simp only [mem_product, mem_Icc, pairBox] at hu ⊢
    omega
  · simp only [mem_product, mem_Icc, pairBox] at hw ⊢
    omega
  · simp
  · simp
  · exact simplexTermK_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The 4-simplex contraction is the 15j symbol of the first kind** (doubled units):
`fifteenJSimplex = √((2i₀+1)⋯(2i₄+1)) · {15j}(a, b, c)` with rows
`a = (i₀, j₀₂, i₂, j₂₄, i₄)`, `b = (j₁₄, i₁, j₁₃, i₃, j₀₃)`, `c = (j₀₁, j₁₂, j₂₃, j₃₄, j₀₄)`,
for all spins. This is the reduction of the Ooguri vertex amplitude to a sum over one spin of five
6j symbols (Donà–Sarno, arXiv:1807.03066, eq. (5)). -/
theorem fifteenJSimplex_eq (j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 : ℕ) :
    fifteenJSimplex j01 j02 j03 j04 j12 j13 j14 j23 j24 j34 i0 i1 i2 i3 i4 =
      Real.sqrt (((i0 : ℝ) + 1) * ((i1 : ℝ) + 1) * ((i2 : ℝ) + 1) * ((i3 : ℝ) + 1) * ((i4 : ℝ) + 1)) *
        fifteenJ ![i0, j02, i2, j24, i4] ![j14, i1, j13, i3, j03] ![j01, j12, j23, j34, j04] := by
  rw [fifteenJSimplex_expand, sum_simplexTermK, ← mobius_simplex_expand, fifteenJ_eq_mobius]
  simp only [Matrix.cons_val_zero]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
    Real.sqrt_mul (by positivity)]

end Lightlike.Recoupling
