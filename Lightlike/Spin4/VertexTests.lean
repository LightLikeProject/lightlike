import Lightlike.Spin4.Vertex
import Lightlike.Spin4.EPRLTests

/-!
# Trust checks for the EPRL vertex amplitude (SF6)

Known values and a deliberately wrong input for `Lightlike/Spin4/Vertex.lean`. Doubled spins
throughout. The configurations live on the 4-cycle `0-3-1-4-0` of `K₅` (edges `03, 04, 13, 14`, all
other spins `0`), where every contraction can be evaluated in closed form. Each value below was
computed independently by `scripts/spin4/vertex_check.py` (SymPy, exact arithmetic), both from the
definition (fusion coefficients from Clebsch–Gordan matrices) and from the 9j form.

| check | value | SymPy | theorem |
|---|---|---|---|
| SU(2) contraction on the cycle, spin `j/2`, `i₁ = i₃ = j/2` | `1/(j+1)` | `1/2`, `1/3` | `fifteenJSimplex_cycle_spin` |
| the same at `j = ½`, a second proof of `fifteenJSimplex_cycle` | `1/2` | `1/2` | `fifteenJSimplex_cycle_half` |
| EPRL vertex, `(j₊, j₋) = (½, 0)` on the cycle (the self-dual sector) | `1/2` | `1/2` | `eprlVertex_cycle_selfDual` |
| EPRL vertex, `γ = 1/3`, `(j₊, j₋) = (1, ½)`, `j = 3/2` on the cycle, `i₁ = i₃ = 3/2` | `2/27` | `2/27` | `eprlVertex_cycle_third` |
| the 9j form with the wrong simplicity spins `|j₊ - j₋| = ½`, `i₁ = i₃ = ½` | `1/54` | `1/54` | `vertexNineJ_wrong_simplicity` |
| the two differ | `2/27 ≠ 1/54` | | `eprlVertex_ne_wrong_simplicity` |

The labels of the `γ = 1/3` configuration are EPRL labels of `γ = 1/3` and not of `γ = 1/2`
(`isEPRLVertexLabel_cycle_third`, `not_isEPRLVertexLabel_cycle_half`), its boundary intertwiners
are admissible and a wrong boundary is not (`isVertexBoundary_cycle_third`,
`not_isVertexBoundary_cycle`), and an odd self-dual spin sum at a node gives zero
(`eprlVertex_odd`).

The value `1/(j+1)` of the cycle is the closed loop of spin `j/2` with four normalised 2-valent
nodes: `dim · (1/√dim)⁴ = 1/dim`.

## The 6j and 9j values used

From Physlib's definitions, evaluated with `sixj_eval` (`Lightlike/Spin4/EPRLTests.lean`) and the
closed form `sixJSym_zero_left`: `{1 ½ 3/2; 0 3/2 ½} = -√2/4`, `{1 ½ ½; 0 ½ ½} = 1/2`,
`{0 1 1; 0 ½ ½; 0 3/2 3/2} = {1 0 1; ½ 0 ½; 3/2 0 3/2} = √6/12`, and
`{0 1 1; 0 ½ ½; 0 ½ ½} = {1 0 1; ½ 0 ½; ½ 0 ½} = √3/6` (all agree with SymPy's `wigner_6j` and
`wigner_9j`).

## Published numerics

The literature studies the Euclidean EPRL vertex for `γ < 1` through its large-spin asymptotics,
analytically and in plots (e.g. Barrett, Dowdall, Fairbairn, Gomes, Hellmann 2009,
arXiv:0902.1170, for the coherent amplitude); we found no tables of exact small-spin values to
compare with. The independent SymPy evaluation above takes their place; it is numerical evidence,
not part of the proof.
-/

open Finset PhyslibAlpha.Sl2 Lightlike.Pentagon Lightlike.Recoupling Lightlike.Spin4

namespace Lightlike.Spin4.VertexTests

/-! ## The SU(2) contraction on the 4-cycle, for every spin -/

/-- `(0 j j; 0 a b) = 0` unless `b = -a`. -/
lemma threeJ_0jj_eq_zero {j : ℕ} {a b : ℤ} (h : b ≠ -a) : threeJ 0 j j 0 a b = 0 := by
  rw [threeJ_zero_left, ite_eq_right (fun h' => h h'.2.2.1)]

/-- `(0 j j; 0 a -a)² = 1/(j+1)` for an admissible projection `a`, and `0` otherwise. -/
lemma threeJ_0jj_sq (j : ℕ) (a : ℤ) :
    threeJ 0 j j 0 a (-a) ^ 2 =
      if -(j : ℤ) ≤ a ∧ a ≤ j ∧ ((j : ℤ) - a) % 2 = 0 then 1 / ((j : ℝ) + 1) else 0 := by
  rw [threeJ_zero_left]
  by_cases h : -(j : ℤ) ≤ a ∧ a ≤ j ∧ ((j : ℤ) - a) % 2 = 0
  · rw [ite_eq_left ⟨rfl, rfl, rfl, h.1, h.2.1, h.2.2⟩, ite_eq_left h, div_pow,
      Real.sq_sqrt (by positivity), ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  · rw [ite_eq_right (fun h' => h ⟨h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2⟩), ite_eq_right h]
    norm_num

/-- The intertwiner `ι^{(0)}` of spins `(0, 0, j, j)` is the 3j symbol `(0 j j; 0 a b)`. -/
lemma fourJ_00jj (j : ℕ) (a b : ℤ) : fourJ 0 0 j j 0 0 0 a b = threeJ 0 j j 0 a b := by
  unfold fourJ
  simp [threeJ_zero_zero]

/-- The intertwiner `ι^{(0)}` of spins `(j, j, 0, 0)` is the 3j symbol `(0 j j; 0 a b)`. -/
lemma fourJ_jj00 (j : ℕ) (a b : ℤ) : fourJ j j 0 0 0 a b 0 0 = threeJ 0 j j 0 a b := by
  unfold fourJ
  simp [threeJ_zero_zero, threeJ_cycle 0 j j 0 a b]

/-- The intertwiner `ι^{(j)}` of spins `(0, j, j, 0)` vanishes unless `b = -a`. -/
lemma fourJ_0jj0_eq_zero {j : ℕ} {a b : ℤ} (h : b ≠ -a) : fourJ 0 j j 0 j 0 a b 0 = 0 := by
  unfold fourJ
  refine mul_eq_zero_of_right _ (sum_eq_zero fun μ _ => ?_)
  rw [threeJ_cycle 0 j j 0 (-μ) b]
  by_cases hμ : μ = -a
  · rw [threeJ_0jj_eq_zero (show b ≠ -(-μ) by omega)]
    ring
  · rw [threeJ_0jj_eq_zero hμ]
    ring

/-- The intertwiner `ι^{(j)}` of spins `(0, j, j, 0)` at `(-a, a)`:
`√(j+1) (-1)^{(j-a)/2} (0 j j; 0 -a a)²`. -/
lemma fourJ_0jj0_diag (j : ℕ) (a : ℤ) :
    fourJ 0 j j 0 j 0 (-a) a 0 =
      Real.sqrt ((j : ℝ) + 1) * (edgeSign j a * threeJ 0 j j 0 (-a) a ^ 2) := by
  unfold fourJ
  congr 1
  rw [sum_eq_single a]
  · rw [threeJ_cycle 0 j j 0 (-a) a, edgeSign]
    ring
  · intro μ _ hμ
    rw [threeJ_0jj_eq_zero (show μ ≠ -(-a) by omega)]
    ring
  · intro ha
    rw [threeJ_zero_left, ite_eq_right (fun h => ha (mem_Icc.mpr ⟨by omega, by omega⟩))]
    ring

/-- The edge sign squares to `1`. -/
lemma edgeSign_sq (j : ℕ) (m : ℤ) : edgeSign j m ^ 2 = 1 := by
  rw [edgeSign, sq, ← mul_zpow, neg_one_mul, neg_neg, one_zpow]

/-- A spin `j/2` has `j + 1` projections: the `m ∈ [-j, j]` with `j - m` even. -/
lemma card_proj (j : ℕ) :
    ((Icc (-(j : ℤ)) j).filter (fun a => ((j : ℤ) - a) % 2 = 0)).card = j + 1 := by
  have h : (Icc (-(j : ℤ)) j).filter (fun a => ((j : ℤ) - a) % 2 = 0) =
      (range (j + 1)).image (fun k : ℕ => (j : ℤ) - 2 * k) := by
    ext a
    simp only [mem_filter, mem_Icc, mem_image, mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(((j : ℤ) - a) / 2).toNat, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [h, card_image_of_injective _ ?_, card_range]
  intro k l hkl
  simp only at hkl
  omega

/-- **Value check (the closed loop).** Spin `j/2` on the four edges of the cycle `0-3-1-4-0` of
`K₅`, spin `0` elsewhere, intertwiners `i₁ = i₃ = j/2` and `i₀ = i₂ = i₄ = 0`: the
4-simplex contraction is `1/(j+1) = 1/dim`, the trace of the identity on spin `j/2` with four
normalised 2-valent nodes. Proved for every `j`, by collapsing the four projection sums. -/
theorem fifteenJSimplex_cycle_spin (j : ℕ) :
    fifteenJSimplex 0 0 j j 0 j j 0 0 0 0 j 0 j 0 = 1 / ((j : ℝ) + 1) := by
  have hcount : ∑ a ∈ Icc (-(j : ℤ)) j,
      (if ((j : ℤ) - a) % 2 = 0 then 1 / ((j : ℝ) + 1) ^ 2 else 0) = 1 / ((j : ℝ) + 1) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, card_proj]
    push_cast
    field_simp
  have e0 : edgeSign 0 0 = 1 := by simp [edgeSign]
  unfold fifteenJSimplex
  simp only [Nat.cast_zero, neg_zero, Icc_self, sum_singleton, fourJ_00jj, fourJ_jj00,
    threeJ_zero_zero, e0, one_mul, mul_one]
  rw [← hcount]
  refine sum_congr rfl fun a ha => ?_
  rw [mem_Icc] at ha
  rw [sum_eq_single (-a)]
  · rw [sum_eq_single (-a)]
    · rw [sum_eq_single a]
      · simp only [neg_neg, fourJ_0jj0_diag]
        by_cases hp : ((j : ℤ) - a) % 2 = 0
        · have h1 := threeJ_0jj_sq j a
          have h2 := threeJ_0jj_sq j (-a)
          rw [ite_eq_left ⟨ha.1, ha.2, hp⟩] at h1
          rw [neg_neg, ite_eq_left ⟨by omega, by omega, by omega⟩] at h2
          have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
          rw [ite_eq_left hp]
          have hε := edgeSign_sq j a
          have hε' := edgeSign_sq j (-a)
          have hj : (j : ℝ) + 1 ≠ 0 := by positivity
          calc _ = (edgeSign j a ^ 2) ^ 2 * edgeSign j (-a) ^ 2 * threeJ 0 j j 0 a (-a) ^ 2 *
                Real.sqrt ((j : ℝ) + 1) ^ 2 * (threeJ 0 j j 0 (-a) a ^ 2) ^ 2 := by ring
            _ = _ := by rw [hε, hε', h1, hs, h2]; field_simp
        · rw [ite_eq_right hp, threeJ_zero_left,
            ite_eq_right (fun h => hp h.2.2.2.2.2)]
          ring
      · intro b _ hb
        rw [threeJ_0jj_eq_zero (show -b ≠ -(- -a) by omega)]
        ring
      · intro h
        exact (h (mem_Icc.mpr ⟨by omega, by omega⟩)).elim
    · intro b _ hb
      simp only [fourJ_0jj0_eq_zero (show -b ≠ -(-a) by omega), zero_mul, mul_zero,
        sum_const_zero]
    · intro h
      exact (h (mem_Icc.mpr ⟨by omega, by omega⟩)).elim
  · intro b _ hb
    simp only [threeJ_0jj_eq_zero hb, zero_mul, mul_zero, sum_const_zero]
  · intro h
    exact (h (mem_Icc.mpr ⟨by omega, by omega⟩)).elim

/-- The intertwiner `ι^{(j)}` of spins `(j, 0, 0, j)`: `√(j+1) (-1)^{(j+a)/2} (0 j j; 0 -a a)²` at `(a, -a)`, and `0`
at other projections. -/
lemma fourJ_j00j (j : ℕ) (a b : ℤ) :
    fourJ j 0 0 j j a 0 0 b = if b = -a then
      Real.sqrt ((j : ℝ) + 1) * (edgeSign j (-a) * (threeJ 0 j j 0 (-a) a * threeJ 0 j j 0 (-a) a)) else 0 := by
  have c1 : ∀ μ : ℤ, threeJ j 0 j a 0 μ = threeJ 0 j j 0 μ a := fun μ =>
    (threeJ_cycle j 0 j a 0 μ).symm ▸ rfl
  have c2 : ∀ μ : ℤ, threeJ j 0 j (-μ) 0 b = threeJ 0 j j 0 b (-μ) := fun μ =>
    (threeJ_cycle j 0 j (-μ) 0 b).symm ▸ rfl
  unfold fourJ
  simp only [c1, c2]
  rw [sum_eq_single (-a)]
  · split_ifs with h
    · subst h
      simp only [neg_neg, edgeSign]
      ring
    · rw [neg_neg, threeJ_0jj_eq_zero (show a ≠ -b by omega)]
      ring
  · intro μ _ hμ
    rw [threeJ_0jj_eq_zero (show a ≠ -μ by omega)]
    ring
  · intro h
    have hz : threeJ 0 j j 0 (-a) a = 0 := by
      rw [threeJ_zero_left, ite_eq_right]
      rintro ⟨-, -, -, h1, h2, h3⟩
      exact h (mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [hz]
    ring

/-- **Value check (the triangle).** Spin `j/2` on the three edges `01, 02, 12` of `K₅`, spin `0`
elsewhere, intertwiners `i₁ = j/2` and `0` at the other four nodes: the 15j contraction is
`1/√(j+1)`. The spins sum to `3j/2`, a half-integer for odd `j`. -/
theorem fifteenJSimplex_triangle (j : ℕ) :
    fifteenJSimplex j j 0 0 j 0 0 0 0 0 0 j 0 0 0 = 1 / Real.sqrt ((j : ℝ) + 1) := by
  have e0 : edgeSign 0 0 = 1 := by simp [edgeSign]
  unfold fifteenJSimplex
  simp only [Nat.cast_zero, neg_zero, Icc_self, sum_singleton, fourJ_00jj, fourJ_jj00,
    e0, mul_one, fourJ_j00j]
  have hs : (0 : ℝ) < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hcount : ∑ a ∈ Icc (-(j : ℤ)) j,
      (if ((j : ℤ) - a) % 2 = 0 then 1 / ((j : ℝ) + 1) ^ 2 else 0) = 1 / ((j : ℝ) + 1) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, card_proj]
    push_cast
    field_simp
  have key : ∀ a ∈ Icc (-(j : ℤ)) j, ∑ x_1 ∈ Icc (-(j : ℤ)) j, ∑ x_2 ∈ Icc (-(j : ℤ)) j,
      edgeSign j a * edgeSign j x_1 * edgeSign j x_2 *
        ((threeJ 0 j j 0 a x_1 *
          (if -a = -x_2 then Real.sqrt ((j : ℝ) + 1) * (edgeSign j (-x_2) *
            (threeJ 0 j j 0 (-x_2) x_2 * threeJ 0 j j 0 (-x_2) x_2)) else 0)) *
          threeJ 0 j j 0 (-x_1) (-x_2) * threeJ 0 0 0 0 0 0 * threeJ 0 0 0 0 0 0) =
      (if ((j : ℤ) - a) % 2 = 0 then 1 / ((j : ℝ) + 1) ^ 2 else 0) * Real.sqrt ((j : ℝ) + 1) := by
    intro a ha
    rw [mem_Icc] at ha
    rw [sum_eq_single (-a)]
    · rw [sum_eq_single a]
      · simp only [neg_neg, ite_true]
        by_cases hp : ((j : ℤ) - a) % 2 = 0
        · have h1 := threeJ_0jj_sq j a
          have h2 := threeJ_0jj_sq j (-a)
          rw [ite_eq_left ⟨ha.1, ha.2, hp⟩] at h1
          rw [neg_neg, ite_eq_left ⟨by omega, by omega, by omega⟩] at h2
          have hε := edgeSign_sq j a
          have hε' := edgeSign_sq j (-a)
          have hj : (j : ℝ) + 1 ≠ 0 := by positivity
          rw [ite_eq_left hp, threeJ_zero_zero]
          calc _ = (edgeSign j a ^ 2) * edgeSign j (-a) ^ 2 * (threeJ 0 j j 0 a (-a) ^ 2) *
                (threeJ 0 j j 0 (-a) a ^ 2) * Real.sqrt ((j : ℝ) + 1) := by ring
            _ = _ := by rw [hε, hε', h1, h2]; field_simp
        · have h1 := threeJ_0jj_sq j a
          rw [ite_eq_right (fun h => hp h.2.2)] at h1
          have h0 : threeJ 0 j j 0 a (-a) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
          rw [ite_eq_right hp, h0]
          ring
      · intro b _ hb
        rw [ite_eq_right (show ¬(-a = -b) by omega)]
        ring
      · intro h
        exact (h (mem_Icc.mpr ⟨by omega, by omega⟩)).elim
    · intro b _ hb
      rw [threeJ_0jj_eq_zero (show b ≠ -a by omega)]
      simp
    · intro h
      exact (h (mem_Icc.mpr ⟨by omega, by omega⟩)).elim
  rw [sum_congr rfl key, ← sum_mul, hcount]
  have hq := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
  field_simp
  nlinarith [hq]

/-- **Cross-check with `fifteenJSimplex_cycle`.** At spin `½` the general closed loop gives `1/2`, the value of
`Lightlike.Recoupling.fifteenJSimplex_cycle`, which was evaluated from a table of spin-½ 3j symbols. -/
theorem fifteenJSimplex_cycle_half :
    fifteenJSimplex 0 0 1 1 0 1 1 0 0 0 0 1 0 1 0 = 1 / 2 := by
  rw [fifteenJSimplex_cycle_spin]
  norm_num

/-! ## The 6j and 9j values -/

/-- `{1 ½ 3/2; 0 3/2 ½} = -√2/4` (doubled `2 1 3 0 3 1`). -/
theorem sixJ_one_half_e : sixJSym 2 1 3 0 3 1 = -√2 / 4 := by sixj_eval

/-- `{1 ½ ½; 0 ½ ½} = 1/2` (doubled `2 1 1 0 1 1`). -/
theorem sixJ_one_half_f : sixJSym 2 1 1 0 1 1 = 1 / 2 := by sixj_eval

/-- The 9j symbol of nine zero spins is `1`. -/
theorem nineJ_zero : nineJSym 0 0 0 0 0 0 0 0 0 = 1 := by
  have h := nineJSym_singlet 0 0
  norm_num at h
  exact h

/-- `{0 1 1; 0 ½ ½; 0 3/2 3/2} = √6/12` (doubled `0 2 2; 0 1 1; 0 3 3`), from Physlib's
definition: only the term `J = 3/2` survives. -/
theorem nineJ_cycle_left : nineJSym 0 2 2 0 1 1 0 3 3 = √6 / 12 := by
  simp only [nineJSym, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sixJSym_zero_left]
  norm_num [Tri, sixJ_one_half_e, Lightlike.Spin4.Test.sixJ_one_half_a]
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  ring

/-- `{1 0 1; ½ 0 ½; 3/2 0 3/2} = √6/12` (doubled `2 0 2; 1 0 1; 3 0 3`), from Physlib's
definition: only the term `J = ½` survives. -/
theorem nineJ_cycle_right : nineJSym 2 0 2 1 0 1 3 0 3 = √6 / 12 := by
  simp only [nineJSym, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sixJSym_zero_left]
  norm_num [Tri, sixJ_one_half_e, Lightlike.Spin4.Test.sixJ_one_half_b]
  field_simp
  ring

/-- With the wrong spins `½` in place of `3/2`: `{0 1 1; 0 ½ ½; 0 ½ ½} = √3/6` (doubled
`0 2 2; 0 1 1; 0 1 1`). -/
theorem nineJ_cycle_left_wrong : nineJSym 0 2 2 0 1 1 0 1 1 = √3 / 6 := by
  simp only [nineJSym, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sixJSym_zero_left]
  norm_num [Tri, sixJ_one_half_f, Lightlike.Spin4.Test.sixJ_one_half_c]
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  field_simp

/-- With the wrong spins `½` in place of `3/2`: `{1 0 1; ½ 0 ½; ½ 0 ½} = √3/6` (doubled
`2 0 2; 1 0 1; 1 0 1`). -/
theorem nineJ_cycle_right_wrong : nineJSym 2 0 2 1 0 1 1 0 1 = √3 / 6 := by
  simp only [nineJSym, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sixJSym_zero_left]
  norm_num [Tri, sixJ_one_half_f, Lightlike.Spin4.Test.sixJ_one_half_d]
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  field_simp

/-! ## Labels and boundaries -/

/-- **Non-vacuity of the labels.** `(j₊, j₋) = (1, ½)` on the cycle edges and `(0, 0)` elsewhere
are EPRL labels of `γ = 1/3` (`j = 3/2`, `j₊ - j₋ = γ j`). -/
theorem isEPRLVertexLabel_cycle_third :
    IsEPRLVertexLabel (1 / 3) ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] := by
  intro e
  rw [isEPRLLabel_iff (by norm_num) (by norm_num)]
  fin_cases e <;> norm_num

/-- **Wrong input.** The same labels are not EPRL labels of `γ = 1/2`. -/
theorem not_isEPRLVertexLabel_cycle_half :
    ¬ IsEPRLVertexLabel (1 / 2) ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0]
      ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] := by
  intro h
  have h2 := (isEPRLLabel_iff (by norm_num) (by norm_num)).mp (h 2)
  norm_num at h2

/-- **Non-vacuity of the boundary condition.** `i₁ = i₃ = 3/2` and `i₀ = i₂ = i₄ = 0` are
admissible intertwiner spins for the `γ = 1/3` labels (`j = 3/2` on the cycle). -/
theorem isVertexBoundary_cycle_third :
    IsVertexBoundary ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0]
      ![0, 3, 0, 3, 0] := by
  decide

/-- **Wrong input.** `i₁ = ½` is not admissible there: node 1 couples `(0, 3/2)` to `(3/2, 0)`. -/
theorem not_isVertexBoundary_cycle :
    ¬ IsVertexBoundary ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0]
      ![0, 1, 0, 3, 0] := by
  decide

/-! ## Values of the vertex amplitude -/

/-- **The selection rule at work.** One edge `01` with `j₊ = ½`: the self-dual spins at node `0`
sum to an odd number, so the amplitude vanishes for every `j₋` and every boundary. -/
theorem eprlVertex_odd (m : Fin 10 → ℕ) (z : Fin 5 → ℕ) :
    eprlVertex ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0] m z = 0 :=
  eprlVertex_eq_zero_of_not_even_left _ m z 0 (by decide)

/-- **Value check (self-dual sector).** `(j₊, j₋) = (½, 0)` on the cycle, `i₁ = i₃ = ½`: the EPRL
vertex is the SU(2) contraction `1/2` (SymPy: `1/2`). -/
theorem eprlVertex_cycle_selfDual :
    eprlVertex ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] 0 ![0, 1, 0, 1, 0] = ((1 / 2 : ℝ) : ℂ) := by
  rw [eprlVertex_zero_right _ _ (by decide)]
  simp only [Matrix.cons_val]
  rw [fifteenJSimplex_cycle_half]

/-- The 9j form at the `γ = 1/3` cycle: one term, with fusion factor `(√6/3)⁴` and the SU(2)
contractions `1/3` and `1/2`. -/
theorem vertexNineJ_cycle_third :
    vertexNineJ ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0]
      (![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] + ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0]) ![0, 3, 0, 3, 0] =
        2 / 27 := by
  unfold vertexNineJ
  rw [show (fun a => nodeChannel4 (k5Spins ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] a)
      (k5Spins ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] a)) =
    fun a => {(![(0, 0), (2, 1), (0, 0), (2, 1), (0, 0)] : Fin 5 → ℕ × ℕ) a} by
    funext a; fin_cases a <;> decide, Fintype.piFinset_singleton, sum_singleton]
  simp only [Fin.prod_univ_five, nodeFusionNineJ, k5Spins, Pi.add_apply, Matrix.cons_val,
    Nat.reduceAdd]
  rw [nineJ_zero, Lightlike.Spin4.Test.nineJ_third, nineJ_cycle_left, nineJ_cycle_right,
    fifteenJSimplex_cycle_spin 2, fifteenJSimplex_cycle_spin 1]
  norm_num
  have h6 : √(6 : ℝ) * √6 = 6 := Real.mul_self_sqrt (by norm_num)
  have h384 : √(384 : ℝ) * √384 = 384 := Real.mul_self_sqrt (by norm_num)
  calc _ = 4 * 4 / (12 ^ 6 * 3 * 2) * (√(6 : ℝ) * √6) ^ 3 * (√384 * √384) := by ring
    _ = 2 / 27 := by rw [h6, h384]; norm_num

/-- **Value check (`γ = 1/3`).** The EPRL vertex with `(j₊, j₋) = (1, ½)`, `j = 3/2`, on the
cycle and intertwiners `i₁ = i₃ = 3/2` is `2/27` (SymPy, from the Clebsch–Gordan definition:
`2/27`). The proof goes through the whole chain of `Vertex.lean`: the definition, the 15j form,
the 9j form of the fusion coefficients, Physlib's 6j symbols and the contraction `fifteenJSimplex`. -/
theorem eprlVertex_cycle_third :
    eprlVertex ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] ![0, 3, 0, 3, 0] =
      ((2 / 27 : ℝ) : ℂ) := by
  rw [eprlVertex_eq_vertexNineJ _ _ _ isVertexBoundary_cycle_third, vertexNineJ_cycle_third]

/-- **Wrong simplicity constraint.** The 9j form with the spins `|j₊ - j₋| = ½` of the relation
`k = |j₊ - j₋|` (the one EPRL uses for `γ > 1`) in place of `j = j₊ + j₋ = 3/2`, and the
admissible intertwiners `i₁ = i₃ = ½`, gives `1/54` (SymPy: `1/54`). -/
theorem vertexNineJ_wrong_simplicity :
    vertexNineJ ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0]
      ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] ![0, 1, 0, 1, 0] = 1 / 54 := by
  unfold vertexNineJ
  rw [show (fun a => nodeChannel4 (k5Spins ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] a)
      (k5Spins ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] a)) =
    fun a => {(![(0, 0), (2, 1), (0, 0), (2, 1), (0, 0)] : Fin 5 → ℕ × ℕ) a} by
    funext a; fin_cases a <;> decide, Fintype.piFinset_singleton, sum_singleton]
  simp only [Fin.prod_univ_five, nodeFusionNineJ, k5Spins, Matrix.cons_val]
  rw [nineJ_zero, Lightlike.Spin4.Test.nineJ_third_wrong, nineJ_cycle_left_wrong,
    nineJ_cycle_right_wrong, fifteenJSimplex_cycle_spin 2, fifteenJSimplex_cycle_spin 1]
  norm_num
  have h3 : √(3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h48 : √(48 : ℝ) * √48 = 48 := Real.mul_self_sqrt (by norm_num)
  calc _ = 2 * 2 / (6 ^ 6 * 3 * 2) * (√(3 : ℝ) * √3) ^ 3 * (√48 * √48) := by ring
    _ = 1 / 54 := by rw [h3, h48]; norm_num

/-- **The wrong simplicity constraint changes the amplitude**: `2/27 ≠ 1/54`. -/
theorem eprlVertex_ne_wrong_simplicity :
    eprlVertex ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] ![0, 3, 0, 3, 0] ≠
      (vertexNineJ ![0, 0, 2, 2, 0, 2, 2, 0, 0, 0] ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0]
        ![0, 0, 1, 1, 0, 1, 1, 0, 0, 0] ![0, 1, 0, 1, 0] : ℂ) := by
  rw [eprlVertex_cycle_third, vertexNineJ_wrong_simplicity, Ne, Complex.ofReal_inj]
  norm_num

end Lightlike.Spin4.VertexTests
