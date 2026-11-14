import Lightlike.Spin4.Fusion
import Lightlike.Spin4.FusionNineJ
import Lightlike.Spin4.SelfDual
import Lightlike.Tests.SixJ

/-!
# Trust checks for the EPRL kinematics (SF5c)

Known values and deliberately wrong inputs for `Lightlike/Spin4/EPRL.lean`,
`Lightlike/Spin4/Intertwiner4.lean` and `Lightlike/Spin4/Fusion.lean`. Doubled spins throughout.

* **Labels.** `γ = 1/2`: `j = 2` gives `(j₊, j₋) = (3/2, 1/2)`, and the admissible `j` are the even
  integers (`4 ∣ J`); `γ = 1/3`: every `j ∈ (3/2) ℕ` (`3 ∣ J`); `j = 1` is not admissible for
  `γ = 1/2`.
* **The EPRL map.** Its entries are the textbook Clebsch–Gordan coefficients of the highest spin:
  `⟨½ ½; ½ -½ | 1 0⟩ = 1/√2`, `⟨3/2 1/2; 1/2 1/2 | 2 1⟩ = √3/2`.
* **Simplicity.** The EPRL labels `(3/2, 1/2)` of `j = 2`, `γ = 1/2`, satisfy weak simplicity;
  the Barrett–Crane-type labels `(1, 1)` and the labels of `γ = 1/2` used with `γ = 1/3` do not.
  The master constraint on the image is `(1 - γ²) j = 3/2`.
* **Fusion coefficients.** On a node with four links `j = 3/2`, `γ = 1/3` (`(j₊, j₋) = (1, ½)`):
  `f(0; 0, 0) = (2j+1)/((2j₊+1)(2j₋+1)) = 2/3`.
  The 2-valent node `j = 2`, `γ = 1/2` has `‖Φ(ι₀)‖² = 5/8 < 1` (the map is not isometric).
* **The 9j form.** At the same node, both sides of `eprlRecoupling_eq_nineJSym` and of
  `fusion_eq_nineJSym` are evaluated independently: the recoupling coefficient
  `λ = √(2j+1)/√((2j₊+1)(2j₋+1)) = √6/3` and `f(0; 0, 0) = 2/3` from the Clebsch–Gordan side
  (`eprlRecoupling_singlet`), and `{1 1 0; ½ ½ 0; 3/2 3/2 0} = √6/12` from Physlib's definition of
  the 9j symbol through three 6j symbols. A wrong simplicity constraint, the spins `|j₊ - j₋| = ½`
  in place of `j = j₊ + j₋ = 3/2` in the 9j symbol, gives `√3/3 ≠ √6/3`.
* **Chirality.** `x ↦ i x` is a self-dual 2-form and `x ↦ x i` is not (it is anti-self-dual), for
  the orientation `(1, i, j, k)`: the first factor of Spin(4), labelled `j₊`, is the self-dual one.
* **Injectivity.** For `γ = 1/3` and four links `j = 3/2` (`Σ 2j⁺ = 8` even) the EPRL map is
  injective on a 4-dimensional space of intertwiners. For `γ = 1/2` and doubled spins
  `(4, 4, 4, 8)` (`Σ 2j⁺ = 15` odd, the case excluded by Kamiński–Kisielowski–Lewandowski 2012,
  Theorem 2) the SU(2) intertwiners form a 3-dimensional space, there are no Spin(4)
  intertwiners, and the map is zero.
-/

open Matrix Finset PhyslibAlpha.Sl2 Lightlike.Pentagon
open scoped Kronecker Quaternion

namespace Lightlike.Spin4.Test

open Lightlike.Spin4 SU2

/-! ## Labels -/

/-- `γ = 1/2`, `j = 2`: `(j₊, j₋) = (3/2, 1/2)`. -/
theorem label_half_four : IsEPRLLabel (1 / 2) (3 + 1) 3 1 :=
  (isEPRLLabel_iff (by norm_num) (by norm_num)).mpr ⟨rfl, by norm_num⟩

/-- `γ = 1/3`, `j = 3/2`: `(j₊, j₋) = (1, 1/2)`. -/
theorem label_third_three : IsEPRLLabel (1 / 3) (2 + 1) 2 1 :=
  (isEPRLLabel_iff (by norm_num) (by norm_num)).mpr ⟨rfl, by norm_num⟩

/-- `γ = 1/2`, `j = 4`: `(j₊, j₋) = (3, 1)`. -/
theorem label_half_eight : IsEPRLLabel (1 / 2) (6 + 2) 6 2 :=
  (isEPRLLabel_iff (by norm_num) (by norm_num)).mpr ⟨rfl, by norm_num⟩

/-- For `γ = 1/2` the admissible spins are the even integers `j` (`4 ∣ 2j`). -/
theorem admissible_half_iff (J : ℕ) : EPRLAdmissible (1 / 2) J ↔ 4 ∣ J := by
  have h := eprlAdmissible_rat_iff (J := J) (p := 1) (q := 2) (by norm_num) (by norm_num)
    (by norm_num)
  rw [show ((1 : ℕ) : ℝ) / (2 : ℕ) = 1 / 2 by norm_num] at h
  rw [h]
  constructor
  · rintro ⟨t, rfl, ht⟩
    rw [show (1 + 2) * t = 3 * t by ring, Nat.even_mul] at ht
    rcases ht with h3 | ⟨s, rfl⟩
    · exact absurd h3 (by decide)
    · exact ⟨s, by ring⟩
  · rintro ⟨s, rfl⟩
    exact ⟨2 * s, by ring, ⟨3 * s, by ring⟩⟩

/-- For `γ = 1/3` the admissible spins are the multiples of `3/2` (`3 ∣ 2j`). -/
theorem admissible_third_iff (J : ℕ) : EPRLAdmissible (1 / 3) J ↔ 3 ∣ J := by
  have h := eprlAdmissible_rat_iff (J := J) (p := 1) (q := 3) (by norm_num) (by norm_num)
    (by norm_num)
  rw [show ((1 : ℕ) : ℝ) / (3 : ℕ) = 1 / 3 by norm_num] at h
  rw [h]
  constructor
  · rintro ⟨t, rfl, -⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl, ⟨2 * t, by ring⟩⟩

/-- **Wrong input**: `j = 1` is not admissible for `γ = 1/2` (`j₊ = 3/4`). -/
theorem not_admissible_half_two : ¬ EPRLAdmissible (1 / 2) 2 := by
  rw [admissible_half_iff]
  decide

/-! ## The EPRL map -/

/-- The highest state goes to the product of highest states. -/
theorem eprlMap_top (n m : ℕ) : eprlMap n m (0, 0) 0 = 1 := by
  rw [eprlMap_apply]
  simp

/-- `⟨½ ½; ½ -½ | 1 0⟩ = 1/√2`: the spin-1 triplet state `M = 0`. -/
theorem eprlMap_one_one : eprlMap 1 1 (0, 1) 1 = ((Real.sqrt 2)⁻¹ : ℝ) := by
  rw [eprlMap_apply]
  simp [Real.sqrt_inv]

/-- `⟨3/2 1/2; 1/2 1/2 | 2 1⟩ = √3/2`. -/
theorem eprlMap_three_one : eprlMap 3 1 (1, 0) 1 = (Real.sqrt 3 / 2 : ℝ) := by
  rw [eprlMap_apply, ite_eq_left (by rfl)]
  congr 1
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h4, ← Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1

/-! ## Simplicity -/

/-- The EPRL labels of `γ = 1/2`, `j = 2` satisfy weak simplicity. -/
theorem weak_simplicity_half {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X 1 1 = -X 0 0) :
    (eprlMap 3 1)ᴴ * simplicityOp (1 / 2) 3 1 X * eprlMap 3 1 = 0 :=
  eprl_weak_simplicity (n := 3) (m := 1) (by norm_num) (by norm_num) label_half_four hX

/-- **Wrong labels**: the Barrett–Crane-type labels `j₊ = j₋ = 1` of `j = 2` violate weak
simplicity for `γ = 1/2`. -/
theorem weak_simplicity_fails_bc :
    ¬ ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 →
      (eprlMap 2 2)ᴴ * simplicityOp (1 / 2) 2 2 X * eprlMap 2 2 = 0 := by
  rw [weak_simplicity_iff (n := 2) (m := 2) (by norm_num)]
  norm_num

/-- **Wrong Immirzi parameter**: the labels `(3/2, 1/2)` of `γ = 1/2` violate weak simplicity for
`γ = 1/3`. -/
theorem weak_simplicity_fails_wrong_gamma :
    ¬ ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 →
      (eprlMap 3 1)ᴴ * simplicityOp (1 / 3) 3 1 X * eprlMap 3 1 = 0 := by
  rw [weak_simplicity_iff (n := 3) (m := 1) (by norm_num)]
  norm_num

/-- The projection theorem for `j₊ = 3/2`, `j₋ = 1/2`: `J₊ = (3/4) L` on the image. -/
theorem projection_half :
    ((3 + 1 : ℕ) : ℂ) • ((eprlMap 3 1)ᴴ * jPlusOp 3 1 matH * eprlMap 3 1) =
      (3 : ℂ) • dSpin (3 + 1) matH := by
  have h := eprlMap_compress_jPlus (n := 3) (m := 1) (X := matH) (by simp [matH])
  exact_mod_cast h

/-- The master constraint on the image for `γ = 1/2`, `j = 2`: `(1 - γ²) j = 3/2`. -/
theorem master_half :
    (eprlMap 3 1)ᴴ * masterOp (1 / 2) 3 1 * eprlMap 3 1 = ((3 / 2 : ℝ) : ℂ) • 1 := by
  rw [eprl_master_constraint (γ := 1 / 2) (n := 3) (m := 1) (by norm_num) (by norm_num)
    label_half_four]
  congr 2
  norm_num

/-- The constraint does not hold strongly for `γ = 1/2`, `j = 2`. -/
theorem not_strong_half :
    ¬ ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 →
      simplicityOp (1 / 2) 3 1 X * eprlMap 3 1 = 0 :=
  eprl_not_strong_simplicity (γ := 1 / 2) (n := 3) (m := 1) (by norm_num) (by norm_num)
    label_half_four (by norm_num)

/-! ## Fusion coefficients -/

/-- **A fusion coefficient**: four links `j = 3/2`, `γ = 1/3` (`(j₊, j₋) = (1, ½)`):
`f(0; 0, 0) = 4/6 = 2/3`. -/
theorem fusion_third : fusion 2 2 2 2 1 1 1 1 0 0 0 = ((2 / 3 : ℝ) : ℂ) := by
  rw [fusion_zero_equal]
  norm_num

/-- The selection rule: `f(6; 0, 0) = 0` (`z = 6 > x + y = 0`). -/
theorem fusion_third_selection : fusion 2 2 2 2 1 1 1 1 6 0 0 = 0 :=
  fusion_eq_zero (zero_mem_channel 2 2) (zero_mem_channel 1 1)
    (by rw [mem_channel]; unfold Tri; omega) (by unfold Tri; omega)

/-! ## The 9j form of the fusion coefficients -/

/-- `√9 = 3`. -/
lemma sqrt_nine : √(9 : ℝ) = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Evaluate a 6j symbol with spins up to `3/2` from Physlib's definition (the method of
`Lightlike/Tests/SixJ.lean`). -/
macro "sixj_eval" : tactic => `(tactic| (
  rw [Lightlike.SixJAudit.sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Lightlike.SixJAudit.mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    Lightlike.SixJAudit.sixSum_eq_sum, Lightlike.SixJAudit.sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [Lightlike.SixJAudit.sqrt_four, sqrt_nine]
  surd_finish))

/-- `{1 ½ 3/2; 3/2 0 1} = -√3/6` (doubled `2 1 3 3 0 2`). -/
theorem sixJ_one_half_a : sixJSym 2 1 3 3 0 2 = -√3 / 6 := by sixj_eval

/-- `{1 ½ 3/2; ½ 1 0} = -√6/6` (doubled `2 1 3 1 2 0`). -/
theorem sixJ_one_half_b : sixJSym 2 1 3 1 2 0 = -√6 / 6 := by sixj_eval

/-- `{0 0 0; 1 1 1} = √3/3` (doubled `0 0 0 2 2 2`). -/
theorem sixJ_zero_one : sixJSym 0 0 0 2 2 2 = √3 / 3 := by sixj_eval

/-- `{1 ½ ½; ½ 0 1} = √6/6` (doubled `2 1 1 1 0 2`). -/
theorem sixJ_one_half_c : sixJSym 2 1 1 1 0 2 = √6 / 6 := by sixj_eval

/-- `{1 ½ ½; ½ 1 0} = √6/6` (doubled `2 1 1 1 2 0`). -/
theorem sixJ_one_half_d : sixJSym 2 1 1 1 2 0 = √6 / 6 := by sixj_eval

/-- `{0 0 0; J 1 1}` vanishes unless `J = 1` (doubled `J = 2`). -/
lemma sixJ_zero_one_eq_zero {J : ℕ} (hJ : J < 2) : sixJSym 0 0 0 J 2 2 = 0 := by
  by_contra h
  have := tri_of_sixJSym_ne_zero h
  unfold Tri at this
  omega

/-- **A 9j symbol from Physlib's definition**: `{1 1 0; ½ ½ 0; 3/2 3/2 0} = √6/12` (doubled
`2 2 0; 1 1 0; 3 3 0`), the sum of three 6j symbols. Only the term `J = 1` (doubled `2`)
survives. -/
theorem nineJ_third : nineJSym 2 2 0 1 1 0 3 3 0 = √6 / 12 := by
  simp only [nineJSym, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sixJ_zero_one_eq_zero (show 0 < 2 by norm_num), sixJ_zero_one_eq_zero (show 1 < 2 by norm_num),
    sixJ_one_half_a, sixJ_one_half_b, sixJ_zero_one, mul_zero]
  ring_nf
  surd_finish

/-- The 9j symbol with the wrong spins `|j₊ - j₋| = ½` in place of `j = 3/2`:
`{1 1 0; ½ ½ 0; ½ ½ 0} = √3/6` (doubled `2 2 0; 1 1 0; 1 1 0`). -/
theorem nineJ_third_wrong : nineJSym 2 2 0 1 1 0 1 1 0 = √3 / 6 := by
  simp only [nineJSym, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    sixJ_zero_one_eq_zero (show 0 < 2 by norm_num), sixJ_zero_one_eq_zero (show 1 < 2 by norm_num),
    sixJ_one_half_c, sixJ_one_half_d, sixJ_zero_one, mul_zero]
  ring_nf
  surd_finish

/-- The recoupling coefficient of the node `j = 3/2`, `γ = 1/3`, from the Clebsch–Gordan side:
`λ = √4/(√3 √2) = √6/3`. -/
lemma eprlRecoupling_third : eprlRecoupling 2 1 2 1 0 0 0 = ((√6 / 3 : ℝ) : ℂ) := by
  rw [eprlRecoupling_singlet]
  congr 1
  norm_num [Lightlike.SixJAudit.sqrt_four]
  rw [show (6 : ℝ) = 3 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
  have h3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have h2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h3' : √(3 : ℝ) ≠ 0 := by positivity
  have h2' : √(2 : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff (mul_ne_zero h3' h2') (by norm_num)]
  linear_combination -((√2 * √2) * h3 + 3 * h2)

/-- **The 9j form of `λ`, with both sides evaluated independently**: at the node `j = 3/2`,
`γ = 1/3`, the Clebsch–Gordan value `λ = √6/3` equals `√((x+1)(y+1)(J₁+1)(J₂+1)) {9j} = 4 · √6/12`
with the 9j symbol computed from Physlib's 6j symbols. -/
theorem eprlRecoupling_nineJ_third :
    eprlRecoupling 2 1 2 1 0 0 0 =
      ((Real.sqrt (((0 : ℕ) + 1) * ((0 : ℕ) + 1) * (((2 + 1 : ℕ) : ℝ) + 1) *
        (((2 + 1 : ℕ) : ℝ) + 1)) * nineJSym 2 2 0 1 1 0 (2 + 1) (2 + 1) 0 : ℝ) : ℂ) := by
  rw [eprlRecoupling_third, show 2 + 1 = 3 from rfl, nineJ_third]
  congr 1
  norm_num
  ring

/-- **The 9j form of the fusion coefficients, with both sides evaluated independently**: at the
node `j = 3/2`, `γ = 1/3`, `f(0; 0, 0) = 2/3 = √(4⁴) {9j}²` with the 9j symbol computed from
Physlib's 6j symbols. -/
theorem fusion_nineJ_third :
    fusion 2 2 2 2 1 1 1 1 0 0 0 = ((Real.sqrt (((0 : ℕ) + 1) * ((0 : ℕ) + 1) * ((0 : ℕ) + 1) *
      (((2 + 1 : ℕ) : ℝ) + 1) * (((2 + 1 : ℕ) : ℝ) + 1) * (((2 + 1 : ℕ) : ℝ) + 1) *
      (((2 + 1 : ℕ) : ℝ) + 1)) * nineJSym 2 2 0 1 1 0 (2 + 1) (2 + 1) 0 *
      nineJSym 2 2 0 1 1 0 (2 + 1) (2 + 1) 0 : ℝ) : ℂ) := by
  rw [fusion_third, show 2 + 1 = 3 from rfl, nineJ_third]
  congr 1
  norm_num
  ring_nf
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

/-- **A wrong simplicity constraint gives a different value**: with the spins `|j₊ - j₋| = ½` in
place of `j = j₊ + j₋ = 3/2`, the 9j formula gives `√3/3`, not the recoupling coefficient
`λ = √6/3`. -/
theorem eprlRecoupling_nineJ_wrong :
    eprlRecoupling 2 1 2 1 0 0 0 ≠
      ((Real.sqrt (((0 : ℕ) + 1) * ((0 : ℕ) + 1) * (((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) + 1)) *
        nineJSym 2 2 0 1 1 0 1 1 0 : ℝ) : ℂ) := by
  rw [eprlRecoupling_third, nineJ_third_wrong, Ne, Complex.ofReal_inj]
  norm_num [Lightlike.SixJAudit.sqrt_four]
  intro h
  have h6 : √(6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h3 : √(3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have := congrArg (· ^ 2) h
  nlinarith

/-- **Not isometric**: the 2-valent node `j = 2`, `γ = 1/2` has `‖Φ(ι₀)‖² = 5/8`. -/
theorem two_valent_half :
    hsInner (eprlIntertwiner 3 3 0 0 1 1 0 0 (ivec (3 + 1) (3 + 1) (0 + 0) (0 + 0) 0))
      (eprlIntertwiner 3 3 0 0 1 1 0 0 (ivec (3 + 1) (3 + 1) (0 + 0) (0 + 0) 0)) =
      ((5 / 8 : ℝ) : ℂ) := by
  rw [eprlIntertwiner_two_valent_norm]
  norm_num

/-! ## The intertwiners `fourJ` -/

/-- **The bridge to `Recoupling/`**: through `fourJ_eq_ivec` and the singlet coefficient,
`ι^{(0)}_{½, -½, -½, ½} = -1/2` for four spins `½` (SF4's `fourJ`, all links outgoing): the
product `(½ ½ 0; ½ -½ 0)(0 ½ ½; 0 -½ ½) = (1/√2)(-1/√2)`. -/
theorem fourJ_half_example : Lightlike.Recoupling.fourJ 1 1 1 1 0 1 (-1) (-1) 1 = -1 / 2 := by
  have hz : 0 ∈ channel 1 1 1 1 := by rw [mem_channel]; unfold Tri; omega
  have h := fourJ_eq_ivec hz ((0, 1) : Idx 1 1) ((0, 1) : Idx 1 1)
  have hc : cgz 1 1 0 ((0, 1) : Idx 1 1) 0 = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
    simp only [cgz, of_apply]
    rw [show (1 + 1 - 0) / 2 = 1 by rfl]
    have := cgCoefficient_singlet (n := 1) (a := 0) (by norm_num)
    norm_num at this ⊢
    rw [this]
    push_cast
    ring
  have hi : ivec 1 1 1 1 0 ((0, 1) : Idx 1 1) ((0, 1) : Idx 1 1) = ((1 / 2 : ℝ) : ℂ) := by
    simp only [ivec, Matrix.smul_apply, mul_apply, conjTranspose_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, smul_eq_mul]
    rw [hc, Complex.star_def, Complex.conj_ofReal]
    push_cast
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
    have h0 : ((Real.sqrt (0 + 1) : ℝ) : ℂ) = 1 := by norm_num
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    rw [h0]
    field_simp
    rw [sq, h2]
  rw [hi] at h
  norm_num at h
  have h' : ((Lightlike.Recoupling.fourJ 1 1 1 1 0 1 (-1) (-1) 1 : ℝ) : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by
    rw [h]; push_cast; ring
  exact_mod_cast h'

/-! ## Chirality -/

/-- The quaternion `i`. -/
private def qi : ℍ := ⟨0, 1, 0, 0⟩

/-- `x ↦ i x` is self-dual: its 2-form is `-(e₀ ∧ e₁ + e₂ ∧ e₃)`. -/
theorem leftMat_i_selfDual : IsSelfDual (leftMat qi) := leftMat_isSelfDual rfl

/-- **Wrong chirality**: `x ↦ x i` is not self-dual (it is anti-self-dual and nonzero). -/
theorem rightMat_i_not_selfDual : ¬ IsSelfDual (rightMat qi) := by
  intro h
  have h1 := (rightMat_isAntiSelfDual (u := qi) rfl).2
  have h2 := congrFun (congrFun (h.2.symm.trans h1) 2) 3
  simp [rightMat, qi] at h2
  norm_num at h2

/-! ## Injectivity -/

/-- The four links `j = 3/2` carry a 4-dimensional space of SU(2) intertwiners. -/
theorem channel_three : channel 3 3 3 3 = {0, 2, 4, 6} := by
  ext z
  simp only [mem_channel, Finset.mem_insert, Finset.mem_singleton]
  unfold Tri
  constructor
  · intro h; omega
  · intro h; omega

/-- **Non-vacuity of injectivity**: for `γ = 1/3` and four links `j = 3/2` (`Σ 2j⁺ = 8` even) the
EPRL map is injective. -/
theorem injective_third (T : Matrix (Idx (2 + 1) (2 + 1)) (Idx (2 + 1) (2 + 1)) ℂ)
    (hT : IsIntertwiner (2 + 1) (2 + 1) (2 + 1) (2 + 1) T)
    (h0 : eprlIntertwiner 2 2 2 2 1 1 1 1 T = 0) : T = 0 :=
  eprlIntertwiner_injective (γ := 1 / 3) (n₁ := 2) (n₂ := 2) (n₃ := 2) (n₄ := 2) (m₁ := 1)
    (m₂ := 1) (m₃ := 1) (m₄ := 1) (by norm_num) (by norm_num) label_third_three
    label_third_three label_third_three label_third_three ⟨4, rfl⟩ hT h0

/-- The SU(2) side of the counterexample: doubled spins `(4, 4, 4, 8)` have the 3 intertwiners
`z ∈ {4, 6, 8}`. -/
theorem channel_counterexample : channel 4 4 4 8 = {4, 6, 8} := by
  ext z
  simp only [mem_channel, Finset.mem_insert, Finset.mem_singleton]
  unfold Tri
  constructor
  · intro h; omega
  · intro h; omega

/-- **Without the parity condition the EPRL map is not injective** (the case excluded by
Kamiński–Kisielowski–Lewandowski 2012, Theorem 2): for `γ = 1/2` and doubled spins `(4, 4, 4, 8)`,
with labels `(3, 1), (3, 1), (3, 1), (6, 2)` and `Σ n_a = 15` odd, the intertwiner `ι₄` is nonzero
and `Φ(ι₄) = 0`. -/
theorem not_injective_without_parity :
    IsIntertwiner (3 + 1) (3 + 1) (3 + 1) (6 + 2) (ivec (3 + 1) (3 + 1) (3 + 1) (6 + 2) 4) ∧
      ivec (3 + 1) (3 + 1) (3 + 1) (6 + 2) 4 ≠ 0 ∧
      eprlIntertwiner 3 3 3 6 1 1 1 2 (ivec (3 + 1) (3 + 1) (3 + 1) (6 + 2) 4) = 0 := by
  have hz : 4 ∈ channel (3 + 1) (3 + 1) (3 + 1) (6 + 2) := by
    rw [mem_channel]; unfold Tri; omega
  refine ⟨(mem_channel.mp hz).elim fun a b => ivec_isIntertwiner a b, fun h => ?_,
    eprlIntertwiner_eq_zero_of_not_even (by rw [Nat.not_even_iff_odd]; decide) _⟩
  have h1 := hsInner_ivec hz hz
  rw [h, ite_eq_left rfl] at h1
  simp [hsInner] at h1

/-- The same counterexample through the general criterion. -/
theorem not_injective_counterexample :
    ¬ ∀ T : Matrix (Idx (3 + 1) (3 + 1)) (Idx (3 + 1) (6 + 2)) ℂ,
      IsIntertwiner (3 + 1) (3 + 1) (3 + 1) (6 + 2) T →
        eprlIntertwiner 3 3 3 6 1 1 1 2 T = 0 → T = 0 := by
  rw [eprlIntertwiner_injective_iff (γ := 1 / 2) (n₁ := 3) (n₂ := 3) (n₃ := 3) (n₄ := 6) (m₁ := 1)
    (m₂ := 1) (m₃ := 1) (m₄ := 2) (by norm_num) (by norm_num) label_half_four label_half_four
    label_half_four label_half_eight]
  rintro (h | h)
  · exact absurd h (by rw [Nat.not_even_iff_odd]; decide)
  · have : 4 ∈ channel (3 + 1) (3 + 1) (3 + 1) (6 + 2) := by
      rw [mem_channel]; unfold Tri; omega
    rw [h] at this
    exact Finset.notMem_empty _ this

end Lightlike.Spin4.Test
