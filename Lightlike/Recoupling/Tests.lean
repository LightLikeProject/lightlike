import Lightlike.Recoupling.Orthogonality
import Lightlike.Recoupling.Simplex
import Lightlike.Tests.SixJ

/-!
# Trust checks for the recoupling theory

Kernel-checked values and deliberately wrong inputs for the definitions of this folder.
Reference values are computed independently with SymPy in `scripts/recoupling/` (numerical
evidence, not proof).

## 4-valent intertwiners (`Intertwiner.lean`)

For four spins 1/2 (doubled spins `1 1 1 1`) the invariant space is two-dimensional, with the
virtual spin `k ∈ {0, 1}` (doubled `0, 2`).

| check | value | theorem |
|---|---|---|
| `ι^{(0)}_{½,-½,½,-½}`, evaluated from the definition | `1/2` | `fourJ_hhhh_zero` |
| `⟨ι^{(12)0} \| ι^{(13)0}⟩` (two singlet pairings) | `1/2` | `fourRecoupling_hhhh_00`, `overlap_singlet_pairings` |
| `⟨ι^{(12)0} \| ι^{(13)1}⟩` | `√3/2` | `fourRecoupling_hhhh_02` |
| row `k = 0` of the recoupling matrix has norm 1 | `1/4 + 3/4` | `fourRecoupling_hhhh_row` |

The magnitudes `1/2` and `√3/2` are the standard singlet/triplet recoupling of four spins 1/2;
the signs follow from the Condon–Shortley 3j phases and are those found by SymPy.

Wrong inputs:

- without the factor `√(2k + 1)` (the bare 4jm symbol) the `k = 1` intertwiner has norm squared
  `1/3`, not `1` (`fourJ_unnormalised_fails`);
- the change-of-channel formula without the phase `(-1)^(j₂+j₃+k+l)` gives `-1/2` instead of the
  true overlap `1/2` (`fourRecoupling_without_phase_fails`);
- an inadmissible virtual spin (`k = 2 > ½ + ½`) gives the zero tensor
  (`fourJ_inadmissible_zero`).

## The 15j symbol and the 4-simplex (`FifteenJ.lean`)

| check | value | theorem |
|---|---|---|
| `{15j}` with all spins `0` | `1` | `fifteenJ_zero` |
| 4-simplex contraction with all spins `0` | `1` | `fifteenJSimplex_zero` |
| `{15j}` with `a = 0`, `b = (½,½,½,½,½)`, `c = (0,0,0,0,½)` | `1/4` | `fifteenJ_value` |
| contraction with spins `½` on the 4-cycle `0-3-1-4-0`, `i₁ = i₃ = ½`, evaluated from the definition | `1/2` | `fifteenJSimplex_cycle` |
| the same contraction is `Π_a √(2i_a + 1) · {15j}` = `2 · 1/4` | `1/2` | `fifteenJSimplex_cycle_eq` |
| `{15j}` with `a = (1,½,1,½,1)`, `b = (½,1,½,1,½)`, `c = (½,½,½,½,½)`: all fifteen spins nonzero | `-7/432` | `fifteenJ_all_nonzero` |
| contraction with all triangle spins `½` and all virtual spins `1`, `9√3 · (-7/432)` | `-7√3/48` | `fifteenJSimplex_all_nonzero` |

The last line is an instance of the identity between the 4-simplex contraction and the 15j symbol
of the first kind, proven in general as `Lightlike.Recoupling.fifteenJSimplex_eq`; here both sides are
evaluated independently (the contraction from its definition, the 15j symbol through the zero-spin
reduction), so it also checks that theorem against explicit values.

The values with a zero row reduce the sum over `x` to one term. In `fifteenJ_all_nonzero` no spin
is zero and two terms contribute: `2 · (1/6)⁵ = 1/3888` at `x = ½` and `4 · (-1/3)⁵ = -4/243` at
`x = 3/2`, with the 6j symbols `{1 ½ ½; 1 ½ ½} = {½ 1 ½; ½ 1 ½} = 1/6` and
`{1 ½ 3/2; 1 ½ ½} = {½ 1 3/2; ½ 1 ½} = -1/3` evaluated from Physlib's definition.
`scripts/recoupling/fifteenj_check.py` evaluates the 4-simplex contraction at the same spins
exactly, from SymPy's 3j symbols and without the 6j formula, and finds `-7√3/48`.

Wrong input: the 15j sum with an untwisted closure `(a₅, b₅) = (a₀, b₀)` (the wrong graph) gives
`0` instead of `1/4` (`fifteenJ_untwisted_fails`), and `0` instead of `-7/432` at the spins of
`fifteenJ_all_nonzero` (`fifteenJ_all_nonzero_untwisted_fails`).

## Orthogonality of the 15j symbols (`Orthogonality.lean`)

For `a₀ = 0`, `b = b' = (½,…,½)`, `c = (0,0,0,0,½)` the orthogonality relation
`sum_fifteenJ_mul_fifteenJ` predicts `1/16` (`fifteenJ_orth_predicts`, which also shows that its
conditions can hold); evaluated directly, the sum has the single term `(1/4)² = 1/16`
(`fifteenJ_orth_direct`). With the untwisted closure the term is `0` (`fifteenJ_untwisted_orth_fails`).

## Orthogonality of the 3j and 6j symbols (`ThreeJ.lean`, `Intertwiner.lean`)

| check | value | theorems |
|---|---|---|
| `Σ_{m₁m₂} (½ ½ J; m₁ m₂ 0)(½ ½ J'; m₁ m₂ 0)` for `(J, J') = (1,1), (1,0), (0,0)` | `1/3, 0, 1` | `threeJ_orth_direct`, `threeJ_orth_predicts` |
| `Σ_x (2x+1)(2q+1) {1 ½ x; 1 ½ q}{1 ½ x; 1 ½ r}` for `q, r ∈ {½, 3/2}` | `δ_{qr}` | `sixJ_orth_direct`, `sixJ_orth_predicts` |

Each sum is evaluated twice: from explicit symbols (`…_direct`; the 3j values
`(½ ½ 1; ±½ ∓½ 0) = 1/√6`, `(½ ½ 0; ±½ ∓½ 0) = ±1/√2` and the 6j values `1/6`, `-1/3`, `-1/3`,
`-1/12`, all from Physlib's definitions) and from the general theorem (`…_predicts`, which also
shows that its admissibility conditions can hold). `scripts/recoupling/intertwiner_check.py`
finds the same values with SymPy.

Wrong inputs: with the absolute values of the 3j symbols (no Condon–Shortley signs) the singlet and
the triplet are not orthogonal (`threeJ_orth_unsigned_fails`); without the weight `2x + 1` the 6j
sum at `q = r = ½` is `5/18`, not `1` (`sixJ_orth_unweighted_fails`).

## References

- A. R. Edmonds, *Angular Momentum in Quantum Mechanics* (Princeton, 1957), §3.7: the 3j symbols,
  their explicit values and their orthogonality, eqs. (3.7.7), (3.7.8); §6.2, eq. (6.2.9): the
  orthogonality of the 6j symbols.
- A. P. Yutsis, I. B. Levinson, V. V. Vanagas, *Mathematical Apparatus of the Theory of Angular
  Momentum* (Israel Program for Scientific Translations, 1962): the 15j symbols of the first kind.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon Lightlike.Recoupling

namespace Lightlike.Recoupling.Tests

/-- `(0 ½ ½; 0 ½ -½) = 1/√2`. -/
lemma threeJ_0hh : threeJ 0 1 1 0 1 (-1) = 1 / Real.sqrt 2 := by
  rw [threeJ_zero_left]
  norm_num

/-- `(½ ½ 0; ½ -½ 0) = 1/√2`, by a cyclic permutation of `threeJ_0hh`. -/
lemma threeJ_hh0 : threeJ 1 1 0 1 (-1) 0 = 1 / Real.sqrt 2 := by
  rw [threeJ_cycle 0 1 1 0 1 (-1), threeJ_0hh]

/-- **Value check.** The singlet–singlet intertwiner of four spins 1/2, evaluated from the
definition: `ι^{(0)}_{½,-½,½,-½} = (½ ½ 0; ½ -½ 0)(0 ½ ½; 0 ½ -½) = 1/2`. -/
theorem fourJ_hhhh_zero : fourJ 1 1 1 1 0 1 (-1) 1 (-1) = 1 / 2 := by
  unfold fourJ
  simp only [CharP.cast_eq_zero, zero_add, Real.sqrt_one, one_mul, neg_zero, Icc_self,
    sum_singleton, sub_zero, EuclideanDomain.zero_div, zpow_zero, threeJ_hh0, threeJ_0hh]
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- **Value check.** `⟨ι^{(12)0} | ι^{(13)0}⟩ = 1/2` for four spins 1/2, from
`{½ ½ 0; ½ ½ 0} = -1/2` (`Lightlike.SixJAudit.sixJ_hh0_hh0`). -/
theorem fourRecoupling_hhhh_00 : fourRecoupling 1 1 1 1 0 0 = 1 / 2 := by
  unfold fourRecoupling
  rw [Lightlike.SixJAudit.sixJ_hh0_hh0]
  norm_num

/-- **Value check.** `⟨ι^{(12)0} | ι^{(13)1}⟩ = √3/2` for four spins 1/2, from
`{½ ½ 0; ½ ½ 1} = 1/2` (`Lightlike.SixJAudit.sixJ_hh0_hh1`). -/
theorem fourRecoupling_hhhh_02 : fourRecoupling 1 1 1 1 0 2 = Real.sqrt 3 / 2 := by
  unfold fourRecoupling
  rw [Lightlike.SixJAudit.sixJ_hh0_hh1]
  norm_num
  ring

/-- The odd virtual spin `l = ½` does not couple `(½ ½)`: the coefficient vanishes. -/
lemma fourRecoupling_hhhh_01 : fourRecoupling 1 1 1 1 0 1 = 0 := by
  unfold fourRecoupling
  have h : sixJSym 1 1 0 1 1 1 = 0 := by
    by_contra h
    obtain ⟨-, t, -, -⟩ := tri_of_sixJSym_ne_zero h
    unfold Tri at t
    omega
  rw [h, mul_zero]

/-- **Consistency check.** The row `k = 0` of the recoupling matrix, from the explicit values,
has norm `1/4 + 0 + 3/4 = 1`, as `sum_fourRecoupling_mul` requires. -/
theorem fourRecoupling_hhhh_row :
    ∑ l ∈ range (1 + 1 + 1), fourRecoupling 1 1 1 1 0 l * fourRecoupling 1 1 1 1 0 l = 1 := by
  rw [show range (1 + 1 + 1) = {0, 1, 2} by decide, sum_insert (by decide),
    sum_insert (by decide), sum_singleton, fourRecoupling_hhhh_00, fourRecoupling_hhhh_01,
    fourRecoupling_hhhh_02]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination h3 / 4

/-- **Value check.** The two singlet pairings `(12)(34)` and `(13)(24)` of four spins 1/2
overlap with `1/2`, computed through `sum_fourJ_mul_fourJ_swap`. -/
theorem overlap_singlet_pairings :
    ∑ m₁ ∈ Icc (-(1 : ℤ)) 1, ∑ m₂ ∈ Icc (-(1 : ℤ)) 1, ∑ m₃ ∈ Icc (-(1 : ℤ)) 1,
      ∑ m₄ ∈ Icc (-(1 : ℤ)) 1, fourJ 1 1 1 1 0 m₁ m₂ m₃ m₄ * fourJ 1 1 1 1 0 m₁ m₃ m₂ m₄ =
      1 / 2 := by
  have h := sum_fourJ_mul_fourJ_swap 1 1 1 1 0 0
  push_cast at h
  rw [h, ← fourRecoupling_hhhh_00, fourRecoupling]
  norm_num

/-- The bare 4jm symbol, `ι^{(k)} / √(2k + 1)`: the intertwiner without its normalisation. Used
only as a deliberately wrong input. -/
noncomputable def fourJUnnormalised (j₁ j₂ j₃ j₄ k : ℕ) (m₁ m₂ m₃ m₄ : ℤ) : ℝ :=
  fourJ j₁ j₂ j₃ j₄ k m₁ m₂ m₃ m₄ / Real.sqrt ((k : ℝ) + 1)

/-- **Wrong input.** Without the factor `√(2k + 1)` the virtual-spin-1 intertwiner of four
spins 1/2 has norm squared `1/3`, not `1`. -/
theorem fourJ_unnormalised_fails :
    ∑ m₁ ∈ Icc (-(1 : ℤ)) 1, ∑ m₂ ∈ Icc (-(1 : ℤ)) 1, ∑ m₃ ∈ Icc (-(1 : ℤ)) 1,
      ∑ m₄ ∈ Icc (-(1 : ℤ)) 1,
        fourJUnnormalised 1 1 1 1 2 m₁ m₂ m₃ m₄ * fourJUnnormalised 1 1 1 1 2 m₁ m₂ m₃ m₄ =
      1 / 3 := by
  have h := sum_fourJ_mul_fourJ 1 1 1 1 2 2
  push_cast at h
  rw [ite_eq_left ⟨by trivial, by unfold Tri; omega, by unfold Tri; omega⟩] at h
  have e : ∀ m₁ m₂ m₃ m₄ : ℤ,
      fourJUnnormalised 1 1 1 1 2 m₁ m₂ m₃ m₄ * fourJUnnormalised 1 1 1 1 2 m₁ m₂ m₃ m₄ =
        (1 / 3) * (fourJ 1 1 1 1 2 m₁ m₂ m₃ m₄ * fourJ 1 1 1 1 2 m₁ m₂ m₃ m₄) := by
    intro m₁ m₂ m₃ m₄
    unfold fourJUnnormalised
    rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity)]
    norm_num
    ring
  simp only [e, ← mul_sum, h]
  norm_num

/-- **Wrong input.** Dropping the phase `(-1)^(j₂+j₃+k+l)` from the change-of-channel formula
gives `-1/2` for the two singlet pairings of four spins 1/2, not the true overlap `1/2`. -/
theorem fourRecoupling_without_phase_fails :
    Real.sqrt (((0 : ℕ) + 1) * ((0 : ℕ) + 1)) * sixJSym 1 1 0 1 1 0 ≠
      fourRecoupling 1 1 1 1 0 0 := by
  rw [fourRecoupling_hhhh_00, Lightlike.SixJAudit.sixJ_hh0_hh0]
  norm_num

/-- **Wrong input.** A virtual spin outside the triangle range (`k = 2 > ½ + ½`, doubled `4`)
gives the zero tensor: its norm squared is `0`. -/
theorem fourJ_inadmissible_zero :
    ∑ m₁ ∈ Icc (-(1 : ℤ)) 1, ∑ m₂ ∈ Icc (-(1 : ℤ)) 1, ∑ m₃ ∈ Icc (-(1 : ℤ)) 1,
      ∑ m₄ ∈ Icc (-(1 : ℤ)) 1, fourJ 1 1 1 1 4 m₁ m₂ m₃ m₄ * fourJ 1 1 1 1 4 m₁ m₂ m₃ m₄ = 0 := by
  have h := sum_fourJ_mul_fourJ 1 1 1 1 4 4
  push_cast at h
  rw [h, ite_eq_right (fun h => by obtain ⟨-, t, -⟩ := h; unfold Tri at t; omega)]

/-! ## The 15j symbol (`FifteenJ.lean`) -/

/-- `{0 ½ ½; ½ 0 0} = -1/√2` (closed form with a zero spin). -/
lemma sixJ_0hh_h00 : sixJSym 0 1 1 1 0 0 = -1 / Real.sqrt 2 := by
  rw [sixJSym_zero_left, ite_eq_left ⟨rfl, rfl, by decide⟩]
  norm_num

/-- **Value check.** `{15j}` with rows `a = (0,0,0,0,0)`, `b = (½,½,½,½,½)`,
`c = (0,0,0,0,½)` is `1/4` (SymPy: `1/4`), through the zero-spin reduction. -/
theorem fifteenJ_value : fifteenJ 0 (fun _ => 1) ![0, 0, 0, 0, 1] = 1 / 4 := by
  rw [fifteenJ_of_a_zero _ _ _ rfl,
    ite_eq_left ⟨rfl, rfl, by decide, by decide⟩]
  simp only [Pi.zero_apply, Matrix.cons_val, Fin.sum_univ_five, sixJ_0hh_h00]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  norm_num
  have h4 : (-1 / Real.sqrt 2 : ℝ) * (-1 / Real.sqrt 2) = 1 / 2 := by
    rw [div_mul_div_comm, h2]; norm_num
  calc -1 / Real.sqrt 2 * (-1 / Real.sqrt 2 * (-1 / Real.sqrt 2) * (-1 / Real.sqrt 2))
      = ((-1 / Real.sqrt 2) * (-1 / Real.sqrt 2)) * ((-1 / Real.sqrt 2) * (-1 / Real.sqrt 2)) := by
        ring
    _ = 1 / 4 := by rw [h4]; norm_num

/-- The 15j sum with the closure **not** twisted, `(a₅, b₅) = (a₀, b₀)`: a deliberately wrong
model of the 4-simplex graph (a prism-like ladder instead of the Möbius ladder). -/
noncomputable def fifteenJUntwisted (a b c : Fin 5 → ℕ) : ℝ :=
  (-1) ^ ((∑ t, (a t + b t + c t)) / 2) *
    ∑ x ∈ range (a 0 + b 0 + 1), ((x : ℝ) + 1) *
      (sixJSym (a 0) (b 0) x (b 1) (a 1) (c 0) * sixJSym (a 1) (b 1) x (b 2) (a 2) (c 1) *
        sixJSym (a 2) (b 2) x (b 3) (a 3) (c 2) * sixJSym (a 3) (b 3) x (b 4) (a 4) (c 3) *
          sixJSym (a 4) (b 4) x (b 0) (a 0) (c 4))

/-- **Wrong input.** With the untwisted closure the value at the arguments of `fifteenJ_value`
is `0`, not `1/4`. -/
theorem fifteenJ_untwisted_fails :
    fifteenJUntwisted 0 (fun _ => 1) ![0, 0, 0, 0, 1] = 0 ∧
      fifteenJUntwisted 0 (fun _ => 1) ![0, 0, 0, 0, 1] ≠ fifteenJ 0 (fun _ => 1) ![0, 0, 0, 0, 1] := by
  have h0 : fifteenJUntwisted 0 (fun _ => 1) ![0, 0, 0, 0, 1] = 0 := by
    unfold fifteenJUntwisted
    apply mul_eq_zero_of_right
    refine sum_eq_zero fun x _ => ?_
    simp only [Pi.zero_apply, Matrix.cons_val]
    rw [show sixJSym 0 1 x 1 0 1 = 0 by
      rw [sixJSym_zero_left, ite_eq_right (fun h => by omega)]]
    ring
  refine ⟨h0, ?_⟩
  rw [h0, fifteenJ_value]
  norm_num

/-- `(0 ½ ½; 0 m m')` for all projections: `1/√2` at `(½, -½)`, `-1/√2` at `(-½, ½)`, else `0`. -/
lemma threeJ_0hh_table (m m' : ℤ) :
    threeJ 0 1 1 0 m m' =
      if m = 1 ∧ m' = -1 then 1 / Real.sqrt 2 else if m = -1 ∧ m' = 1 then -1 / Real.sqrt 2
      else 0 := by
  rw [threeJ_zero_left]
  by_cases h1 : m = 1 ∧ m' = -1
  · obtain ⟨rfl, rfl⟩ := h1
    norm_num
  by_cases h2 : m = -1 ∧ m' = 1
  · obtain ⟨rfl, rfl⟩ := h2
    norm_num
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (fun h => by omega)]

/-- The intertwiner `ι^{(0)}` of spins `(0, 0, ½, ½)` is the 3j symbol `(0 ½ ½; 0 m m')`. -/
lemma fourJ_00hh (m m' : ℤ) : fourJ 0 0 1 1 0 0 0 m m' = threeJ 0 1 1 0 m m' := by
  unfold fourJ
  simp [threeJ_zero_zero]

/-- The intertwiner `ι^{(0)}` of spins `(½, ½, 0, 0)` is the 3j symbol `(0 ½ ½; 0 m m')`. -/
lemma fourJ_hh00 (m m' : ℤ) : fourJ 1 1 0 0 0 m m' 0 0 = threeJ 0 1 1 0 m m' := by
  unfold fourJ
  simp [threeJ_zero_zero, threeJ_cycle 0 1 1 0 m m']

/-- The intertwiner `ι^{(½)}` of spins `(0, ½, ½, 0)`: `-1/√2` at `(½, -½)`, `1/√2` at
`(-½, ½)`, else `0`. -/
lemma fourJ_0hh0 (m m' : ℤ) :
    fourJ 0 1 1 0 1 0 m m' 0 =
      if m = 1 ∧ m' = -1 then -1 / Real.sqrt 2 else if m = -1 ∧ m' = 1 then 1 / Real.sqrt 2
      else 0 := by
  unfold fourJ
  have hI : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  have hc : ∀ μ : ℤ, threeJ 1 1 0 (-μ) m' 0 = threeJ 0 1 1 0 (-μ) m' :=
    fun μ => threeJ_cycle 0 1 1 0 (-μ) m'
  simp only [hI, hc, threeJ_0hh_table]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  by_cases h1 : m = 1 ∧ m' = -1
  · obtain ⟨rfl, rfl⟩ := h1
    norm_num
    field_simp
  by_cases h3 : m = -1 ∧ m' = 1
  · obtain ⟨rfl, rfl⟩ := h3
    norm_num
    field_simp
  rw [ite_eq_right h1, ite_eq_right h3]
  simp only [sum_insert (show (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) by decide),
    sum_insert (show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide), sum_singleton]
  split_ifs <;> first | omega | simp_all

/-- **Value check (4-simplex).** Spins `½` on the four edges of the cycle `0-3-1-4-0`, spins `0`
elsewhere, intertwiners `i₁ = i₃ = ½`, `i₀ = i₂ = i₄ = 0`: the contraction of the five
intertwiners is `1/2` (SymPy: `1/2`). -/
theorem fifteenJSimplex_cycle : fifteenJSimplex 0 0 1 1 0 1 1 0 0 0 0 1 0 1 0 = 1 / 2 := by
  unfold fifteenJSimplex
  simp only [Nat.cast_zero, neg_zero, Icc_self, sum_singleton, fourJ_zero, neg_zero]
  simp only [fourJ_00hh, fourJ_hh00, fourJ_0hh0, threeJ_0hh_table, edgeSign]
  have hI : Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {-1, 0, 1} := by decide
  simp only [hI, sum_insert (show (-1 : ℤ) ∉ ({0, 1} : Finset ℤ) by decide),
    sum_insert (show (0 : ℤ) ∉ ({1} : Finset ℤ) by decide), sum_singleton]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  norm_num
  field_simp
  nlinarith [h2]

/-- **Consistency check (4-simplex ↔ 15j).** At the cycle configuration of
`fifteenJSimplex_cycle` the contraction equals `Π_a √(2i_a + 1)` times the 15j symbol of the
first kind with rows `a = (i₀, j₀₂, i₂, j₂₄, i₄)`, `b = (j₁₄, i₁, j₁₃, i₃, j₀₃)`,
`c = (j₀₁, j₁₂, j₂₃, j₃₄, j₀₄)`, as the general (numerical) identity of `FifteenJ.lean` says. -/
theorem fifteenJSimplex_cycle_eq :
    fifteenJSimplex 0 0 1 1 0 1 1 0 0 0 0 1 0 1 0 =
      Real.sqrt ((0 + 1) * (1 + 1) * (0 + 1) * (1 + 1) * (0 + 1)) *
        fifteenJ ![0, 0, 0, 0, 0] ![1, 1, 1, 1, 1] ![0, 0, 0, 0, 1] := by
  have e1 : (![0, 0, 0, 0, 0] : Fin 5 → ℕ) = 0 := by decide
  have e2 : (![1, 1, 1, 1, 1] : Fin 5 → ℕ) = fun _ => 1 := by decide
  rw [fifteenJSimplex_cycle, e1, e2, fifteenJ_value]
  rw [show ((0 : ℝ) + 1) * (1 + 1) * (0 + 1) * (1 + 1) * (0 + 1) = 2 * 2 by norm_num,
    Real.sqrt_mul_self (by norm_num)]
  norm_num

/-! ## Orthogonality of the 15j symbols (`Orthogonality.lean`) -/

/-- **Non-vacuity of the orthogonality relation.** For `a₀ = 0`, `b = b' = (½,½,½,½,½)`,
`c = (0,0,0,0,½)` all vertices are admissible, so `sum_fifteenJ_mul_fifteenJ` predicts
`1/(2·2·2·2) = 1/16`. -/
theorem fifteenJ_orth_predicts :
    (∑ x1 ∈ range (0 + 0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + 0 + 1), ((x2 : ℝ) + 1) *
      ∑ x3 ∈ range (x2 + 0 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + 0 + 1), ((x4 : ℝ) + 1) *
        (fifteenJ ![0, x1, x2, x3, x4] ![1, 1, 1, 1, 1] ![0, 0, 0, 0, 1] *
          fifteenJ ![0, x1, x2, x3, x4] ![1, 1, 1, 1, 1] ![0, 0, 0, 0, 1])) = 1 / 16 := by
  rw [sum_fifteenJ_mul_fifteenJ 0 1 1 1 1 1 1 1 1 1 0 0 0 0 1, ite_eq_left ⟨⟨rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide,
    by decide, by decide⟩]
  norm_num

/-- **Value check (orthogonality).** The same sum evaluated directly: all spin ranges collapse to
`a₁ = … = a₄ = 0`, and the single term is `{15j}² = (1/4)² = 1/16` by `fifteenJ_value`, as the
orthogonality relation predicts (`fifteenJ_orth_predicts`). -/
theorem fifteenJ_orth_direct :
    (∑ x1 ∈ range (0 + 0 + 1), ((x1 : ℝ) + 1) * ∑ x2 ∈ range (x1 + 0 + 1), ((x2 : ℝ) + 1) *
      ∑ x3 ∈ range (x2 + 0 + 1), ((x3 : ℝ) + 1) * ∑ x4 ∈ range (x3 + 0 + 1), ((x4 : ℝ) + 1) *
        (fifteenJ ![0, x1, x2, x3, x4] ![1, 1, 1, 1, 1] ![0, 0, 0, 0, 1] *
          fifteenJ ![0, x1, x2, x3, x4] ![1, 1, 1, 1, 1] ![0, 0, 0, 0, 1])) = (1 / 4) ^ 2 := by
  have e1 : (![0, 0, 0, 0, 0] : Fin 5 → ℕ) = 0 := by decide
  have e2 : (![1, 1, 1, 1, 1] : Fin 5 → ℕ) = fun _ => 1 := by decide
  simp only [add_zero, zero_add, range_one, sum_singleton, CharP.cast_eq_zero, one_mul]
  rw [e1, e2, fifteenJ_value]
  norm_num

/-- **Wrong input (orthogonality).** With the untwisted closure the single term of the same sum
is `0² = 0`, not the `1/16` that orthogonality requires (`fifteenJ_untwisted_fails`). -/
theorem fifteenJ_untwisted_orth_fails :
    fifteenJUntwisted 0 (fun _ => 1) ![0, 0, 0, 0, 1] *
      fifteenJUntwisted 0 (fun _ => 1) ![0, 0, 0, 0, 1] ≠ 1 / 16 := by
  rw [fifteenJ_untwisted_fails.1]
  norm_num

/-! ### A 15j value with all fifteen spins nonzero -/

/-- `√9 = 3`. -/
lemma sqrt_nine : √(9 : ℝ) = 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Evaluate a 6j symbol with spins up to `3/2` from Physlib's definition (the method of
`Lightlike/Tests/SixJ.lean`: the sum over three free projections, then `surd_finish`). -/
local macro "sixj_value" : tactic => `(tactic| (
  rw [Lightlike.SixJAudit.sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Lightlike.SixJAudit.mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    Lightlike.SixJAudit.sixSum_eq_sum, Lightlike.SixJAudit.sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [Lightlike.SixJAudit.sqrt_four, sqrt_nine]
  surd_finish))

/-- `{1 ½ ½; 1 ½ ½} = 1/6` (doubled `2 1 1 2 1 1`; SymPy: `1/6`). -/
lemma sixJ_1hh_1hh : sixJSym 2 1 1 2 1 1 = 1 / 6 := by sixj_value

/-- `{½ 1 ½; ½ 1 ½} = 1/6` (doubled `1 2 1 1 2 1`; SymPy: `1/6`). -/
lemma sixJ_h1h_h1h : sixJSym 1 2 1 1 2 1 = 1 / 6 := by sixj_value

/-- `{1 ½ 3/2; 1 ½ ½} = -1/3` (doubled `2 1 3 2 1 1`; SymPy: `-1/3`). -/
lemma sixJ_1h3_1hh : sixJSym 2 1 3 2 1 1 = -1 / 3 := by sixj_value

/-- `{½ 1 3/2; ½ 1 ½} = -1/3` (doubled `1 2 3 1 2 1`; SymPy: `-1/3`). -/
lemma sixJ_h13_h1h : sixJSym 1 2 3 1 2 1 = -1 / 3 := by sixj_value

/-- **Value check with all fifteen spins nonzero.** `{15j}` with rows `a = (1,½,1,½,1)`,
`b = (½,1,½,1,½)`, `c = (½,½,½,½,½)` (doubled `2 1 2 1 2`, `1 2 1 2 1`, `1 1 1 1 1`) is `-7/432`
(SymPy: `-7/432`). The sum over `x` has two nonzero terms, `2 · (1/6)⁵` at `x = ½` and
`4 · (-1/3)⁵` at `x = 3/2`; at `x = 0, 1` the triad `(a₀ b₀ x)` has odd perimeter. -/
theorem fifteenJ_all_nonzero :
    fifteenJ ![2, 1, 2, 1, 2] ![1, 2, 1, 2, 1] ![1, 1, 1, 1, 1] = -7 / 432 := by
  unfold fifteenJ
  simp only [Fin.sum_univ_five, Matrix.cons_val, sum_range_succ, sum_range_zero]
  rw [Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (j₁ := 2) (j₂ := 1) (j₃ := 0) (by norm_num),
    Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (j₁ := 2) (j₂ := 1) (j₃ := 2) (by norm_num)]
  norm_num [sixJ_1hh_1hh, sixJ_h1h_h1h, sixJ_1h3_1hh, sixJ_h13_h1h]

/-- **Value check of the 4-simplex contraction with all spins nonzero.** All ten triangle spins
`½` and all five virtual spins `1` give `-7√3/48`, which is `Π_a √(2i_a + 1) = 9√3` times
`fifteenJ_all_nonzero` (`fifteenJSimplex_eq`). `scripts/recoupling/fifteenj_check.py` finds the
same value from a direct contraction of the ten 3j symbols with SymPy's `wigner_3j`. -/
theorem fifteenJSimplex_all_nonzero :
    fifteenJSimplex 1 1 1 1 1 1 1 1 1 1 2 2 2 2 2 = -7 * √3 / 48 := by
  rw [fifteenJSimplex_eq]
  simp only [Nat.cast_ofNat]
  rw [fifteenJ_all_nonzero,
    show ((2 : ℝ) + 1) * (2 + 1) * (2 + 1) * (2 + 1) * (2 + 1) = 9 ^ 2 * 3 by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  ring

/-- **Wrong input.** With the untwisted closure the sum at the spins of `fifteenJ_all_nonzero` is
`0`, not `-7/432`: the last 6j symbol becomes `{1 ½ x; ½ 1 ½} = {1 1 ½; ½ ½ x}`, whose first triad
has odd perimeter. -/
theorem fifteenJ_all_nonzero_untwisted_fails :
    fifteenJUntwisted ![2, 1, 2, 1, 2] ![1, 2, 1, 2, 1] ![1, 1, 1, 1, 1] = 0 ∧
      fifteenJUntwisted ![2, 1, 2, 1, 2] ![1, 2, 1, 2, 1] ![1, 1, 1, 1, 1] ≠
        fifteenJ ![2, 1, 2, 1, 2] ![1, 2, 1, 2, 1] ![1, 1, 1, 1, 1] := by
  have h0 : fifteenJUntwisted ![2, 1, 2, 1, 2] ![1, 2, 1, 2, 1] ![1, 1, 1, 1, 1] = 0 := by
    unfold fifteenJUntwisted
    apply mul_eq_zero_of_right
    refine sum_eq_zero fun x _ => ?_
    simp only [Matrix.cons_val]
    rw [sixJSym_flip₂₃ 2 1 x 1 2 1,
      Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (j₁ := 2) (j₂ := 2) (j₃ := 1) (by norm_num)]
    ring
  refine ⟨h0, ?_⟩
  rw [h0, fifteenJ_all_nonzero]
  norm_num

/-! ### Orthogonality of the 3j and 6j symbols at fixed spins -/

/-- `(½ ½ 1; ½ -½ 0) = 1/√6`, evaluated from Physlib's definition (Racah's formula). -/
lemma threeJ_hh1 : threeJ 1 1 2 1 (-1) 0 = 1 / √6 := by
  norm_num [threeJ, Adm3, threeJR, reggeJ, Lightlike.SixJAudit.sixSum_eq_sum, Lightlike.SixJAudit.sum_Icc_int,
    sixTerm, invFact, Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]

/-- `(½ ½ 1; -½ ½ 0) = 1/√6`: exchanging the two columns of `threeJ_hh1` gives the sign
`(-1)^(½+½+1) = 1`. -/
lemma threeJ_hh1_swap : threeJ 1 1 2 (-1) 1 0 = 1 / √6 := by
  rw [threeJ_swap 1 1 2 1 (-1) 0, threeJ_hh1]
  norm_num

/-- `(½ ½ 0; -½ ½ 0) = -1/√2`: exchanging the two columns of `threeJ_hh0` gives the sign
`(-1)^(½+½+0) = -1`. -/
lemma threeJ_hh0_swap : threeJ 1 1 0 (-1) 1 0 = -1 / √2 := by
  rw [threeJ_swap 1 1 0 1 (-1) 0, threeJ_hh0]
  norm_num [neg_div]

/-- For two spins `½` and total projection `0`, only `(m₁, m₂) = (½, -½)` and `(-½, ½)`
contribute to the sum of `sum_threeJ_mul_threeJ`: the other seven pairs of `Icc (-1) 1` have
`m₁ + m₂ ≠ 0` or a projection of the wrong parity. -/
lemma sum_threeJ_hh (J J' : ℕ) :
    ∑ m₁ ∈ Icc (-1 : ℤ) 1, ∑ m₂ ∈ Icc (-1 : ℤ) 1, threeJ 1 1 J m₁ m₂ 0 * threeJ 1 1 J' m₁ m₂ 0 =
      threeJ 1 1 J 1 (-1) 0 * threeJ 1 1 J' 1 (-1) 0 +
        threeJ 1 1 J (-1) 1 0 * threeJ 1 1 J' (-1) 1 0 := by
  have hI : Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
  have hz : ∀ K m₁ m₂, ¬ (m₁ = 1 ∧ m₂ = -1) → ¬ (m₁ = -1 ∧ m₂ = 1) →
      threeJ 1 1 K m₁ m₂ 0 = 0 := by
    intro K m₁ m₂ h1 h2
    exact threeJ_of_not fun h => by unfold Adm3 at h; omega
  rw [hI]
  simp only [sum_insert (by decide : (-1 : ℤ) ∉ ({0, 1} : Finset ℤ)),
    sum_insert (by decide : (0 : ℤ) ∉ ({1} : Finset ℤ)), sum_singleton]
  rw [hz J (-1) (-1) (by omega) (by omega), hz J (-1) 0 (by omega) (by omega),
    hz J 0 (-1) (by omega) (by omega), hz J 0 0 (by omega) (by omega),
    hz J 0 1 (by omega) (by omega), hz J 1 0 (by omega) (by omega),
    hz J 1 1 (by omega) (by omega)]
  ring

/-- **Value check (3j orthogonality).** For `j₁ = j₂ = ½` and `μ = μ' = 0`, the sums of
`sum_threeJ_mul_threeJ` evaluated from the 3j values: `2 · (1/√6)² = 1/3` for `J = J' = 1`,
`(1/√6)(1/√2) + (1/√6)(-1/√2) = 0` for `J = 1, J' = 0`, and `2 · (1/√2)² = 1` for `J = J' = 0`. -/
theorem threeJ_orth_direct :
    ∑ m₁ ∈ Icc (-1 : ℤ) 1, ∑ m₂ ∈ Icc (-1 : ℤ) 1, threeJ 1 1 2 m₁ m₂ 0 * threeJ 1 1 2 m₁ m₂ 0 =
        1 / 3 ∧
      ∑ m₁ ∈ Icc (-1 : ℤ) 1, ∑ m₂ ∈ Icc (-1 : ℤ) 1, threeJ 1 1 2 m₁ m₂ 0 * threeJ 1 1 0 m₁ m₂ 0 =
        0 ∧
      ∑ m₁ ∈ Icc (-1 : ℤ) 1, ∑ m₂ ∈ Icc (-1 : ℤ) 1, threeJ 1 1 0 m₁ m₂ 0 * threeJ 1 1 0 m₁ m₂ 0 =
        1 := by
  simp only [sum_threeJ_hh, threeJ_hh1, threeJ_hh1_swap, threeJ_hh0, threeJ_hh0_swap]
  refine ⟨?_, ?_, ?_⟩
  · rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
  · ring
  · rw [div_mul_div_comm, div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num

/-- **Non-vacuity of the 3j orthogonality relation.** The same three sums as predicted by
`sum_threeJ_mul_threeJ`: `1/(2J + 1)` for `J = J'` admissible (`1/3` and `1`), `0` for `J ≠ J'`.
They agree with the direct evaluation `threeJ_orth_direct`. -/
theorem threeJ_orth_predicts :
    ∑ m₁ ∈ Icc (-1 : ℤ) 1, ∑ m₂ ∈ Icc (-1 : ℤ) 1, threeJ 1 1 2 m₁ m₂ 0 * threeJ 1 1 2 m₁ m₂ 0 =
        1 / 3 ∧
      ∑ m₁ ∈ Icc (-1 : ℤ) 1, ∑ m₂ ∈ Icc (-1 : ℤ) 1, threeJ 1 1 2 m₁ m₂ 0 * threeJ 1 1 0 m₁ m₂ 0 =
        0 ∧
      ∑ m₁ ∈ Icc (-1 : ℤ) 1, ∑ m₂ ∈ Icc (-1 : ℤ) 1, threeJ 1 1 0 m₁ m₂ 0 * threeJ 1 1 0 m₁ m₂ 0 =
        1 := by
  have h22 := sum_threeJ_mul_threeJ 1 1 2 2 0 0
  have h20 := sum_threeJ_mul_threeJ 1 1 2 0 0 0
  have h00 := sum_threeJ_mul_threeJ 1 1 0 0 0 0
  simp only [Nat.cast_one] at h22 h20 h00
  refine ⟨?_, ?_, ?_⟩
  · rw [h22, ite_eq_left (by decide)]
    norm_num
  · rw [h20, ite_eq_right fun h => absurd h.1 (by decide)]
  · rw [h00, ite_eq_left (by decide)]
    norm_num

/-- **Wrong model (3j orthogonality).** Without the Condon–Shortley signs, i.e. with the absolute
values of the 3j symbols, the `J = 1, J' = 0` sum is `2 · (1/√6)(1/√2) ≠ 0`: the singlet and the
triplet would not be orthogonal. -/
theorem threeJ_orth_unsigned_fails :
    |threeJ 1 1 2 1 (-1) 0| * |threeJ 1 1 0 1 (-1) 0| +
      |threeJ 1 1 2 (-1) 1 0| * |threeJ 1 1 0 (-1) 1 0| ≠ 0 := by
  rw [threeJ_hh1, threeJ_hh1_swap, threeJ_hh0, threeJ_hh0_swap, neg_div, abs_neg]
  positivity

/-- `{1 ½ ½; 1 ½ 3/2} = -1/3`, evaluated from Physlib's definition. -/
lemma sixJ_1hh_1h3 : sixJSym 2 1 1 2 1 3 = -1 / 3 := by sixj_value

/-- `{1 ½ 3/2; 1 ½ 3/2} = -1/12`, evaluated from Physlib's definition. -/
lemma sixJ_1h3_1h3 : sixJSym 2 1 3 2 1 3 = -1 / 12 := by sixj_value

/-- **Value check (6j orthogonality).** The sum of `sixJSym_orth_all` at `(B, A, E, F) =
(1, ½, 1, ½)` with `q, r ∈ {½, 3/2}`, evaluated from the 6j values: the terms `x = 0, 1` vanish
(odd perimeter of the first triad), and `x = ½, 3/2` give `2 · 2 (1/36 + 4/9) = 1`,
`2 · 2 · (1/6)(-1/3) + 4 · 2 · (-1/3)(-1/12) = 0` and `4 (2/9 + 4/144) = 1`. -/
theorem sixJ_orth_direct (q r : ℕ) (hq : q = 1 ∨ q = 3) (hr : r = 1 ∨ r = 3) :
    ∑ x ∈ range (2 + 1 + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym 2 1 x 2 1 q * sixJSym 2 1 x 2 1 r) = if q = r then 1 else 0 := by
  have h0 : ∀ j₄ j₅ j₆, sixJSym 2 1 0 j₄ j₅ j₆ = 0 := fun _ _ _ =>
    Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (by norm_num)
  have h2 : ∀ j₄ j₅ j₆, sixJSym 2 1 2 j₄ j₅ j₆ = 0 := fun _ _ _ =>
    Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (by norm_num)
  simp only [sum_range_succ, sum_range_zero, zero_add, h0, h2]
  rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;>
    norm_num [sixJ_1hh_1hh, sixJ_1h3_1hh, sixJ_1hh_1h3, sixJ_1h3_1h3]

/-- **Non-vacuity of the 6j orthogonality relation.** At the spins of `sixJ_orth_direct` the
triads `(½ 1 q)` and `(1 q ½)` are admissible for `q ∈ {½, 3/2}`, so `sixJSym_orth_all` predicts
`δ_{qr}`, as found by the direct evaluation. -/
theorem sixJ_orth_predicts (q r : ℕ) (hq : q = 1 ∨ q = 3) (hr : r = 1 ∨ r = 3) :
    ∑ x ∈ range (2 + 1 + 1), ((x : ℝ) + 1) * ((q : ℝ) + 1) *
        (sixJSym 2 1 x 2 1 q * sixJSym 2 1 x 2 1 r) = if q = r then 1 else 0 := by
  rw [sixJSym_orth_all]
  rcases hq with rfl | rfl <;> rcases hr with rfl | rfl <;> norm_num [Tri]

/-- **Wrong input (6j orthogonality).** Without the weight `2x + 1` the `q = r = ½` sum is
`2 (1/36 + 1/9) = 5/18`, not `1`. -/
theorem sixJ_orth_unweighted_fails :
    ∑ x ∈ range (2 + 1 + 1), (2 : ℝ) * (sixJSym 2 1 x 2 1 1 * sixJSym 2 1 x 2 1 1) = 5 / 18 ∧
      ∑ x ∈ range (2 + 1 + 1), (2 : ℝ) * (sixJSym 2 1 x 2 1 1 * sixJSym 2 1 x 2 1 1) ≠ 1 := by
  have h0 : ∀ j₄ j₅ j₆, sixJSym 2 1 0 j₄ j₅ j₆ = 0 := fun _ _ _ =>
    Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (by norm_num)
  have h2 : ∀ j₄ j₅ j₆, sixJSym 2 1 2 j₄ j₅ j₆ = 0 := fun _ _ _ =>
    Lightlike.SixJAudit.sixJSym_eq_zero_of_parity (by norm_num)
  have h : ∑ x ∈ range (2 + 1 + 1), (2 : ℝ) * (sixJSym 2 1 x 2 1 1 * sixJSym 2 1 x 2 1 1) =
      5 / 18 := by
    simp only [sum_range_succ, sum_range_zero, zero_add, h0, h2]
    norm_num [sixJ_1hh_1hh, sixJ_1h3_1hh]
  exact ⟨h, by rw [h]; norm_num⟩

end Lightlike.Recoupling.Tests
