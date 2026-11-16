import Lightlike.TuraevViro.LevelOne

/-!
# Trust checks for the Turaev–Viro model

Checks of `TuraevViro/` against values computed by hand and by an independent script, each with a
deliberately wrong model that gives a different answer.

## Main results

* `tv4_orth_instance`, `tv4_be_instance`: orthogonality and Biedenharn–Elliott at `r = 4`, on
  explicit spins.
* `tv4_classical_dims_fail`: the same checks with the classical dimensions `x + 1` fail.
* `turaevViro3_sphere`: the `r = 3` state sum of `∂Δ⁴` is `1/2`.
* `classical3_sphere_fails`: with the integer dimensions `J + 1` the value is wrong.

## Implementation notes

### Level `r = 4`

`tvModel r` uses the quantum 6j symbols `qSixJ r` and the quantum dimensions `[J + 1]` at
`q = e^{iπ/r}` (doubled spins). The move invariance of `turaevViro` assumes `qOrthogonality` and
`qBiedenharnElliott`, which the library proves at `r = 3` only
(`Lightlike/TuraevViro/LevelOne.lean`). The checks below evaluate both at `r = 4`, where `[2] = √2`,
on explicit spins.

| check | value | from the identity | computed |
|---|---|---|---|
| `{1 1 0; 1 1 0}`, `{1 1 2; 1 1 0}`, `{1 2 1; 1 2 1}`, `{0 0 0; 1 1 1}²` | `−√2/2`, `√2/2`, `√2/2`, `√2/2` | | `q6j4_110_110`, `q6j4_112_110`, `q6j4_121_121`, `q6j4_000_111_sq` |
| orthogonality at `(B, A, E, F, q) = (1, 2, 1, 2, 1)` | `√2/2 = 1/[2]` | `tv4_orth_predicts` | `tv4_orth_direct`; together `tv4_orth_instance` |
| orthogonality at `(1, 1, 1, 1, 0)` | `1/2 + [3]/2 = 1` | | `tv4_orth_instance'` |
| Biedenharn–Elliott at `a = … = f = 1`, `p = q = r = 0` | `√2/4 + √2/4 = √2/2` | `tv4_be_predicts` | `tv4_be_direct`; together `tv4_be_instance` |

Wrong model: with the classical dimensions `x + 1` in place of `[x + 1]`, orthogonality at
`(1, 2, 1, 2, 1)` gives `1` where that model's own identity asks for `1/(1 + 1) = 1/2`, and
Biedenharn–Elliott gives `√2`, not `√2/2` (`tv4_classical_dims_fail`). These are instances, not
a proof of either identity at `r = 4`. `scripts/recoupling/intertwiner_check.py` (section 10)
repeats the values exactly and evaluates all `3⁵` orthogonality and `3⁹` Biedenharn–Elliott
instances at `r = 4` to 30 digits (numerical evidence, not proof).

### `S³` at `r = 3`

The library normalises the state sum as `Z(K) = W^{−#vertices} Σ_col weight(K, col)` with
`W = Σ_{J < r − 1} [J + 1]²`, the edge factors `[J + 1](−1)^J`, the triangle signs `triW` and one
6j symbol per tetrahedron (`Lightlike/TuraevViro/Model.lean`). The textbook value is `TV(S³) = 1/W`
(Turaev and Viro); that this normalisation is the textbook one is a convention match, stated here,
not a theorem. The check evaluates `Z` on `sphere3`, the boundary `∂Δ⁴` of the 4-simplex (5
vertices, 10 edges, 10 triangles, 5 tetrahedra), at `r = 3`, where `[1] = [2] = 1` and `W = 2`.

| check | value | from the normalisation | computed |
|---|---|---|---|
| `TV₃(∂Δ⁴)` | `1/2` | `tv3_W` (`1/W = 1/2`) | `turaevViro3_sphere` (`2⁻⁵ · 16` over the `2¹⁰` colourings) |

`Z_sphere` reduces the state sum of any two-colour model with the `r = 3` 6j symbols to a sum of
integers, which the kernel evaluates (`sphere3_count_tv`). Wrong model: with the integer
dimensions `J + 1`, `W = 5` and `Z = 721/3125`, not `1/5` (`classical3_sphere_fails`).
`scripts/recoupling/intertwiner_check.py` (section 11) evaluates the state sum directly from the
6j formula, the five tetrahedra and the ten triangles (an independent computation, not proof).

## References

- V. G. Turaev, O. Y. Viro, *State sum invariants of 3-manifolds and quantum 6j-symbols*,
  Topology 31, 865–902 (1992): the state sum, its normalisation and `TV(S³) = 1/W`.
- A. N. Kirillov, N. Yu. Reshetikhin, *Representations of the algebra U_q(sl(2)), q-orthogonal
  polynomials and invariants of links*, in *Infinite-dimensional Lie algebras and groups*, Adv.
  Ser. Math. Phys. 7, 285–339 (1989): the q-Racah formula for the quantum 6j symbols.
-/

open Finset Lightlike.Pentagon Lightlike.PR

set_option maxRecDepth 100000

namespace Lightlike.TV.Test

section TuraevViroFour
open Real

/-- `[1] = 1` at `r = 4`. -/
lemma qnum4_one : qnum 4 1 = 1 := qnum_one (by norm_num)

/-- `[2] = √2` at `r = 4`. -/
lemma qnum4_two : qnum 4 2 = √2 := by
  have h1 : ((2 : ℕ) : ℝ) * π / ((4 : ℕ) : ℝ) = π / 2 := by push_cast; ring
  have h2 : π / ((4 : ℕ) : ℝ) = π / 4 := by norm_num
  rw [qnum, h1, h2, sin_pi_div_two, sin_pi_div_four, one_div_div, div_sqrt]

/-- `[3] = [1] = 1` at `r = 4`. -/
lemma qnum4_three : qnum 4 3 = 1 := by
  have := qnum_sub (r := 4) (n := 1) (by norm_num) (by norm_num)
  rw [show 4 - 1 = 3 from rfl] at this
  rw [this, qnum4_one]

/-- `[4] = 0` at `r = 4`. -/
lemma qnum4_four : qnum 4 4 = 0 := qnum_self (by norm_num)

/-- The quantum factorials at `r = 4`: `1, 1, √2, √2, 0, 0, …`. -/
lemma qfact4 (n : ℕ) : qfact 4 n = if n ≤ 1 then 1 else if n ≤ 3 then √2 else 0 := by
  unfold qfact
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> simp [prod_range_succ, qnum4_one, qnum4_two, qnum4_three]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    exact prod_eq_zero (mem_range.mpr (by omega : 3 < n)) qnum4_four

/-- `1/[u]!` at `r = 4`. -/
lemma invQFact4 (u : ℤ) :
    invQFact 4 u = if 0 ≤ u ∧ u ≤ 1 then 1 else if 2 ≤ u ∧ u ≤ 3 then (√2)⁻¹ else 0 := by
  unfold invQFact
  rw [qfact4]
  split_ifs <;> first | (exfalso; omega) | simp

/-- `√2² = 2`. -/
lemma sqrt_two_sq : √2 ^ 2 = 2 := sq_sqrt (by norm_num)

/-- `1/√2 = √2/2`. -/
lemma inv_sqrt_two : (√2)⁻¹ = √2 / 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← mul_div_assoc, mul_self_sqrt (by norm_num)]; norm_num)

/-- The triangle coefficient `Δ = (√2)^{-1/2}`, written `√((√2)⁻¹)`, squares to `√2/2`. -/
lemma delta4_sq : √((√2)⁻¹) ^ 2 = √2 / 2 := by
  rw [sq_sqrt (by positivity), inv_sqrt_two]

/-- `Δ⁴ = 1/2`. -/
lemma delta4_four : √((√2)⁻¹) ^ 4 = 1 / 2 := by
  rw [show √((√2)⁻¹) ^ 4 = (√((√2)⁻¹) ^ 2) ^ 2 by ring, delta4_sq, div_pow, sqrt_two_sq]
  norm_num

/-- `Δ(1, 1, 0) = (√2)^{-1/2}` at `r = 4`. -/
lemma qDelta4_110 : qDelta 4 1 1 0 = √((√2)⁻¹) := by
  unfold qDelta; congr 1; norm_num [qfact4]

/-- `Δ(0, 1, 1)`. -/
lemma qDelta4_011 : qDelta 4 0 1 1 = √((√2)⁻¹) := by
  unfold qDelta; congr 1; norm_num [qfact4]

/-- `Δ(1, 0, 1)`. -/
lemma qDelta4_101 : qDelta 4 1 0 1 = √((√2)⁻¹) := by
  unfold qDelta; congr 1; norm_num [qfact4]

/-- `Δ(1, 1, 2)`. -/
lemma qDelta4_112 : qDelta 4 1 1 2 = √((√2)⁻¹) := by
  unfold qDelta; congr 1; norm_num [qfact4]

/-- `Δ(1, 2, 1)`. -/
lemma qDelta4_121 : qDelta 4 1 2 1 = √((√2)⁻¹) := by
  unfold qDelta; congr 1; norm_num [qfact4]

/-- `Δ(0, 0, 0) = 1`. -/
lemma qDelta4_000 : qDelta 4 0 0 0 = 1 := by
  unfold qDelta; norm_num [qfact4]

/-- **Explicit value** `{1 1 0; 1 1 0}_q = -√2/2` at `r = 4` (spins `1/2, 1/2, 0`). -/
theorem q6j4_110_110 : qSixJ 4 1 1 0 1 1 0 = -(√2 / 2) := by
  have hR : qRacahSum 4 1 1 0 1 1 0 = -√2 := by
    unfold qRacahSum qRacahTerm
    norm_num [sum_range_succ, invQFact4, qfact4]
  rw [qSixJ, ite_eq_left (by decide), qDelta4_110, hR]
  linear_combination (-√2) * delta4_four

/-- **Explicit value** `{1 1 2; 1 1 0}_q = √2/2`. -/
theorem q6j4_112_110 : qSixJ 4 1 1 2 1 1 0 = √2 / 2 := by
  have hR : qRacahSum 4 1 1 2 1 1 0 = √2 := by
    unfold qRacahSum qRacahTerm
    norm_num [sum_range_succ, invQFact4, qfact4]
  rw [qSixJ, ite_eq_left (by decide), qDelta4_110, qDelta4_112, hR]
  linear_combination √2 * delta4_four

/-- **Explicit value** `{1 2 1; 1 2 1}_q = √2/2`. -/
theorem q6j4_121_121 : qSixJ 4 1 2 1 1 2 1 = √2 / 2 := by
  have hR : qRacahSum 4 1 2 1 1 2 1 = √2 := by
    unfold qRacahSum qRacahTerm
    norm_num [sum_range_succ, invQFact4, qfact4]
  rw [qSixJ, ite_eq_left (by decide), qDelta4_121, hR]
  linear_combination √2 * delta4_four

/-- **Explicit value** `{0 0 0; 1 1 1}_q² = √2/2` (the symbol itself is `-2^{-1/4}`). -/
theorem q6j4_000_111_sq : qSixJ 4 0 0 0 1 1 1 ^ 2 = √2 / 2 := by
  have hR : qRacahSum 4 0 0 0 1 1 1 = -√2 := by
    unfold qRacahSum qRacahTerm
    norm_num [sum_range_succ, invQFact4, qfact4]
  rw [qSixJ, ite_eq_left (by decide), qDelta4_000, qDelta4_011, qDelta4_101, qDelta4_110, hR]
  have h : (1 * √((√2)⁻¹) * √((√2)⁻¹) * √((√2)⁻¹) * -√2) ^ 2 =
      √2 ^ 2 * (√((√2)⁻¹) ^ 2) ^ 3 := by ring
  rw [h, delta4_sq, sqrt_two_sq]
  linear_combination (√2 / 4) * sqrt_two_sq

/-- An inadmissible symbol vanishes (`(1, 2, 0)` is not a triangle). -/
lemma q6j4_120_121 : qSixJ 4 1 2 0 1 2 1 = 0 := by
  rw [qSixJ, ite_eq_right (by decide)]

/-- An inadmissible symbol vanishes (`(1, 2, 2)` has odd perimeter). -/
lemma q6j4_122_121 : qSixJ 4 1 2 2 1 2 1 = 0 := by
  rw [qSixJ, ite_eq_right (by decide)]

/-- An inadmissible symbol vanishes (`(1, 1, 1)` has odd perimeter). -/
lemma q6j4_111_110 : qSixJ 4 1 1 1 1 1 0 = 0 := by
  rw [qSixJ, ite_eq_right (by decide)]

/-- **Prediction** (`qOrthogonality` at `(B, A, E, F, q) = (1, 2, 1, 2, 1)`): the right side is
`1/[2] = √2/2`. -/
theorem tv4_orth_predicts :
    (if qAdm 4 2 1 1 ∧ qAdm 4 1 1 2 then 1 / qnum 4 (1 + 1) else 0) = √2 / 2 := by
  rw [ite_eq_left (by decide), show 1 + 1 = 2 from rfl, qnum4_two, one_div, inv_sqrt_two]

/-- **Direct computation:** only `x = 1` contributes, `[2] · (√2/2)² = √2/2`. -/
theorem tv4_orth_direct :
    ∑ x ∈ range 3, qnum 4 (x + 1) * qSixJ 4 1 2 x 1 2 1 ^ 2 = √2 / 2 := by
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero, q6j4_120_121,
    q6j4_121_121, q6j4_122_121, show 1 + 1 = 2 from rfl, qnum4_two]
  linear_combination (√2 / 4) * sqrt_two_sq

/-- **The `r = 4` orthogonality hypothesis holds at `(1, 2, 1, 2, 1)`.** -/
theorem tv4_orth_instance :
    ∑ x ∈ range (tvModel 4 (by norm_num)).N,
        (tvModel 4 (by norm_num)).dim x * (tvModel 4 (by norm_num)).f 1 2 x 1 2 1 ^ 2 =
      if (tvModel 4 (by norm_num)).ok 2 1 1 ∧ (tvModel 4 (by norm_num)).ok 1 1 2 then
        1 / (tvModel 4 (by norm_num)).dim 1 else 0 :=
  tv4_orth_direct.trans tv4_orth_predicts.symm

/-- **Second orthogonality instance**, `(1, 1, 1, 1, 0)`: `[1] · 1/2 + [3] · 1/2 = 1 = 1/[1]`. -/
theorem tv4_orth_instance' :
    ∑ x ∈ range 3, qnum 4 (x + 1) * qSixJ 4 1 1 x 1 1 0 ^ 2 = 1 ∧
      (if qAdm 4 1 1 0 ∧ qAdm 4 1 0 1 then 1 / qnum 4 (0 + 1) else 0) = 1 := by
  constructor
  · rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero, q6j4_110_110,
      q6j4_111_110, q6j4_112_110, show 0 + 1 = 1 from rfl, show 2 + 1 = 3 from rfl,
      qnum4_one, qnum4_three]
    linear_combination (1 / 2) * sqrt_two_sq
  · rw [ite_eq_left (by decide), show 0 + 1 = 1 from rfl, qnum4_one, div_one]

/-- **Prediction** (`qBiedenharnElliott` at `a = … = f = 1`, `p = q = r = 0`): the right side is
`{0 0 0; 1 1 1}² = √2/2`. -/
theorem tv4_be_predicts : qSixJ 4 0 0 0 1 1 1 * qSixJ 4 0 0 0 1 1 1 = √2 / 2 := by
  rw [← sq, q6j4_000_111_sq]

/-- **Direct computation:** the left side is `x = 0` plus `x = 2`, `√2/4 + √2/4`. -/
theorem tv4_be_direct :
    ∑ x ∈ range 3, (-1 : ℝ) ^ ((1 + 1 + 1 + 1 + 1 + 1 + 0 + 0 + 0 + x) / 2) * qnum 4 (x + 1) *
      (qSixJ 4 1 1 x 1 1 0 * qSixJ 4 1 1 x 1 1 0 * qSixJ 4 1 1 x 1 1 0) = √2 / 2 := by
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero, q6j4_110_110,
    q6j4_111_110, q6j4_112_110, show 0 + 1 = 1 from rfl, show 2 + 1 = 3 from rfl,
    qnum4_one, qnum4_three]
  norm_num
  linear_combination (√2 / 4) * sqrt_two_sq

/-- **The `r = 4` Biedenharn–Elliott hypothesis holds at `(1, 1, 1, 1, 1, 1, 0, 0, 0)`.** -/
theorem tv4_be_instance :
    ∑ x ∈ range (tvModel 4 (by norm_num)).N,
        (-1 : ℝ) ^ ((1 + 1 + 1 + 1 + 1 + 1 + 0 + 0 + 0 + x) / 2) * (tvModel 4 (by norm_num)).dim x *
          ((tvModel 4 (by norm_num)).f 1 1 x 1 1 0 * (tvModel 4 (by norm_num)).f 1 1 x 1 1 0 *
            (tvModel 4 (by norm_num)).f 1 1 x 1 1 0) =
      (tvModel 4 (by norm_num)).f 0 0 0 1 1 1 * (tvModel 4 (by norm_num)).f 0 0 0 1 1 1 :=
  tv4_be_direct.trans tv4_be_predicts.symm

/-- **Wrong model:** classical dimensions `x + 1` in place of `[x + 1]` break both identities:
orthogonality gives `2 · 1/2 = 1 ≠ 1/2`, Biedenharn–Elliott gives `√2/4 + 3√2/4 = √2 ≠ √2/2`. -/
theorem tv4_classical_dims_fail :
    ∑ x ∈ range 3, ((x : ℝ) + 1) * qSixJ 4 1 2 x 1 2 1 ^ 2 ≠ 1 / ((1 : ℝ) + 1) ∧
      ∑ x ∈ range 3, (-1 : ℝ) ^ ((1 + 1 + 1 + 1 + 1 + 1 + 0 + 0 + 0 + x) / 2) * ((x : ℝ) + 1) *
        (qSixJ 4 1 1 x 1 1 0 * qSixJ 4 1 1 x 1 1 0 * qSixJ 4 1 1 x 1 1 0) ≠
        qSixJ 4 0 0 0 1 1 1 * qSixJ 4 0 0 0 1 1 1 := by
  have hs : 0 < √2 := by positivity
  constructor
  · rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero, q6j4_120_121,
      q6j4_121_121, q6j4_122_121]
    intro h
    nlinarith [sqrt_two_sq]
  · rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero, q6j4_110_110,
      q6j4_111_110, q6j4_112_110, tv4_be_predicts]
    intro h
    norm_num at h
    nlinarith [sqrt_two_sq]

end TuraevViroFour

section TuraevViroSphere

/-- The boundary of the 4-simplex, a triangulation of `S³`: the five 4-subsets of `Fin 5`. -/
def sphere3 : Complex3 (Fin 5) where
  tets := powersetCard 4 univ
  card_eq := fun _ ht => (mem_powersetCard.mp ht).2

/-- The ten edges of `∂Δ⁴`, in lexicographic order. -/
def sphereEdges : List (Finset (Fin 5)) :=
  [{0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}]

/-- The ten triangles of `∂Δ⁴`. -/
def sphereTris : List (Finset (Fin 5)) :=
  [{0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4},
    {1, 3, 4}, {2, 3, 4}]

/-- The five tetrahedra of `∂Δ⁴`. -/
def sphereTets : List (Finset (Fin 5)) :=
  [{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}]

/-- The edge list is the edge set of `∂Δ⁴`, without repetition. -/
lemma sphere3_edges : sphere3.edges = sphereEdges.toFinset ∧ sphereEdges.Nodup := by
  decide +kernel

/-- The triangle list is the triangle set of `∂Δ⁴`, without repetition. -/
lemma sphere3_tris : sphere3.tris = sphereTris.toFinset ∧ sphereTris.Nodup := by
  decide +kernel

/-- The tetrahedron list is the tetrahedron set of `∂Δ⁴`, without repetition. -/
lemma sphere3_tets : sphere3.tets = sphereTets.toFinset ∧ sphereTets.Nodup := by
  decide +kernel

/-- `∂Δ⁴` has five vertices. -/
lemma sphere3_vertices : #(Model.vertices sphere3) = 5 := by
  decide +kernel

/-- The edges of a triangle `a < b < c`. -/
lemma tri_facts : ∀ a b c : Fin 5, a < b → b < c →
    powersetCard 2 ({a, b, c} : Finset (Fin 5)) = [{a, b}, {a, c}, {b, c}].toFinset ∧
      [({a, b} : Finset (Fin 5)), {a, c}, {b, c}].Nodup := by
  decide +kernel

/-- A tetrahedron `a < b < c < d` has four vertices and `![a, b, c, d]` enumerates it. -/
lemma tet_facts : ∀ a b c d : Fin 5, a < b → b < c → c < d →
    #({a, b, c, d} : Finset (Fin 5)) = 4 ∧ Function.Injective ![a, b, c, d] := by
  decide +kernel

/-- The triangle sign of `a < b < c`. -/
lemma triW_sphere (col : Colouring (Fin 5)) {a b c : Fin 5} (hab : a < b) (hbc : b < c) :
    triW col {a, b, c} = (-1) ^ ((col {a, b} + col {a, c} + col {b, c}) / 2) := by
  obtain ⟨hp, hn⟩ := tri_facts a b c hab hbc
  rw [triW, hp, List.sum_toFinset _ hn]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]

/-- The tetrahedron weight of `a < b < c < d` in a model whose 6j symbol is the `r = 3` one. -/
lemma tetW_sphere (M : Model)
    (hf : ∀ j₁ j₂ j₃ j₄ j₅ j₆, M.f j₁ j₂ j₃ j₄ j₅ j₆ = qSixJ 3 j₁ j₂ j₃ j₄ j₅ j₆)
    (col : Colouring (Fin 5)) {a b c d : Fin 5} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    M.tetW col {a, b, c, d} =
      (t3 (col {c, d}) (col {b, d}) (col {b, c}) (col {a, b}) (col {a, c}) (col {a, d}) : ℝ) := by
  obtain ⟨hc, hp⟩ := tet_facts a b c d hab hbc hcd
  rw [M.tetW_eq_tetAmp col hc hp (fun i => by fin_cases i <;> simp), M.tetAmp_eq, hf]
  exact qSixJ_three _ _ _ _ _ _

/-- The weight of a colouring of `∂Δ⁴` with colours `0, 1`, as an integer: edge factors `ε`,
ten triangle signs, five `r = 3` 6j symbols. -/
def w3 (ε : ℕ → ℤ) (c01 c02 c03 c04 c12 c13 c14 c23 c24 c34 : ℕ) : ℤ :=
  ε c01 * ε c02 * ε c03 * ε c04 * ε c12 * ε c13 * ε c14 * ε c23 * ε c24 * ε c34 *
    ((-1) ^ ((c01 + c02 + c12) / 2) * (-1) ^ ((c01 + c03 + c13) / 2) *
      (-1) ^ ((c01 + c04 + c14) / 2) * (-1) ^ ((c02 + c03 + c23) / 2) *
      (-1) ^ ((c02 + c04 + c24) / 2) * (-1) ^ ((c03 + c04 + c34) / 2) *
      (-1) ^ ((c12 + c13 + c23) / 2) * (-1) ^ ((c12 + c14 + c24) / 2) *
      (-1) ^ ((c13 + c14 + c34) / 2) * (-1) ^ ((c23 + c24 + c34) / 2)) *
    (t3 c23 c13 c12 c01 c02 c03 * t3 c24 c14 c12 c01 c02 c04 * t3 c34 c14 c13 c01 c03 c04 *
      t3 c34 c24 c23 c02 c03 c04 * t3 c34 c24 c23 c12 c13 c14)

/-- The weight of `∂Δ⁴` in a model with the `r = 3` 6j symbols and edge weights `ε` on `{0, 1}`. -/
theorem weight_sphere (M : Model)
    (hf : ∀ j₁ j₂ j₃ j₄ j₅ j₆, M.f j₁ j₂ j₃ j₄ j₅ j₆ = qSixJ 3 j₁ j₂ j₃ j₄ j₅ j₆)
    (ε : ℕ → ℤ) (hε : ∀ J, J < 2 → M.edgeW J = ε J)
    (col : Colouring (Fin 5)) (hcol : ∀ e, col e < 2) :
    M.weight sphere3 col = (w3 ε (col {0, 1}) (col {0, 2}) (col {0, 3}) (col {0, 4}) (col {1, 2})
      (col {1, 3}) (col {1, 4}) (col {2, 3}) (col {2, 4}) (col {3, 4}) : ℝ) := by
  have hε' : ∀ e, M.edgeW (col e) = ε (col e) := fun e => hε _ (hcol e)
  rw [Model.weight, sphere3_edges.1, sphere3_tris.1, sphere3_tets.1,
    List.prod_toFinset _ sphere3_edges.2, List.prod_toFinset _ sphere3_tris.2,
    List.prod_toFinset _ sphere3_tets.2]
  simp only [sphereEdges, sphereTris, sphereTets, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, hε']
  simp (disch := decide) only [triW_sphere, tetW_sphere M hf]
  simp only [w3]
  push_cast
  ring

/-- Nested sum over the colours `{0, 1}` of a list of edges. -/
noncomputable def nestSum2 {V : Type*} [DecidableEq V] :
    List (Finset V) → (Colouring V → ℝ) → ℝ
  | [], F => F (fun _ => 0)
  | a :: l, F => nestSum2 l (fun col => ∑ x ∈ range 2, F (Function.update col a x))

/-- A state sum over colourings `S → {0, 1}` is a nested sum, edge by edge. -/
lemma sum_pi_eq_nestSum2 {V : Type*} [DecidableEq V] :
    ∀ (l : List (Finset V)), l.Nodup → ∀ (F G : Colouring V → ℝ),
      (∀ col : Colouring V, (∀ e, col e < 2) → F col = G col) →
      ∑ σ ∈ l.toFinset.pi (fun _ => range 2), F (extS l.toFinset σ) = nestSum2 l G := by
  intro l
  induction l with
  | nil =>
    intro _ F G hFG
    rw [List.toFinset_nil, pi_empty, sum_singleton, nestSum2, hFG _ fun e => by simp [extS]]
    exact congrArg G (funext fun e => by simp [extS])
  | cons a l ih =>
    intro hl F G hFG
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    rw [List.toFinset_cons, sum_pi_insert (by rwa [List.mem_toFinset]), nestSum2]
    exact ih hl (fun col => ∑ x ∈ range 2, F (Function.update col a x))
      (fun col => ∑ x ∈ range 2, G (Function.update col a x))
      fun col hcol => sum_congr rfl fun x hx => hFG _ fun e => by
        rcases eq_or_ne e a with rfl | he
        · rw [Function.update_self]; exact mem_range.mp hx
        · rw [Function.update_of_ne he]; exact hcol e

/-- **The state sum of `∂Δ⁴`** in a two-colour model with the `r = 3` 6j symbols:
`Z = W^{-5} · Σ w3`, the sum over the `2¹⁰` colourings. -/
theorem Z_sphere (M : Model) (hN : M.N = 2)
    (hf : ∀ j₁ j₂ j₃ j₄ j₅ j₆, M.f j₁ j₂ j₃ j₄ j₅ j₆ = qSixJ 3 j₁ j₂ j₃ j₄ j₅ j₆)
    (ε : ℕ → ℤ) (hε : ∀ J, J < 2 → M.edgeW J = ε J) :
    M.Z sphere3 = M.W⁻¹ ^ 5 * ((∑ x₁₀ ∈ range 2, ∑ x₉ ∈ range 2, ∑ x₈ ∈ range 2,
      ∑ x₇ ∈ range 2, ∑ x₆ ∈ range 2, ∑ x₅ ∈ range 2, ∑ x₄ ∈ range 2, ∑ x₃ ∈ range 2,
      ∑ x₂ ∈ range 2, ∑ x₁ ∈ range 2, w3 ε x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℤ) : ℝ) := by
  rw [Model.Z, hN, sphere3_vertices, sphere3_edges.1,
    sum_pi_eq_nestSum2 sphereEdges sphere3_edges.2 (M.weight sphere3) _
      (fun col hcol => weight_sphere M hf ε hε col hcol)]
  simp only [sphereEdges, nestSum2]
  simp (disch := decide) only [Function.update_self, Function.update_of_ne]
  push_cast
  rfl

/-- The Turaev–Viro edge factor at `r = 3` on the colours `{0, 1}`: `[J + 1](-1)^J = (-1)^J`. -/
def epsTV (J : ℕ) : ℤ := (-1) ^ J

/-- The classical edge factor `(J + 1)(-1)^J` (integer dimensions; wrong model). -/
def epsCl (J : ℕ) : ℤ := (J + 1) * (-1) ^ J

/-- `2¹⁰` colourings, 16 of weight `+1` (the `ℤ/2` coboundaries), all others `0`. -/
lemma sphere3_count_tv : ∑ x₁₀ ∈ range 2, ∑ x₉ ∈ range 2, ∑ x₈ ∈ range 2,
      ∑ x₇ ∈ range 2, ∑ x₆ ∈ range 2, ∑ x₅ ∈ range 2, ∑ x₄ ∈ range 2, ∑ x₃ ∈ range 2,
      ∑ x₂ ∈ range 2, ∑ x₁ ∈ range 2, w3 epsTV x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ = 16 := by
  decide +kernel

/-- The same sum with integer dimensions. -/
lemma sphere3_count_cl : ∑ x₁₀ ∈ range 2, ∑ x₉ ∈ range 2, ∑ x₈ ∈ range 2,
      ∑ x₇ ∈ range 2, ∑ x₆ ∈ range 2, ∑ x₅ ∈ range 2, ∑ x₄ ∈ range 2, ∑ x₃ ∈ range 2,
      ∑ x₂ ∈ range 2, ∑ x₁ ∈ range 2, w3 epsCl x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ = 721 := by
  decide +kernel

/-- **Prediction** (the normalisation): at `r = 3`, `W = [1]² + [2]² = 2`, so a triangulation
invariant with `Z(S³) = 1/W` must give `1/2`. -/
theorem tv3_W : (tvModel 3 (by norm_num)).W = 2 := by
  show ∑ d ∈ range 2, qnum 3 (d + 1) ^ 2 = 2
  rw [sum_range_succ, sum_range_succ, sum_range_zero, zero_add, show 1 + 1 = 2 from rfl,
    qnum3_one, qnum3_two]
  norm_num

/-- **Direct computation:** `TV₃(∂Δ⁴) = 2⁻⁵ · 16 = 1/2`, over all `2¹⁰` colourings. With the
library's normalisation `Z = W^{-#vertices} Σ weight`, this is the textbook `TV(S³) = 1/W`. -/
theorem turaevViro3_sphere : turaevViro (r := 3) (by norm_num) sphere3 = 1 / 2 := by
  have hε : ∀ J, J < 2 → (tvModel 3 (by norm_num)).edgeW J = epsTV J := by
    intro J hJ
    show qnum 3 (J + 1) * (-1) ^ J = ((-1 : ℤ) ^ J : ℤ)
    interval_cases J
    · rw [zero_add, qnum3_one]; norm_num
    · rw [show 1 + 1 = 2 from rfl, qnum3_two]; norm_num
  rw [turaevViro, Z_sphere _ rfl (fun _ _ _ _ _ _ => rfl) epsTV hε, sphere3_count_tv, tv3_W]
  norm_num

/-- The two-colour model with the `r = 3` 6j symbols and integer dimensions `J + 1`. -/
noncomputable def classical3 : Model :=
  { tvModel 3 (by norm_num) with dim := fun J => (J : ℝ) + 1 }

/-- **Wrong model:** with integer dimensions, `W = 1 + 4 = 5` but the state sum of `∂Δ⁴` is
`721/3125`, not `1/5`. -/
theorem classical3_sphere_fails :
    classical3.W = 5 ∧ classical3.Z sphere3 = 721 / 3125 ∧
      classical3.Z sphere3 ≠ 1 / classical3.W := by
  have hW : classical3.W = 5 := by
    show ∑ d ∈ range 2, ((d : ℝ) + 1) ^ 2 = 5
    rw [sum_range_succ, sum_range_succ, sum_range_zero]
    norm_num
  have hε : ∀ J, J < 2 → classical3.edgeW J = epsCl J := by
    intro J hJ
    show ((J : ℝ) + 1) * (-1) ^ J = (((J : ℤ) + 1) * (-1) ^ J : ℤ)
    push_cast
    ring
  have hZ : classical3.Z sphere3 = 721 / 3125 := by
    rw [Z_sphere _ rfl (fun _ _ _ _ _ _ => rfl) epsCl hε, sphere3_count_cl, hW]
    norm_num
  refine ⟨hW, hZ, ?_⟩
  rw [hZ, hW]
  norm_num

end TuraevViroSphere

end Lightlike.TV.Test
