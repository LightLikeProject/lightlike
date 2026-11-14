module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.NineJ

/-!
# Audit of Physlib's 6j symbols against standard values

We build Milestones 4–5 on PhyslibAlpha's 6j symbols (`PhyslibAlpha.Sl2.sixJSym`, Physlib commit
`cdfa609`, **Alpha tier**). As with the curvature definitions, we first check that the definition
gives the standard numbers, by **Lean proofs** (kernel-checked, no `sorry`) evaluating their
definition - a sum over projections of four Racah-formula 3j symbols - at concrete arguments.

Method: restrict the 6j sum to the projection tuples where all four 3j symbols are admissible
(completeness of that list is checked by kernel `decide` over the whole projection box), then
evaluate each 3j symbol exactly (factorials, `Real.sqrt`, Racah's alternating sum).

Reference values: computed independently with SymPy's `wigner_6j` (Racah's formula), and agree
with the standard closed form for a zero argument `{a b c; 0 c b} = (-1)^(a+b+c)/√((2b+1)(2c+1))`.

| 6j symbol | doubled arguments | value | theorem |
|---|---|---|---|
| {0 0 0; 0 0 0} | 0 0 0 0 0 0 | 1 | `sixJ_000000` |
| {½ ½ 0; ½ ½ 0} | 1 1 0 1 1 0 | -1/2 | `sixJ_hh0_hh0` |
| {½ ½ 1; ½ ½ 0} | 1 1 2 1 1 0 | 1/2 | `sixJ_hh1_hh0` |
| {½ ½ 0; ½ ½ 1} | 1 1 0 1 1 2 | 1/2 | `sixJ_hh0_hh1` |
| {½ ½ 1; ½ ½ 1} | 1 1 2 1 1 2 | 1/6 | `sixJ_hh1_hh1` |
| {1 1 1; 1 1 0} | 2 2 2 2 2 0 | -1/3 | `sixJ_111_110` |
| {1 1 1; ½ ½ ½} | 2 2 2 1 1 1 | -1/3 | `sixJ_111_hhh` |
| {1 1 3; 1 1 1} | 2 2 6 2 2 2 | 0 (triangle rule) | `sixJ_113_111` |
| {½ ½ ½; ½ ½ ½} | 1 1 1 1 1 1 | 0 (½+½+½ not an integer) | `sixJ_hhh_hhh` |
| {2 2 1; 1 1 1} | 4 4 2 2 2 2 | -√5/10 | `sixJ_221_111` |
| {2 2 2; 1 1 1} | 4 4 4 2 2 2 | √21/30 | `sixJ_222_111` |
| {2 2 2; 2 2 2} | 4 4 4 4 4 4 | -3/70 | `sixJ_222_222` |
| {5/2 5/2 1; ½ ½ 2} | 5 5 2 1 1 4 | √35/30 | `sixJ_5h5h1_hh2` |
| {5/2 5/2 1; 5/2 5/2 1} | 5 5 2 5 5 2 | -31/210 | `sixJ_5h5h1_5h5h1` |

The last five (spins 2 and 5/2, no zero argument) are evaluated through `sixJSym_eq_triple`, a
general reduction of the 6j sum to three free projections; see the section "Larger spins".

The signs (−1/2, −1/3) confirm the standard Racah–Wigner phase convention; half-integer spins are
covered. General vanishing lemmas: `sixJSym_eq_zero_of_triangle`, `sixJSym_eq_zero_of_parity`.

## Conventions (for Ponzano–Regge)

* **Units.** `sixJSym j₁ … j₆` takes *doubled* spins `2j ∈ ℕ`: `{j₁ … j₆} = sixJSym (2j₁) … (2j₆)`.
* **Arrangement.** Triads `(j₁ j₂ j₃), (j₁ j₅ j₆), (j₄ j₂ j₆), (j₄ j₅ j₃)` - the standard
  `{j₁ j₂ j₃; j₄ j₅ j₆}` (columns = pairs of opposite edges of the tetrahedron).
* **Normalisation/phase.** Standard Racah–Wigner 6j: tetrahedral symmetry (`sixJSymEdge_comp_map`),
  orthogonality `Σ (2j₁₂+1)(2j₂₃+1){…}{…} = δ` (`sum_sixJ_mul_sixJ`), recoupling relation
  `⟨(j₁j₂)j₁₂,j₃;J|j₁,(j₂j₃)j₂₃;J⟩ = (-1)^(j₁+j₂+j₃+J) √((2j₁₂+1)(2j₂₃+1)) {j₁ j₂ j₁₂; j₃ J j₂₃}`
  with Condon–Shortley Clebsch–Gordan phases - and the values above. This is the 6j symbol of the
  Ponzano–Regge state sum, so **no rescaling is needed**; the Ponzano–Regge edge, triangle and
  vertex factors (`(2j+1)`, signs `(-1)^(…)`) are separate and must be added by the amplitude.
* **Edge indexing.** `sixJSymEdge j` labels the six arguments by pairs of *triads* (vertices of the
  dual tetrahedron). For a geometric tetrahedron with vertices `0…3`, the face opposite vertex `i`
  is triad `i`, and faces `i, k` share the edge `{0,1,2,3} \ {i,k}`; so the spin on Physlib's
  pair `s(i,k)` is the spin of the geometric edge complementary to `{i,k}`. All 24 relabellings
  leave the symbol invariant, so any consistent labelling works.
-/

@[expose] public section

open PhyslibAlpha.Sl2

namespace Lightlike.SixJAudit

set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

/-- `sixSum` as a finite sum over `z ∈ [a₁, b₁]` (outside, `invFact` of a negative argument is 0). -/
lemma sixSum_eq_sum (a₁ a₂ a₃ b₁ b₂ b₃ : ℤ) :
    sixSum a₁ a₂ a₃ b₁ b₂ b₃ = ∑ z ∈ Finset.Icc a₁ b₁, sixTerm a₁ a₂ a₃ b₁ b₂ b₃ z := by
  rw [sixSum, finsum_eq_sum_of_support_subset]
  intro z hz
  simp only [Function.mem_support] at hz
  have h1 : invFact (z - a₁) ≠ 0 := fun h => hz (by simp [sixTerm, h])
  have h2 : invFact (b₁ - z) ≠ 0 := fun h => hz (by simp [sixTerm, h])
  have := nonneg_of_invFact_ne_zero h1
  have := nonneg_of_invFact_ne_zero h2
  simp only [Finset.coe_Icc, Set.mem_Icc]; omega

/-- A `sixJTerm` vanishes unless all four 3j symbols are admissible. -/
lemma sixJTerm_eq_zero {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} {m : Fin 6 → ℤ}
    (h : ¬ (Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) ∧ Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5) ∧
      Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5) ∧ Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2))) :
    sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m = 0 := by
  simp only [sixJTerm]
  by_cases h1 : Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2)
  · by_cases h2 : Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5)
    · by_cases h3 : Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5)
      · have h4 : ¬ Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2) := fun h4 => h ⟨h1, h2, h3, h4⟩
        simp [threeJ_of_not h4]
      · simp [threeJ_of_not h3]
    · simp [threeJ_of_not h2]
  · simp [threeJ_of_not h1]

/-- Sums over an integer interval as sums over `range`, so that `simp` can unroll them. -/
lemma sum_Icc_int (a b : ℤ) (f : ℤ → ℝ) :
    ∑ z ∈ Finset.Icc a b, f z = ∑ i ∈ Finset.range (b - a + 1).toNat, f (a + i) := by
  have h : Finset.Icc a b = (Finset.range (b - a + 1).toNat).map
      ⟨fun i : ℕ => a + (i : ℤ), fun i j h => by simpa using h⟩ := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(z - a).toNat, by omega, ?_⟩
      show a + ((z - a).toNat : ℤ) = z
      omega
    · rintro ⟨i, hi, rfl⟩
      show a ≤ a + (i : ℤ) ∧ a + (i : ℤ) ≤ b
      omega
  rw [h, Finset.sum_map]
  rfl

/-- All four 3j symbols of a `sixJTerm` are admissible (as a `Bool`, so `decide` needs only one
generic `Decidable` instance). -/
def adm4 (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (m : Fin 6 → ℤ) : Bool :=
  decide (Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2)) && decide (Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5)) &&
    decide (Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5)) && decide (Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2))

/-- Restrict the 6j sum to an explicit duplicate-free list `l` of projection tuples, given that
every other tuple in the box has an inadmissible 3j symbol (checked by `decide`). -/
lemma sixJSym_eq_list (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) (l : List (Fin 6 → ℤ)) (hnd : l.Nodup)
    (hS : ∀ m ∈ l, m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆)
    (hz : ∀ m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆, m ∉ l.toFinset → adm4 j₁ j₂ j₃ j₄ j₅ j₆ m = false) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = (l.map (sixJTerm j₁ j₂ j₃ j₄ j₅ j₆)).sum := by
  rw [sixJSym, ← List.sum_toFinset _ hnd]
  refine (Finset.sum_subset (fun m hm => hS m (List.mem_toFinset.mp hm))
    fun m hm hml => sixJTerm_eq_zero ?_).symm
  have := hz m hm hml
  simp only [adm4, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
  tauto

/-- A 6j symbol whose first triad violates the triangle inequality vanishes. -/
theorem sixJSym_eq_zero_of_triangle {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : j₁ + j₂ < j₃) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = 0 :=
  Finset.sum_eq_zero fun m _ => sixJTerm_eq_zero fun ⟨h1, _⟩ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h3, -⟩ := h1; omega

/-- A 6j symbol whose first triad has odd (doubled) perimeter - i.e. `j₁ + j₂ + j₃` is not an
integer - vanishes. -/
theorem sixJSym_eq_zero_of_parity {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} (h : (j₁ + j₂ + j₃) % 2 = 1) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = 0 :=
  Finset.sum_eq_zero fun m _ => sixJTerm_eq_zero fun ⟨h1, _⟩ => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hp⟩ := h1; omega

lemma sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) : √x ^ 4 = x ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hx]

lemma sqrt_six : √(6 : ℝ) = √2 * √3 := by
  rw [← Real.sqrt_mul (by norm_num)]; norm_num

lemma sqrt_four : √(4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma sqrt_twentyfour : √(24 : ℝ) = 2 * (√2 * √3) := by
  rw [show (24 : ℝ) = 2 ^ 2 * (2 * 3) by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num), Real.sqrt_mul (by norm_num)]

lemma sqrt_eight : √(8 : ℝ) = 2 * √2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- **{0 0 0; 0 0 0} = 1.** -/
theorem sixJ_000000 : sixJSym 0 0 0 0 0 0 = 1 := by
  rw [sixJSym_eq_list 0 0 0 0 0 0 [fun _ => 0] (by decide) (by decide) (by decide +kernel)]
  norm_num [sixJTerm, threeJ, Adm3, threeJR, reggeJ, sixSum_eq_sum, sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three]

/-- **{½ ½ 0; ½ ½ 0} = -½** (half-integer spins; doubled arguments `1 1 0 1 1 0`). -/
theorem sixJ_hh0_hh0 : sixJSym 1 1 0 1 1 0 = -1 / 2 := by
  rw [sixJSym_eq_list 1 1 0 1 1 0 [![1, -1, 0, 1, 1, 0], ![-1, 1, 0, -1, -1, 0]] (by decide)
    (by decide) (by decide +kernel)]
  norm_num [sixJTerm, threeJ, Adm3, threeJR, reggeJ, sixSum_eq_sum, sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  norm_num [mul_pow, inv_pow, sqrt_pow_four, Real.sq_sqrt, Nat.factorial]

/-- **{½ ½ 1; ½ ½ 0} = ½** (doubled `1 1 2 1 1 0`). -/
theorem sixJ_hh1_hh0 : sixJSym 1 1 2 1 1 0 = 1 / 2 := by
  rw [sixJSym_eq_list 1 1 2 1 1 0 [![-1, -1, 2, 1, -1, 0], ![-1, 1, 0, -1, -1, 0],
    ![1, -1, 0, 1, 1, 0], ![1, 1, -2, -1, 1, 0]] (by decide) (by decide) (by decide +kernel)]
  norm_num [sixJTerm, threeJ, Adm3, threeJR, reggeJ, sixSum_eq_sum, sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [sqrt_six]
  try ring_nf
  norm_num [mul_pow, inv_pow, sqrt_pow_four, Real.sq_sqrt, Nat.factorial]

/-- **{½ ½ 1; ½ ½ 1} = 1/6** (half-integer spins, no zero argument; doubled `1 1 2 1 1 2`). -/
theorem sixJ_hh1_hh1 : sixJSym 1 1 2 1 1 2 = 1 / 6 := by
  rw [sixJSym_eq_list 1 1 2 1 1 2 [![-1, -1, 2, 1, -1, 0], ![-1, 1, 0, -1, -1, 0],
    ![-1, 1, 0, 1, 1, 2], ![1, -1, 0, -1, -1, -2], ![1, -1, 0, 1, 1, 0], ![1, 1, -2, -1, 1, 0]]
    (by decide) (by decide) (by decide +kernel)]
  norm_num [sixJTerm, threeJ, Adm3, threeJR, reggeJ, sixSum_eq_sum, sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [sqrt_six]
  try ring_nf
  norm_num [mul_pow, inv_pow, sqrt_pow_four, Real.sq_sqrt, Nat.factorial]

/-- **{1 1 1; 1 1 0} = -1/3** (integer spins; doubled `2 2 2 2 2 0`). -/
theorem sixJ_111_110 : sixJSym 2 2 2 2 2 0 = -1 / 3 := by
  rw [sixJSym_eq_list 2 2 2 2 2 0 [![-2, 0, 2, 0, -2, 0], ![-2, 2, 0, -2, -2, 0],
    ![0, -2, 2, 2, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 2, -2, -2, 0, 0], ![2, -2, 0, 2, 2, 0],
    ![2, 0, -2, 0, 2, 0]] (by decide) (by decide) (by decide +kernel)]
  norm_num [sixJTerm, threeJ, Adm3, threeJR, reggeJ, sixSum_eq_sum, sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [sqrt_six, sqrt_four]
  try ring_nf
  norm_num [mul_pow, inv_pow, sqrt_pow_four, Real.sq_sqrt, Nat.factorial]

/-- **{1 1 3; 1 1 1} = 0** by the triangle rule (`3 > 1 + 1`; doubled `2 2 6 2 2 2`). -/
theorem sixJ_113_111 : sixJSym 2 2 6 2 2 2 = 0 := sixJSym_eq_zero_of_triangle (by norm_num)

/-- **{½ ½ ½; ½ ½ ½} = 0**: `½ + ½ + ½` is not an integer (doubled perimeter 3 is odd). -/
theorem sixJ_hhh_hhh : sixJSym 1 1 1 1 1 1 = 0 := sixJSym_eq_zero_of_parity (by norm_num)

/-- **{½ ½ 0; ½ ½ 1} = ½** (doubled `1 1 0 1 1 2`). -/
theorem sixJ_hh0_hh1 : sixJSym 1 1 0 1 1 2 = 1 / 2 := by
  rw [sixJSym_eq_list 1 1 0 1 1 2 [![-1, 1, 0, -1, -1, 0], ![-1, 1, 0, 1, 1, 2],
    ![1, -1, 0, -1, -1, -2], ![1, -1, 0, 1, 1, 0]] (by decide) (by decide) (by decide +kernel)]
  norm_num [sixJTerm, threeJ, Adm3, threeJR, reggeJ, sixSum_eq_sum, sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [sqrt_six]
  try ring_nf
  norm_num [mul_pow, inv_pow, sqrt_pow_four, Real.sq_sqrt, Nat.factorial]

/-- **{1 1 1; ½ ½ ½} = -1/3** (doubled `2 2 2 1 1 1`). -/
theorem sixJ_111_hhh : sixJSym 2 2 2 1 1 1 = -1 / 3 := by
  rw [sixJSym_eq_list 2 2 2 1 1 1 [![-2, 0, 2, 1, -1, 1], ![-2, 2, 0, -1, -1, 1],
    ![0, -2, 2, 1, -1, -1], ![0, 0, 0, -1, -1, -1], ![0, 0, 0, 1, 1, 1], ![0, 2, -2, -1, 1, 1],
    ![2, -2, 0, 1, 1, -1], ![2, 0, -2, -1, 1, -1]] (by decide) (by decide) (by decide +kernel)]
  norm_num [sixJTerm, threeJ, Adm3, threeJR, reggeJ, sixSum_eq_sum, sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [sqrt_six]
  try ring_nf
  norm_num [mul_pow, inv_pow, sqrt_pow_four, Real.sq_sqrt, Nat.factorial]

/-! ## Larger spins (2 and 5/2)

The `decide` over the whole projection box used above does not scale: at spin 2 the box has
`9⁶ = 531 441` tuples. `sixJSym_eq_triple` instead reduces the sum, for all spins, to the three free
projections `m₁, m₂, m₄` (admissibility of the 3j symbols fixes the other three). The values are
then sums of products of square roots, closed by `surd_finish`: split every `√n` over the primes
`2, 3, 5, 7` (`sqrt_split_n`, each proven by squaring), clear denominators, reduce powers. -/

/-- The projection tuple fixed by the free projections `m₁ = 2i - j₁`, `m₂ = 2k - j₂`,
`m₄ = 2l - j₄`; the other three are forced by the zero-sum condition of the 3j symbols. -/
def mTuple (j₁ j₂ j₄ : ℕ) (p : ℕ × ℕ × ℕ) : Fin 6 → ℤ :=
  ![2 * p.1 - j₁, 2 * p.2.1 - j₂, -(2 * p.1 - j₁) - (2 * p.2.1 - j₂), 2 * p.2.2 - j₄,
    (2 * p.2.2 - j₄) + (2 * p.1 - j₁) + (2 * p.2.1 - j₂), (2 * p.2.2 - j₄) + (2 * p.2.1 - j₂)]

lemma mTuple_apply (j₁ j₂ j₄ i k l : ℕ) :
    mTuple j₁ j₂ j₄ (i, k, l) 0 = 2 * (i : ℤ) - j₁ ∧ mTuple j₁ j₂ j₄ (i, k, l) 1 = 2 * (k : ℤ) - j₂ ∧
    mTuple j₁ j₂ j₄ (i, k, l) 2 = -(2 * (i : ℤ) - j₁) - (2 * (k : ℤ) - j₂) ∧
    mTuple j₁ j₂ j₄ (i, k, l) 3 = 2 * (l : ℤ) - j₄ ∧
    mTuple j₁ j₂ j₄ (i, k, l) 4 = (2 * (l : ℤ) - j₄) + (2 * (i : ℤ) - j₁) + (2 * (k : ℤ) - j₂) ∧
    mTuple j₁ j₂ j₄ (i, k, l) 5 = (2 * (l : ℤ) - j₄) + (2 * (k : ℤ) - j₂) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma sixJBox_triple_mem {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ} {m : Fin 6 → ℤ}
    (hm : sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m ≠ 0) :
    m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆ ∧
      m ∈ (Finset.range (j₁ + 1) ×ˢ (Finset.range (j₂ + 1) ×ˢ Finset.range (j₄ + 1))).image
        (mTuple j₁ j₂ j₄) := by
  have hA : Adm3 j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) ∧ Adm3 j₁ j₅ j₆ (m 0) (-m 4) (m 5) ∧
      Adm3 j₄ j₂ j₆ (m 3) (m 1) (-m 5) ∧ Adm3 j₄ j₅ j₃ (-m 3) (m 4) (m 2) := by
    by_contra h
    exact hm (sixJTerm_eq_zero h)
  obtain ⟨⟨s1, a1, a2, b1, b2, c1, c2, p1, p2, p3, -⟩, ⟨s2, d1, d2, e1, e2, f1, f2, q1, q2, q3, -⟩,
    ⟨s3, g1, g2, h1, h2, k1, k2, r1, r2, r3, -⟩, ⟨s4, l1, l2, n1, n2, o1, o2, t1, t2, t3, -⟩⟩ := hA
  refine ⟨?_, ?_⟩
  · rw [mem_sixJBox]; omega
  · rw [Finset.mem_image]
    obtain ⟨I, hI⟩ : ∃ I : ℕ, (I : ℤ) = (m 0 + j₁) / 2 := ⟨((m 0 + j₁) / 2).toNat, by omega⟩
    obtain ⟨K, hK⟩ : ∃ K : ℕ, (K : ℤ) = (m 1 + j₂) / 2 := ⟨((m 1 + j₂) / 2).toNat, by omega⟩
    obtain ⟨L, hL⟩ : ∃ L : ℕ, (L : ℤ) = (m 3 + j₄) / 2 := ⟨((m 3 + j₄) / 2).toNat, by omega⟩
    refine ⟨(I, K, L), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · obtain ⟨u0, u1, u2, u3, u4, u5⟩ := mTuple_apply j₁ j₂ j₄ I K L
      funext x
      fin_cases x
      · show mTuple j₁ j₂ j₄ (I, K, L) 0 = m 0; rw [u0]; omega
      · show mTuple j₁ j₂ j₄ (I, K, L) 1 = m 1; rw [u1]; omega
      · show mTuple j₁ j₂ j₄ (I, K, L) 2 = m 2; rw [u2]; omega
      · show mTuple j₁ j₂ j₄ (I, K, L) 3 = m 3; rw [u3]; omega
      · show mTuple j₁ j₂ j₄ (I, K, L) 4 = m 4; rw [u4]; omega
      · show mTuple j₁ j₂ j₄ (I, K, L) 5 = m 5; rw [u5]; omega

/-- **The 6j sum over three free projections.** Only tuples with admissible 3j symbols contribute
(`sixJTerm_eq_zero`); admissibility fixes `m₃, m₅, m₆` from `m₁, m₂, m₄` and makes each `jᵢ - mᵢ`
even. So the sum over the `∏ (jᵢ + 1)`-element box reduces to `(j₁ + 1)(j₂ + 1)(j₄ + 1)` terms,
which `norm_num` unrolls without a kernel `decide` over the box. -/
lemma sixJSym_eq_triple (j₁ j₂ j₃ j₄ j₅ j₆ : ℕ) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = ∑ i ∈ Finset.range (j₁ + 1), ∑ k ∈ Finset.range (j₂ + 1),
      ∑ l ∈ Finset.range (j₄ + 1), sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ (mTuple j₁ j₂ j₄ (i, k, l)) := by
  have hinj : Set.InjOn (mTuple j₁ j₂ j₄)
      ↑(Finset.range (j₁ + 1) ×ˢ (Finset.range (j₂ + 1) ×ˢ Finset.range (j₄ + 1))) := by
    rintro ⟨i, k, l⟩ _ ⟨i', k', l'⟩ _ h
    obtain ⟨e0, e1, -, e3, -⟩ := mTuple_apply j₁ j₂ j₄ i k l
    obtain ⟨e0', e1', -, e3', -⟩ := mTuple_apply j₁ j₂ j₄ i' k' l'
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h3 := congrFun h 3
    rw [e0, e0'] at h0
    rw [e1, e1'] at h1
    rw [e3, e3'] at h3
    simp only [Prod.mk.injEq]
    omega
  have hR : (∑ i ∈ Finset.range (j₁ + 1), ∑ k ∈ Finset.range (j₂ + 1),
      ∑ l ∈ Finset.range (j₄ + 1), sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ (mTuple j₁ j₂ j₄ (i, k, l))) =
      ∑ m ∈ (Finset.range (j₁ + 1) ×ˢ (Finset.range (j₂ + 1) ×ˢ Finset.range (j₄ + 1))).image
        (mTuple j₁ j₂ j₄), sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m := by
    rw [Finset.sum_image hinj, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_product]
  rw [hR, sixJSym]
  calc ∑ m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆, sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m
      = ∑ m ∈ sixJBox j₁ j₂ j₃ j₄ j₅ j₆ ∩
          (Finset.range (j₁ + 1) ×ˢ (Finset.range (j₂ + 1) ×ˢ Finset.range (j₄ + 1))).image
            (mTuple j₁ j₂ j₄), sixJTerm j₁ j₂ j₃ j₄ j₅ j₆ m :=
        (Finset.sum_subset Finset.inter_subset_left fun m _ hn => by
          by_contra h; exact hn (Finset.mem_inter.mpr (sixJBox_triple_mem h))).symm
    _ = _ :=
        Finset.sum_subset Finset.inter_subset_right fun m _ hn => by
          by_contra h; exact hn (Finset.mem_inter.mpr (sixJBox_triple_mem h))

/-- Powers of a square root, reduced (`0 ≤ x`). -/
lemma sqrt_pow_red {x : ℝ} (hx : 0 ≤ x) :
    √x ^ 2 = x ∧ √x ^ 3 = x * √x ∧ √x ^ 4 = x ^ 2 ∧ √x ^ 5 = x ^ 2 * √x ∧ √x ^ 6 = x ^ 3 ∧
      √x ^ 7 = x ^ 3 * √x ∧ √x ^ 8 = x ^ 4 := by
  have h := Real.sq_sqrt hx
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show √x ^ 3 = √x ^ 2 * √x by ring, h]
  · rw [show √x ^ 4 = (√x ^ 2) ^ 2 by ring, h]
  · rw [show √x ^ 5 = (√x ^ 2) ^ 2 * √x by ring, h]
  · rw [show √x ^ 6 = (√x ^ 2) ^ 3 by ring, h]
  · rw [show √x ^ 7 = (√x ^ 2) ^ 3 * √x by ring, h]
  · rw [show √x ^ 8 = (√x ^ 2) ^ 4 by ring, h]

/-- Prove a square-root splitting `√n = a * (√p * …)` by squaring both sides. -/
macro "surd_split" : tactic => `(tactic|
  (rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)]; ring_nf;
   first | done | norm_num [Real.sq_sqrt]))

lemma sqrt_split_6 : √(6 : ℝ) = √2 * √3 := by surd_split
lemma sqrt_split_8 : √(8 : ℝ) = 2 * √2 := by surd_split
lemma sqrt_split_10 : √(10 : ℝ) = √2 * √5 := by surd_split
lemma sqrt_split_12 : √(12 : ℝ) = 2 * √3 := by surd_split
lemma sqrt_split_15 : √(15 : ℝ) = √3 * √5 := by surd_split
lemma sqrt_split_16 : √(16 : ℝ) = 4 := by surd_split
lemma sqrt_split_21 : √(21 : ℝ) = √3 * √7 := by surd_split
lemma sqrt_split_24 : √(24 : ℝ) = 2 * (√2 * √3) := by surd_split
lemma sqrt_split_32 : √(32 : ℝ) = 4 * √2 := by surd_split
lemma sqrt_split_35 : √(35 : ℝ) = √5 * √7 := by surd_split
lemma sqrt_split_48 : √(48 : ℝ) = 4 * √3 := by surd_split
lemma sqrt_split_96 : √(96 : ℝ) = 4 * (√2 * √3) := by surd_split
lemma sqrt_split_128 : √(128 : ℝ) = 8 * √2 := by surd_split
lemma sqrt_split_192 : √(192 : ℝ) = 8 * √3 := by surd_split
lemma sqrt_split_315 : √(315 : ℝ) = 3 * (√5 * √7) := by surd_split
lemma sqrt_split_480 : √(480 : ℝ) = 4 * (√2 * (√3 * √5)) := by surd_split

/-- Finish an identity between sums of products of square roots of small integers. -/
macro "surd_finish" : tactic => `(tactic| (
  try simp only [sqrt_split_6, sqrt_split_8, sqrt_split_10, sqrt_split_12, sqrt_split_15, sqrt_split_16, sqrt_split_21, sqrt_split_24, sqrt_split_32, sqrt_split_35, sqrt_split_48, sqrt_split_96, sqrt_split_128, sqrt_split_192, sqrt_split_315, sqrt_split_480];
  have h2 : (0:ℝ) < √2 := Real.sqrt_pos.mpr (by norm_num);
  have h3 : (0:ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num);
  have h5 : (0:ℝ) < √5 := Real.sqrt_pos.mpr (by norm_num);
  have h7 : (0:ℝ) < √7 := Real.sqrt_pos.mpr (by norm_num);
  field_simp;
  try ring_nf;
  obtain ⟨a2, a3, a4, a5, a6, a7, a8⟩ := sqrt_pow_red (show (0:ℝ) ≤ 2 by norm_num);
  obtain ⟨b2, b3, b4, b5, b6, b7, b8⟩ := sqrt_pow_red (show (0:ℝ) ≤ 3 by norm_num);
  obtain ⟨c2, c3, c4, c5, c6, c7, c8⟩ := sqrt_pow_red (show (0:ℝ) ≤ 5 by norm_num);
  obtain ⟨d2, d3, d4, d5, d6, d7, d8⟩ := sqrt_pow_red (show (0:ℝ) ≤ 7 by norm_num);
  try simp only [a2, a3, a4, a5, a6, a7, a8, b2, b3, b4, b5, b6, b7, b8, c2, c3, c4, c5, c6, c7, c8,
    d2, d3, d4, d5, d6, d7, d8];
  try ring_nf))

/-- **{2 2 1; 1 1 1} = -√5/10** (doubled `4 4 2 2 2 2`; no zero argument). -/
theorem sixJ_221_111 : sixJSym 4 4 2 2 2 2 = -√5 / 10 := by
  rw [sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    sixSum_eq_sum, sum_Icc_int, sixTerm, invFact, Finset.sum_range_succ, Fin.prod_univ_three,
    Nat.factorial]
  ring_nf
  surd_finish

/-- **{2 2 2; 1 1 1} = √21/30** (doubled `4 4 4 2 2 2`; no zero argument). -/
theorem sixJ_222_111 : sixJSym 4 4 4 2 2 2 = √21 / 30 := by
  rw [sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    sixSum_eq_sum, sum_Icc_int, sixTerm, invFact, Finset.sum_range_succ, Fin.prod_univ_three,
    Nat.factorial]
  ring_nf
  surd_finish

/-- **{2 2 2; 2 2 2} = -3/70** (doubled `4 4 4 4 4 4`; no zero argument). -/
theorem sixJ_222_222 : sixJSym 4 4 4 4 4 4 = -3 / 70 := by
  rw [sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    sixSum_eq_sum, sum_Icc_int, sixTerm, invFact, Finset.sum_range_succ, Fin.prod_univ_three,
    Nat.factorial]
  ring_nf
  surd_finish

/-- **{5/2 5/2 1; ½ ½ 2} = √35/30** (doubled `5 5 2 1 1 4`; no zero argument). -/
theorem sixJ_5h5h1_hh2 : sixJSym 5 5 2 1 1 4 = √35 / 30 := by
  rw [sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    sixSum_eq_sum, sum_Icc_int, sixTerm, invFact, Finset.sum_range_succ, Fin.prod_univ_three,
    Nat.factorial]
  ring_nf
  surd_finish

/-- **{5/2 5/2 1; 5/2 5/2 1} = -31/210** (doubled `5 5 2 5 5 2`; no zero argument). -/
theorem sixJ_5h5h1_5h5h1 : sixJSym 5 5 2 5 5 2 = -31 / 210 := by
  rw [sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    sixSum_eq_sum, sum_Icc_int, sixTerm, invFact, Finset.sum_range_succ, Fin.prod_univ_three,
    Nat.factorial]
  ring_nf
  surd_finish

end Lightlike.SixJAudit

