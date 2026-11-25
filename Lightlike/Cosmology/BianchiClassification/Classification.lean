import Lightlike.Cosmology.BianchiClassification.ClassB4

/-!
# The Bianchi classification of three-dimensional real Lie algebras

Every Bianchi bracket `(n, a)` (`n` symmetric, `n a = 0`) is isomorphic to a bracket with
diagonal `n` and `a = (0, 0, α)` taken from an explicit list, the Bianchi types
(Ellis–MacCallum normalisation):

* class A (`a = 0`): `I`, `II`, `VI₀`, `VII₀`, `VIII`, `IX`;
* class B (`a ≠ 0`): `IV`, `V`, `VI_h` (`h < 0`) and `VII_h` (`h > 0`), where
  `h = α² / (n₁ n₂)`; type `III` is `VI_{-1}`.

## Main definitions

* `Lightlike.Rows.G1_039.BianchiType`: the types, with the families `VI h`, `VII h`.
* `Lightlike.Rows.G1_039.BianchiType.Valid`, `.n`, `.a`, `.IsClassA`, `.numeral`.

## Main results

* `Lightlike.Rows.G1_039.exists_bianchiType`: the classification theorem.
* `Lightlike.Rows.G1_039.numeral_surjective`: the Roman numerals `1, …, 9` all occur and no
  other (nine types `I`–`IX`).

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Rows.G1_039

open Matrix

/-- The Bianchi types.  `VI h` and `VII h` are the families (admissible for `h ≤ 0` resp.
`0 ≤ h`, see `BianchiType.Valid`); `VI 0` and `VII 0` are the class A types `VI₀`, `VII₀`, and
type `III` is `VI (-1)`. -/
inductive BianchiType : Type
  | I | II | IV | V | VIII | IX
  | VI (h : ℝ)
  | VII (h : ℝ)

namespace BianchiType

/-- Admissible parameters: `h ≤ 0` for `VI h`, `0 ≤ h` for `VII h`. -/
def Valid : BianchiType → Prop
  | VI h => h ≤ 0
  | VII h => 0 ≤ h
  | _ => True

/-- The diagonal of the matrix `n` of the normal form. -/
def n : BianchiType → Fin 3 → ℝ
  | I => ![0, 0, 0]
  | II => ![1, 0, 0]
  | IV => ![1, 0, 0]
  | V => ![0, 0, 0]
  | VIII => ![1, 1, -1]
  | IX => ![1, 1, 1]
  | VI _ => ![1, -1, 0]
  | VII _ => ![1, 1, 0]

/-- The vector `a` of the normal form (`a = (0, 0, √|h|)` for the families). -/
noncomputable def a : BianchiType → V3
  | I => 0
  | II => 0
  | VIII => 0
  | IX => 0
  | IV => ![0, 0, 1]
  | V => ![0, 0, 1]
  | VI h => ![0, 0, Real.sqrt (-h)]
  | VII h => ![0, 0, Real.sqrt h]

/-- Class A types (`a = 0`). -/
def IsClassA : BianchiType → Prop
  | I | II | VIII | IX => True
  | IV | V => False
  | VI h => h = 0
  | VII h => h = 0

/-- Class A is exactly `a = 0` for admissible parameters. -/
theorem isClassA_iff (T : BianchiType) (hT : T.Valid) : T.IsClassA ↔ T.a = 0 := by
  cases T with
  | I => simp [IsClassA, a]
  | II => simp [IsClassA, a]
  | VIII => simp [IsClassA, a]
  | IX => simp [IsClassA, a]
  | IV =>
    simp only [IsClassA, a, false_iff]
    intro h
    have := congrFun h 2
    simp at this
  | V =>
    simp only [IsClassA, a, false_iff]
    intro h
    have := congrFun h 2
    simp at this
  | VI h =>
    have hh : h ≤ 0 := hT
    simp only [IsClassA, a]
    constructor
    · intro h0; subst h0; ext i; fin_cases i <;> simp
    · intro h0
      have := congrFun h0 2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply,
        Real.sqrt_eq_zero'] at this
      linarith
  | VII h =>
    have hh : 0 ≤ h := hT
    simp only [IsClassA, a]
    constructor
    · intro h0; subst h0; ext i; fin_cases i <;> simp
    · intro h0
      have := congrFun h0 2
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply,
        Real.sqrt_eq_zero'] at this
      linarith

/-- The Roman numeral of the type, `1, …, 9`; `VI (-1)` is type `III`. -/
noncomputable def numeral : BianchiType → ℕ
  | I => 1
  | II => 2
  | IV => 4
  | V => 5
  | VIII => 8
  | IX => 9
  | VI h => if h = -1 then 3 else 6
  | VII _ => 7

end BianchiType

/-- Symmetric `n` diagonalised with `a = 0 ↔ a' = 0` (strengthening of `exists_diagonalisation`). -/
theorem exists_diagonalisation_iff (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a : V3) :
    ∃ (d : Fin 3 → ℝ) (a' : V3), BracketIso n a (diagonal d) a' ∧
      (n.mulVec a = 0 → (diagonal d).mulVec a' = 0) ∧ (a = 0 ↔ a' = 0) := by
  obtain ⟨U, d, hU, hd⟩ := exists_orthogonal_diagonal n hn
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hdet : Uᵀ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hP := bracketIso_transform n a Uᵀ hdet
  rw [Matrix.transpose_transpose, hd, Matrix.inv_eq_right_inv hU, ← Matrix.diagonal_smul] at hP
  have hUa : U.mulVec (Uᵀ.mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  refine ⟨(Uᵀ.det)⁻¹ • d, Uᵀ.mulVec a, hP, ?_, ?_⟩
  · intro h0
    rw [Matrix.diagonal_smul, Matrix.smul_mulVec, ← hd, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hUa, h0, Matrix.mulVec_zero, smul_zero]
  · constructor
    · intro h0
      rw [h0, Matrix.mulVec_zero]
    · intro h0
      rw [← hUa, h0, Matrix.mulVec_zero]

/-- **Bianchi classification** (class A/B, types I–IX, families VI_h and VII_h): every
three-dimensional real Lie algebra given by Bianchi data `(n, a)` with `n` symmetric and
`n a = 0` is isomorphic to the normal form of an admissible Bianchi type, and the type is in
class A exactly when `a = 0`. -/
theorem exists_bianchiType (n : Matrix (Fin 3) (Fin 3) ℝ) (hn : n.IsSymm) (a : V3)
    (hna : n.mulVec a = 0) :
    ∃ T : BianchiType, T.Valid ∧ BracketIso n a (diagonal T.n) T.a ∧ (a = 0 ↔ T.IsClassA) := by
  obtain ⟨d, a', hiso, hna', hiff⟩ := exists_diagonalisation_iff n hn a
  have hna'' := hna' hna
  by_cases ha : a = 0
  · have ha' : a' = 0 := hiff.mp ha
    subst ha'
    obtain ⟨t, ht, hiso2⟩ := exists_classA_normal d
    have h := hiso.trans hiso2
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.I, trivial, h, by simp [BianchiType.IsClassA, ha]⟩
    · exact ⟨.II, trivial, h, by simp [BianchiType.IsClassA, ha]⟩
    · refine ⟨.VI 0, le_refl _, ?_, by simp [BianchiType.IsClassA, ha]⟩
      have e : BianchiType.a (.VI 0) = 0 := by
        ext i; fin_cases i <;> simp [BianchiType.a]
      rw [e]; exact h
    · refine ⟨.VII 0, le_refl _, ?_, by simp [BianchiType.IsClassA, ha]⟩
      have e : BianchiType.a (.VII 0) = 0 := by
        ext i; fin_cases i <;> simp [BianchiType.a]
      rw [e]; exact h
    · exact ⟨.VIII, trivial, h, by simp [BianchiType.IsClassA, ha]⟩
    · exact ⟨.IX, trivial, h, by simp [BianchiType.IsClassA, ha]⟩
  · have ha' : a' ≠ 0 := fun h => ha (hiff.mpr h)
    have hla : ∀ i, d i * a' i = 0 := by
      intro i
      have := congrFun hna'' i
      simpa [Matrix.mulVec_diagonal] using this
    obtain ⟨t, α, ht, hiso2⟩ := exists_classB_normal d a' hla ha'
    have h := hiso.trans hiso2
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hα⟩ | ⟨rfl, hα⟩
    · exact ⟨.V, trivial, h, by simp [BianchiType.IsClassA, ha]⟩
    · exact ⟨.IV, trivial, h, by simp [BianchiType.IsClassA, ha]⟩
    · refine ⟨.VI (-(α ^ 2)), (show -(α ^ 2) ≤ 0 by nlinarith [sq_nonneg α]), ?_, ?_⟩
      · have e : BianchiType.a (.VI (-(α ^ 2))) = ![0, 0, α] := by
          simp [BianchiType.a, Real.sqrt_sq hα.le]
        rw [e]; exact h
      · simp only [BianchiType.IsClassA]
        constructor
        · intro h0; exact absurd h0 ha
        · intro h0
          have : α ^ 2 = 0 := by linarith
          exact absurd (pow_eq_zero_iff (by norm_num) |>.mp this) hα.ne'
    · refine ⟨.VII (α ^ 2), sq_nonneg α, ?_, ?_⟩
      · have e : BianchiType.a (.VII (α ^ 2)) = ![0, 0, α] := by
          simp [BianchiType.a, Real.sqrt_sq hα.le]
        rw [e]; exact h
      · simp only [BianchiType.IsClassA]
        constructor
        · intro h0; exact absurd h0 ha
        · intro h0
          exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h0) hα.ne'

/-- The nine Bianchi types: every Roman numeral `1, …, 9` is the numeral of an admissible type
(`III` being `VI (-1)`), and no other numeral occurs. -/
theorem numeral_surjective :
    (∀ T : BianchiType, T.Valid → 1 ≤ T.numeral ∧ T.numeral ≤ 9) ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ 9 → ∃ T : BianchiType, T.Valid ∧ T.numeral = k := by
  refine ⟨?_, ?_⟩
  · intro T _
    cases T <;> simp only [BianchiType.numeral] <;> (try split_ifs) <;> omega
  · intro k h1 h9
    have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.I, trivial, rfl⟩
    · exact ⟨.II, trivial, rfl⟩
    · exact ⟨.VI (-1), by norm_num [BianchiType.Valid], by simp [BianchiType.numeral]⟩
    · exact ⟨.IV, trivial, rfl⟩
    · exact ⟨.V, trivial, rfl⟩
    · exact ⟨.VI 0, le_refl _, by simp [BianchiType.numeral]⟩
    · exact ⟨.VII 0, le_refl _, rfl⟩
    · exact ⟨.VIII, trivial, rfl⟩
    · exact ⟨.IX, trivial, rfl⟩

end Lightlike.Rows.G1_039
