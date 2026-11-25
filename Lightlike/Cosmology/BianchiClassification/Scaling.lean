import Lightlike.Cosmology.BianchiClassification.Diagonalise

/-!
# Diagonal rescalings and permutations of a diagonal Bianchi bracket

For diagonal `n` the rescaling of the basis `e_i ↦ d_i e_i` gives `n_i ↦ n_i d_i² / (d₀ d₁ d₂)`
and `a_i ↦ a_i / d_i`.  The rotation `-S` through the transposition `S` of two basis vectors
interchanges two diagonal entries of `n` (and the matching entries of `a`, up to sign).

## Main results

* `Lightlike.Cosmology.BianchiClassification.bracketIso_diagonal_scale`
* `Lightlike.Cosmology.BianchiClassification.bracketIso_swap01`, `bracketIso_swap12`

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Cosmology.BianchiClassification

open Matrix

/-- Rescaling the basis vectors of a diagonal Bianchi bracket by `d_i ≠ 0`. -/
theorem bracketIso_diagonal_scale (l : Fin 3 → ℝ) (a : V3) (d : Fin 3 → ℝ) (hd : ∀ i, d i ≠ 0) :
    BracketIso (diagonal l) a (diagonal fun i => l i * d i ^ 2 / (d 0 * d 1 * d 2))
      (fun i => a i / d i) := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  refine ⟨diagonal d, ?_, fun x y => ?_⟩
  · rw [Matrix.det_diagonal, Fin.prod_univ_three]
    exact mul_ne_zero (mul_ne_zero h0 h1) h2
  · unfold bracket
    ext i
    fin_cases i <;>
    · simp [crossProduct, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three]
      field_simp

/-- Interchanging the first two basis vectors (with a sign, so that `det = 1`). -/
theorem bracketIso_swap01 (l : Fin 3 → ℝ) (a : V3) :
    BracketIso (diagonal l) a (diagonal ![l 1, l 0, l 2]) ![-a 1, -a 0, -a 2] := by
  refine ⟨!![0, -1, 0; -1, 0, 0; 0, 0, -1], ?_, fun x y => ?_⟩
  · simp [Matrix.det_fin_three]
  · unfold bracket
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal]
    fin_cases i <;>
    · simp [crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring

/-- Interchanging the last two basis vectors (with a sign, so that `det = 1`). -/
theorem bracketIso_swap12 (l : Fin 3 → ℝ) (a : V3) :
    BracketIso (diagonal l) a (diagonal ![l 0, l 2, l 1]) ![-a 0, -a 2, -a 1] := by
  refine ⟨!![-1, 0, 0; 0, 0, -1; 0, -1, 0], ?_, fun x y => ?_⟩
  · simp [Matrix.det_fin_three]
  · unfold bracket
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Matrix.mulVec_diagonal]
    fin_cases i <;>
    · simp [crossProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring

end Lightlike.Cosmology.BianchiClassification

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bracketIso_diagonal_scale := _root_.Lightlike.Cosmology.BianchiClassification.bracketIso_diagonal_scale
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bracketIso_swap01 := _root_.Lightlike.Cosmology.BianchiClassification.bracketIso_swap01
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_039.bracketIso_swap12 := _root_.Lightlike.Cosmology.BianchiClassification.bracketIso_swap12
