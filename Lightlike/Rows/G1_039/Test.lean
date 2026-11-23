import Lightlike.Rows.G1_039.Classification

/-! Sanity checks for G1-039: the classification theorem uses only the standard axioms. -/

open Lightlike.Rows.G1_039

#print axioms exists_bianchiType
#print axioms numeral_surjective

example : (BianchiType.VI (-1)).numeral = 3 := by simp [BianchiType.numeral]
example : (BianchiType.VII 2).numeral = 7 := rfl
