import Lightlike.SpinFoam.EPRLStateSum.NodeRecoupling
import Lightlike.PonzanoRegge.Parity
import Lightlike.PonzanoRegge.BEZero

/-!
# The recoupling matrix is symmetric under exchange of channels, and orthogonal on both sides

`sum_fourRecoupling_mul` is the orthogonality of the rows of `fourRecoupling j₁ j₂ j₃ j₄ k l`
(sum over the second-channel label `l`). The sum over the *first* channel label `k` is needed when
two 4-simplices share a tetrahedron and the tetrahedron label is summed once:

* `fourRecoupling_swap`: `⟨ι^{(13)l} | ι^{(12)k}⟩ = ⟨ι^{(12)k} | ι^{(13)l}⟩`, the matrix of the
  inverse change of channel is the transpose;
* `sum_fourRecoupling_mul_left`: `Σ_k R(k, l) R(k, l') = δ_{ll'}` on admissible `l`.
-/

open Finset Lightlike.Recoupling PhyslibAlpha.Sl2 Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

/-- The change of channel from `(13)(24)` back to `(12)(34)` is the transpose of the change from
`(12)(34)` to `(13)(24)`. -/
theorem fourRecoupling_swap (j₁ j₂ j₃ j₄ k l : ℕ) :
    fourRecoupling j₁ j₃ j₂ j₄ l k = fourRecoupling j₁ j₂ j₃ j₄ k l := by
  unfold fourRecoupling
  rw [sixJSym_flip₂₃ j₁ j₂ k j₄ j₃ l, mul_comm ((l : ℝ) + 1) ((k : ℝ) + 1)]
  have : j₃ + j₂ + l + k = j₂ + j₃ + k + l := by omega
  rw [this]

/-- **Orthogonality of the columns of the recoupling matrix**:
`Σ_k ⟨ι^{(12)k} | ι^{(13)l}⟩ ⟨ι^{(12)k} | ι^{(13)l'}⟩ = δ_{ll'}` for admissible `l` (triads
`(j₁ j₃ l)` and `(l j₂ j₄)`), `0` otherwise. The sum runs over `k ≤ j₁ + j₂`. -/
theorem sum_fourRecoupling_mul_left (j₁ j₂ j₃ j₄ l l' : ℕ) :
    ∑ k ∈ range (j₁ + j₂ + 1), fourRecoupling j₁ j₂ j₃ j₄ k l * fourRecoupling j₁ j₂ j₃ j₄ k l' =
      if l = l' ∧ Pentagon.Tri j₁ j₃ l ∧ Pentagon.Tri l j₂ j₄ then 1 else 0 := by
  have h := sum_fourRecoupling_mul j₁ j₃ j₂ j₄ l l'
  rw [← h]
  exact sum_congr rfl fun k _ => by
    rw [fourRecoupling_swap j₁ j₂ j₃ j₄ k l, fourRecoupling_swap j₁ j₂ j₃ j₄ k l']

/-- The 6j symbol of the recoupling matrix is invariant under the exchange of the two pairs of
legs `(j₁ j₂)(j₃ j₄) → (j₃ j₄)(j₁ j₂)`. -/
lemma sixJSym_swapPairs (j₁ j₂ j₃ j₄ k l : ℕ) :
    sixJSym j₃ j₄ k j₂ j₁ l = sixJSym j₁ j₂ k j₄ j₃ l := by
  rw [sj_swap12 j₄ j₃ k j₁ j₂ l, sj_flip12 j₁ j₂ k j₄ j₃ l]

/-- **The recoupling matrix under the exchange of the two pairs of legs**:
`R(j₃ j₄ j₁ j₂; k, l) = (-1)^((j₁+j₂+j₃+j₄)/2 + k + l) R(j₁ j₂ j₃ j₄; k, l)`. Both sides vanish
unless the four triads are even, in which case the exponent is an integer. -/
theorem fourRecoupling_swapPairs (j₁ j₂ j₃ j₄ k l : ℕ) :
    fourRecoupling j₃ j₄ j₁ j₂ k l =
      (-1) ^ ((j₁ + j₂ + j₃ + j₄) / 2 + k + l) * fourRecoupling j₁ j₂ j₃ j₄ k l := by
  by_cases hz : sixJSym j₁ j₂ k j₄ j₃ l = 0
  · unfold fourRecoupling
    rw [sixJSym_swapPairs, hz]
    simp
  · have hev : (j₁ + j₂ + k) % 2 = 0 ∧ (j₁ + j₃ + l) % 2 = 0 ∧ (j₄ + j₂ + l) % 2 = 0 ∧
        (j₄ + j₃ + k) % 2 = 0 := by
      by_contra hn
      apply hz
      refine Lightlike.PR.sixJSym_eq_zero_of_odd ?_
      omega
    unfold fourRecoupling
    rw [sixJSym_swapPairs]
    have e1 : (-1 : ℝ) ^ ((j₄ + j₁ + k + l) / 2) * (-1) ^ ((j₂ + j₃ + k + l) / 2) =
        (-1) ^ ((j₁ + j₂ + j₃ + j₄) / 2 + k + l) := by
      rw [← pow_add]
      congr 1
      omega
    have e2 : ((-1 : ℝ) ^ ((j₂ + j₃ + k + l) / 2)) * (-1) ^ ((j₂ + j₃ + k + l) / 2) = 1 :=
      negOnePow_mul_self _
    calc (-1 : ℝ) ^ ((j₄ + j₁ + k + l) / 2) * √(((k : ℝ) + 1) * ((l : ℝ) + 1)) *
          sixJSym j₁ j₂ k j₄ j₃ l
        = ((-1 : ℝ) ^ ((j₄ + j₁ + k + l) / 2) * (-1) ^ ((j₂ + j₃ + k + l) / 2)) *
          ((-1) ^ ((j₂ + j₃ + k + l) / 2) * √(((k : ℝ) + 1) * ((l : ℝ) + 1)) *
            sixJSym j₁ j₂ k j₄ j₃ l) := by
          linear_combination (-((-1 : ℝ) ^ ((j₄ + j₁ + k + l) / 2) * √(((k : ℝ) + 1) * ((l : ℝ) + 1)) *
            sixJSym j₁ j₂ k j₄ j₃ l)) * e2
      _ = _ := by rw [e1]

end Lightlike.SpinFoam.EPRLStateSum
