import Lightlike.GR.ColourOrdered

/-!
# Four-point Mandelstam variables in spinor-helicity form

Row G3-261 (T-PG7, double copy at tree level). For four massless particles with angle spinors
`lt i` and square spinors `l i` (the conventions of `Lightlike.SpinorHelicity`: the amplitude
`parkeTaylor` takes the angle spinors `lt`, and momentum conservation is `Conserved l lt`),
the Mandelstam variable of the pair `i, j` is `s_{ij} = ⟨i j⟩ [j i]` (`sBr`, Elvang-Huang (2.39),
`mandelstam_nullMom`).

* `sBr_symm`: `s_{ij} = s_{ji}`.
* `sBr_sum_zero`: with momentum conservation, `s₁₂ + s₁₃ + s₁₄ = 0`, i.e. `s + t + u = 0`.
* `sBr_zero_one_eq`, `sBr_zero_two_eq`, `sBr_zero_three_eq`: `s₁₂ = s₃₄`, `s₁₃ = s₂₄`, `s₁₄ = s₂₃`.

These are the kinematic facts the four-point BCJ and KLT relations of the same row use.

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, (2.39).
-/

noncomputable section

namespace Lightlike.GR.KLTBCJRelations

open Lightlike.SpinorHelicity

/-- The Mandelstam variable `s_{ij} = ⟨i j⟩ [j i]` of two massless particles with angle spinors
`lt i`, `lt j` and square spinors `l i`, `l j` (Elvang-Huang (2.39)). Particles are labelled
`0, 1, 2, 3` (the particles `1, 2, 3, 4` of the literature). -/
def sBr (l lt : Fin 4 → Fin 2 → ℂ) (i j : Fin 4) : ℂ :=
  angleBr (lt i) (lt j) * squareBr (l j) (l i)

/-- `s_{ij}` is symmetric in `i` and `j`. -/
theorem sBr_symm (l lt : Fin 4 → Fin 2 → ℂ) (i j : Fin 4) : sBr l lt i j = sBr l lt j i := by
  simp only [sBr, angleBr_eq, squareBr_eq]; ring

/-- `s_{ii} = 0`. -/
theorem sBr_self (l lt : Fin 4 → Fin 2 → ℂ) (i : Fin 4) : sBr l lt i i = 0 := by
  simp only [sBr, angleBr_eq]; ring

/-- **Momentum conservation at a vertex**: for each particle `k`, `Σ_i s_{ki} = 0`. -/
theorem sBr_row_sum {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt) (k : Fin 4) :
    ∑ i, sBr l lt k i = 0 := by
  have := contract_conserved h (lt k) (l k)
  simpa only [sBr] using this

/-- **`s + t + u = 0`**: with momentum conservation, `s₁₂ + s₁₃ + s₁₄ = 0`. -/
theorem sBr_sum_zero {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt) :
    sBr l lt 0 1 + sBr l lt 0 2 + sBr l lt 0 3 = 0 := by
  have := sBr_row_sum h 0
  simpa only [Fin.sum_univ_four, sBr_self, zero_add] using this

/-- With momentum conservation, `s₁₂ = s₃₄`. -/
theorem sBr_zero_one_eq {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt) :
    sBr l lt 0 1 = sBr l lt 2 3 := by
  have h0 := sBr_row_sum h 0
  have h1 := sBr_row_sum h 1
  have h2 := sBr_row_sum h 2
  have h3 := sBr_row_sum h 3
  simp only [Fin.sum_univ_four, sBr_self] at h0 h1 h2 h3
  rw [sBr_symm l lt 1 0, sBr_symm l lt 2 0, sBr_symm l lt 3 0, sBr_symm l lt 2 1,
    sBr_symm l lt 3 1, sBr_symm l lt 3 2] at *
  linear_combination (h0 + h1 - h2 - h3) / 2

/-- With momentum conservation, `s₁₃ = s₂₄`. -/
theorem sBr_zero_two_eq {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt) :
    sBr l lt 0 2 = sBr l lt 1 3 := by
  have h0 := sBr_row_sum h 0
  have h1 := sBr_row_sum h 1
  have h2 := sBr_row_sum h 2
  have h3 := sBr_row_sum h 3
  simp only [Fin.sum_univ_four, sBr_self] at h0 h1 h2 h3
  rw [sBr_symm l lt 1 0, sBr_symm l lt 2 0, sBr_symm l lt 3 0, sBr_symm l lt 2 1,
    sBr_symm l lt 3 1, sBr_symm l lt 3 2] at *
  linear_combination (h0 - h1 + h2 - h3) / 2

/-- With momentum conservation, `s₁₄ = s₂₃`. -/
theorem sBr_zero_three_eq {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt) :
    sBr l lt 0 3 = sBr l lt 1 2 := by
  have h0 := sBr_row_sum h 0
  have h1 := sBr_row_sum h 1
  have h2 := sBr_row_sum h 2
  have h3 := sBr_row_sum h 3
  simp only [Fin.sum_univ_four, sBr_self] at h0 h1 h2 h3
  rw [sBr_symm l lt 1 0, sBr_symm l lt 2 0, sBr_symm l lt 3 0, sBr_symm l lt 2 1,
    sBr_symm l lt 3 1, sBr_symm l lt 3 2] at *
  linear_combination (h0 - h1 - h2 + h3) / 2

end Lightlike.GR.KLTBCJRelations

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr := _root_.Lightlike.GR.KLTBCJRelations.sBr
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr_row_sum := _root_.Lightlike.GR.KLTBCJRelations.sBr_row_sum
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr_self := _root_.Lightlike.GR.KLTBCJRelations.sBr_self
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr_sum_zero := _root_.Lightlike.GR.KLTBCJRelations.sBr_sum_zero
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr_symm := _root_.Lightlike.GR.KLTBCJRelations.sBr_symm
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr_zero_one_eq := _root_.Lightlike.GR.KLTBCJRelations.sBr_zero_one_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr_zero_three_eq := _root_.Lightlike.GR.KLTBCJRelations.sBr_zero_three_eq
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G3_261.sBr_zero_two_eq := _root_.Lightlike.GR.KLTBCJRelations.sBr_zero_two_eq
