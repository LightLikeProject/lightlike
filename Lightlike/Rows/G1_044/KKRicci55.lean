import Lightlike.Rows.G1_044.KKDiv

/-!
# The Ricci tensor of the Kaluza-Klein metric: the `55` component (G1-044)

At a point over `U` where `A = 0`, `R̂_{55} = -φ □φ - ¼ φ⁴ F_a{}ᶜ F_c{}ᵃ` (`ricci_kk_55`), the dilaton equation.
The proof applies `ricci_of_christoffel_add_cov` to the product metric `kkRef g` and the difference tensor `kkDiff`.

Supporting file for the row G1-044 (Kaluza-Klein reduction).
-/

open Matrix Filter
open scoped ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Lightlike

namespace KK

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {A : (Fin n → ℝ) → Fin n → ℝ}
  {φ : (Fin n → ℝ) → ℝ} {U : Set (Fin n → ℝ)} {x : Fin (n + 1) → ℝ}

/-- The inverse of a symmetric matrix is symmetric. -/
theorem inv_symm_of (hgs : ∀ y a b, g y a b = g y b a) (p : Fin n → ℝ) (c d : Fin n) :
    (g p)⁻¹ c d = (g p)⁻¹ d c := by
  have hT : ((g p)⁻¹)ᵀ = (g p)⁻¹ := by
    have : (g p)ᵀ = g p := by ext i j; exact hgs p j i
    rw [Matrix.transpose_nonsing_inv, this]
  simpa [Matrix.transpose_apply] using (congrFun (congrFun hT c) d).symm

/-- **Trace of the difference tensor on a base index**: `Σ_ρ (Γ̂^ρ_{ρa} - Γ̃^ρ_{ρa}) = φ⁻¹ ∂_a φ`. -/
theorem sum_kkDiff_trace_a (hgs : ∀ y a b, g y a b = g y b a) (h : KKReg g A φ (proj x)) (a : Fin n) :
    ∑ l, kkDiff g A φ l l a.castSucc x = (φ (proj x))⁻¹ * pd a φ (proj x) := by
  rw [Fin.sum_univ_castSucc, kkDiff_symm hgs (Fin.last n) (Fin.last n) a.castSucc, kkDiff_5a5 h a]
  simp only [kkDiff_cab h]
  exact trace_a (inv_symm_of hgs _) a

/-- **Trace of the difference tensor on the fifth index**: `Σ_ρ (Γ̂^ρ_{ρ5} - Γ̃^ρ_{ρ5}) = 0`. -/
theorem sum_kkDiff_trace_five (hgs : ∀ y a b, g y a b = g y b a) (h : KKReg g A φ (proj x)) :
    ∑ l, kkDiff g A φ l l (Fin.last n) x = 0 := by
  rw [Fin.sum_univ_castSucc, kkDiff_555 h]
  simp only [kkDiff_ca5 h]
  exact trace_five (inv_symm_of hgs _)

end KK

end Lightlike
