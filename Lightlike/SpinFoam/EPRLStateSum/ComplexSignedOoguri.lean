import Lightlike.SpinFoam.EPRLStateSum.ComplexSignTypes
import Lightlike.SpinFoam.EPRLStateSum.ComplexOoguriShape

/-!
# The EPRL (γ = 1) tetrahedron-label sum as a sign-twisted Ooguri sum, with the sign explicit

`complex_tetSum_labels_ooguri` writes the tetrahedron-label sum of the glued EPRL vertex weights as a
sum over virtual spins `L` of `Π_t [triangle constraints] · (Π_s recoupSign) · Π_s simpW (extL K col L) s`.
The triangle constraints contain the parity conditions, so on their support every tetrahedron is
admissible (`TetAdm`), and `prod_recoupSign_eq_tri_mul_types` replaces `Π_s recoupSign` by the explicit
sign `eprlGlobalSign` (a triangle part and a product over tetrahedra of the position sign types).
This is the sign-twisted form of the equality of the EPRL (γ = 1) amplitude with the Ooguri model.
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- **The explicit global sign**: `(-1)^(Σ_s triPart) * Π_t (-1)^(εU_t e₁(t) + εV_t e₃(t))`. -/
noncomputable def eprlGlobalSign (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) : ℝ :=
  (-1 : ℝ) ^ (∑ s : K.simps, triPart (complexJ K col s)) *
    ∏ t : K.tets, (-1 : ℝ) ^ ((sgnU (e (t, false)).2 + sgnU (e (t, true)).2) * tetE1 K col L e t +
      (sgnV (e (t, false)).2 + sgnV (e (t, true)).2) * tetE3 K col L e t)

/-- The triangle constraints of a tetrahedron (with parity) give its admissibility. -/
theorem tetAdm_of_tri (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets)
    (h : Lightlike.Pentagon.Tri
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
              (L t) ∧
            Lightlike.Pentagon.Tri (L t)
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))) :
    TetAdm K col L e t := by
  obtain ⟨⟨h1, -⟩, ⟨h2, -⟩⟩ := h
  refine ⟨Nat.even_iff.2 h1, Nat.even_iff.2 ?_⟩
  omega

/-- **The tetrahedron-label sum of the EPRL weight at `γ = 1` with the explicit sign**: the sign
`Π_s recoupSign` of `complex_tetSum_labels_ooguri` is replaced by `eprlGlobalSign`. The right-hand side
is the Ooguri vertex factor of the coloured complex `(col, L)` times an explicit sign. -/
theorem complex_tetSum_labels_ooguri_explicit (K : Complex4 V) (col : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    ∑ i ∈ Fintype.piFinset (fun t : K.tets =>
        range (complexJ K col (e (t, false)).1 (e (t, false)).2
          ((e (t, false)).2.succAbove 0) +
          complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1) + 1)),
      tetSumTerm K col i =
    ∑ L ∈ Fintype.piFinset (fun t : K.tets =>
        simpBox (complexJ K col (e (t, false)).1) (e (t, false)).2 ∩
          simpBox (complexJ K col (e (t, true)).1) (e (t, true)).2),
      (∏ t : K.tets, if
            Lightlike.Pentagon.Tri
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
              (L t) ∧
            Lightlike.Pentagon.Tri (L t)
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
          then (1 : ℝ) else 0) *
        (eprlGlobalSign K col L e * ∏ s : K.simps, simpW (extL K col L) s.1) := by
  rw [complex_tetSum_labels_ooguri K col e he]
  refine Finset.sum_congr rfl fun L _ => ?_
  by_cases hall : ∀ t : K.tets,
      Lightlike.Pentagon.Tri
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
        (L t) ∧
      Lightlike.Pentagon.Tri (L t)
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
  · congr 2
    exact prod_recoupSign_eq_tri_mul_types K col L e he fun t => tetAdm_of_tri K col L e t (hall t)
  · push_neg at hall
    obtain ⟨t, ht⟩ := hall
    have : (∏ t : K.tets, if
            Lightlike.Pentagon.Tri
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
              (L t) ∧
            Lightlike.Pentagon.Tri (L t)
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
          then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ t) (if_neg (by tauto))
    rw [this, zero_mul, zero_mul]

end Lightlike.SpinFoam.EPRLStateSum
