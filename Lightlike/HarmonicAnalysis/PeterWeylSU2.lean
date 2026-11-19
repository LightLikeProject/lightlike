import Lightlike.HarmonicAnalysis.CharacterOrthogonality
import Lightlike.HarmonicAnalysis.RepresentationBridge
import Lightlike.Spin4.SO4

/-!
# Check of Schur orthogonality on `SU(2)`

The spin-`n/2` representations of `SU(2)` (`Lightlike.SU2.spinRep`, irreducible by
`Lightlike.SU2.spinRepresentation_isIrreducible`) are irreducible unitary matrix representations in the sense
of the Peter–Weyl files (`su2Spin`, `su2Spin_isIrreducible`), pairwise inequivalent
(`su2Spin_not_equivalent`). So for a Haar probability measure `μ` on `SU(2)`:

* `su2_character_orthogonality`: `∫ χ_n · conj χ_m dμ = δ_{nm}` for the characters `χ_n = tr ∘ spinRep n`;
* `su2_schur_orthogonality`: `∫ D^n_{ij} · conj D^n_{lk} dμ = δ_{il} δ_{jk} / (n + 1)`.

Checks of the milestone; no catalogue entry.
-/

open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

open UnitaryMatrixRep

/-- The spin-`n/2` representation of `SU(2)` as a continuous unitary matrix representation. -/
def su2Spin (n : ℕ) : UnitaryMatrixRep SU2 (Fin (n + 1)) := ⟨SU2.spinRep n, SU2.continuous_spinRep⟩

lemma su2Spin_mat (n : ℕ) (g : SU2) : (su2Spin n).mat g = SU2.spinMat n g := rfl

/-- The spin representations are irreducible. -/
theorem su2Spin_isIrreducible (n : ℕ) : (su2Spin n).IsIrreducible := by
  rw [isIrreducible_iff_toRepresentation]
  have h : (su2Spin n).toRepresentation = SU2.spinRepresentation n := MonoidHom.ext fun g => rfl
  rw [h]
  exact SU2.spinRepresentation_isIrreducible

/-- Spin representations of different dimension are inequivalent. -/
theorem su2Spin_not_equivalent {n m : ℕ} (h : n ≠ m) : ¬ Equivalent (su2Spin n) (su2Spin m) := by
  rintro ⟨e, -⟩
  have h1 := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  omega

variable (μ : Measure SU2) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

/-- **Check: Schur orthogonality of the characters of `SU(2)`.** -/
theorem su2_character_orthogonality (n m : ℕ) :
    ∫ g, (su2Spin n).character g * starRingEnd ℂ ((su2Spin m).character g) ∂μ =
      if n = m then 1 else 0 := by
  by_cases h : n = m
  · subst h
    rw [if_pos rfl]
    exact character_orthogonality_eq μ (su2Spin_isIrreducible n)
  · rw [if_neg h]
    exact character_orthogonality_ne μ (su2Spin_isIrreducible n) (su2Spin_isIrreducible m)
      (su2Spin_not_equivalent h)

/-- **Check: Schur orthogonality of the matrix coefficients of the spin-`n/2` representation.** -/
theorem su2_schur_orthogonality (n : ℕ) (i j k l : Fin (n + 1)) :
    ∫ g : SU2, SU2.spinMat n g i j * starRingEnd ℂ (SU2.spinMat n g l k) ∂μ =
      if i = l ∧ j = k then 1 / ((n : ℂ) + 1) else 0 := by
  have h := schur_orthogonality_eq μ (su2Spin_isIrreducible n) i j k l
  simpa [su2Spin_mat] using h

end

end Lightlike.HarmonicAnalysis
