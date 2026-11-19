import Lightlike.Gauge.ReducedForm

/-!
# Trust check for the reduced symplectic form

A line `D = ℝ v` in a symplectic space is isotropic (`σ(v, v) = 0`), so the hypotheses of
`reducedForm_nondegenerate` are met by every line of every finite-dimensional symplectic space, so the theorem is not
vacuous (the standard symplectic form of Physlib's phase space is `Lightlike.Gauge.isSymplecticForm_gradForm`).
-/

open ClassicalMechanics

namespace Lightlike.Gauge

variable {E : Type} [AddCommGroup E] [Module ℝ E] {σ : LinearMap.BilinForm ℝ E}

/-- **A line is isotropic** for an alternating form. -/
theorem isIsotropicSub_span_singleton (hσ : IsSymplecticForm σ) (v : E) :
    IsIsotropicSub σ (Submodule.span ℝ {v}) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
  show σ (d • v) (c • v) = 0
  simp [hσ.alt v]

/-- **The reduction of a symplectic space by a line is symplectic**: the hypotheses of the nondegeneracy theorem hold
for every line of a finite-dimensional symplectic space. -/
theorem reducedForm_line_nondegenerate [FiniteDimensional ℝ E] (hσ : IsSymplecticForm σ) (v : E) :
    (reducedForm (LinearMap.BilinForm.IsAlt.isRefl hσ.alt) (isIsotropicSub_span_singleton hσ v)).Nondegenerate :=
  reducedForm_nondegenerate hσ.nondeg _ _

end Lightlike.Gauge
