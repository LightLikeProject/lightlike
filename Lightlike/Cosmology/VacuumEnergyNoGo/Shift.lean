import Mathlib

/-!
# Weinberg's no-go theorem: vacua of a constant-field potential and field-independent shifts

A Lorentz-invariant vacuum of a field theory with scalar fields `φ : ι → ℝ` has constant fields, and
its stress tensor is `T_{μν} = -V(φ) g_{μν}` (the vacuum energy density is `ρ = V(φ)`); the field
equations say that `φ` is a stationary point of the potential `V`. This file formalises that setting
and the first half of Weinberg's no-go theorem: a *field-independent* adjustment `V ↦ V + c` of the
vacuum energy leaves the vacua unchanged and moves every vacuum energy by the same `c`, so it makes
the energy vanish for all vacua of `V` only if all of them have the same energy, and for a single
vacuum only for the one value `c = -V(φ)`, which depends on the parameters of `V`: a tuning.

## Main results

* `IsVacuum`: a stationary point of a differentiable potential.
* `isVacuum_add_const`: a constant shift does not change the vacua.
* `vacuumEnergy_add_const`: it shifts the vacuum energy by the constant.
* `no_constant_adjustment`: two vacua of different energy cannot both be cancelled by one constant.
* `constant_adjustment_unique`: at one vacuum, the cancelling constant is `-V(φ)` and nothing else.

## References

* `padilla-2015`, Section 3.2 (Weinberg's no-go theorem; the table of contents of the arXiv text
  confirms the section, and the formulation here is the one of Weinberg, Rev. Mod. Phys. 61 (1989),
  as we state it ourselves).
-/

namespace Lightlike.Cosmology.VacuumEnergyNoGo

variable {ι : Type*} [Fintype ι]

/-- **A vacuum of the potential `V`** on the space of constant scalar fields `ι → ℝ`: `V` is
differentiable at `φ` and `φ` is a stationary point. For constant fields in a Poincaré-invariant
vacuum the field equations reduce to `∂V/∂φᵢ = 0`; the stress tensor is `-V(φ) g`
(compare `cosmoT`), so the vacuum energy density is `V φ`. -/
def IsVacuum (V : (ι → ℝ) → ℝ) (φ : ι → ℝ) : Prop :=
  DifferentiableAt ℝ V φ ∧ fderiv ℝ V φ = 0

/-- The vacuum energy density of the vacuum `φ`: the value of the potential. -/
def vacuumEnergy (V : (ι → ℝ) → ℝ) (φ : ι → ℝ) : ℝ := V φ

/-- The potential `V` shifted by a field-independent constant `c`. -/
def shiftPot (V : (ι → ℝ) → ℝ) (c : ℝ) : (ι → ℝ) → ℝ := fun x => V x + c

/-- **A field-independent shift does not change the vacua.** -/
theorem isVacuum_add_const (V : (ι → ℝ) → ℝ) (c : ℝ) (φ : ι → ℝ) :
    IsVacuum (shiftPot V c) φ ↔ IsVacuum V φ := by
  unfold IsVacuum shiftPot
  constructor
  · rintro ⟨h, h0⟩
    have hV : DifferentiableAt ℝ V φ := by
      have := h.sub_const c
      simpa using this
    refine ⟨hV, ?_⟩
    rw [fderiv_add_const] at h0
    exact h0
  · rintro ⟨h, h0⟩
    refine ⟨h.add_const c, ?_⟩
    rw [fderiv_add_const]
    exact h0

omit [Fintype ι] in
/-- **A field-independent shift moves the vacuum energy by the same constant.** -/
theorem vacuumEnergy_add_const (V : (ι → ℝ) → ℝ) (c : ℝ) (φ : ι → ℝ) :
    vacuumEnergy (shiftPot V c) φ = vacuumEnergy V φ + c := rfl

omit [Fintype ι] in
/-- **At a single vacuum, a constant cancels the vacuum energy iff it is `-V φ`**: the adjustment
is fixed by the value of the potential at the vacuum, a function of the parameters of `V`. -/
theorem constant_adjustment_unique (V : (ι → ℝ) → ℝ) (φ : ι → ℝ) (c : ℝ) :
    vacuumEnergy (shiftPot V c) φ = 0 ↔ c = -V φ := by
  unfold vacuumEnergy shiftPot
  constructor <;> intro h <;> linarith

omit [Fintype ι] in
/-- **No single constant cancels two vacua of different energy** (the field-independent adjustment
cannot make the vacuum energy vanish for every vacuum of `V`). -/
theorem no_constant_adjustment (V : (ι → ℝ) → ℝ) {φ₁ φ₂ : ι → ℝ}
    (hne : vacuumEnergy V φ₁ ≠ vacuumEnergy V φ₂) :
    ¬ ∃ c : ℝ, vacuumEnergy (shiftPot V c) φ₁ = 0 ∧ vacuumEnergy (shiftPot V c) φ₂ = 0 := by
  rintro ⟨c, h1, h2⟩
  rw [constant_adjustment_unique] at h1 h2
  exact hne (by unfold vacuumEnergy; linarith)

end Lightlike.Cosmology.VacuumEnergyNoGo

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.IsVacuum := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.IsVacuum
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.constant_adjustment_unique := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.constant_adjustment_unique
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.isVacuum_add_const := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.isVacuum_add_const
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.no_constant_adjustment := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.no_constant_adjustment
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.shiftPot := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.shiftPot
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.vacuumEnergy := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.vacuumEnergy
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_045.vacuumEnergy_add_const := _root_.Lightlike.Cosmology.VacuumEnergyNoGo.vacuumEnergy_add_const
