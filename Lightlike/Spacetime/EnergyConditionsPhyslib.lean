import Lightlike.Spacetime.EnergyConditions
import Physlib.Cosmology.FLRW.EnergyConditions

/-!
# The energy conditions of a perfect fluid: ours and Physlib's

Physlib (`Physlib.Cosmology.FLRW.EnergyConditions`) defines the null, weak, strong and dominant energy conditions of a
cosmic fluid `F` (density `F.ρ`, pressure `F.p` as functions of Physlib's `Time`, speed of light `c` explicit) by their
effective forms. Ours (`EnergyConditions.lean`) are the conditions on the stress-energy form `T(ξ, ξ)` of a Lorentzian
vector space. For a perfect fluid with a unit timelike velocity the two agree at `c = 1` (the effective forms
`fluid_nullEC_iff`, `fluid_weakEC_iff`, `fluid_strongEC_iff`, `fluid_dominantEC_iff`).

* `fluid_nullEC_iff_physlib`, `fluid_weakEC_iff_physlib`, `fluid_strongEC_iff_physlib`, `fluid_dominantEC_iff_physlib`.
-/

noncomputable section
namespace Lightlike

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [FiniteDimensional ℝ V]
  {g : V →L[ℝ] V →L[ℝ] ℝ} {u : V}

/-- **The null condition of a perfect fluid is Physlib's** `NullEnergyCondition` at `c = 1`. -/
theorem fluid_nullEC_iff_physlib (hg : IsLorentzianForm 4 g) (hu : g u u = -1) (F : _root_.Cosmology.CosmicFluid)
    (t : Time) : NullEC g (fluidT g u (F.ρ t) (F.p t)) ↔ F.NullEnergyCondition 1 t := by
  rw [fluid_nullEC_iff hg hu, _root_.Cosmology.CosmicFluid.NullEnergyCondition]
  norm_num

/-- **The weak condition of a perfect fluid is Physlib's** `WeakEnergyCondition` at `c = 1`. -/
theorem fluid_weakEC_iff_physlib (hg : IsLorentzianForm 4 g) (hu : g u u = -1) (F : _root_.Cosmology.CosmicFluid)
    (t : Time) : WeakEC g (fluidT g u (F.ρ t) (F.p t)) ↔ F.WeakEnergyCondition 1 t := by
  rw [fluid_weakEC_iff hg hu, _root_.Cosmology.CosmicFluid.WeakEnergyCondition]
  norm_num

/-- **The strong condition of a perfect fluid is Physlib's** `StrongEnergyCondition` at `c = 1`. -/
theorem fluid_strongEC_iff_physlib (hg : IsLorentzianForm 4 g) (hu : g u u = -1) (F : _root_.Cosmology.CosmicFluid)
    (t : Time) : StrongEC g (fluidT g u (F.ρ t) (F.p t)) hg ↔ F.StrongEnergyCondition 1 t := by
  rw [fluid_strongEC_iff hg hu, _root_.Cosmology.CosmicFluid.StrongEnergyCondition]
  norm_num

/-- **The dominant condition of a perfect fluid is Physlib's** `DominantEnergyCondition` at `c = 1`. -/
theorem fluid_dominantEC_iff_physlib (hg : IsLorentzianForm 4 g) (hu : g u u = -1) (F : _root_.Cosmology.CosmicFluid)
    (t : Time) : DominantEC g (fluidT g u (F.ρ t) (F.p t)) hg ↔ F.DominantEnergyCondition 1 t := by
  rw [fluid_dominantEC_iff hg hu, _root_.Cosmology.CosmicFluid.DominantEnergyCondition]
  constructor
  · intro h; exact ⟨(abs_nonneg _).trans h, by simpa using h⟩
  · rintro ⟨-, h⟩; simpa using h

end Lightlike
