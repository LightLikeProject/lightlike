module

public import Lightlike.Poincare.StandardMomenta
public import Physlib.Relativity.LorentzGroup.Rotations
public import Physlib.Relativity.LorentzGroup.ToVector

/-!
# The little group of the rest momentum is the rotation group

Signature `(+,−,−,−)`, `m ≠ 0`. A Lorentz transformation fixes the rest momentum `(m, 0, 0, 0)` exactly when its
`(0,0)` entry is `1` (`mem_littleGroup_massiveStd_iff`); a proper one does so exactly when it lies in Physlib's
rotation subgroup `LorentzGroup.Rotations 3` (`mem_littleGroup_massiveStd_iff_mem_rotations`), which Physlib
identifies with `SO(3)` (`LorentzGroup.ofSpecialOrthogonal`). This is the massive little group of the Wigner
classification; with `isCompact_littleGroup_massive` it is compact.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2: "By going to a rest-frame, it is easy to show that the stabilizer of a time-like
  vector `q = (m, 0) ≠ 0` is the rotation subgroup `SO(D − 1) ⊂ SO(D − 1, 1)↑`" (page 12 of v2).
-/

@[expose] public section

noncomputable section

open Lorentz LorentzGroup

namespace Lightlike.Poincare

/-- A Lorentz transformation fixes the rest momentum iff it fixes `e₀`. -/
lemma mem_littleGroup_massiveStd_iff_fix_basis {m : ℝ} (hm : m ≠ 0) (Λ : LorentzGroup 3) :
    Λ ∈ littleGroup (massiveStd m) ↔
      Λ • (Lorentz.Vector.basis (Sum.inl 0) : Lorentz.Vector 3) = Lorentz.Vector.basis (Sum.inl 0) := by
  show Λ • massiveStd m = massiveStd m ↔ _
  have h : Λ • massiveStd m = m • (Λ • (Lorentz.Vector.basis (Sum.inl 0) : Lorentz.Vector 3)) := by
    rw [massiveStd, Lorentz.Vector.smul_eq_mulVec, Lorentz.Vector.smul_eq_mulVec, Matrix.mulVec_smul]
  rw [h, massiveStd]
  exact (smul_right_injective _ hm).eq_iff

/-- **The little group of the rest momentum**: `Λ` fixes `(m, 0, 0, 0)` iff `Λ₀₀ = 1`. -/
theorem mem_littleGroup_massiveStd_iff {m : ℝ} (hm : m ≠ 0) (Λ : LorentzGroup 3) :
    Λ ∈ littleGroup (massiveStd m) ↔ Λ.1 (Sum.inl 0) (Sum.inl 0) = 1 := by
  rw [mem_littleGroup_massiveStd_iff_fix_basis hm, ← toVector_eq_basis_iff_timeComponent_eq_one]
  rfl

/-- **The proper part of the massive little group is the rotation group** `SO(3)`. -/
theorem mem_littleGroup_massiveStd_iff_mem_rotations {m : ℝ} (hm : m ≠ 0) (Λ : LorentzGroup 3)
    (hΛ : IsProper Λ) : Λ ∈ littleGroup (massiveStd m) ↔ Λ ∈ Rotations 3 := by
  rw [mem_littleGroup_massiveStd_iff hm, mem_rotations_iff]
  exact ⟨fun h => ⟨h, hΛ⟩, fun h => h.1⟩

/-- Every rotation fixes the rest momentum. -/
theorem rotations_le_littleGroup_massiveStd {m : ℝ} (hm : m ≠ 0) :
    ((Rotations 3 : Subgroup (LorentzGroup 3)) : Set (LorentzGroup 3)) ⊆ littleGroup (massiveStd m) :=
  fun Λ hΛ => (mem_littleGroup_massiveStd_iff hm Λ).2 ((mem_rotations_iff Λ).1 hΛ).1

end Lightlike.Poincare
