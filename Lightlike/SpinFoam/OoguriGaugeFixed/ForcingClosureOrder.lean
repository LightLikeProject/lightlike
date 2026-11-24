import Lightlike.SpinFoam.OoguriGaugeFixed.ForcingClosureTotal

/-!
# The forcing preorder on Ooguri gauge sets

Forcing between gauge sets inside `K.tris` is the inclusion order of their forcing closures, and
mutual forcing is equality of closures. So the gauge sets modulo mutual forcing form the lattice of
closed sets, and the gauge-fixed state sum is constant on each class.

## Main results

* `forcedTris_subset_forcedTris_iff`: closure inclusion is inclusion in the closure.
* `forces_iff_forcedTris_subset`: `T` forces `T'` iff the closure of `T'` is in that of `T`.
* `Forces.trans'`: forcing is transitive on subsets of `K.tris`.
* `forcedTris_eq_iff_mutual_forces`: equal closures iff mutual forcing.
* `amplitudeGF_eq_of_forces_forces`: mutual forcing gives equal state sums (closure form).

Limits: finite cutoff statements; no claim about gauge sets with different closures.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- **Closure inclusion.** For `T ⊆ K.tris`, the closure of `T` lies in the closure of `T'` exactly
when `T` itself does. -/
theorem forcedTris_subset_forcedTris_iff {K : Complex4 V} {T T' : Finset (Finset V)}
    (hT : T ⊆ K.tris) :
    forcedTris K T ⊆ forcedTris K T' ↔ T ⊆ forcedTris K T' :=
  ⟨fun h => (subset_forcedTris hT).trans h,
    fun h => (forcedTris_mono K h).trans (forcedTris_forcedTris K T').le⟩

/-- **Forcing is the closure order.** For `T' ⊆ K.tris`, `T` forces `T'` iff the closure of `T'` lies
in the closure of `T`. -/
theorem forces_iff_forcedTris_subset {K : Complex4 V} {T T' : Finset (Finset V)}
    (hT' : T' ⊆ K.tris) :
    Forces K T' T ↔ forcedTris K T' ⊆ forcedTris K T :=
  (forces_iff_subset_forcedTris hT').trans (forcedTris_subset_forcedTris_iff hT').symm

/-- **Forcing is transitive.** If `T` forces `U` and `U` forces `W`, then `T` forces `W`
(for `U`, `W` inside `K.tris`). -/
theorem Forces.trans' {K : Complex4 V} {T U W : Finset (Finset V)} (hU : U ⊆ K.tris)
    (hW : W ⊆ K.tris) (h1 : Forces K U T) (h2 : Forces K W U) : Forces K W T := by
  rw [forces_iff_forcedTris_subset hW] at h2 ⊢
  rw [forces_iff_forcedTris_subset hU] at h1
  exact h2.trans h1

/-- **Equal closures iff mutual forcing.** -/
theorem forcedTris_eq_iff_mutual_forces {K : Complex4 V} {T T' : Finset (Finset V)}
    (hT : T ⊆ K.tris) (hT' : T' ⊆ K.tris) :
    forcedTris K T = forcedTris K T' ↔ Forces K T' T ∧ Forces K T T' :=
  ⟨fun h => ⟨(forces_iff_forcedTris_subset hT').mpr h.ge, (forces_iff_forcedTris_subset hT).mpr h.le⟩,
    fun h => forcedTris_eq_of_mutual_forces h.1 h.2⟩

/-- **State sums are constant on forcing classes.** Mutual forcing of gauge sets inside `K.tris`
gives equal gauge-fixed state sums at every cutoff, through equality of closures. -/
theorem amplitudeGF_eq_of_forces_forces {K : Complex4 V} {T T' : Finset (Finset V)}
    (hT : T ⊆ K.tris) (hT' : T' ⊆ K.tris) (h : Forces K T' T) (h' : Forces K T T')
    (cut : Finset V → ℕ) : amplitudeGF K T cut = amplitudeGF K T' cut :=
  amplitudeGF_eq_of_forcedTris_eq hT hT'
    ((forcedTris_eq_iff_mutual_forces hT hT').mpr ⟨h, h'⟩) cut

end Lightlike.SpinFoam
