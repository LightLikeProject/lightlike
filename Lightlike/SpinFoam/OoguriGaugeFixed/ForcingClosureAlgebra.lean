import Lightlike.SpinFoam.OoguriGaugeFixed.ForcingClosure

/-!
# The forcing closure of an Ooguri gauge set is a closure operator

`forcedTris K T` (the triangles of `K` that the gauge set `T` forces) is monotone, extensive on
`T ∩ K.tris` and idempotent. Forcing a set of triangles is equivalent to containing it in the closure,
so two gauge sets inside `K.tris` have the same gauge-fixed state sum as soon as their closures
agree.

## Main results

* `forcedTris_mono`, `forcedTris_union_forcedTris`, `forcedTris_forcedTris`: closure-operator laws.
* `forces_iff_subset_forcedTris`: `Forces K U T ↔ U ⊆ forcedTris K T` for `U ⊆ K.tris`.
* `amplitudeGF_eq_of_forcedTris_eq`: equal closures give equal gauge-fixed state sums.

Limits: finite cutoff statements; nothing says that unequal closures give unequal state sums.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- The forcing closure consists of triangles of `K`. -/
theorem forcedTris_subset_tris (K : Complex4 V) (T : Finset (Finset V)) :
    forcedTris K T ⊆ K.tris := fun _ hf => (mem_forcedTris.mp hf).1

/-- Triangles of `K` in the gauge set are in its closure. -/
theorem subset_forcedTris {K : Complex4 V} {T : Finset (Finset V)} (hT : T ⊆ K.tris) :
    T ⊆ forcedTris K T :=
  fun f hf => mem_forcedTris.mpr ⟨hT hf, .done (by simpa using hf)⟩

/-- The forcing closure is monotone in the gauge set. -/
theorem forcedTris_mono (K : Complex4 V) {T T' : Finset (Finset V)} (h : T ⊆ T') :
    forcedTris K T ⊆ forcedTris K T' := fun _ hf =>
  let hf' := mem_forcedTris.mp hf
  mem_forcedTris.mpr ⟨hf'.1, hf'.2.mono subset_rfl h⟩

/-- Adding the closure to the gauge set does not change the closure. -/
theorem forcedTris_union_forcedTris (K : Complex4 V) (T : Finset (Finset V)) :
    forcedTris K (T ∪ forcedTris K T) = forcedTris K T := by
  refine Subset.antisymm (fun f hf => ?_) (forcedTris_mono K subset_union_left)
  have hf' := mem_forcedTris.mp hf
  exact mem_forcedTris.mpr ⟨hf'.1, (forces_forcedTris K T).of_union hf'.2⟩

/-- **Idempotence**: the closure of the closure is the closure. -/
theorem forcedTris_forcedTris (K : Complex4 V) (T : Finset (Finset V)) :
    forcedTris K (forcedTris K T) = forcedTris K T := by
  refine Subset.antisymm ?_ (subset_forcedTris (forcedTris_subset_tris K T))
  intro f hf
  have hf' := mem_forcedTris.mp hf
  refine mem_forcedTris.mpr ⟨hf'.1, (forces_forcedTris K T).of_union ?_⟩
  exact hf'.2.mono subset_rfl subset_union_right

/-- **Forcing is containment in the closure**, for sets of triangles of `K`. -/
theorem forces_iff_subset_forcedTris {K : Complex4 V} {U T : Finset (Finset V)}
    (hU : U ⊆ K.tris) : Forces K U T ↔ U ⊆ forcedTris K T :=
  ⟨fun h _ hf => mem_forcedTris.mpr ⟨hU hf, h.mono_target (singleton_subset_iff.mpr (mem_union_left _ hf))⟩,
    fun h => (forces_forcedTris K T).mono_target (fun _ hf => mem_union_left _ (h hf))⟩

/-- **Equal closures give equal state sums.** Two gauge sets inside `K.tris` with the same forcing
closure have the same gauge-fixed state sum at every cutoff. -/
theorem amplitudeGF_eq_of_forcedTris_eq {K : Complex4 V} {T T' : Finset (Finset V)}
    (hT : T ⊆ K.tris) (hT' : T' ⊆ K.tris) (h : forcedTris K T = forcedTris K T')
    (cut : Finset V → ℕ) : amplitudeGF K T cut = amplitudeGF K T' cut :=
  amplitudeGF_eq_of_mutual_forces
    ((forces_iff_subset_forcedTris hT').mpr (h ▸ subset_forcedTris hT'))
    ((forces_iff_subset_forcedTris hT).mpr (h ▸ subset_forcedTris hT)) cut

/-- Conversely, mutual forcing implies equal closures. -/
theorem forcedTris_eq_of_mutual_forces {K : Complex4 V} {T T' : Finset (Finset V)}
    (h : Forces K T' T) (h' : Forces K T T') :
    forcedTris K T = forcedTris K T' := by
  refine Subset.antisymm ?_ ?_
  · intro f hf
    have hf' := mem_forcedTris.mp hf
    exact mem_forcedTris.mpr ⟨hf'.1, h'.of_union (hf'.2.mono subset_rfl subset_union_right)⟩
  · intro f hf
    have hf' := mem_forcedTris.mp hf
    exact mem_forcedTris.mpr ⟨hf'.1, h.of_union (hf'.2.mono subset_rfl subset_union_right)⟩

end Lightlike.SpinFoam
