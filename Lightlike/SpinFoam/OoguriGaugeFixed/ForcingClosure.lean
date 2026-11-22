import Lightlike.SpinFoam.ForcingMoves
import Lightlike.SpinFoam.GaugeChain

/-!
# Gauge independence of the Ooguri state sum through forcing closures

`amplitudeGF_eq_of_forces` (in `GaugeIndependence.lean`) says that two gauge sets that each force
every triangle give the same gauge-fixed state sum. This file removes the word "every": the state
sum depends on the gauge set `T` only through what `T` forces (`Forces K U T`), whether or not that
is all of `K.tris`.

## Main results

* `Forces.union`: forcing is closed under unions of targets.
* `amplitudeGF_union_of_forces`: adding to the gauge set faces that the gauge set forces does not
  change the state sum, for every cutoff.
* `amplitudeGF_insert_of_step`: one forcing step.

Limits: finite cutoff statements, sufficient criteria. Nothing here says that gauge sets that do not
force each other give different state sums.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- Forcing is closed under unions of targets. -/
theorem Forces.union {K : Complex4 V} {U U' T : Finset (Finset V)} (h : Forces K U T)
    (h' : Forces K U' T) : Forces K (U ∪ U') T := by
  refine h.of_union ?_
  have h'' : Forces K U' (T ∪ U) := h'.mono subset_rfl subset_union_left
  exact h''.mono_target (fun x hx => by
    rcases mem_union.mp hx with hx | hx
    · exact mem_union_right _ (mem_union_right _ hx)
    · exact mem_union_left _ hx)

/-- **Adding forced faces to the gauge set changes nothing.** If the gauge set `T` forces the faces
`U`, the gauge-fixed state sum with gauge set `T ∪ U` equals the one with `T`, at every cutoff. -/
theorem amplitudeGF_union_of_forces {K : Complex4 V} {T U : Finset (Finset V)}
    (h : Forces K U T) (cut : Finset V → ℕ) :
    amplitudeGF K (T ∪ U) cut = amplitudeGF K T cut := by
  refine amplitudeGF_eq_of_vanish K subset_union_left (fun col hW hT f hf => ?_) cut
  rcases mem_union.mp hf with hf | hf
  · exact hT f hf
  · exact h.sound hW hT f hf

/-- **One forcing step.** If a tetrahedron `t` of `K` has three triangles in the gauge set `T`,
its fourth triangle `f` can be added to the gauge set without changing the state sum. -/
theorem amplitudeGF_insert_of_step {K : Complex4 V} {T : Finset (Finset V)} {t f : Finset V}
    (ht : t ∈ K.tets) (hf : f ∈ t.powersetCard 3) (hT : ∀ g ∈ t.powersetCard 3, g ≠ f → g ∈ T)
    (cut : Finset V → ℕ) : amplitudeGF K (insert f T) cut = amplitudeGF K T cut := by
  have h : Forces K {f} T :=
    .step t f ht hf hT (.done (by simp))
  rw [insert_eq, union_comm]
  exact amplitudeGF_union_of_forces h cut

end Lightlike.SpinFoam
