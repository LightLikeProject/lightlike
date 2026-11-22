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
* `forcedTris`, `forces_forcedTris`, `amplitudeGF_eq_forcedTris`: closure of a gauge set.
* `amplitudeGF_eq_of_mutual_forces`: mutually forcing gauge sets give equal state sums.

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

/-- Forcing a finite set of faces one at a time: if `T` forces each `{f}`, `f ∈ S`, it forces `S`. -/
theorem Forces.of_forall_mem {K : Complex4 V} {T : Finset (Finset V)} :
    ∀ (S : Finset (Finset V)), (∀ f ∈ S, Forces K {f} T) → Forces K S T := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ => .done (empty_subset _)
  | insert a s _ ih =>
    intro h
    rw [insert_eq]
    exact (h a (mem_insert_self _ _)).union (ih fun f hf => h f (mem_insert_of_mem hf))

open Classical in
/-- **The forcing closure of a gauge set**: the triangles of `K` that `T` forces. -/
noncomputable def forcedTris (K : Complex4 V) (T : Finset (Finset V)) : Finset (Finset V) :=
  K.tris.filter fun f => Forces K {f} T

/-- A triangle is in `forcedTris K T` iff it is a triangle of `K` forced by `T`. -/
theorem mem_forcedTris {K : Complex4 V} {T : Finset (Finset V)} {f : Finset V} :
    f ∈ forcedTris K T ↔ f ∈ K.tris ∧ Forces K {f} T := by
  classical
  simp [forcedTris]

/-- `T` forces its whole forcing closure. -/
theorem forces_forcedTris (K : Complex4 V) (T : Finset (Finset V)) :
    Forces K (forcedTris K T) T :=
  Forces.of_forall_mem _ fun _ hf => (mem_forcedTris.mp hf).2

/-- **Closing the gauge set under forcing changes nothing.** The gauge-fixed state sum for
`T ∪ forcedTris K T` equals the one for `T`, at every cutoff. -/
theorem amplitudeGF_eq_forcedTris (K : Complex4 V) (T : Finset (Finset V)) (cut : Finset V → ℕ) :
    amplitudeGF K (T ∪ forcedTris K T) cut = amplitudeGF K T cut :=
  amplitudeGF_union_of_forces (forces_forcedTris K T) cut

/-- **Mutual forcing gives equal state sums.** If two gauge sets each force the other, their
gauge-fixed state sums agree at every cutoff (no assumption that they force all of `K.tris`). -/
theorem amplitudeGF_eq_of_mutual_forces {K : Complex4 V} {T T' : Finset (Finset V)}
    (h : Forces K T' T) (h' : Forces K T T') (cut : Finset V → ℕ) :
    amplitudeGF K T cut = amplitudeGF K T' cut := by
  rw [← amplitudeGF_union_of_forces h cut, union_comm, amplitudeGF_union_of_forces h' cut]

end Lightlike.SpinFoam
