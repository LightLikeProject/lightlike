import Lightlike.SpinFoam.OoguriGaugeFixed.ForcingClosureAlgebra

/-!
# Total forcing and unions of closures for Ooguri gauge sets

The forcing closure `forcedTris K T` of a gauge set is all of `K.tris` exactly when `T` forces every
triangle (the situation in which the gauge-fixed state sum is independent of the gauge set). The
closure of a union is the closure of the union of the closures.

## Main results

* `forcedTris_eq_tris_iff`: the closure is everything iff `T` forces `K.tris`.
* `amplitudeGF_forcedTris`: replacing a gauge set by its closure does not change the state sum.
* `forcedTris_union_subset`: the closure of a union contains the union of the closures.
* `forcedTris_union_eq`: the closure of a union is the closure of the union of the closures.

Limits: finite cutoff statements; no claim about gauge sets with different closures.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- **Total closure iff total forcing.** The forcing closure of `T` is every triangle of `K` if and
only if `T` forces `K.tris`. -/
theorem forcedTris_eq_tris_iff (K : Complex4 V) (T : Finset (Finset V)) :
    forcedTris K T = K.tris ↔ Forces K K.tris T := by
  refine ⟨fun h => h ▸ forces_forcedTris K T, fun h => ?_⟩
  exact Subset.antisymm (forcedTris_subset_tris K T)
    ((forces_iff_subset_forcedTris subset_rfl).mp h)

/-- **A gauge set and its closure have the same state sum.** For `T ⊆ K.tris`, the gauge-fixed state
sum with gauge set `forcedTris K T` equals the one with `T`, at every cutoff. -/
theorem amplitudeGF_forcedTris {K : Complex4 V} {T : Finset (Finset V)} (hT : T ⊆ K.tris)
    (cut : Finset V → ℕ) : amplitudeGF K (forcedTris K T) cut = amplitudeGF K T cut := by
  rw [← amplitudeGF_eq_forcedTris K T cut, union_eq_right.mpr (subset_forcedTris hT)]

/-- **Total closure gives the trivial state sum.** If the closure of `T` is `K.tris`, the
gauge-fixed state sum is `1` at every cutoff. -/
theorem amplitudeGF_eq_one_of_forcedTris_eq_tris {K : Complex4 V} {T : Finset (Finset V)}
    (h : forcedTris K T = K.tris) (cut : Finset V → ℕ) :
    amplitudeGF K T cut = 1 :=
  amplitudeGF_eq_one_of_forces ((forcedTris_eq_tris_iff K T).mp h) cut

/-- The closure of a union contains the union of the closures. -/
theorem forcedTris_union_subset (K : Complex4 V) (T U : Finset (Finset V)) :
    forcedTris K T ∪ forcedTris K U ⊆ forcedTris K (T ∪ U) :=
  union_subset (forcedTris_mono K subset_union_left) (forcedTris_mono K subset_union_right)

/-- **Closure of a union.** For gauge sets inside `K.tris`, the closure of `T ∪ U` is the closure of
the union of the closures of `T` and `U`. -/
theorem forcedTris_union_eq {K : Complex4 V} {T U : Finset (Finset V)} (hT : T ⊆ K.tris)
    (hU : U ⊆ K.tris) :
    forcedTris K (T ∪ U) = forcedTris K (forcedTris K T ∪ forcedTris K U) := by
  refine Subset.antisymm ?_ ?_
  · exact forcedTris_mono K (union_subset_union (subset_forcedTris hT) (subset_forcedTris hU))
  · intro f hf
    have hf' := mem_forcedTris.mp hf
    refine mem_forcedTris.mpr ⟨hf'.1, ?_⟩
    have h1 : Forces K (forcedTris K T ∪ forcedTris K U) (T ∪ U) :=
      ((forces_forcedTris K T).mono subset_rfl subset_union_left).union
        ((forces_forcedTris K U).mono subset_rfl subset_union_right)
    exact h1.of_union (hf'.2.mono subset_rfl subset_union_right)

/-- **State sum of a union through closures.** For gauge sets inside `K.tris`, the gauge-fixed state
sum of `T ∪ U` equals that of `forcedTris K T ∪ forcedTris K U`, at every cutoff. -/
theorem amplitudeGF_union_eq_forcedTris_union {K : Complex4 V} {T U : Finset (Finset V)}
    (hT : T ⊆ K.tris) (hU : U ⊆ K.tris) (cut : Finset V → ℕ) :
    amplitudeGF K (T ∪ U) cut = amplitudeGF K (forcedTris K T ∪ forcedTris K U) cut :=
  amplitudeGF_eq_of_forcedTris_eq (union_subset hT hU)
    (union_subset (forcedTris_subset_tris K T) (forcedTris_subset_tris K U))
    (forcedTris_union_eq hT hU) cut

end Lightlike.SpinFoam
