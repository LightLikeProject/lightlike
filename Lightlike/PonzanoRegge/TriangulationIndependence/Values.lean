module

public import Lightlike.PonzanoRegge.TriangulationIndependence.Moves

/-!
# The set of gauge-fixed amplitudes of a complex

`ampValues K` is the set of all values `amplitudeGF K T cut` over maximal trees `T` and cut-offs
`cut` of `K`. The cut-off is a regulator, so equal amplitudes of two triangulations can only mean
that their sets of regularised values are related, not that the values agree at every cut-off:
raising the cut-off of a summed edge changes the amplitude.

* `ampValues_mono_forward`: along a chain of 2-3 and 1-4 moves the set of values grows.
* `ampValues_move32_subset`, `ampValues_move41_subset`: the smaller complex of a 3-2 or 4-1 move
  has fewer values (the inverse moves read as forward moves).

The converse inclusions (the bigger complex has no more values than the smaller one) are not
claimed: a 3-2 or 4-1 move needs cut-off inequalities on the new edges, which a general state of
the bigger complex does not satisfy.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- **The regularised values of a complex**: the gauge-fixed amplitudes over all maximal trees and
all cut-offs. -/
noncomputable def ampValues (K : Complex3 V) : Set ℝ :=
  {a | ∃ (T : Finset (Finset V)) (cut : Finset V → ℕ), IsMaxTree K T ∧ amplitudeGF K T cut = a}

/-- **Forward chains of moves only enlarge the set of regularised values.** -/
theorem ampValues_mono_forward {K K' : Complex3 V} (h : ForwardMoves K K') :
    ampValues K ⊆ ampValues K' := by
  rintro a ⟨T, cut, hT, rfl⟩
  obtain ⟨T', cut', hT', he⟩ := h.exists_amplitudeGF_eq hT cut
  exact ⟨T', cut', hT', he⟩

/-- A 3-2 move: the smaller complex has a subset of the values of the bigger one. -/
theorem ampValues_move32_subset {K : Complex3 V} {A B C D E : V} (h : IsMove32 K A B C D E) :
    ampValues (move32 K h) ⊆ ampValues K := by
  have hf : ForwardMoves (move32 K h) K := by
    have := ForwardStep.m23 (isMove23_move32 h)
    rw [move23_move32] at this
    exact Relation.ReflTransGen.single this
  exact ampValues_mono_forward hf

/-- A 4-1 move: the smaller complex has a subset of the values of the bigger one. -/
theorem ampValues_move41_subset {K : Complex3 V} {A B C D E : V} (h : IsMove41 K A B C D E) :
    ampValues (move41 K h) ⊆ ampValues K := by
  have hf : ForwardMoves (move41 K h) K := by
    have := ForwardStep.m14 (isMove14_move41 h)
    rw [move14_move41] at this
    exact Relation.ReflTransGen.single this
  exact ampValues_mono_forward hf

end Lightlike.PR
