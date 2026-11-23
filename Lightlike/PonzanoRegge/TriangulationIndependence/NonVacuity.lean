module

public import Lightlike.PonzanoRegge.TriangulationIndependence.Main

/-!
# Non-vacuity of the forward Pachner hypothesis

`PachnerForwardHyp Same` is a hypothesis, so it should be satisfiable by a nontrivial `Same`. Here
the relation "related by one forward move or equal" is shown to satisfy it, and the conclusion of
`triangulation_independence_of_pachner` is evaluated on a single 2-3 and a single 1-4 move.

* `commonForward_move23`, `commonForward_move14`: a complex and its image under one forward move
  have a common forward descendant (the image).
* `pachnerForwardHyp_oneForward`: the relation `K = K' ∨ ForwardStep K K' ∨ ForwardStep K' K`
  satisfies `PachnerForwardHyp`.
-/

@[expose] public section

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- A complex and the result of a 2-3 move have a common forward descendant. -/
theorem commonForward_move23 {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    CommonForward K (move23 K h) :=
  ⟨move23 K h, Relation.ReflTransGen.single (ForwardStep.m23 h), .refl⟩

/-- A complex and the result of a 1-4 move have a common forward descendant. -/
theorem commonForward_move14 {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    CommonForward K (move14 K h) :=
  ⟨move14 K h, Relation.ReflTransGen.single (ForwardStep.m14 h), .refl⟩

/-- A complex and anything a forward step leads to have a common forward descendant. -/
theorem commonForward_of_forwardStep {K K' : Complex3 V} (h : ForwardStep K K') :
    CommonForward K K' :=
  ⟨K', Relation.ReflTransGen.single h, .refl⟩

/-- The relation "equal, or one forward step apart" satisfies the forward Pachner hypothesis, so
`PachnerForwardHyp` is satisfiable by a nontrivial relation. For the relation "triangulate the same
manifold" it is the content of Pachner's theorem, which is not proved here. -/
theorem pachnerForwardHyp_oneForward :
    PachnerForwardHyp (fun K K' : Complex3 V => K = K' ∨ ForwardStep K K' ∨ ForwardStep K' K) := by
  rintro K K' (rfl | h | h)
  · exact .refl _
  · exact commonForward_of_forwardStep h
  · exact (commonForward_of_forwardStep h).symm

/-- A 2-3 move: every regularised value of the original complex is one of the new complex. -/
theorem ampValues_move23_subset {K : Complex3 V} {A B C D E : V} (h : IsMove23 K A B C D E) :
    ampValues K ⊆ ampValues (move23 K h) :=
  ampValues_mono_forward (Relation.ReflTransGen.single (ForwardStep.m23 h))

/-- A 1-4 move: every regularised value of the original complex is one of the new complex. -/
theorem ampValues_move14_subset {K : Complex3 V} {A B C D E : V} (h : IsMove14 K A B C D E) :
    ampValues K ⊆ ampValues (move14 K h) :=
  ampValues_mono_forward (Relation.ReflTransGen.single (ForwardStep.m14 h))

end Lightlike.PR
