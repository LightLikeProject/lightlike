module

public import Lightlike.PonzanoRegge.TriangulationIndependence.CompleteSkeleton

/-!
# Trust check: the boundary of the 4-simplex has tree-independent gauge-fixed amplitude

On `K5` the path `01, 12, 23, 34` and the star at `0` are two maximal trees; they are connected by
triangle exchanges (`treeConnected_K5`), so their gauge-fixed amplitudes agree at every cut-off.
This is the positive counterpart of the ring of three tetrahedra, where the two trees differ and
`TreeConnected` fails (`Tests/Cocycle.lean`).
-/

@[expose] public section

namespace Lightlike.PR.Test.K5

open Finset

/-- The path `0 - 1 - 2 - 3 - 4`. -/
def Tpath : Finset (Finset (Fin 5)) := {{0, 1}, {1, 2}, {2, 3}, {3, 4}}

/-- The star at `0`. -/
def Tstar : Finset (Finset (Fin 5)) := {{0, 1}, {0, 2}, {0, 3}, {0, 4}}

/-- The path is a maximal tree of `K5`. -/
theorem isMaxTree_path : IsMaxTree K5 Tpath := by
  refine ⟨by decide, ⟨by decide, ?_, by decide⟩⟩
  intro u hu v hv
  have step : ∀ a b : Fin 5, ({a, b} : Finset (Fin 5)) ∈ Tpath →
      Relation.ReflTransGen (fun x y => ({x, y} : Finset (Fin 5)) ∈ Tpath) a b :=
    fun a b h => .single h
  have to0 : ∀ w : Fin 5, Relation.ReflTransGen
      (fun x y => ({x, y} : Finset (Fin 5)) ∈ Tpath) w 0 := by
    intro w
    fin_cases w
    · exact .refl
    · exact step _ _ (by decide)
    · exact (step 2 1 (by decide)).trans (step 1 0 (by decide))
    · exact ((step 3 2 (by decide)).trans (step 2 1 (by decide))).trans (step 1 0 (by decide))
    · exact (((step 4 3 (by decide)).trans (step 3 2 (by decide))).trans
        (step 2 1 (by decide))).trans (step 1 0 (by decide))
  have from0 : ∀ w : Fin 5, Relation.ReflTransGen
      (fun x y => ({x, y} : Finset (Fin 5)) ∈ Tpath) 0 w := by
    intro w
    fin_cases w
    · exact .refl
    · exact step _ _ (by decide)
    · exact (step 0 1 (by decide)).trans (step 1 2 (by decide))
    · exact ((step 0 1 (by decide)).trans (step 1 2 (by decide))).trans (step 2 3 (by decide))
    · exact (((step 0 1 (by decide)).trans (step 1 2 (by decide))).trans
        (step 2 3 (by decide))).trans (step 3 4 (by decide))
  exact (to0 u).trans (from0 v)

/-- The star is a maximal tree of `K5`. -/
theorem isMaxTree_star : IsMaxTree K5 Tstar := by
  refine ⟨by decide, ⟨by decide, ?_, by decide⟩⟩
  intro u hu v hv
  have to0 : ∀ w : Fin 5, Relation.ReflTransGen
      (fun x y => ({x, y} : Finset (Fin 5)) ∈ Tstar) w 0 := by
    intro w
    fin_cases w
    · exact .refl
    all_goals exact .single (by decide)
  have from0 : ∀ w : Fin 5, Relation.ReflTransGen
      (fun x y => ({x, y} : Finset (Fin 5)) ∈ Tstar) 0 w := by
    intro w
    fin_cases w
    · exact .refl
    all_goals exact .single (by decide)
  exact (to0 u).trans (from0 v)

/-- The path and the star give the same gauge-fixed amplitude on `K5`, for every cut-off. -/
theorem amplitudeGF_path_eq_star (cut : Finset (Fin 5) → ℕ) :
    amplitudeGF K5 Tpath cut = amplitudeGF K5 Tstar cut :=
  amplitudeGF_K5_eq isMaxTree_path isMaxTree_star cut

end Lightlike.PR.Test.K5
