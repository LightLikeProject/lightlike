import Mathlib

/-!
# A component of `U ∩ B` reaches the frontier of `B`

Row G3-188, milestone PL5 (third pass), step towards the local connectedness of a Jordan domain at its
boundary (item 5b).  If `U` is open and connected, `B` is open and `U ⊄ B`, then every component `W` of `U ∩ B`
has a limit point in `U ∖ B`: otherwise `W` would be open and closed in `U`, hence all of `U`.  In the
"teeth" argument for a Jordan domain `U` and a small ball `B`, this says that every tooth reaches `∂B`.

* `exists_mem_closure_component_not_mem`: the statement.
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- **Components reach out.** Let `U` be open and connected, `B` open, `y ∈ U ∩ B` and `U ⊄ B`.  The component
of `y` in `U ∩ B` has a limit point in `U` that is not in `B`. -/
theorem exists_mem_closure_component_not_mem {U B : Set (ℝ × ℝ)} (hUo : IsOpen U) (hUc : IsConnected U)
    (hB : IsOpen B) {y : ℝ × ℝ} (hy : y ∈ U ∩ B) (hUB : ¬ U ⊆ B) :
    ∃ w ∈ closure (connectedComponentIn (U ∩ B) y), w ∈ U ∧ w ∉ B := by
  by_contra hcon
  push Not at hcon
  set W := connectedComponentIn (U ∩ B) y with hW
  have hWo : IsOpen W := (hUo.inter hB).connectedComponentIn
  have hWc : IsPreconnected W := isPreconnected_connectedComponentIn
  have hyW : y ∈ W := mem_connectedComponentIn hy
  have hcl : closure W ∩ U ⊆ W := by
    rintro w ⟨hwc, hwU⟩
    have hwB : w ∈ B := hcon w hwc hwU
    have hS : IsPreconnected (insert w W) :=
      hWc.subset_closure (subset_insert _ _) (insert_subset hwc subset_closure)
    have hSsub : insert w W ⊆ U ∩ B := by
      refine insert_subset ⟨hwU, hwB⟩ ?_
      exact connectedComponentIn_subset _ _
    exact hS.subset_connectedComponentIn (mem_insert_of_mem _ hyW) hSsub (mem_insert _ _)
  have hWU : U ⊆ W := hUc.isPreconnected.subset_of_closure_inter_subset hWo ⟨y, hy.1, hyW⟩ hcl
  apply hUB
  intro z hz
  exact (connectedComponentIn_subset _ _ (hWU hz)).2

end Lightlike.PL.Schoenflies
