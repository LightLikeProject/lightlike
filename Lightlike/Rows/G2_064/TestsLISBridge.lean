import Lightlike.Rows.G2_064.LISBridge

/-!
# Trust checks for the longest-increasing-subsequence bridge (row G2-064)
-/

namespace Lightlike.CausalSets

/-- The identity has the whole of `Fin 4` as increasing subsequence. -/
example : IsIncSubseq (1 : Equiv.Perm (Fin 4)) Finset.univ := by
  intro i _ j _ h; simpa using h

/-- The reversal has no increasing subsequence with two elements. -/
example : ¬ IsIncSubseq (Fin.revPerm : Equiv.Perm (Fin 4)) {0, 1} := by
  intro h
  have := h (by simp : (0 : Fin 4) ∈ ((({0, 1} : Finset (Fin 4)) : Set (Fin 4))))
    (by simp : (1 : Fin 4) ∈ ((({0, 1} : Finset (Fin 4)) : Set (Fin 4)))) (by decide)
  revert this; decide

/-- Longest chain of the sprinkled points of the identity in `ℝ^{1+1}` is `lis`, that is `longestChain`
(`4`). -/
example : coneLongestChain (Finset.univ.image (sprinklePt (1 : Equiv.Perm (Fin 4)))) = 4 := by
  rw [coneLongestChain_sprinklePt, ← longestChain_eq_lis]; decide

end Lightlike.CausalSets
