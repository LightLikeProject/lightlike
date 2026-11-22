import Lightlike.SpinFoam.EPRLStateSum.BFWeight

/-!
# The leg order of a node of the 15j symbol is not intrinsic to the tetrahedron

In `fifteenJSimplex` (hence in `eprlVertex`) the intertwiner at the node `a` of a 4-simplex has its
legs in the cyclic order `a+1, a+2, a+3, a+4` (mod 5) and its label `i_a` couples the first two.
The tetrahedron `t = s∖{s_a}` has its own sorted order of triangles. This file computes the
relation between the two.

* `cyc_eq_succAbove`: the `k`-th leg of node `a` is the triangle at sorted position
  `legPos a k = (a + k) mod 4` of the tetrahedron.
* `legPair_eq_iff`: the channel `(leg 0, leg 1)(leg 2, leg 3)` of the EPRL label, read in the
  sorted order of the tetrahedron, is `(01)(23)` for `a ∈ {0, 2, 4}` and `(12)(30)` for
  `a ∈ {1, 3}`: it depends on the parity of the position `a` of the omitted vertex.
* `legPairOoguri_const`: the channel `(leg 0, leg 2)(leg 1, leg 3)` of the Ooguri label is the same
  pairing `(02)(13)` for every `a`.

So the EPRL tetrahedron label means different intertwiners in two 4-simplices that glue `t` at
positions of different parity, while the Ooguri label does not. This is why the per-vertex relation
`simpE_one_eq_sum_ampP` does not lift to the state sums with the positional conventions of
`EPRL.simpE`.
-/

open Finset Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The sorted position, in the tetrahedron `s∖{s_a}`, of the triangle of the `k`-th leg of node
`a` in the cyclic order `a+1, …, a+4`. -/
def legPos (a : Fin 5) (k : Fin 4) : Fin 4 := ⟨(a.val + k.val) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- **The cyclic leg order of node `a` is a rotation by `a mod 4`** of the sorted order of the
tetrahedron: the `k`-th neighbour `a + 1 + k` of `a` is the vertex `a.succAbove (legPos a k)`. -/
theorem cyc_eq_succAbove (a : Fin 5) (k : Fin 4) :
    a + 1 + Fin.castSucc k = a.succAbove (legPos a k) := by
  revert a k; decide

/-- The same on 4-simplices: the triangle `s∖{s_a, s_{a+1+k}}` is the triangle of the tetrahedron
`s∖{s_a}` opposite to its vertex of sorted position `legPos a k`. -/
theorem tri_leg_eq (s : Finset V) (hs : #s = 5) (a : Fin 5) (k : Fin 4)
    (ht : #(s.erase (s.orderEmbOfFin hs a)) = 4) :
    (s.erase (s.orderEmbOfFin hs a)).erase (s.orderEmbOfFin hs (a + 1 + Fin.castSucc k)) =
      (s.erase (s.orderEmbOfFin hs a)).erase
        ((s.erase (s.orderEmbOfFin hs a)).orderEmbOfFin ht (legPos a k)) := by
  rw [Lightlike.SpinFoam.orderEmbOfFin_erase hs a ht, cyc_eq_succAbove]

/-- The unordered pairing of the four sorted positions `{0,1,2,3}` of a tetrahedron given by the
EPRL channel of node `a`: legs `0, 1` against legs `2, 3`, as the set of the pair containing
the position `0`. -/
def legPairEPRL (a : Fin 5) : Finset (Fin 4) :=
  if legPos a 0 = 0 ∨ legPos a 1 = 0 then {legPos a 0, legPos a 1} else {legPos a 2, legPos a 3}

/-- The same for the Ooguri channel: legs `0, 2` against legs `1, 3`. -/
def legPairOoguri (a : Fin 5) : Finset (Fin 4) :=
  if legPos a 0 = 0 ∨ legPos a 2 = 0 then {legPos a 0, legPos a 2} else {legPos a 1, legPos a 3}

/-- **The EPRL channel depends on the position of the omitted vertex**: the pairing is the same
for two positions exactly when they have the same parity. -/
theorem legPair_eq_iff (a b : Fin 5) : legPairEPRL a = legPairEPRL b ↔ a.val % 2 = b.val % 2 := by
  revert a b; decide

/-- The pairing of the EPRL channel is `{0,1}|{2,3}` for the even positions `0, 2, 4`. -/
theorem legPairEPRL_even (a : Fin 5) (h : a.val % 2 = 0) : legPairEPRL a = {0, 1} := by
  revert a; decide

/-- The pairing of the EPRL channel is `{0,3}|{1,2}` for the odd positions `1, 3`. -/
theorem legPairEPRL_odd (a : Fin 5) (h : a.val % 2 = 1) : legPairEPRL a = {0, 3} := by
  revert a; decide

/-- **The Ooguri channel does not depend on the position** of the omitted vertex: it is the
pairing `{0,2}|{1,3}` for all `a`. -/
theorem legPairOoguri_const (a : Fin 5) : legPairOoguri a = {0, 2} := by
  revert a; decide

/-- **A mismatch occurs on the boundary of the 5-simplex.** The tetrahedron `{0,1,2,4}` lies in the
4-simplices `{0,1,2,3,4}` and `{0,1,2,4,5}`, which omit the vertices `3` and `5` of sorted
positions `3` and `4`: the EPRL channels of the two nodes are different pairings. -/
theorem legPair_mismatch_example :
    Lightlike.FourD.pos ({0, 1, 2, 3, 4} : Finset ℕ) 3 = 3 ∧
    Lightlike.FourD.pos ({0, 1, 2, 4, 5} : Finset ℕ) 5 = 4 ∧
    legPairEPRL 3 ≠ legPairEPRL 4 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [Ne, legPair_eq_iff]
  decide

end Lightlike.SpinFoam.EPRLStateSum
