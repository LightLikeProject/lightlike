import Lightlike.SpinFoam.EPRLStateSum.GlobalGluing

/-!
# The sorted leg spins of a tetrahedron do not depend on the 4-simplex containing it

For a closed 4-complex each tetrahedron `t` lies in two 4-simplices `s`, `s'`, omitting the vertices
`s_a`, `s'_{a'}` (sorted positions `a`, `a'`, possibly different). The `k`-th triangle of `t` in
its own sorted order is the triangle `s∖{s_a, s_{succAbove a k}}` of `s` and likewise of `s'`.
`simplexJ_succAbove_eq` states that the triangle spins agree: this is the hypothesis `hleg` of
`global_gluing_nodeI` for a concrete complex.
-/

open Finset Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The `succAbove`-leg of a 4-simplex `s` at the omitted position `a` is the `k`-th sorted
triangle of the tetrahedron `s∖{s_a}`. -/
theorem simplexJ_succAbove (s : Finset V) (hs : #s = 5) (col : Finset V → ℕ) (a : Fin 5)
    (ht : #(s.erase (s.orderEmbOfFin hs a)) = 4) (k : Fin 4) :
    simplexJ s hs col a (a.succAbove k) =
      col ((s.erase (s.orderEmbOfFin hs a)).erase
        ((s.erase (s.orderEmbOfFin hs a)).orderEmbOfFin ht k)) := by
  unfold simplexJ
  rw [Lightlike.SpinFoam.orderEmbOfFin_erase hs a ht]

/-- **The sorted leg spins of a shared tetrahedron agree.** If the tetrahedra `s∖{s_a}` and
`s'∖{s'_{a'}}` of two 4-simplices coincide, then their `k`-th sorted leg spins `simplexJ …
(succAbove k)` agree for every `k`. -/
theorem simplexJ_succAbove_eq (s s' : Finset V) (hs : #s = 5) (hs' : #s' = 5) (col : Finset V → ℕ)
    (a a' : Fin 5)
    (h : s.erase (s.orderEmbOfFin hs a) = s'.erase (s'.orderEmbOfFin hs' a')) (k : Fin 4) :
    simplexJ s hs col a (a.succAbove k) = simplexJ s' hs' col a' (a'.succAbove k) := by
  have ht : #(s.erase (s.orderEmbOfFin hs a)) = 4 := by
    rw [Finset.card_erase_of_mem (s.orderEmbOfFin_mem hs a), hs]
  have ht' : #(s'.erase (s'.orderEmbOfFin hs' a')) = 4 := by
    rw [← h]; exact ht
  rw [simplexJ_succAbove s hs col a ht k, simplexJ_succAbove s' hs' col a' ht' k]
  generalize s.erase (s.orderEmbOfFin hs a) = t at *
  generalize s'.erase (s'.orderEmbOfFin hs' a') = t' at *
  subst h
  rfl

end Lightlike.SpinFoam.EPRLStateSum
