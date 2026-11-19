import Lightlike.SpinFoam.ForcingMove24

/-!
# Forcing under the inverse 4-2 move, and the 3-3 move read backwards

`forces_move24_iff` and `forces_move33_iff` start from a set that forces the complex before the move.
Here the starting point is the complex after the move, which is the 4-2 move for a 2-4 move and the
3-3 move again for a 3-3 move.

* `forces_move42_iff`: let `K'` be the complex around an edge `τ = {p, q}` with four 4-simplices, `K`
  the complex after the 4-2 move, and `T ∪ {a, p, q}` a set that forces `K'`. Then `T` forces `K` if and
  only if the closure of `T` under the tetrahedra of `K` other than the new tetrahedron `σ` already
  reaches every triangle of `K`. In general the transported set `T` does not force `K`
  (observed in `scripts/spinfoam/forcechain.py`), and this is the extra condition.
-/

open Finset Lightlike.FourD Complex4

namespace Lightlike.SpinFoam.Forcing24

variable {V : Type*} [LinearOrder V] {K' : Complex4 V} {σ τ : Finset V}

/-- **Forcing under the 4-2 move.** If `T ∪ {a, p, q}` forces every triangle of `K'` (the complex with
the edge `τ = {p, q}` inside four 4-simplices) and the 4-2 move `K' → K` removes the edge, then `T`
forces every triangle of `K` if and only if the closure of `T` under the tetrahedra of `K` other than
the new tetrahedron `σ` is already complete. -/
theorem forces_move42_iff (h' : K'.IsMove τ σ) (hσ : #σ = 4) {a : V} (ha : a ∈ σ)
    {T : Finset (Finset V)} (hT : T ⊆ (K'.move h').tris)
    (hF' : Forces K' K'.tris (insert (insert a τ) T)) :
    Forces (K'.move h') (K'.move h').tris T ↔
      ForcesIn ((K'.move h').tets.filter fun t => ¬ σ ⊆ t) (K'.move h').tris T := by
  have h : (K'.move h').IsMove σ τ := h'.symm
  have e : (K'.move h').move h = K' := move_move h'
  constructor
  · intro hK
    have := (forces_move24_iff h hσ ha hT hK).mp (by rw [e]; exact hF')
    exact this
  · intro hS
    rw [Forcing33.forces_iff_forcesIn]
    exact hS.mono (fun x hx => (mem_filter.mp hx).1) subset_rfl

end Lightlike.SpinFoam.Forcing24
