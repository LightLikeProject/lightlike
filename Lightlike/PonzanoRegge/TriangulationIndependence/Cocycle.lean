module

public import Lightlike.PonzanoRegge.TriangulationIndependence.TreeConnected

/-!
# A cohomological obstruction to tree-connectedness

Part of the closed-manifold gauge-tree question (Freidel–Louapre 2004, Section III). Triangle
exchanges (`TreeExchange`) keep a hidden invariant of the gauge tree, which this file isolates for
coefficients in `ZMod 2` (so that no orientation is needed on the edges of `K`).

* `Cocycle2 K ω`: a `ZMod 2`-valued function `ω` on edges with `ω uv + ω vw = ω uw` on every
  triangle `uvw` of `K` (a 1-cocycle of the 2-skeleton).
* `FlatOn ω g T`: the gauge edges `T` are *flat* for the potential `g : V → ZMod 2`, that is
  `g x + g y = ω xy` on every edge `xy ∈ T`.
* `flatOn_iff_of_exchange`, `flatOn_iff_of_eqvGen_exchange`: for a cocycle, flatness of `T` for a
  fixed potential `g` is unchanged by one exchange, hence along a chain of exchanges.
* `TreeConnected.flatOn`: on a tree-connected complex, if one maximal tree is flat for `g` then so
  is every maximal tree.
* `not_treeConnected_of_cocycle`: if a maximal tree is flat for `g` and another maximal tree is not,
  the complex is not `TreeConnected`.

Every maximal tree `T` is flat for a potential `g_T` (unique up to a constant, and all of them
are potentials), and an edge `e` outside `T` is flat for `g_T` exactly when `ω` vanishes on the
cycle that `e` closes in `T`. So `¬ TreeConnected` follows whenever `ω` is not a coboundary on the
1-skeleton, i.e. whenever `H¹(K; ZMod 2)` of the 2-skeleton is not zero (a cohomology class that
no tree can see as exact): see `Lightlike/PonzanoRegge/TriangulationIndependence/Tests/Cocycle.lean`.
This shows that `TreeConnected` cannot hold on every closed combinatorial 3-manifold; it does not
show that the amplitude depends on the tree there.
-/

@[expose] public section

namespace Lightlike.PR

open Finset

variable {V : Type*} [DecidableEq V]

/-- A `ZMod 2`-valued 1-cocycle on the 2-skeleton of `K`. -/
def Cocycle2 (K : Complex3 V) (ω : Finset V → ZMod 2) : Prop :=
  ∀ ⦃u v w : V⦄, u ≠ v → v ≠ w → u ≠ w → ({u, v, w} : Finset V) ∈ K.tris →
    ω {u, v} + ω {v, w} = ω {u, w}

/-- The edges `T` are flat for the potential `g` of the cochain `ω`. -/
def FlatOn (ω : Finset V → ZMod 2) (g : V → ZMod 2) (T : Finset (Finset V)) : Prop :=
  ∀ ⦃x y : V⦄, ({x, y} : Finset V) ∈ T → g x + g y = ω {x, y}

private lemma zmod2_two (a : ZMod 2) : a + a = 0 := by revert a; decide

/-- **One triangle exchange keeps flatness**, in both directions (for a cocycle). -/
theorem flatOn_iff_of_exchange {K : Complex3 V} {ω : Finset V → ZMod 2} (hω : Cocycle2 K ω)
    (g : V → ZMod 2) {T T' : Finset (Finset V)} (h : TreeExchange K T T') :
    FlatOn ω g T ↔ FlatOn ω g T' := by
  obtain @⟨hT, u, v, w, huv, hvw, huw, hτ, he, hg, hf⟩ := h
  have hc := hω huv hvw huw hτ
  have hge : ({v, w} : Finset V) ≠ {u, v} := fun h => huw (by
    have : w ∈ ({u, v} : Finset V) := h ▸ (by simp)
    simp only [mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact h'.symm
    · exact absurd h'.symm hvw)
  constructor
  · intro hfl x y hxy
    rcases mem_insert.mp hxy with h | h
    · have key : g u + g w = ω {u, w} := by
        have a := hfl he
        have b := hfl hg
        linear_combination a + b + hc - zmod2_two (g v)
      rcases pair_eq_pair_iff'.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact key
      · rw [h1, h2, add_comm, pair_comm]; exact key
    · exact hfl (mem_of_mem_erase h)
  · intro hfl x y hxy
    by_cases hx : ({x, y} : Finset V) = {u, v}
    · rw [hx]
      have a := hfl (x := u) (y := w) (mem_insert_self _ _)
      have b := hfl (x := v) (y := w) (mem_insert_of_mem (mem_erase.mpr ⟨hge, hg⟩))
      have key : g u + g v = ω {u, v} := by
        linear_combination a + b - hc - zmod2_two (g w) + zmod2_two (ω {v, w})
      rcases pair_eq_pair_iff'.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact key
      · rw [h1, h2, add_comm]; exact key
    · exact hfl (mem_insert_of_mem (mem_erase.mpr ⟨hx, hxy⟩))

/-- Flatness for a fixed potential is the same along a chain of exchanges. -/
theorem flatOn_iff_of_eqvGen_exchange {K : Complex3 V} {ω : Finset V → ZMod 2}
    (hω : Cocycle2 K ω) (g : V → ZMod 2) {T T' : Finset (Finset V)}
    (h : Relation.EqvGen (TreeExchange K) T T') : FlatOn ω g T ↔ FlatOn ω g T' := by
  induction h with
  | rel _ _ hs => exact flatOn_iff_of_exchange hω g hs
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- **On a tree-connected complex, flatness of one maximal tree for a potential gives flatness of
all of them.** -/
theorem TreeConnected.flatOn {K : Complex3 V} (h : TreeConnected K) {ω : Finset V → ZMod 2}
    (hω : Cocycle2 K ω) {g : V → ZMod 2} {T T' : Finset (Finset V)} (hT : IsMaxTree K T)
    (hT' : IsMaxTree K T') (hfl : FlatOn ω g T) : FlatOn ω g T' :=
  (flatOn_iff_of_eqvGen_exchange hω g (h hT hT')).mp hfl

/-- **Obstruction**: a cocycle `ω`, a potential `g` for which one maximal tree is flat and another
is not, show that `K` is not `TreeConnected`. -/
theorem not_treeConnected_of_cocycle {K : Complex3 V} {ω : Finset V → ZMod 2}
    (hω : Cocycle2 K ω) {g : V → ZMod 2} {T T' : Finset (Finset V)} (hT : IsMaxTree K T)
    (hT' : IsMaxTree K T') (hfl : FlatOn ω g T) (hnf : ¬ FlatOn ω g T') : ¬ TreeConnected K :=
  fun h => hnf (h.flatOn hω hT hT' hfl)

end Lightlike.PR
