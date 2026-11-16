import Lightlike.GFT.ColoredGraph

/-!
# Bubbles of a colored graph: the graph side of the dual's pseudo-manifold conditions

For a colored graph `G` (Gurau, *Lost in translation: topological singularities in group field theory*,
Class. Quantum Grav. 27 (2010) 235023, arXiv:1006.0714, Section 5) this file proves the statements about
bubbles that need only the graph, not the dual complex `Δ_G`:

* `bubble_singleton`: "the 1-bubbles are its lines": the bubble of one color is the two ends of a line.
* `card_bubble_singleton`: a line has exactly two ends. For the dual this is the non-branching condition
  of Section 2 (a `(D - 1)`-simplex is a face of precisely two `D`-simplices).
* `mem_bubble_self`: every bubble contains a vertex, the dual of a top simplex: purity of Section 2.
* `strongChain_of_connected`: in a connected graph any two vertices (top simplices) are joined by a
  chain of lines, the strong connectivity of Section 2.
* `restrict`, `restrict_isConnected`: "the `p`-bubbles are themselves colored GFT graphs in `(p - 1)`
  dimensions" (Section 5, before Theorem 1): the lines of `p` colors restricted to a bubble form a
  `ColoredGraph (p - 1)`, and it is connected: the graph-side shadow of the condition that every link of
  the dual is a pseudo manifold (normality).

## Not proved here

Theorem 1 (the `p`-bubbles are the link graphs of the `(n - p)`-simplices of the gluing `Δ_G`) and
Theorem 2 (every connected colored graph is dual to a normal simplicial pseudo manifold) are not stated.
They need the stranded graph with its link graphs (Section 3.1) and the gluing `Δ_G` of eqs. (37) and
(38), whose simplices are indexed: `Δ_G` is a multiset in Section 2, and the same vertex set can occur
for two top simplices. In the graph with two vertices and three lines both top simplices have the vertex
set `{(0, {a, b}), (1, {a, b}), (2, {a, b})}`, so a set of faces such as `SComplex.closure` would
collapse them into one. The statements here are the graph-side clauses of the definitions only.

## References

* R. Gurau, *Lost in translation: topological singularities in group field theory*, Class. Quantum
  Grav. 27 (2010) 235023, arXiv:1006.0714, Sections 2 and 5.
-/

open Finset

namespace Lightlike.GFT

variable {D E : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

/-- A vertex lies in its own bubble. -/
lemma mem_bubble_self (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (v : V) :
    v ∈ G.bubble S v :=
  (mem_bubble_iff G S v v).2 Relation.ReflTransGen.refl

omit [Fintype V] [DecidableEq V] in
lemma adj_symm (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) {a b : V} (h : G.Adj S a b) :
    G.Adj S b a := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, G.inv_inv c a⟩

omit [Fintype V] [DecidableEq V] in
/-- Reachability along lines is symmetric. -/
lemma reflTransGen_adj_symm (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) {a b : V}
    (h : Relation.ReflTransGen (G.Adj S) a b) : Relation.ReflTransGen (G.Adj S) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (adj_symm G S hbc)).trans ih

/-- **The 1-bubbles are the lines**: the bubble of the single color `c` at `v` is the two ends of the
line of color `c` at `v`. -/
theorem bubble_singleton (G : ColoredGraph D V) (c : Fin (D + 1)) (v : V) :
    G.bubble {c} v = {v, G.inv c v} := by
  ext w
  rw [mem_bubble_iff]
  simp only [mem_insert, mem_singleton]
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hadj ih =>
      obtain ⟨c', hc', rfl⟩ := hadj
      rw [mem_singleton.1 hc']
      rcases ih with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (G.inv_inv c _)
  · rintro (rfl | rfl)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨c, mem_singleton_self c, rfl⟩

/-- **A line has exactly two ends**: a bubble of one color has two vertices, since `inv c` has no
fixed point. This is the non-branching condition for the dual of a colored graph: a `(D - 1)`-simplex
is a face of exactly two `D`-simplices. -/
theorem card_bubble_singleton (G : ColoredGraph D V) (c : Fin (D + 1)) (v : V) :
    #(G.bubble {c} v) = 2 := by
  rw [bubble_singleton, card_pair (G.inv_ne c v).symm]

/-- A colored graph is connected when every vertex is in the bubble of all colors of every other. -/
def IsConnected (G : ColoredGraph D V) : Prop := ∀ v w, w ∈ G.bubble Finset.univ v

/-- **Strong connectivity of the dual of a connected colored graph**: any two vertices, the dual of
two top simplices, are joined by a chain in which neighbours are the two ends of a line, that is, share
a `(D - 1)`-simplex. -/
theorem strongChain_of_connected (G : ColoredGraph D V) (h : G.IsConnected) (v w : V) :
    Relation.ReflTransGen (G.Adj Finset.univ) v w :=
  (mem_bubble_iff G _ v w).1 (h v w)

/-- The bubble of the colors `σ c`, `c ∈ Fin (E + 1)`, is closed under the lines of those colors. -/
lemma inv_mem_bubble (G : ColoredGraph D V) (σ : Fin (E + 1) ↪ Fin (D + 1)) (v : V) (c : Fin (E + 1))
    {w : V} (hw : w ∈ G.bubble (univ.image σ) v) : G.inv (σ c) w ∈ G.bubble (univ.image σ) v := by
  rw [mem_bubble_iff] at hw ⊢
  exact hw.tail ⟨σ c, mem_image_of_mem σ (mem_univ c), rfl⟩

/-- **A `p`-bubble is a colored graph in dimension `p - 1`**: the lines of the `p` colors `σ c`
(`σ : Fin p ↪ Fin (D + 1)`, `p = E + 1`) restricted to the bubble of `v` form a colored graph with the
colors re-indexed by `Fin (E + 1)`, the orientation kept. -/
def restrict (G : ColoredGraph D V) (σ : Fin (E + 1) ↪ Fin (D + 1)) (v : V) :
    ColoredGraph E {w // w ∈ G.bubble (univ.image σ) v} where
  inv c w := ⟨G.inv (σ c) w.1, inv_mem_bubble G σ v c w.2⟩
  sign w := G.sign w.1
  inv_inv c w := Subtype.ext (G.inv_inv (σ c) w.1)
  sign_inv c w := G.sign_inv (σ c) w.1

/-- **A bubble is connected as a colored graph**: the restricted graph is connected, the graph-side
form of the normality condition for the dual (every link is a pseudo manifold, in particular strongly
connected). -/
theorem restrict_isConnected (G : ColoredGraph D V) (σ : Fin (E + 1) ↪ Fin (D + 1)) (v : V) :
    (G.restrict σ v).IsConnected := by
  intro w w'
  have hw := (mem_bubble_iff G _ v w.1).1 w.2
  have hw' := (mem_bubble_iff G _ v w'.1).1 w'.2
  have hch : Relation.ReflTransGen (G.Adj (univ.image σ)) w.1 w'.1 :=
    (reflTransGen_adj_symm G _ hw).trans hw'
  have key : ∀ u, Relation.ReflTransGen (G.Adj (univ.image σ)) w.1 u →
      ∃ hu : u ∈ G.bubble (univ.image σ) v,
        Relation.ReflTransGen ((G.restrict σ v).Adj univ) w ⟨u, hu⟩ := by
    intro u hu
    induction hu with
    | refl => exact ⟨w.2, Relation.ReflTransGen.refl⟩
    | tail _ hadj ih =>
      obtain ⟨hb, hr⟩ := ih
      obtain ⟨col, hcol, rfl⟩ := hadj
      obtain ⟨c, -, rfl⟩ := mem_image.1 hcol
      exact ⟨inv_mem_bubble G σ v c hb, hr.tail ⟨c, mem_univ c, rfl⟩⟩
  obtain ⟨hb, hr⟩ := key _ hch
  exact (mem_bubble_iff _ _ _ _).2 hr

end ColoredGraph

/-- **Trust check**: in the graph with two vertices and three lines the `1`-bubble of color `0` at `0` is
the line `{0, 1}`, and it is not the single vertex, which is the `0`-bubble. -/
example : theta.bubble {0} 0 = {0, 1} ∧ theta.bubble {0} 0 ≠ theta.bubble ∅ 0 := by
  decide +kernel

end Lightlike.GFT
