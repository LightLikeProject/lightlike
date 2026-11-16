import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Relation
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Fin.VecNotation

/-!
# Colored graphs and the Euler characteristic of their dual complex

A colored graph of dimension `D` has vertices of two orientations (positive and negative) and lines
of `D + 1` colors; every vertex has exactly one line of each color and every line joins a positive
vertex to a negative one (Gurau 2010, Section 5). `ColoredGraph D V` models this with one
fixed-point-free involution per color, `inv c v` being the other end of the line of color `c` at `v`,
and an orientation `sign` that every involution flips. Mathlib's `SimpleGraph.EdgeLabeling` does not
fit: colored graphs have parallel lines of different colors, as in the graph with two vertices and
three lines.

A `p`-bubble is a connected component of the subgraph of the lines whose colors lie in a set `S` with
`#S = p`; `bubble G S v` computes it as the set of vertices reachable from `v` in `#V` steps. The
dual complex `Δ_G` has one `k`-simplex for each `(D − k)`-bubble (Gurau, Theorem 2 and eq. (38)); its
simplices are counted here, not built, because they can share their vertex sets (a simplicial
*pseudo*-complex).

## Main results

* `ColoredGraph`, `ColoredGraph.bubble`, `ColoredGraph.nBubbles`: the definitions.
* `ColoredGraph.mem_bubble_iff`: the computed bubble is the connected component: `w` lies in the
  `S`-bubble of `v` exactly when it is reachable along lines with colors in `S`.
* `ColoredGraph.nBubbles_empty`: there are `#V` `0`-bubbles, the top simplices of the dual.
* `ColoredGraph.even_card`, `not_nonempty_coloredGraph_fin3`: a colored graph has an even number of
  vertices, so there is none on three vertices.
* `ColoredGraph.twoChi2`: twice the Euler characteristic of the dual of a graph of dimension `2`,
  `2 (B₀₁ + B₀₂ + B₁₂) − #V`, from `#V` triangles, `3 #V / 2` edges (the lines) and the bicolored
  cycles as vertices. The genus is `1 − χ / 2`.
* `twoChi2_theta`, `twoChi2_torus`: the graph with two vertices gives `χ = 2` (sphere) and a graph
  with six vertices gives `χ = 0` (torus); both by `decide +kernel`.
* `IsProper`, `badLines_not_proper`: an improperly colored graph (two lines of one color at a
  vertex) is not a colored graph.

Open: only the face count of the dual is formalized, not a closed surface built from it, so the face
count is not shown to be that surface's Euler characteristic; and the evenness of `χ` for a connected
graph is not shown.

## References

- R. Gurau, *Lost in translation: topological singularities in group field theory*,
  Class. Quantum Grav. 27 (2010) 235023, arXiv:1006.0714, Section 5, Theorems 1 and 2.
-/

open Finset

namespace Lightlike.GFT

/-- A properly colored graph of dimension `D`: `inv c v` is the other end of the line of color `c`
at `v`, `sign` is the orientation. -/
structure ColoredGraph (D : ℕ) (V : Type*) where
  /-- The other end of the line of color `c` at `v`. -/
  inv : Fin (D + 1) → V → V
  /-- The orientation of a vertex. -/
  sign : V → Bool
  /-- A line has two ends. -/
  inv_inv : ∀ c v, inv c (inv c v) = v
  /-- Every line joins vertices of opposite orientation. -/
  sign_inv : ∀ c v, sign (inv c v) ≠ sign v

variable {D : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace ColoredGraph

/-- One step along a line of a color in `S`. -/
def step (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (A : Finset V) : Finset V :=
  A ∪ (univ.filter fun w => ∃ c ∈ S, ∃ v ∈ A, G.inv c v = w)

/-- The `S`-bubble of `v`: all vertices reachable along lines with colors in `S`. -/
def bubble (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (v : V) : Finset V :=
  (G.step S)^[Fintype.card V] {v}

/-- The number of `S`-bubbles. -/
def nBubbles (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) : ℕ :=
  #(univ.image (G.bubble S))

/-- Twice the Euler characteristic of the dual complex of a graph of dimension `2`:
`2χ = 2 (B₀₁ + B₀₂ + B₁₂) − V`, from `V` triangles (0-bubbles), `3V/2` edges (the lines) and the
vertices `B_{ij}` (the bicolored cycles). -/
def twoChi2 (G : ColoredGraph 2 V) : ℤ :=
  2 * ((G.nBubbles {0, 1} : ℤ) + G.nBubbles {0, 2} + G.nBubbles {1, 2}) - Fintype.card V

omit [Fintype V] [DecidableEq V] in
/-- A line has two distinct ends: `inv c` has no fixed point, because it flips the orientation. -/
lemma inv_ne (G : ColoredGraph D V) (c : Fin (D + 1)) (v : V) : G.inv c v ≠ v :=
  fun h => G.sign_inv c v (by rw [h])

/-- A step along no color does not move. -/
lemma step_empty (G : ColoredGraph D V) (A : Finset V) : G.step ∅ A = A := by
  unfold step
  ext x
  simp

/-- The `0`-bubbles are the vertices. -/
lemma bubble_empty (G : ColoredGraph D V) (v : V) : G.bubble ∅ v = {v} := by
  have h : ∀ n, (G.step ∅)^[n] {v} = {v} := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, step_empty]
  exact h _

/-- There are as many `0`-bubbles as vertices: the `V` simplices of top dimension of the dual. -/
lemma nBubbles_empty (G : ColoredGraph D V) : G.nBubbles ∅ = Fintype.card V := by
  unfold nBubbles
  rw [show G.bubble ∅ = fun v => ({v} : Finset V) from funext (bubble_empty G),
    Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_univ]


/-- The lines of the colors in `S`, as a relation between vertices. -/
def Adj (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (a b : V) : Prop :=
  ∃ c ∈ S, G.inv c a = b

lemma subset_step (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (A : Finset V) :
    A ⊆ G.step S A := subset_union_left

lemma mem_step (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (A : Finset V) (w : V) :
    w ∈ G.step S A ↔ w ∈ A ∨ ∃ v ∈ A, G.Adj S v w := by
  unfold step Adj
  simp only [mem_union, mem_filter, mem_univ, true_and]
  constructor
  · rintro (h | ⟨c, hc, v, hv, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, c, hc, rfl⟩
  · rintro (h | ⟨v, hv, c, hc, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, v, hv, rfl⟩

/-- The iterates of the step are increasing, and stable from `#V` steps on. -/
lemma step_stable (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (v : V) :
    G.step S ((G.step S)^[Fintype.card V] {v}) = (G.step S)^[Fintype.card V] {v} := by
  set a : ℕ → Finset V := fun n => (G.step S)^[n] {v} with ha
  have hsucc : ∀ n, a (n + 1) = G.step S (a n) := fun n => by
    simp only [ha, Function.iterate_succ_apply']
  have hmono : ∀ n, a n ⊆ a (n + 1) := fun n => by rw [hsucc]; exact subset_step _ _ _
  have hcard : ∀ n, (∀ m < n, a m ≠ a (m + 1)) → n + 1 ≤ #(a n) := by
    intro n
    induction n with
    | zero => intro _; simp [ha]
    | succ n ih =>
      intro h
      have h1 := ih (fun m hm => h m (by omega))
      have h2 : a n ⊂ a (n + 1) := (hmono n).ssubset_of_ne (h n (by omega))
      have := card_lt_card h2
      omega
  by_cases hall : ∀ m < Fintype.card V, a m ≠ a (m + 1)
  · have := hcard _ hall
    have h2 : #(a (Fintype.card V)) ≤ Fintype.card V := card_le_univ _
    omega
  · push Not at hall
    obtain ⟨m, hm, hEq⟩ := hall
    have hfix : ∀ k, a (m + k) = a m := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        show a (m + k + 1) = a m
        rw [hsucc, ih, ← hsucc]
        exact hEq.symm
    have hN : a (Fintype.card V) = a m := by
      have := hfix (Fintype.card V - m); rwa [Nat.add_sub_cancel' hm.le] at this
    show G.step S (a (Fintype.card V)) = a (Fintype.card V)
    rw [hN, ← hsucc]
    exact hEq.symm

/-- **The computed bubble is the connected component.** `w` lies in the `S`-bubble of `v` exactly
when `w` is reachable from `v` along lines with colors in `S`. -/
theorem mem_bubble_iff (G : ColoredGraph D V) (S : Finset (Fin (D + 1))) (v w : V) :
    w ∈ G.bubble S v ↔ Relation.ReflTransGen (G.Adj S) v w := by
  constructor
  · intro h
    unfold bubble at h
    generalize Fintype.card V = N at h
    induction N generalizing w with
    | zero => simp at h; subst h; exact Relation.ReflTransGen.refl
    | succ N ih =>
      rw [Function.iterate_succ_apply', mem_step] at h
      rcases h with h | ⟨u, hu, hadj⟩
      · exact ih w h
      · exact (ih u hu).tail hadj
  · intro h
    have hclosed := step_stable G S v
    induction h with
    | refl => 
      unfold bubble
      generalize Fintype.card V = N
      induction N with
      | zero => simp
      | succ N ih => rw [Function.iterate_succ_apply']; exact subset_step _ _ _ ih
    | tail _ hadj ih =>
      have : _ ∈ G.step S (G.bubble S v) := (mem_step _ _ _ _).2 (Or.inr ⟨_, ih, hadj⟩)
      unfold bubble at this ih ⊢
      rwa [hclosed] at this

omit [DecidableEq V] in
/-- **A colored graph has an even number of vertices**: the line of color `0` pairs every positive
vertex with a negative one. -/
theorem even_card (G : ColoredGraph D V) : Even (Fintype.card V) := by
  have hP : #(univ.filter fun v => G.sign v = true) = #(univ.filter fun v => G.sign v = false) := by
    apply Finset.card_nbij' (G.inv 0) (G.inv 0)
    · intro v hv
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hv ⊢
      have := G.sign_inv 0 v
      cases h : G.sign (G.inv 0 v) <;> simp_all
    · intro v hv
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hv ⊢
      have := G.sign_inv 0 v
      cases h : G.sign (G.inv 0 v) <;> simp_all
    · intro v _; exact G.inv_inv 0 v
    · intro v _; exact G.inv_inv 0 v
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset V)) (fun v => G.sign v = true)
  simp only [Bool.not_eq_true, Finset.card_univ] at this
  exact ⟨#(univ.filter fun v => G.sign v = true), by omega⟩

end ColoredGraph

/-! ### Examples -/

/-- The graph with two vertices and three lines, of the three colors: the dual complex is the
2-sphere made of two triangles. -/
def theta : ColoredGraph 2 (Fin 2) where
  inv _ v := 1 - v
  sign v := decide (v = 0)
  inv_inv := by decide
  sign_inv := by decide

/-- The theta graph has `B₀₁ = B₀₂ = B₁₂ = 1`, so `2χ = 2·3 − 2 = 4`: genus `0`. -/
theorem twoChi2_theta : theta.twoChi2 = 4 := by decide +kernel

/-- A colored graph with six vertices whose dual complex is a torus: positive vertices `0, 1, 2`,
negative vertices `3, 4, 5`, and the three colors the three cyclic matchings `i ↔ 3 + i`,
`0 ↔ 4, 1 ↔ 5, 2 ↔ 3`, `0 ↔ 5, 1 ↔ 3, 2 ↔ 4`. -/
def torus : ColoredGraph 2 (Fin 6) where
  inv c := ![![3, 4, 5, 0, 1, 2], ![4, 5, 3, 2, 0, 1], ![5, 3, 4, 1, 2, 0]] c
  sign v := decide (v.val < 3)
  inv_inv := by decide
  sign_inv := by decide

/-- The torus graph has `B₀₁ + B₀₂ + B₁₂ = 3` and `V = 6`, so `2χ = 0`: genus `1`. -/
theorem twoChi2_torus : torus.twoChi2 = 0 := by decide +kernel

/-! ### An improperly colored graph -/

/-- An edge-colored graph given by a list of lines `(u, v, color)`. It is *properly colored* when
every vertex lies on exactly one line of every color. -/
def IsProper (D : ℕ) (V : Type*) [Fintype V] [DecidableEq V] (E : List (V × V × Fin (D + 1))) : Prop :=
  ∀ v c, (E.filter fun e => (e.1 = v || e.2.1 = v) && e.2.2 = c).length = 1

instance (D : ℕ) (V : Type*) [Fintype V] [DecidableEq V] (E : List (V × V × Fin (D + 1))) :
    Decidable (IsProper D V E) := by unfold IsProper; infer_instance

/-- The lines of the theta graph. -/
def thetaLines : List (Fin 2 × Fin 2 × Fin 3) := [(0, 1, 0), (0, 1, 1), (0, 1, 2)]

/-- Two lines of color `0` meet at vertex `1` and vertex `2` has no line of color `1`. -/
def badLines : List (Fin 3 × Fin 3 × Fin 2) := [(0, 1, 0), (1, 2, 0), (0, 2, 1)]

theorem thetaLines_proper : IsProper 2 (Fin 2) thetaLines := by decide

/-- **Wrong model.** An improperly colored graph is not a colored graph: vertex `1` carries two lines
of color `0`, so no involution of color `0` exists and the dual gluing has no `2`-simplex around it. -/
theorem badLines_not_proper : ¬ IsProper 1 (Fin 3) badLines := by decide

/-- **No colored graph on three vertices**: the pairing of the vertices by one color is impossible
with an odd number of them, so an edge-colored graph with a vertex of degree one in every color on
three vertices (such as `badLines`, which has two lines of color `0` at one vertex instead) cannot be
a colored graph. -/
theorem not_nonempty_coloredGraph_fin3 (D : ℕ) : IsEmpty (ColoredGraph D (Fin 3)) :=
  ⟨fun G => by
    have h := G.even_card
    rw [Fintype.card_fin] at h
    obtain ⟨r, hr⟩ := h
    omega⟩

end Lightlike.GFT
