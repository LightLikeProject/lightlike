import Lightlike.PL.HexFalse

/-!
# No polygonal drawing of `K₃,₃` in the plane

This is the second claim of the proof of the weak Jordan
theorem by C. Thomassen, in the exposition of M. Klazar, arXiv:2604.04296, Section 2, Claim 2
(Klazar's numbering).

**The embedding notion.** A *polygonal drawing of `K₃,₃`* consists of six distinct points `u i`,
`v j` (`i, j ∈ Fin 3`) and nine **simple polygonal arcs**, one from `u i` to `v j` for each pair, each
a finite chain of straight segments (`IsSimpleChain`: consecutive points differ and no segment meets
the later ones except at the shared vertex), such that two different arcs meet **only in common
endpoints**. In particular an arc contains none of the six points except its own two ends. The
arcs are polygonal; the statement for arbitrary continuous arcs is a later step (Klazar, Claim 3).

**The proof route.** Klazar follows Thomassen with an orientation (left/right) argument. The proof
here splits the 6-cycle along polygonal chords (theta-split: a chord inside or outside a simple
polygon splits it into two simple polygons whose insides add up) instead.
-/

open Set

namespace Lightlike.PL

/-- A **polygonal drawing** in the plane of the bipartite graph with vertex classes of three
points and with the edges `E ⊆ Fin 3 × Fin 3`. With `E = Set.univ` this is a polygonal drawing of
`K₃,₃`. -/
structure PLDrawing (E : Set (Fin 3 × Fin 3)) where
  /-- The three points of the first class. -/
  u : Fin 3 → ℝ × ℝ
  /-- The three points of the second class. -/
  v : Fin 3 → ℝ × ℝ
  /-- The vertices of the arc from `u i` to `v j`, in order (used for `(i, j) ∈ E`). -/
  arc : Fin 3 → Fin 3 → List (ℝ × ℝ)
  /-- Each arc is a simple polygonal arc. -/
  simple : ∀ i j, (i, j) ∈ E → IsSimpleChain (arc i j)
  /-- Each arc starts at `u i`. -/
  head : ∀ i j, (i, j) ∈ E → (arc i j).head? = some (u i)
  /-- Each arc ends at `v j`. -/
  last : ∀ i j, (i, j) ∈ E → (arc i j).getLast? = some (v j)
  /-- Each arc has at least one segment. -/
  length_ge : ∀ i j, (i, j) ∈ E → 2 ≤ (arc i j).length
  /-- Two different arcs meet only in common endpoints. -/
  disj : ∀ i j i' j', (i, j) ∈ E → (i', j') ∈ E → (i, j) ≠ (i', j') →
    chainSet (arc i j) ∩ chainSet (arc i' j') ⊆ {u i, v j} ∩ {u i', v j'}
  /-- The three points of the first class are distinct. -/
  inj_u : Function.Injective u
  /-- The three points of the second class are distinct. -/
  inj_v : Function.Injective v
  /-- The two classes are disjoint. -/
  uv_ne : ∀ i j, u i ≠ v j

namespace PLDrawing

variable {d : PLDrawing Set.univ}

/-- A chain with first point `a`, last point `b` and at least two points is `a`, its interior
points, `b`. -/
lemma chain_split {l : List (ℝ × ℝ)} {a b : ℝ × ℝ} (h1 : l.head? = some a)
    (h2 : l.getLast? = some b) (h3 : 2 ≤ l.length) : ∃ m, l = a :: m ++ [b] := by
  rcases l with _ | ⟨x, t⟩
  · simp at h1
  · simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    rcases List.eq_nil_or_concat t with rfl | ⟨L, c, rfl⟩
    · simp at h3
    · simp only [List.concat_eq_append] at h2
      refine ⟨L, ?_⟩
      have : (x :: (L ++ [c])).getLast? = some c := by
        rw [← List.cons_append]; exact List.getLast?_concat ..
      rw [this] at h2
      simp only [Option.some.injEq] at h2
      subst h2
      simp

lemma exists_mid (d : PLDrawing Set.univ) :
    ∃ m : Fin 3 → Fin 3 → List (ℝ × ℝ), ∀ i j, d.arc i j = d.u i :: m i j ++ [d.v j] := by
  have : ∀ i j, ∃ m, d.arc i j = d.u i :: m ++ [d.v j] := fun i j =>
    chain_split (d.head i j (Set.mem_univ _)) (d.last i j (Set.mem_univ _))
      (d.length_ge i j (Set.mem_univ _))
  choose m hm using this
  exact ⟨m, hm⟩

/-- The corners of the hexagon `u₀ v₀ u₁ v₁ u₂ v₂`. -/
def hp (d : PLDrawing Set.univ) : Fin 6 → ℝ × ℝ := ![d.u 0, d.v 0, d.u 1, d.v 1, d.u 2, d.v 2]

/-- The pair of the arc that is the side `k` of the hexagon. -/
def hE : Fin 6 → Fin 3 × Fin 3 := ![(0, 0), (1, 0), (1, 1), (2, 1), (2, 2), (0, 2)]

/-- The pair of the arc that is the chord `k` of the hexagon. -/
def hF : Fin 6 → Fin 3 × Fin 3 := ![(0, 1), (2, 0), (1, 2), (0, 1), (2, 0), (1, 2)]

lemma hp_inj (d : PLDrawing Set.univ) : Function.Injective d.hp := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [hp, d.inj_u.eq_iff, d.inj_v.eq_iff, d.uv_ne, (d.uv_ne _ _).symm] at h ⊢

/-- The interior points of the sides. -/
def hh (m : Fin 3 → Fin 3 → List (ℝ × ℝ)) : Fin 6 → List (ℝ × ℝ) :=
  ![m 0 0, (m 1 0).reverse, m 1 1, (m 2 1).reverse, m 2 2, (m 0 2).reverse]

/-- The interior points of the chords. -/
def hd (m : Fin 3 → Fin 3 → List (ℝ × ℝ)) : Fin 6 → List (ℝ × ℝ) :=
  ![m 0 1, (m 2 0).reverse, m 1 2, (m 0 1).reverse, m 2 0, (m 1 2).reverse]

lemma hexArc_eq (d : PLDrawing Set.univ) (m) (hm : ∀ i j, d.arc i j = d.u i :: m i j ++ [d.v j])
    (k : Fin 6) : hexArc d.hp (hh m) k = d.arc (hE k).1 (hE k).2 ∨
      hexArc d.hp (hh m) k = (d.arc (hE k).1 (hE k).2).reverse := by
  fin_cases k <;> simp [hexArc, hp, hh, hE, hm]

lemma hexChord_eq (d : PLDrawing Set.univ) (m) (hm : ∀ i j, d.arc i j = d.u i :: m i j ++ [d.v j])
    (k : Fin 6) : hexChord d.hp (hd m) k = d.arc (hF k).1 (hF k).2 ∨
      hexChord d.hp (hd m) k = (d.arc (hF k).1 (hF k).2).reverse := by
  fin_cases k <;> simp [hexChord, hp, hd, hF, hm]

lemma hE_inj : Function.Injective hE := by decide

lemma hE_ne_hF (i j : Fin 6) : hE i ≠ hF j := by revert i j; decide

lemma hF_ne (i j : Fin 6) (h1 : i ≠ j) (h2 : i ≠ j + 3) : hF i ≠ hF j := by
  revert i j; decide

lemma ends_E (d : PLDrawing Set.univ) (k : Fin 6) :
    ({d.hp k, d.hp (k + 1)} : Set (ℝ × ℝ)) = {d.u (hE k).1, d.v (hE k).2} := by
  fin_cases k <;> simp [hp, hE, Set.pair_comm]

lemma ends_F (d : PLDrawing Set.univ) (k : Fin 6) :
    ({d.hp k, d.hp (k + 3)} : Set (ℝ × ℝ)) = {d.u (hF k).1, d.v (hF k).2} := by
  fin_cases k <;> simp [hp, hF, Set.pair_comm]

lemma set_E (d : PLDrawing Set.univ) (m) (hm : ∀ i j, d.arc i j = d.u i :: m i j ++ [d.v j])
    (k : Fin 6) : chainSet (hexArc d.hp (hh m) k) = chainSet (d.arc (hE k).1 (hE k).2) := by
  rcases hexArc_eq d m hm k with h | h <;> rw [h]; rw [chainSet_reverse]

lemma set_F (d : PLDrawing Set.univ) (m) (hm : ∀ i j, d.arc i j = d.u i :: m i j ++ [d.v j])
    (k : Fin 6) : chainSet (hexChord d.hp (hd m) k) = chainSet (d.arc (hF k).1 (hF k).2) := by
  rcases hexChord_eq d m hm k with h | h <;> rw [h]; rw [chainSet_reverse]

/-- The hexagon with three chords of a polygonal drawing of `K₃,₃`. -/
def toHex (d : PLDrawing Set.univ) (m : Fin 3 → Fin 3 → List (ℝ × ℝ))
    (hm : ∀ i j, d.arc i j = d.u i :: m i j ++ [d.v j]) : Hex where
  p := d.hp
  h := hh m
  d := hd m
  inj := d.hp_inj
  hrev k := by fin_cases k <;> simp [hd]
  simpleH k := by
    rcases hexArc_eq d m hm k with h | h <;> rw [h]
    · exact d.simple _ _ (Set.mem_univ _)
    · exact isSimpleChain_reverse (d.simple _ _ (Set.mem_univ _))
  simpleD k := by
    rcases hexChord_eq d m hm k with h | h <;> rw [h]
    · exact d.simple _ _ (Set.mem_univ _)
    · exact isSimpleChain_reverse (d.simple _ _ (Set.mem_univ _))
  interHH i j hij := by
    rw [set_E d m hm, set_E d m hm, ends_E, ends_E]
    exact d.disj _ _ _ _ (Set.mem_univ _) (Set.mem_univ _)
      (fun h => hij (hE_inj (Prod.ext_iff.2 ⟨by simpa using congrArg Prod.fst h,
        by simpa using congrArg Prod.snd h⟩)))
  interHD i j := by
    rw [set_E d m hm, set_F d m hm, ends_E, ends_F]
    exact d.disj _ _ _ _ (Set.mem_univ _) (Set.mem_univ _) (hE_ne_hF i j)
  interDD i j hij hij3 := by
    rw [set_F d m hm, set_F d m hm, ends_F, ends_F]
    exact d.disj _ _ _ _ (Set.mem_univ _) (Set.mem_univ _) (hF_ne i j hij hij3)

end PLDrawing

/-- **There is no polygonal drawing of `K₃,₃` in the plane.** Six distinct points, joined across the
two classes by nine simple polygonal arcs that meet only in common endpoints, do not exist
(Thomassen's proof of the weak Jordan theorem; Klazar, Section 2, Claim 2, Klazar's numbering).

The proof splits the 6-cycle along polygonal chords instead of Thomassen's orientation argument. It
uses that the parity of the crossings of the horizontal ray, which is a count modulo 2, is additive
when a closed chain is cut along a chord and glued from the two halves: `chainParity_append` and
`chainParity_reverse` in `Lightlike/PL/Chain.lean` (the chord is counted twice, and `1 + 1 = 0`),
with `Polygon.parity_ofList` linking it to the parity of a polygon.

**Limits.** The arcs are polygonal arcs only; the statement for arbitrary continuous arcs is
Claim 3 (a later step). **Non-vacuity (planned).** The hypotheses can be satisfied: the drawing
with the edge `(2, 2)` removed, `PLDrawing (Set.univ \ {(2, 2)})`, is inhabited by eight explicit
segments in a convex position of the six points, so the disjointness hypotheses are not
contradictory; the example is built in `TestsK33.lean`. -/
theorem no_PL_K33 (d : PLDrawing Set.univ) : False := by
  obtain ⟨m, hm⟩ := PLDrawing.exists_mid d
  exact (PLDrawing.toHex d m hm).false

end Lightlike.PL
