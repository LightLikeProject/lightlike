import Lightlike.PL.SimpleChain

/-!
# No polygonal drawing of `K₃,₃` in the plane

Statements only (not imported; `sorry`). This is the second claim of the proof of the weak Jordan
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

/-- A **polygonal drawing of `K₃,₃`** in the plane. -/
structure PLK33 where
  /-- The three points of the first class. -/
  u : Fin 3 → ℝ × ℝ
  /-- The three points of the second class. -/
  v : Fin 3 → ℝ × ℝ
  /-- The vertices of the arc from `u i` to `v j`, in order. -/
  arc : Fin 3 → Fin 3 → List (ℝ × ℝ)
  /-- Each arc is a simple polygonal arc. -/
  simple : ∀ i j, IsSimpleChain (arc i j)
  /-- Each arc starts at `u i`. -/
  head : ∀ i j, (arc i j).head? = some (u i)
  /-- Each arc ends at `v j`. -/
  last : ∀ i j, (arc i j).getLast? = some (v j)
  /-- Each arc has at least one segment. -/
  length_ge : ∀ i j, 2 ≤ (arc i j).length
  /-- Two different arcs meet only in common endpoints. -/
  disj : ∀ i j i' j', (i, j) ≠ (i', j') →
    chainSet (arc i j) ∩ chainSet (arc i' j') ⊆ {u i, v j} ∩ {u i', v j'}
  /-- The three points of the first class are distinct. -/
  inj_u : Function.Injective u
  /-- The three points of the second class are distinct. -/
  inj_v : Function.Injective v
  /-- The two classes are disjoint. -/
  uv_ne : ∀ i j, u i ≠ v j

/-- **There is no polygonal drawing of `K₃,₃` in the plane.** The six points, joined pairwise
across the two classes by nine simple polygonal arcs that meet only in common endpoints, do not
exist (Thomassen's proof of the weak Jordan theorem; Klazar, Section 2, Claim 2, Klazar's
numbering; the proof here splits the 6-cycle along polygonal chords instead of using an orientation
argument). -/
theorem no_PL_K33 (c : PLK33) : False := by
  sorry

end Lightlike.PL
