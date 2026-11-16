import Lightlike.PL.ArcSet
import Lightlike.PL.ContK33

/-!
# No drawing of `K₃,₃` by arcs given as sets

`no_K33` for a drawing whose arcs are given as subsets of the plane (`IsArc`), the form used when
the arcs are built from pieces of other arcs.

## Main results

* `SetDrawing`, `no_K33_set`.
-/

open Set

namespace Lightlike.PL

/-- A drawing of `K₃,₃` whose nine arcs are given as sets: `A i j` is an arc from `u i` to `v j`,
and two different arcs meet only in common endpoints. -/
structure SetDrawing where
  /-- The three points of the first class. -/
  u : Fin 3 → ℝ × ℝ
  /-- The three points of the second class. -/
  v : Fin 3 → ℝ × ℝ
  /-- The arc from `u i` to `v j`, as a set. -/
  A : Fin 3 → Fin 3 → Set (ℝ × ℝ)
  /-- Each `A i j` is an arc from `u i` to `v j`. -/
  arc : ∀ i j, IsArc (A i j) (u i) (v j)
  /-- Two different arcs meet only in common endpoints. -/
  disj : ∀ i j i' j', (i, j) ≠ (i', j') → A i j ∩ A i' j' ⊆ {u i, v j} ∩ {u i', v j'}
  /-- The three points of the first class are distinct. -/
  inj_u : Function.Injective u
  /-- The three points of the second class are distinct. -/
  inj_v : Function.Injective v
  /-- The two classes are disjoint. -/
  uv_ne : ∀ i j, u i ≠ v j

/-- **There is no drawing of `K₃,₃` in the plane by arcs given as sets.** -/
theorem no_K33_set (D : SetDrawing) : False := by
  choose γ hc hi h0 h1 himg using D.arc
  exact no_K33
    { u := D.u
      v := D.v
      γ := γ
      cont := hc
      inj := hi
      start := h0
      stop := h1
      disj := fun i j i' j' hne => by
        rw [himg, himg]
        exact D.disj i j i' j' hne
      inj_u := D.inj_u
      inj_v := D.inj_v
      uv_ne := D.uv_ne }

end Lightlike.PL
