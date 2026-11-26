import Mathlib
import Lightlike.PL.Schoenflies.RegionCompact

/-!
# Limit points of a subset of the inside

Row G3-188 (PL5), ring cells.  A point of the closure of a subset of the inside of a simple polygon that is not on the
carrier lies in the inside.
-/

open Set

namespace Lightlike.PL.Schoenflies

open Lightlike.PL

theorem mem_inside_of_mem_closure {n : ℕ} [NeZero n] {Q : Polygon n} (hs : Q.IsSimple) {S : Set (ℝ × ℝ)}
    (hS : S ⊆ Q.inside) {x : ℝ × ℝ} (hx : x ∈ closure S) (hxC : x ∉ Q.carrier) : x ∈ Q.inside := by
  have h1 : x ∈ closure Q.inside := closure_mono hS hx
  rw [← region_eq_closure_inside hs] at h1
  rcases h1 with h | h
  · exact h
  · exact absurd h hxC

end Lightlike.PL.Schoenflies
