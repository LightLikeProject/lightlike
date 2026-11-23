import Lightlike.PL.Schoenflies.RegionExtension
import Lightlike.PL.Schoenflies.PolygonExhaust

/-!
# The closed region of a simple polygon is compact

Row G3-188, milestone PL5 (third pass), item 5c.  For a simple polygon `p` the closed region
`region p = p.inside ∪ p.carrier` is the closure of the inside (the carrier is the frontier of the inside),
hence closed, and it is bounded (parity vanishes far away); so it is compact.

* `region_eq_closure_inside`, `isCompact_region`.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- The closed region of a simple polygon is the closure of its inside. -/
lemma region_eq_closure_inside {n : ℕ} [NeZero n] {p : Polygon n} (hs : p.IsSimple) :
    region p = closure p.inside := by
  have hf : frontier p.inside = p.carrier := Polygon.frontier_class hs 1
  rw [region, closure_eq_interior_union_frontier, (Polygon.isOpen_inside p).interior_eq, hf]

/-- **The closed region of a simple polygon is compact.** -/
theorem isCompact_region {n : ℕ} [NeZero n] {p : Polygon n} (hs : p.IsSimple) :
    IsCompact (region p) := by
  have hcl : IsClosed (region p) := by
    rw [region_eq_closure_inside hs]; exact isClosed_closure
  set M : ℝ := ∑ i, ‖p i‖ with hMdef
  have hM : ∀ i, ‖p i‖ ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => ‖p i‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hb : Bornology.IsBounded (region p) := by
    refine (Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := M)).subset ?_
    rintro z (hz | hz)
    · by_contra hzn
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hzn
      have h0 := Polygon.parity_eq_zero_far (p := p) hM0 hM hzn
      have h1 : p.parity z = 1 := hz.2
      rw [h0] at h1
      exact absurd h1 (by decide)
    · exact Polygon.carrier_subset_closedBall hM hz
  exact Metric.isCompact_of_isClosed_isBounded hcl hb

end Lightlike.PL.Schoenflies
