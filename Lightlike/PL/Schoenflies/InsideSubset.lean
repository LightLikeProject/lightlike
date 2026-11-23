import Mathlib
import Lightlike.PL.Polygon
import Lightlike.PL.PolygonJordan

/-!
# The inside of a polygon avoids a connected unbounded set

Row G3-188, milestone PL5 (third pass), item 5b, route A, step R5.  A preconnected unbounded set that misses
the carrier of a polygon lies in the class of crossing parity `0` (the unbounded one).  Hence if the carrier
of a polygon lies in an open set `U` whose complement is preconnected and unbounded, every point of
crossing parity `1` lies in `U`: the inside of the polygon lies in `U`.

* `parity_eq_zero_of_unbounded`: the first statement.
* `mem_of_parity_eq_one`: the second.
-/

namespace Lightlike.PL.Schoenflies

open Set Lightlike.PL

/-- **A preconnected unbounded set off the carrier has parity `0`.** -/
lemma parity_eq_zero_of_unbounded {n : ℕ} (p : Polygon n) {A : Set (ℝ × ℝ)} (hA : IsPreconnected A)
    (hAc : A ⊆ p.carrierᶜ) (hub : ¬ Bornology.IsBounded A) : ∀ z ∈ A, p.parity z = 0 := by
  obtain ⟨M, hM0, hM⟩ := Polygon.exists_bound p
  have hfar : ∃ y ∈ A, M < ‖y‖ := by
    by_contra hcon
    push Not at hcon
    exact hub ((Metric.isBounded_closedBall (x := (0 : ℝ × ℝ)) (r := M)).subset fun y hy => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hcon y hy)
  obtain ⟨y, hyA, hy⟩ := hfar
  intro z hz
  rw [constOn_of_isPreconnected (Polygon.isClosed_carrier p)
    (fun x hx => Polygon.eventually_parity_eq p hx) hA hAc hz hyA]
  exact Polygon.parity_eq_zero_far hM0 hM hy

/-- **The inside of a polygon in an open set with preconnected unbounded complement lies in the set.**
If `p.carrier ⊆ U` and `Uᶜ` is preconnected and unbounded, then `p.parity z = 1` implies `z ∈ U`. -/
theorem mem_of_parity_eq_one {n : ℕ} (p : Polygon n) {U : Set (ℝ × ℝ)} (hcar : p.carrier ⊆ U)
    (hV : IsPreconnected Uᶜ) (hub : ¬ Bornology.IsBounded Uᶜ) {z : ℝ × ℝ} (hz : p.parity z = 1) :
    z ∈ U := by
  by_contra hzU
  have h0 := parity_eq_zero_of_unbounded p hV (fun w hw hw' => hw (hcar hw')) hub z hzU
  rw [h0] at hz
  exact absurd hz (by decide)

end Lightlike.PL.Schoenflies
