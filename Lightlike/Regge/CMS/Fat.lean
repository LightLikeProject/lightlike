import Mathlib
import Lightlike.Regge.CMS.Angle

/-!
# Fat triangles, vertex stars and the vertex deficit (RC6b, step 3)

In dimension two the Regge deficit sits at the vertices. A vertex `v` of a triangulated surface is
surrounded by the cyclic list of its neighbours `w 0, …, w (n - 1)`, and the triangles of its star
are `(v, w i, w (i + 1))`. Given squared edge lengths `d`, the deficit is `2π` minus the sum of the
angles at `v`.

The triangulation lives in a chart, as straight triangles of the plane, and a triangle is fat when
its Euclidean angles stay away from `0` and `π`. Fatness is measured in the chart, which is
equivalent to fatness in any metric that is uniformly equivalent to the Euclidean one.

## Main results

* `IsFat κ x y z`: the three Euclidean angles of the triangle `x y z` lie in `[κ, π - κ]`.
* `IsStar v w`: the neighbours `w` surround `v` in the plane: the Euclidean angles at `v` of the
  triangles `(v, w i, w (i + 1))` add up to `2π`.
* `starAngleSum d v w`: the sum of the angles at `v` computed from the squared lengths `d`.
* `vertexDeficit d v w`: `2π - starAngleSum d v w`.

* `IsStar.vertexDeficit_euclid`: with the Euclidean squared lengths the deficit of a star is `0`.
  This is the flat trust check.
* `vertexDeficit_euclid_ne`: the deficit of a star whose angles do not close up is not `0`, so the
  hypothesis `IsStar` is needed.
-/

open Real EuclideanGeometry

namespace Lightlike.CMS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A triangle is `κ`-**fat** when its three Euclidean angles lie in `[κ, π - κ]`. -/
def IsFat (κ : ℝ) (x y z : E) : Prop :=
  (κ ≤ ∠ y x z ∧ ∠ y x z ≤ π - κ) ∧ (κ ≤ ∠ x y z ∧ ∠ x y z ≤ π - κ) ∧
    (κ ≤ ∠ x z y ∧ ∠ x z y ≤ π - κ)

/-- The sum of the angles at `v` of the triangles `(v, w i, w (i + 1))`, with the squared edge
lengths `d`. The index runs over `ZMod n`, so the list of neighbours is cyclic. -/
noncomputable def starAngleSum {n : ℕ} [NeZero n] (d : E → E → ℝ) (v : E) (w : ZMod n → E) : ℝ :=
  ∑ i, triAngle (d v (w i)) (d v (w (i + 1))) (d (w i) (w (i + 1)))

/-- The **deficit angle** at `v`: `2π` minus the sum of the angles at `v` of its star. -/
noncomputable def vertexDeficit {n : ℕ} [NeZero n] (d : E → E → ℝ) (v : E) (w : ZMod n → E) : ℝ :=
  2 * π - starAngleSum d v w

/-- The neighbours `w` **surround** `v`: the Euclidean angles at `v` of the triangles
`(v, w i, w (i + 1))` add up to `2π`. -/
def IsStar {n : ℕ} [NeZero n] (v : E) (w : ZMod n → E) : Prop :=
  ∑ i, ∠ (w i) v (w (i + 1)) = 2 * π

/-- The squared Euclidean distance. -/
def eucSq (x y : E) : ℝ := dist x y ^ 2

theorem starAngleSum_euclid {n : ℕ} [NeZero n] (v : E) (w : ZMod n → E) :
    starAngleSum eucSq v w = ∑ i, ∠ (w i) v (w (i + 1)) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have := triAngle_eq_angle (w i) v (w (i + 1))
  simpa [eucSq, dist_comm] using this

/-- **A flat star has zero deficit.** With the squared Euclidean lengths, the deficit of the
neighbours that surround `v` is `0`. -/
theorem IsStar.vertexDeficit_euclid {n : ℕ} [NeZero n] {v : E} {w : ZMod n → E}
    (h : IsStar v w) : vertexDeficit eucSq v w = 0 := by
  rw [vertexDeficit, starAngleSum_euclid, h]; ring

/-- **The hypothesis `IsStar` is needed.** When the Euclidean angles at `v` do not add up to `2π`,
the deficit computed from the Euclidean lengths is `2π` minus their sum, which is not `0`. -/
theorem vertexDeficit_euclid_ne {n : ℕ} [NeZero n] {v : E} {w : ZMod n → E}
    (h : ¬ IsStar v w) : vertexDeficit eucSq v w ≠ 0 := by
  intro h0
  apply h
  rw [vertexDeficit, starAngleSum_euclid] at h0
  unfold IsStar
  linarith

/-! ## Non-vacuity: the four axis points surround the origin -/

/-- The four unit vectors `e₀, e₁, -e₀, -e₁` of the plane, cyclically. -/
noncomputable def axisNbrs : ZMod 4 → EuclideanSpace ℝ (Fin 2) :=
  ![EuclideanSpace.single 0 1, EuclideanSpace.single 1 1, EuclideanSpace.single 0 (-1),
    EuclideanSpace.single 1 (-1)]

/-- Each pair of consecutive axis points makes a right angle at the origin, so they surround it. -/
theorem axisNbrs_isStar : IsStar (0 : EuclideanSpace ℝ (Fin 2)) axisNbrs := by
  have hang : ∀ i : ZMod 4, ∠ (axisNbrs i) 0 (axisNbrs (i + 1)) = π / 2 := by
    intro i
    rw [EuclideanGeometry.angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    have e0 : (0 : ZMod 4) + 1 = 1 := by decide
    have e1 : (1 : ZMod 4) + 1 = 2 := by decide
    have e2 : (2 : ZMod 4) + 1 = 3 := by decide
    have e3 : (3 : ZMod 4) + 1 = 0 := by decide
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl <;> simp [axisNbrs, EuclideanSpace.inner_single_left, e0, e1, e2, e3]
  unfold IsStar
  rw [Finset.sum_congr rfl fun i _ => hang i]
  simp
  ring

/-- Non-vacuity of `vertexDeficit_euclid`: the four axis points have deficit `0`. -/
theorem axisNbrs_deficit : vertexDeficit eucSq (0 : EuclideanSpace ℝ (Fin 2)) axisNbrs = 0 :=
  axisNbrs_isStar.vertexDeficit_euclid

end Lightlike.CMS
