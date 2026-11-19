import Lightlike.Spacetime.EHManifold.Locality

/-!
# A smooth retraction of `ℝⁿ` onto a ball

For a smooth bump function `φ` centred at `c` (equal to `1` on the ball of radius `φ.rIn`, supported in the
ball of radius `φ.rOut`), the map `ballRetract φ x = c + φ x • (x - c)` is smooth, maps `ℝⁿ` into the ball of
radius `φ.rOut` and is the identity on the ball of radius `φ.rIn`.

So a coordinate metric `g` that is smooth and nondegenerate only on the ball of radius `φ.rOut` gives, by
composition, a metric `g ∘ ballRetract φ` that is smooth on all of `ℝⁿ` (`contDiff_comp_ballRetract`) and
agrees with `g` near every point of the small ball (`eventuallyEq_comp_ballRetract`). This is how the chart
components of a metric on a manifold, which are defined only on the target of the chart, are brought under
theorems stated for metrics on all of `ℝⁿ`.

Supporting lemmas for the Einstein–Hilbert variation on a manifold; no catalogue entry.
-/

open Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ} {c : Fin n → ℝ}

/-- The smooth retraction `x ↦ c + φ x • (x - c)` of `ℝⁿ` onto the ball of radius `φ.rOut`. -/
def ballRetract (φ : ContDiffBump c) (x : Fin n → ℝ) : Fin n → ℝ := c + φ x • (x - c)

lemma contDiff_ballRetract (φ : ContDiffBump c) : ContDiff ℝ ∞ (ballRetract φ) :=
  contDiff_const.add (φ.contDiff.smul (contDiff_id.sub contDiff_const))

lemma ballRetract_of_mem (φ : ContDiffBump c) {x : Fin n → ℝ} (hx : x ∈ ball c φ.rIn) :
    ballRetract φ x = x := by
  unfold ballRetract
  rw [φ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul, add_sub_cancel]

lemma ballRetract_mem (φ : ContDiffBump c) (x : Fin n → ℝ) : ballRetract φ x ∈ ball c φ.rOut := by
  unfold ballRetract
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg φ.nonneg]
  by_cases hx : x ∈ ball c φ.rOut
  · calc φ x * ‖x - c‖ ≤ 1 * ‖x - c‖ := mul_le_mul_of_nonneg_right φ.le_one (norm_nonneg _)
      _ = dist x c := by rw [one_mul, dist_eq_norm]
      _ < φ.rOut := hx
  · rw [φ.zero_of_le_dist (not_lt.1 hx), zero_mul]
    exact φ.rOut_pos

/-- The composed metric agrees with the original one near every point of the small ball. -/
lemma eventuallyEq_comp_ballRetract (φ : ContDiffBump c)
    (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) {x : Fin n → ℝ} (hx : x ∈ ball c φ.rIn) :
    (fun y => g (ballRetract φ y)) =ᶠ[𝓝 x] g :=
  Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) fun y hy => by
    show g (ballRetract φ y) = g y
    rw [ballRetract_of_mem φ hy]

/-- The composed metric is smooth on all of `ℝⁿ` when the original one is smooth on the big ball. -/
lemma contDiff_comp_ballRetract (φ : ContDiffBump c) {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun y => g y a b) (ball c φ.rOut)) (a b : Fin n) :
    ContDiff ℝ ∞ (fun y => g (ballRetract φ y) a b) :=
  (hg a b).comp_contDiff (contDiff_ballRetract φ) fun y => ballRetract_mem φ y

end Lightlike
