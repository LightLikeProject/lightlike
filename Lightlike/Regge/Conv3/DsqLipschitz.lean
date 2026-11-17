import Lightlike.Regge.Conv3.ClassUniform

/-!
# The dihedral angle is uniformly Lipschitz near a compact set of admissible lengths

For a compact set `K` of admissible squared lengths (`Valid`, an open condition), the dihedral angle
`Dsq` is Lipschitz with one constant `C` on the balls of one radius `δ` around the points of `K`
(`Dsq_lipschitz_uniform`). It is used to replace the squared geodesic lengths of a star by their jet
polynomial: an error of relative size `ε³` in the lengths gives an error of size `C ε³` in the angle.

## Main results

* `Dsq_lipschitz_uniform`: `|Dsq L' - Dsq L| ≤ C ‖L' - L‖` for `L`, `L'` within `δ` of a point of `K`.

**Limits.** The constants depend on `K` and are not explicit.
-/

open Real Matrix Lightlike Filter Topology Metric Set
namespace Lightlike.Regge.Conv3

/-- **The dihedral angle is uniformly Lipschitz near a compact set of admissible lengths.** For a compact
set `K` of admissible squared lengths there are `δ > 0` and `C` such that
`|Dsq L' - Dsq L| ≤ C ‖L' - L‖` whenever `q ∈ K` and `L`, `L'` lie within `δ` of `q`. -/
theorem Dsq_lipschitz_uniform {K : Set (Fin 6 → ℝ)} (hK : IsCompact K) (hKV : ∀ L ∈ K, Valid L) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ q ∈ K, ∀ L L' : Fin 6 → ℝ, ‖L - q‖ ≤ δ → ‖L' - q‖ ≤ δ →
      |Dsq L' - Dsq L| ≤ C * ‖L' - L‖ := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open isOpen_valid (fun L hL => hKV L hL)
  have hT : IsCompact (Metric.cthickening δ K) := hK.cthickening
  have hdiff : ∀ x ∈ Metric.cthickening δ K, DifferentiableAt ℝ Dsq x := fun x hx =>
    (contDiffAt_Dsq (hsub hx)).differentiableAt (by norm_num)
  have hcont : ContinuousOn (fun x => ‖fderiv ℝ Dsq x‖) (Metric.cthickening δ K) := by
    have : ContinuousOn (fderiv ℝ Dsq) (Metric.cthickening δ K) := fun x hx =>
      ((contDiffAt_Dsq (hsub hx)).fderiv_right (m := 2) (by norm_num)).continuousAt.continuousWithinAt
    exact this.norm
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hcont
  refine ⟨δ, max C 0, hδ, le_max_right _ _, fun q hq L L' hL hL' => ?_⟩
  have hball : Metric.closedBall q δ ⊆ Metric.cthickening δ K := fun x hx =>
    Metric.mem_cthickening_of_dist_le x q δ K hq (Metric.mem_closedBall.1 hx)
  have h := (convex_closedBall q δ).norm_image_sub_le_of_norm_fderiv_le (f := Dsq) (C := max C 0)
    (fun x hx => hdiff x (hball hx))
    (fun x hx => by
      have := hC x (hball hx)
      rw [norm_norm] at this
      exact this.trans (le_max_left _ _))
    (Metric.mem_closedBall.2 (by rw [dist_eq_norm]; exact hL))
    (Metric.mem_closedBall.2 (by rw [dist_eq_norm]; exact hL'))
  simpa [Real.norm_eq_abs] using h

end Lightlike.Regge.Conv3
