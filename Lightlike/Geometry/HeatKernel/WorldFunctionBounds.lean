import Mathlib
import Lightlike.Geometry.HeatKernel.ParamLaplacian
import Lightlike.Upstream.GeodesicExpansion.ReggeLength
import Lightlike.Geodesic.Gauss

/-!
# Normal coordinates are bi-Lipschitz near the diagonal, uniformly in the base point

For `V : ℝⁿ × ℝⁿ → ℝⁿ` smooth on an open `W ∋ (x, x)` with `V(p, p) = 0` and `D_y V(p, p) = id` (the velocity map of
`Lightlike.Geodesic.exists_sqDist_eikonal`), there is `r > 0` such that for `‖p − x‖, ‖y − x‖ < r`

`‖y − p‖ ≤ 2 ‖V(p, y)‖`   (`exists_norm_sub_le_two_mul_norm`),

by the mean value inequality: `D_y V(p, y)` is within `1/2` of the identity near `(x, x)` (joint continuity). With a
uniform positive lower bound of a Riemannian metric this gives the Gaussian lower bound `σ(p, y) ≥ c ‖y − p‖²` of the
world function, which the parametrix estimates use.
-/

open Set Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The derivative in the second variable, `D_y V(p, y) = DV(p, y) ∘ inr`. -/
theorem fderiv_snd_eq {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} {q : (Fin n → ℝ) × (Fin n → ℝ)}
    (hd : DifferentiableAt ℝ V q) :
    fderiv ℝ (fun y => V (q.1, y)) q.2 = (fderiv ℝ V q).comp (ContinuousLinearMap.inr ℝ _ _) := by
  have h : HasFDerivAt V (fderiv ℝ V q) (q.1, q.2) := hd.hasFDerivAt
  exact (h.comp q.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)).fderiv

/-- **Normal coordinates are bi-Lipschitz near the diagonal**: `‖y − p‖ ≤ 2 ‖V(p, y)‖` for `p, y` near `x`. -/
theorem exists_norm_sub_le_two_mul_norm {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)}
    {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hWo : IsOpen W) (hVs : ContDiffOn ℝ ∞ V W) {x : Fin n → ℝ}
    (hxW : (x, x) ∈ W) (hV0 : ∀ p, (p, p) ∈ W → V (p, p) = 0)
    (hDV : ∀ p, (p, p) ∈ W → HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) :
    ∃ r > 0, ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - x‖ < r → (p, y) ∈ W ∧ ‖y - p‖ ≤ 2 * ‖V (p, y)‖ := by
  -- joint continuity of `D_y V` on `W`
  have hD : ContinuousOn (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
      (fderiv ℝ V q).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))) W :=
    ((hVs.continuousOn_fderiv_of_isOpen hWo (by simp)).clm_comp continuousOn_const)
  have hxid : (fderiv ℝ V (x, x)).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    rw [← fderiv_snd_eq ((hVs.contDiffAt (hWo.mem_nhds hxW)).differentiableAt (by simp))]
    exact (hDV x hxW).fderiv
  -- a ball around `(x, x)` in `W` where `D_y V` is within `1/2` of the identity
  have hev : ∀ᶠ q in 𝓝 (x, x), q ∈ W ∧
      ‖(fderiv ℝ V q).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) -
        ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ < 1 / 2 := by
    refine (hWo.eventually_mem hxW).and ?_
    have hc := (hD.continuousAt (hWo.mem_nhds hxW)).tendsto
    rw [hxid] at hc
    exact hc.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2)) |>.mono fun q hq => by
      simpa [dist_eq_norm] using hq
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨r, hr, fun p y hp hy => ?_⟩
  have hmem : ∀ z : Fin n → ℝ, ‖z - x‖ < r → (p, z) ∈ ball (x, x) r := fun z hz => by
    rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    exact max_lt hp hz
  refine ⟨(hball _ (hmem y hy)).1, ?_⟩
  -- the mean value inequality on the ball `B(x, r)` in the second variable
  set B := ball x r with hB
  have hpB : p ∈ B := by rw [mem_ball, dist_eq_norm]; exact hp
  have hyB : y ∈ B := by rw [mem_ball, dist_eq_norm]; exact hy
  have hdiff : ∀ z ∈ B, DifferentiableAt ℝ (fun w => V (p, w)) z := fun z hz => by
    have hzW := (hball _ (hmem z (by rwa [mem_ball, dist_eq_norm] at hz))).1
    exact ((hVs.contDiffAt (hWo.mem_nhds hzW)).differentiableAt (by simp)).comp z
      ((differentiableAt_const p).prodMk differentiableAt_id)
  have hbound : ∀ z ∈ B, ‖fderiv ℝ (fun w => V (p, w)) z - ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤ 1 / 2 := by
    intro z hz
    have hz' : ‖z - x‖ < r := by rwa [mem_ball, dist_eq_norm] at hz
    have hq := hball _ (hmem z hz')
    rw [fderiv_snd_eq (q := (p, z)) ((hVs.contDiffAt (hWo.mem_nhds hq.1)).differentiableAt (by simp))]
    exact hq.2.le
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le' hdiff hbound (convex_ball x r) hpB hyB
  have hpp : V (p, p) = 0 := hV0 p (hball _ (hmem p hp)).1
  simp only [hpp, sub_zero, ContinuousLinearMap.id_apply] at hmv
  -- `‖y - p‖ ≤ ‖V(p, y)‖ + ‖V(p, y) - (y - p)‖ ≤ ‖V(p, y)‖ + ‖y - p‖/2`
  have htri : ‖y - p‖ ≤ ‖V (p, y)‖ + ‖V (p, y) - (y - p)‖ := by
    have := norm_sub_le (V (p, y)) (V (p, y) - (y - p))
    simpa using this
  linarith

/-- **The Gaussian lower bound of the world function**: for a Riemannian coordinate metric and `V` as in
`exists_norm_sub_le_two_mul_norm`, there are `r, c > 0` with `c ‖y − p‖² ≤ g_p(V(p, y), V(p, y))` for
`‖p − x‖, ‖y − x‖ < r`. -/
theorem exists_pairing_lower {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : Upstream.GeodesicExpansion.IsRiemMetric g U) {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)}
    {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hWo : IsOpen W) (hVs : ContDiffOn ℝ ∞ V W) {x : Fin n → ℝ}
    (hx : x ∈ U) (hxW : (x, x) ∈ W) (hV0 : ∀ p, (p, p) ∈ W → V (p, p) = 0)
    (hDV : ∀ p, (p, p) ∈ W → HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) :
    ∃ r c : ℝ, 0 < r ∧ 0 < c ∧ ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - x‖ < r →
      c * ‖y - p‖ ^ 2 ≤ Geodesic.pairing g p (V (p, y)) (V (p, y)) := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_norm_sub_le_two_mul_norm hWo hVs hxW hV0 hDV
  -- a compact neighbourhood of `x` in `U`, and the uniform quadratic lower bound of `g` there
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hg.coord.isOpen x hx
  set K := closedBall x (ε / 2) with hK
  have hKU : K ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨l, rw, hl, hrw, hlow⟩ := Upstream.GeodesicExpansion.IsRiemMetric.normSq_lower
    (U := ⟨U, hg.coord.isOpen⟩) hg (isCompact_closedBall x (ε / 2)) hKU
  -- `V` is small near `(x, x)`
  have hVc : ContinuousAt V (x, x) := hVs.continuousOn.continuousAt (hWo.mem_nhds hxW)
  have hVx : V (x, x) = 0 := hV0 x hxW
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff_ball.1
    ((hVc.tendsto.eventually (Metric.closedBall_mem_nhds (V (x, x)) hrw)))
  refine ⟨min (min r₁ r₂) (ε / 2), l / 4, lt_min (lt_min hr₁ hr₂) (by linarith), by linarith,
    fun p y hp hy => ?_⟩
  have hp1 : ‖p - x‖ < r₁ := lt_of_lt_of_le hp ((min_le_left _ _).trans (min_le_left _ _))
  have hy1 : ‖y - x‖ < r₁ := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))
  have hp2 : ‖p - x‖ < r₂ := lt_of_lt_of_le hp ((min_le_left _ _).trans (min_le_right _ _))
  have hy2 : ‖y - x‖ < r₂ := lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_right _ _))
  have hpK : p ∈ K := by
    rw [hK, mem_closedBall, dist_eq_norm]; exact (lt_of_lt_of_le hp (min_le_right _ _)).le
  have hVsmall : ‖V (p, y)‖ ≤ rw := by
    have := h₂ (p, y) (show (p, y) ∈ ball (x, x) r₂ by
      rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]; exact max_lt hp2 hy2)
    simpa [hVx, mem_closedBall, dist_eq_norm] using this
  have hq := hlow p hpK _ hVsmall
  have hb := (h₁ p y hp1 hy1).2
  rw [Geodesic.pairing_eq_dotProduct]
  have : ‖y - p‖ ^ 2 ≤ 4 * ‖V (p, y)‖ ^ 2 := by nlinarith [norm_nonneg (y - p), norm_nonneg (V (p, y))]
  nlinarith

end Lightlike
