import Mathlib
import Lightlike.Geometry.HeatKernel.WorldFunctionBounds
import Lightlike.Geodesic.Gauss

/-!
# The world function is the quadratic form of the metric to third order

For `V : ℝⁿ × ℝⁿ → ℝⁿ` smooth on an open `W ∋ (x, x)` with `V(p, p) = 0` and `D_y V(p, p) = id` there are `r, C` with

`‖V(p, y) − (y − p)‖ ≤ C ‖y − p‖²`   for `‖p − x‖, ‖y − x‖ < r`   (`exists_norm_V_sub_le`),

by the mean value inequality twice: `D_y V` is `C¹` jointly, so `‖D_y V(p, z) − id‖ ≤ L ‖z − p‖` on a ball, and then
`‖V(p, y) − (y − p)‖ ≤ L ‖y − p‖²`. For the world function `σ(p, y) = g_p(V, V)` this gives
`|σ(p, y) − g_p(y − p, y − p)| ≤ C ‖y − p‖³` (`exists_abs_pairing_sub_le`): the parametrix is, to leading order, the
Gaussian of the frozen metric `g_p`.
-/

open Set Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **Normal coordinates to second order**: `‖V(p, y) − (y − p)‖ ≤ C ‖y − p‖²` near `(x, x)`. -/
theorem exists_norm_V_sub_le {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)}
    {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hWo : IsOpen W) (hVs : ContDiffOn ℝ ∞ V W) {x : Fin n → ℝ}
    (hxW : (x, x) ∈ W) (hV0 : ∀ p, (p, p) ∈ W → V (p, p) = 0)
    (hDV : ∀ p, (p, p) ∈ W → HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - x‖ < r →
      ‖V (p, y) - (y - p)‖ ≤ C * ‖y - p‖ ^ 2 := by
  -- `DV` is Lipschitz near `(x, x)`
  have hDVs0 : ContDiffOn ℝ ∞ (fderiv ℝ V) W := hVs.fderiv_of_isOpen hWo (by exact_mod_cast le_top)
  obtain ⟨Kl, t, ht, hlip⟩ :=
    ((hDVs0.contDiffAt (hWo.mem_nhds hxW)).of_le (by exact_mod_cast le_top) :
      ContDiffAt ℝ 1 (fderiv ℝ V) (x, x)).exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hρtW⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht (hWo.mem_nhds hxW))
  set r := ρ / 2 with hr
  have hrpos : 0 < r := by positivity
  set K := closedBall ((x, x) : (Fin n → ℝ) × (Fin n → ℝ)) r with hK
  have hKtW : K ⊆ t ∩ W := (closedBall_subset_ball (by linarith)).trans hρtW
  have hKW : K ⊆ W := fun q hq => (hKtW hq).2
  set L : ℝ := (Kl : ℝ) with hLdef
  refine ⟨r, |L| * 1, hrpos, by positivity, fun p y hp hy => ?_⟩
  have hmem : ∀ z : Fin n → ℝ, ‖z - x‖ < r → (p, z) ∈ K := fun z hz => by
    rw [hK, mem_closedBall, Prod.dist_eq, dist_eq_norm, dist_eq_norm]; exact max_le hp.le hz.le
  set B := ball x r with hB
  have hpB : p ∈ B := by rw [hB, mem_ball, dist_eq_norm]; exact hp
  have hyB : y ∈ B := by rw [hB, mem_ball, dist_eq_norm]; exact hy
  have hzK : ∀ z ∈ B, (p, z) ∈ K := fun z hz => hmem z (by rwa [hB, mem_ball, dist_eq_norm] at hz)
  -- `F z = DV(p, z)` and its derivative
  have hstepA : ∀ z ∈ B, ‖fderiv ℝ V (p, z) - fderiv ℝ V (p, p)‖ ≤ |L| * ‖z - p‖ := by
    intro z hz
    have h := hlip.norm_sub_le (hKtW (hzK z hz)).1 (hKtW (hzK p hpB)).1
    have hn : ‖((p, z) : (Fin n → ℝ) × (Fin n → ℝ)) - (p, p)‖ = ‖z - p‖ := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero]
      exact max_eq_right (norm_nonneg _)
    rw [hn] at h
    exact h.trans (by rw [hLdef]; gcongr; exact le_abs_self _)
  -- the derivative of `V(p, ·)` is within `|L| ‖z − p‖` of the identity
  have hdiffV : ∀ z ∈ B, DifferentiableAt ℝ V (p, z) := fun z hz =>
    (hVs.contDiffAt (hWo.mem_nhds (hKW (hzK z hz)))).differentiableAt (by simp)
  have hpp : (p, p) ∈ W := hKW (hzK p hpB)
  have hidp : (fderiv ℝ V (p, p)).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)) =
      ContinuousLinearMap.id ℝ (Fin n → ℝ) := by
    rw [← fderiv_snd_eq (q := (p, p)) (hdiffV p hpB)]
    exact (hDV p hpp).fderiv
  have hstepA' : ∀ z ∈ B, ‖fderiv ℝ (fun w => V (p, w)) z - ContinuousLinearMap.id ℝ (Fin n → ℝ)‖ ≤
      |L| * ‖z - p‖ := by
    intro z hz
    rw [fderiv_snd_eq (q := (p, z)) (hdiffV z hz), ← hidp, ← ContinuousLinearMap.sub_comp]
    calc ‖(fderiv ℝ V (p, z) - fderiv ℝ V (p, p)).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ))‖
        ≤ ‖fderiv ℝ V (p, z) - fderiv ℝ V (p, p)‖ * ‖ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ |L| * ‖z - p‖ * 1 := by
          gcongr
          · exact hstepA z hz
          · exact ContinuousLinearMap.norm_inr_le_one ℝ (Fin n → ℝ) (Fin n → ℝ)
      _ = |L| * ‖z - p‖ := mul_one _
  -- the mean value inequality on the segment `[p, y]`
  set S := segment ℝ p y with hS
  have hSB : S ⊆ B := (convex_ball x r).segment_subset hpB hyB
  have hseg : ∀ z ∈ S, ‖z - p‖ ≤ ‖y - p‖ := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have : a • p + b • y - p = b • (y - p) := by
      rw [show a = 1 - b by linarith]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hφd : ∀ z ∈ S, HasFDerivAt (fun w => V (p, w) - (w - p))
      (fderiv ℝ (fun w => V (p, w)) z - ContinuousLinearMap.id ℝ (Fin n → ℝ)) z := by
    intro z hz
    have h1 := ((hdiffV z (hSB hz)).comp z ((differentiableAt_const p).prodMk differentiableAt_id)).hasFDerivAt
    exact h1.sub ((hasFDerivAt_id z).sub_const p)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun w => V (p, w) - (w - p))
    (C := |L| * ‖y - p‖) (fun z hz => (hφd z hz).differentiableAt)
    (fun z hz => by
      rw [(hφd z hz).fderiv]
      exact (hstepA' z (hSB hz)).trans (by gcongr; exact hseg z hz))
    (convex_segment p y) (left_mem_segment ℝ p y) (right_mem_segment ℝ p y)
  simp only [hV0 p hpp, sub_self, sub_zero] at hmv
  calc ‖V (p, y) - (y - p)‖ ≤ |L| * ‖y - p‖ * ‖y - p‖ := hmv
    _ = |L| * 1 * ‖y - p‖ ^ 2 := by ring

/-- `|g_p(a, b)| ≤ (Σᵢⱼ |g_p(i, j)|) ‖a‖ ‖b‖` (sup norms). -/
theorem abs_pairing_le (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (p a b : Fin n → ℝ) :
    |Geodesic.pairing g p a b| ≤ (∑ i, ∑ j, |g p i j|) * ‖a‖ * ‖b‖ := by
  unfold Geodesic.pairing
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul, abs_mul]
  have ha : |a i| ≤ ‖a‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm a i
  have hb : |b j| ≤ ‖b‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm b j
  calc |a i| * (|g p i j| * |b j|) ≤ ‖a‖ * (|g p i j| * ‖b‖) := by gcongr
    _ = |g p i j| * ‖a‖ * ‖b‖ := by ring

/-- **The world function to third order**: `|g_p(V, V) − g_p(y − p, y − p)| ≤ C ‖y − p‖³` near `(x, x)`. -/
theorem exists_abs_pairing_sub_le {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
    (hg : IsCoordMetric g U) {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)}
    {W : Set ((Fin n → ℝ) × (Fin n → ℝ))} (hWo : IsOpen W) (hVs : ContDiffOn ℝ ∞ V W) {x : Fin n → ℝ}
    (hx : x ∈ U) (hxW : (x, x) ∈ W) (hV0 : ∀ p, (p, p) ∈ W → V (p, p) = 0)
    (hDV : ∀ p, (p, p) ∈ W → HasFDerivAt (fun y => V (p, y)) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) p) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ p y : Fin n → ℝ, ‖p - x‖ < r → ‖y - x‖ < r →
      |Geodesic.pairing g p (V (p, y)) (V (p, y)) - Geodesic.pairing g p (y - p) (y - p)| ≤
        C * ‖y - p‖ ^ 3 := by
  obtain ⟨r₁, C₁, hr₁, hC₁, h₁⟩ := exists_norm_V_sub_le hWo hVs hxW hV0 hDV
  -- a bound for the entries of `g` near `x`
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hg.isOpen x hx
  have hcont : ContinuousOn (fun q => ∑ i, ∑ j, |g q i j|) (closedBall x (ε / 2)) :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      ((hg.smooth i j).continuousOn.mono ((closedBall_subset_ball (by linarith)).trans hεU)).abs
  obtain ⟨M, hM⟩ := (isCompact_closedBall x (ε / 2)).exists_bound_of_continuousOn hcont
  set r := min r₁ (ε / 2) with hr
  have hrpos : 0 < r := lt_min hr₁ (by linarith)
  refine ⟨r, |M| * (2 * C₁ + C₁ ^ 2 * (2 * r)), hrpos, by positivity, fun p y hp hy => ?_⟩
  have hp1 : ‖p - x‖ < r₁ := lt_of_lt_of_le hp (min_le_left _ _)
  have hy1 : ‖y - x‖ < r₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hpK : p ∈ closedBall x (ε / 2) := by
    rw [mem_closedBall, dist_eq_norm]; exact (lt_of_lt_of_le hp (min_le_right _ _)).le
  have hMp : ∑ i, ∑ j, |g p i j| ≤ |M| := by
    have := hM p hpK
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => abs_nonneg _)] at this
    exact this.trans (le_abs_self _)
  set z := y - p with hz
  set e := V (p, y) - z with he
  have he' : ‖e‖ ≤ C₁ * ‖z‖ ^ 2 := h₁ p y hp1 hy1
  have hzr : ‖z‖ ≤ 2 * r := by
    have := norm_sub_le_norm_sub_add_norm_sub y x p
    rw [norm_sub_rev x p] at this; rw [hz]; linarith
  have hVe : V (p, y) = z + e := by rw [he]; abel
  -- the expansion `g(z + e, z + e) − g(z, z) = g(z, e) + g(e, z) + g(e, e)`
  have hexp : Geodesic.pairing g p (z + e) (z + e) - Geodesic.pairing g p z z =
      Geodesic.pairing g p z e + Geodesic.pairing g p e z + Geodesic.pairing g p e e := by
    simp only [Geodesic.pairing, Pi.add_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hVe, hexp]
  have hG := fun a b => abs_pairing_le g p a b
  have hM0 : 0 ≤ ∑ i, ∑ j, |g p i j| := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hz0 := norm_nonneg z
  have he0 := norm_nonneg e
  calc |Geodesic.pairing g p z e + Geodesic.pairing g p e z + Geodesic.pairing g p e e|
      ≤ |Geodesic.pairing g p z e| + |Geodesic.pairing g p e z| + |Geodesic.pairing g p e e| :=
        abs_add_three _ _ _
    _ ≤ |M| * ‖z‖ * ‖e‖ + |M| * ‖e‖ * ‖z‖ + |M| * ‖e‖ * ‖e‖ := by
        gcongr <;> exact (hG _ _).trans (by gcongr)
    _ = |M| * ‖e‖ * (2 * ‖z‖ + ‖e‖) := by ring
    _ ≤ |M| * (C₁ * ‖z‖ ^ 2) * (2 * ‖z‖ + C₁ * ‖z‖ ^ 2) := by gcongr
    _ = |M| * ‖z‖ ^ 3 * (2 * C₁ + C₁ ^ 2 * ‖z‖) := by ring
    _ ≤ |M| * ‖z‖ ^ 3 * (2 * C₁ + C₁ ^ 2 * (2 * r)) := by gcongr
    _ = |M| * (2 * C₁ + C₁ ^ 2 * (2 * r)) * ‖z‖ ^ 3 := by ring

end Lightlike
