import Lightlike.Gauge.Connection.SmallLoop
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The small-loop holonomy for a connection on an open set

Svetlichny, *Preparation for Gauge Theory*, arXiv:math-ph/9902027v1, pp. 41-42, states eq. (62) for the local gauge
potential `A_U` on the open set `U` of a trivialisation. `squareHolonomy_eq` (in `SmallLoop`) needs `A` to be `C²` on
all of `E`; here `A` is `C²` only on an open `U ∋ x`. In a space with smooth bump functions (every
finite-dimensional space, the case of the source, whose base is an `n`-dimensional manifold), `A` agrees near `x`
with a globally `C²` cutoff `χ A`, which has the same transports along the four legs and the same curvature at `x`.

* `IsSegmentTransport.congr`: a transport depends only on `A` along the leg.
* `exists_contDiff_eqOn_ball`: a globally `C²` one-form equal to `A` on a ball around `x`.
* `squareHolonomy_eq_of_contDiffOn`: eq. (62) on `U`.
-/

open Set Metric
open scoped Topology

noncomputable section

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- A transport depends only on the one-form along the leg. -/
lemma IsSegmentTransport.congr {A B : E → E →L[ℝ] 𝔄} {y ζ : E} {U : ℝ → 𝔄}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, A (y + t • ζ) = B (y + t • ζ)) (hU : IsSegmentTransport A y ζ U) :
    IsSegmentTransport B y ζ U :=
  ⟨hU.1, fun t ht => by rw [← h t ht]; exact hU.2 t ht⟩

/-- **A global `C²` cutoff**: if `A` is `C²` on an open `U ∋ x`, some globally `C²` one-form equals `A` on a ball
around `x`. -/
theorem exists_contDiff_eqOn_ball [HasContDiffBump E] {A : E → E →L[ℝ] 𝔄} {U : Set E} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {x : E} (hx : x ∈ U) :
    ∃ B : E → E →L[ℝ] 𝔄, ContDiff ℝ 2 B ∧ ∃ r : ℝ, 0 < r ∧ ∀ y ∈ ball x r, B y = A y := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x hx
  let φ : ContDiffBump x := ⟨R / 4, R / 2, by positivity, by linarith⟩
  refine ⟨fun y => φ y • A y, ?_, R / 4, by positivity, fun y hy => ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun y => ?_
    by_cases hy : y ∈ ball x R
    · exact φ.contDiffAt.smul (hA.contDiffAt (hU.mem_nhds (hRU hy)))
    · have hys : y ∉ tsupport φ := by
        rw [φ.tsupport_eq]
        intro h
        exact hy (lt_of_le_of_lt (mem_closedBall.1 h) (by simp only [φ]; linarith))
      have h0 : (fun y => φ y • A y) =ᶠ[𝓝 y] fun _ => 0 :=
        (notMem_tsupport_iff_eventuallyEq.1 hys).mono fun z hz => by
          simp only [Pi.zero_apply] at hz
          show φ z • A z = 0
          rw [hz]; exact zero_smul ℝ (A z)
      exact (contDiffAt_const (c := (0 : E →L[ℝ] 𝔄))).congr_of_eventuallyEq h0
  · have h1 : φ y = 1 := φ.one_of_mem_closedBall (mem_closedBall.2 (le_of_lt (mem_ball.1 hy)))
    simp [h1]

/-- A point of a leg `y + t ζ` (`t ∈ [0, 1]`) is within `‖y - x‖ + ‖ζ‖` of `x`. -/
lemma dist_leg_le (x y ζ : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : dist (y + t • ζ) x ≤ ‖y - x‖ + ‖ζ‖ := by
  rw [dist_eq_norm, show y + t • ζ - x = (y - x) + t • ζ by abel]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul, Real.norm_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

variable [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- **The small-loop holonomy on an open set** (Svetlichny eq. (62), stated for the local gauge potential on the open
set `U` of a trivialisation): if `A` is `C²` on an open `U ∋ x`, the transport around the parallelogram
`x, x + εξ, x + εξ + εη, x + εη` is `1 + ε² F(η, ξ) + O(ε³)`. -/
theorem squareHolonomy_eq_of_contDiffOn [HasContDiffBump E] {A : E → E →L[ℝ] 𝔄} {U : Set E} (hU : IsOpen U)
    (hA : ContDiffOn ℝ 2 A U) {x : E} (hx : x ∈ U) (ξ η : E) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ U₁ U₂ U₃ U₄ : ℝ → 𝔄,
      IsSegmentTransport A x (ε • ξ) U₁ →
      IsSegmentTransport A (x + ε • ξ) (ε • η) U₂ →
      IsSegmentTransport A (x + ε • ξ + ε • η) (-(ε • ξ)) U₃ →
      IsSegmentTransport A (x + ε • η) (-(ε • η)) U₄ →
      ‖U₄ 1 * U₃ 1 * U₂ 1 * U₁ 1 - (1 + ε ^ 2 • curvature A x η ξ)‖ ≤ C * ε ^ 3 := by
  obtain ⟨B, hB, r, hr, hBA⟩ := exists_contDiff_eqOn_ball hU hA hx
  obtain ⟨C, ε₀, hε₀, hmain⟩ := squareHolonomy_eq hB x ξ η
  set M : ℝ := 2 * (‖ξ‖ + ‖η‖) + 1 with hM
  have hMpos : 0 < M := by positivity
  refine ⟨C, min ε₀ (r / (2 * M)), lt_min hε₀ (by positivity), fun ε hε hεle U₁ U₂ U₃ U₄ h₁ h₂ h₃ h₄ => ?_⟩
  have hε₀' : ε ≤ ε₀ := hεle.trans (min_le_left _ _)
  have hεr : ε * M < r := by
    have h := hεle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  have hn : ∀ v : E, ‖ε • v‖ = ε * ‖v‖ := fun v => by rw [norm_smul, Real.norm_of_nonneg hε.le]
  -- every point of the four legs lies in the ball where `B = A`
  have hball : ∀ y ζ : E, ‖y - x‖ + ‖ζ‖ ≤ ε * (2 * (‖ξ‖ + ‖η‖)) →
      ∀ t ∈ Icc (0 : ℝ) 1, A (y + t • ζ) = B (y + t • ζ) := by
    intro y ζ hyζ t ht
    refine (hBA _ (mem_ball.2 ((dist_leg_le x y ζ ht).trans_lt ?_))).symm
    calc ‖y - x‖ + ‖ζ‖ ≤ ε * (2 * (‖ξ‖ + ‖η‖)) := hyζ
      _ < ε * M := by rw [hM]; nlinarith
      _ < r := hεr
  have hξ := norm_nonneg ξ
  have hη := norm_nonneg η
  have g₁ := h₁.congr (hball x (ε • ξ) (by rw [sub_self, norm_zero, zero_add, hn]; nlinarith))
  have g₂ := h₂.congr (hball (x + ε • ξ) (ε • η) (by
    rw [add_sub_cancel_left, hn, hn]; nlinarith))
  have g₃ := h₃.congr (hball (x + ε • ξ + ε • η) (-(ε • ξ)) (by
    rw [add_assoc, add_sub_cancel_left, norm_neg, hn]
    nlinarith [norm_add_le (ε • ξ) (ε • η), hn ξ, hn η]))
  have g₄ := h₄.congr (hball (x + ε • η) (-(ε • η)) (by
    rw [add_sub_cancel_left, norm_neg, hn]; nlinarith))
  have hcurv : curvature A x η ξ = curvature B x η ξ :=
    curvature_congr (Filter.eventually_of_mem (ball_mem_nhds x hr) fun y hy => (hBA y hy).symm) η ξ
  rw [hcurv]
  exact hmain ε hε hε₀' U₁ U₂ U₃ U₄ g₁ g₂ g₃ g₄

end Lightlike.Gauge
