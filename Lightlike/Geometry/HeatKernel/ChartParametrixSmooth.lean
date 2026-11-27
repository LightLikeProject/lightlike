import Mathlib
import Lightlike.Geometry.HeatKernel.ChartBaseDelta

/-!
# Joint smoothness of the chart parametrix

The chart parametrix `H(t, p, y) = θ(y − p) (4πt)^{-n/2} e^{-σ(p, y)/4t} Σ_{k ≤ N} tᵏ u_k(p, y)`
(`Lightlike.IsChartParametrix`) is jointly smooth in `(t, p, y)` for `t > 0` and `p` in the ball of radius `r` around
the centre (`Lightlike.IsChartParametrix.contDiffOn_joint`): near the support of the cutoff every factor is smooth,
and off it `H` vanishes identically nearby.
-/

open Set Filter Metric
open scoped ContDiff Topology

noncomputable section

namespace Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The chart parametrix is jointly smooth** in `(t, p, y)` on `t > 0`, `‖p − x‖ < r`. -/
theorem IsChartParametrix.contDiffOn_joint {x : Fin n → ℝ} {N : ℕ} {r : ℝ}
    {u : ℕ → (Fin n → ℝ) × (Fin n → ℝ) → ℝ} {H : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    {Ω : Set ((Fin n → ℝ) × (Fin n → ℝ))} {θ : (Fin n → ℝ) → ℝ} {σ : (Fin n → ℝ) × (Fin n → ℝ) → ℝ}
    {V : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)} (h : IsChartParametrix g U x N r u H Ω θ σ V)
    (hg : IsCoordMetric g U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => H z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r}) := by
  set S := Ioi (0 : ℝ) ×ˢ {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r} with hS
  set W := {q : (Fin n → ℝ) × (Fin n → ℝ) | ‖q.1 - x‖ < r ∧ ‖q.2 - q.1‖ < r} with hWdef
  have hWo : IsOpen W := (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const).inter
    (isOpen_lt (continuous_snd.sub continuous_fst).norm continuous_const)
  have hWΩ : W ⊆ Ω := fun q hq => h.mem_of_lt q.1 q.2 hq.1 hq.2
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ht, hp⟩ := hz
  have ht0 : 0 < z.1 := ht
  by_cases hsupp : z.2.2 - z.2.1 ∈ tsupport θ
  · have hyp : ‖z.2.2 - z.2.1‖ < r := by
      have := h.θ_tsupport hsupp; rwa [mem_ball, dist_zero_right] at this
    have hqW : z.2 ∈ W := ⟨hp, hyp⟩
    set T := Ioi (0 : ℝ) ×ˢ W with hT
    have hTo : IsOpen T := isOpen_Ioi.prod hWo
    have hzT : z ∈ T := ⟨ht0, hqW⟩
    have hfun : (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => H z.1 z.2.1 z.2.2) = fun z =>
        θ (z.2.2 - z.2.1) * ((4 * Real.pi * z.1) ^ (-(n : ℝ) / 2) * Real.exp (-σ z.2 / (4 * z.1)) *
          ∑ k ∈ Finset.range (N + 1), z.1 ^ k * u k z.2) := by
      funext z; rw [h.H_eq]; rfl
    rw [hfun]
    refine ContDiffOn.contDiffAt ?_ (hTo.mem_nhds hzT)
    have hσT : ContDiffOn ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => σ z.2) T :=
      (h.σ_contDiffOn hg).comp contDiffOn_snd fun z hz => hz.2
    have huT : ∀ k, ContDiffOn ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => u k z.2) T := fun k =>
      ((h.u_smooth k).mono hWΩ).comp contDiffOn_snd fun z hz => hz.2
    have ht0T : ∀ z ∈ T, z.1 ≠ 0 := fun z hz => (show (0 : ℝ) < z.1 from hz.1).ne'
    have hθT : ContDiffOn ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => θ (z.2.2 - z.2.1)) T :=
      (h.θ_smooth.comp ((contDiff_snd.comp contDiff_snd).sub (contDiff_fst.comp contDiff_snd))).contDiffOn
    have hpow : ContDiffOn ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        (4 * Real.pi * z.1) ^ (-(n : ℝ) / 2)) T := by
      intro z hz
      have hpos : 0 < 4 * Real.pi * z.1 := by have : (0 : ℝ) < z.1 := hz.1; positivity
      exact ((Real.contDiffAt_rpow_const_of_ne hpos.ne').comp z
        ((contDiffAt_const.mul contDiffAt_fst))).contDiffWithinAt
    have hexp : ContDiffOn ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => Real.exp (-σ z.2 / (4 * z.1))) T :=
      Real.contDiff_exp.comp_contDiffOn (hσT.neg.div (contDiffOn_const.mul contDiffOn_fst)
        fun z hz => mul_ne_zero four_ne_zero (ht0T z hz))
    have hsum : ContDiffOn ℝ ∞ (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        ∑ k ∈ Finset.range (N + 1), z.1 ^ k * u k z.2) T :=
      ContDiffOn.sum fun k _ => (contDiffOn_fst.pow k).mul (huT k)
    exact hθT.mul ((hpow.mul hexp).mul hsum)
  · have h0 : ∀ᶠ w in 𝓝 (z.2.2 - z.2.1), θ w = 0 := notMem_tsupport_iff_eventuallyEq.mp hsupp
    have hc : Continuous fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => z.2.2 - z.2.1 :=
      (continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd)
    have h1 : (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => H z.1 z.2.1 z.2.2) =ᶠ[𝓝 z] fun _ => 0 :=
      ((hc.continuousAt (x := z)).eventually h0).mono fun z' hz' => by
        show H z'.1 z'.2.1 z'.2.2 = 0
        rw [h.H_eq, show θ (z'.2.2 - z'.2.1) = 0 from hz', zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq h1

end Lightlike
