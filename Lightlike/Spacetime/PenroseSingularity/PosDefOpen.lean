import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Positive definiteness is an open condition along a continuous path (G1-012, step D4)

If `M t` is a continuous family of symmetric real matrices and `M t₀` is positive definite, then `M t` is
positive definite for `t` near `t₀`.
-/

open Set Filter Topology Matrix

namespace Lightlike.Penrose

variable {m : ℕ}

/-- The quadratic form of a matrix is bounded by the sum of the absolute values of its entries. -/
theorem abs_dotProduct_mulVec_le (D : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ (∑ i, ∑ j, |D i j|) * ‖x‖ ^ 2 := by
  have hx : ∀ i, |x i| ≤ ‖x‖ := fun i => by simpa using norm_le_pi_norm x i
  simp only [dotProduct, mulVec]
  calc |∑ i, x i * ∑ j, D i j * x j| ≤ ∑ i, ∑ j, |D i j| * ‖x‖ ^ 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [show x i * (D i j * x j) = D i j * (x i * x j) by ring, abs_mul, abs_mul]
        have := mul_le_mul (hx i) (hx j) (abs_nonneg _) (norm_nonneg _)
        nlinarith [abs_nonneg (D i j)]
    _ = (∑ i, ∑ j, |D i j|) * ‖x‖ ^ 2 := by simp only [Finset.sum_mul]

/-- **Positive definiteness persists along a continuous path of symmetric matrices.** -/
theorem eventually_posDef {M : ℝ → Matrix (Fin m) (Fin m) ℝ} {t₀ : ℝ} (hc : ContinuousAt M t₀)
    (hsym : ∀ t, (M t).IsHermitian) (h : (M t₀).PosDef) : ∀ᶠ t in 𝓝 t₀, (M t).PosDef := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact Filter.Eventually.of_forall fun t => Matrix.PosDef.of_dotProduct_mulVec_pos (hsym t) fun x hx =>
      absurd (Subsingleton.elim x 0) hx
  -- the minimum of the quadratic form on the unit sphere
  have hS : IsCompact (Metric.sphere (0 : Fin m → ℝ) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : Fin m → ℝ) 1).Nonempty := by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact NormedSpace.sphere_nonempty.2 zero_le_one
  have hcont : ContinuousOn (fun x : Fin m → ℝ => x ⬝ᵥ (M t₀ *ᵥ x)) (Metric.sphere (0 : Fin m → ℝ) 1) := by
    refine Continuous.continuousOn ?_
    unfold dotProduct mulVec
    fun_prop
  obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hne hcont
  have hx₀ne : x₀ ≠ 0 := by
    intro h0; rw [h0] at hx₀; simp at hx₀
  have hpos : 0 < x₀ ⬝ᵥ (M t₀ *ᵥ x₀) := by simpa using h.dotProduct_mulVec_pos hx₀ne
  set μ := x₀ ⬝ᵥ (M t₀ *ᵥ x₀) with hμ
  -- entries near `t₀`
  have hent : ∀ᶠ t in 𝓝 t₀, (∑ i, ∑ j, |M t i j - M t₀ i j|) < μ / 2 := by
    have : Tendsto (fun t => ∑ i, ∑ j, |M t i j - M t₀ i j|) (𝓝 t₀) (𝓝 (∑ i : Fin m, ∑ j : Fin m, |M t₀ i j - M t₀ i j|)) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hc) |>.sub
          continuousAt_const).abs
    simp only [sub_self, abs_zero, Finset.sum_const_zero] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hent] with t ht
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hsym t) fun x hx => ?_
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  set u : Fin m → ℝ := (‖x‖⁻¹) • x with hu
  have hun : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn.ne']
  have hq : x ⬝ᵥ (M t *ᵥ x) = ‖x‖ ^ 2 * (u ⬝ᵥ (M t *ᵥ u)) := by
    have hx' : x = ‖x‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
    conv_lhs => rw [hx']
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hmu : μ ≤ u ⬝ᵥ (M t₀ *ᵥ u) := hmin (by simpa using hun)
  have hdiff : u ⬝ᵥ (M t *ᵥ u) = u ⬝ᵥ (M t₀ *ᵥ u) + u ⬝ᵥ ((M t - M t₀) *ᵥ u) := by
    rw [sub_mulVec, dotProduct_sub]; ring
  have hb := abs_dotProduct_mulVec_le (M t - M t₀) u
  rw [hun] at hb
  have hb' : |u ⬝ᵥ ((M t - M t₀) *ᵥ u)| ≤ μ / 2 := by
    have : (∑ i, ∑ j, |(M t - M t₀) i j|) ≤ μ / 2 := by
      simpa only [Matrix.sub_apply] using ht.le
    calc _ ≤ (∑ i, ∑ j, |(M t - M t₀) i j|) * 1 ^ 2 := hb
      _ ≤ μ / 2 := by linarith
  have hlow : μ / 2 ≤ u ⬝ᵥ (M t *ᵥ u) := by
    rw [hdiff]
    have := (abs_le.1 hb').1
    linarith
  rw [star_trivial, hq]
  have : 0 < ‖x‖ ^ 2 := by positivity
  nlinarith

end Lightlike.Penrose
