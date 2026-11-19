import Mathlib
import Lightlike.Canonical.ADM
import Lightlike.Canonical.MomentumBracket
import Lightlike.Canonical.MomentumADM

/-!
# The bracket of two momentum constraints on a concrete example

In dimension one, with the flat metric `h = 1`, the momentum `π(y) = y` and the shifts `ξ = b`, `η = y b` for a bump function
`b`, the Lie bracket is `[ξ, η] = b²`, and the bracket `{D[ξ], D[η]} = D[[ξ, η]] = −2 ∫ b²` is not zero. The computation
runs through `bracket_momentum_momentum` and the ADM form of the momentum constraint
(`momentumConstraint_eq_adm_of_smooth`), the divergence of `π = y` being `1`. So the bracket is not the zero functional and
its definition through `π`-gradients and Gateaux derivatives is exercised on a case where the answer is nonzero.
-/

open Matrix MeasureTheory
open scoped ContDiff

namespace Lightlike.Canonical

/-- **A nonzero bracket**: for the flat metric on `ℝ`, `π(y) = y`, `ξ = b`, `η = y b` with `b` a bump function,
`{D[ξ], D[η]} ≠ 0`. -/
theorem bracket_momentum_momentum_ne_zero :
    ∃ (ξ η : VectorField 1) (h π : TensorField 1),
      admBracket (momentumConstraint ξ) (momentumConstraint η) (fun h _ => lieTensor ξ h)
        (fun h _ => lieTensor η h) h π ≠ 0 := by
  let b : ContDiffBump (0 : Fin 1 → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let ξ : VectorField 1 := fun y _ => b y
  let η : VectorField 1 := fun y _ => y 0 * b y
  let h : TensorField 1 := fun _ => 1
  let π : TensorField 1 := fun y => Matrix.of fun _ _ => y 0
  have hcoord : ContDiff ℝ ∞ (fun y : Fin 1 → ℝ => y 0) := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)).contDiff
  have hξ : SmoothVec ξ := fun _ => b.contDiff
  have hη : SmoothVec η := fun _ => hcoord.mul b.contDiff
  have hh : SmoothTensor h := fun i j => contDiff_const
  have hξc : ∀ k, HasCompactSupport (fun y => ξ y k) := fun _ => b.hasCompactSupport
  have hηc : ∀ k, HasCompactSupport (fun y => η y k) := fun _ => b.hasCompactSupport.mul_left
  have hπc : ∀ i j, Continuous (fun x => π x i j) := fun i j => continuous_apply 0
  have hπ : SmoothTensor π := fun i j => hcoord
  have hpos : ∀ x, (h x).PosDef := fun x => by simpa [h] using Matrix.PosDef.one
  have key := bracket_momentum_momentum hξ hη hξc hηc hh hπc
  refine ⟨ξ, η, h, π, ?_⟩
  rw [key]
  have hp : ∀ y : Fin 1 → ℝ, Lightlike.pd (0 : Fin 1) (fun y : Fin 1 → ℝ => y 0) y = 1 := fun y => by
    simp only [Lightlike.pd]
    rw [(hasFDerivAt_apply (0 : Fin 1) y).fderiv]
    simp
  -- the Lie bracket is `b²`
  have hl : ∀ y k, lieBracket ξ η y k = b y ^ 2 := by
    intro y k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    have h1 : Lightlike.pd (0 : Fin 1) (fun y => η y 0) y = b y + y 0 * Lightlike.pd (0 : Fin 1) (fun y => ξ y 0) y := by
      have := Lightlike.pd_mul (f₁ := fun y : Fin 1 → ℝ => y 0) (f₂ := fun y => b y)
        (hcoord.differentiable (by simp) y) ((b.contDiff (n := 1)).differentiable (by simp) y) 0
      simpa [η, ξ, hp y] using this
    simp only [lieBracket, Fin.sum_univ_one, h1]
    simp only [ξ, η]
    ring
  have hζ : (fun y k => lieBracket ξ η y k) = fun y _ => b y ^ 2 := funext fun y => funext fun k => hl y k
  rw [hζ]
  have hζs : SmoothVec (fun y (_ : Fin 1) => b y ^ 2) := fun _ => b.contDiff.pow 2
  have hζc : ∀ k : Fin 1, HasCompactSupport (fun y => b y ^ 2) := fun _ => (b.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp) : HasCompactSupport (fun y => b y ^ 2))
  rw [momentumConstraint_eq_adm_of_smooth hζs hζc hh hpos hπ (fun x => by ext i j; simp [π])]
  have hdiv : ∀ y : Fin 1 → ℝ, momentumDivergence h π 0 y = 1 := fun y => by
    have hc : ∀ k l : Fin 1, Lightlike.christoffel h 0 k l y = 0 := by
      intro k l; simp [h, Lightlike.christoffel_const]
    simp [momentumDivergence, hc, hp, π]
  have hint : (fun x => -2 * ∑ i : Fin 1, (∑ k : Fin 1, h x i k * b x ^ 2) * momentumDivergence h π i x) =
      fun x => -2 * b x ^ 2 := by
    funext x; simp [h, hdiv]
  rw [hint, integral_const_mul]
  have hb2 : 0 < ∫ x, b x ^ 2 := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (b.continuous.pow 2)
      ((b.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp) : HasCompactSupport (fun y => b y ^ 2))) (fun x => sq_nonneg _) ?_
    rw [b.one_of_mem_closedBall (x := 0) (by simp [b])]; norm_num
  nlinarith

end Lightlike.Canonical
