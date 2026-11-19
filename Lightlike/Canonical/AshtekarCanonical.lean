import Lightlike.Canonical.SpinConnection
import Lightlike.Canonical.IntegrationByParts
import Lightlike.Canonical.MomentumBracket

/-!
# The canonical transformation ADM ↔ Ashtekar–Barbero: `δ(∫ Γ E) = ∫ Γ δE`

The Ashtekar–Barbero connection `A = Γ + γK` is obtained from the triad variables by the canonical transformation
`A ↦ A + γ δf/δE`, `f[E] = ∫ Γ^i_a E^a_i` (Holst, arXiv:gr-qc/9511026, eqs. (5)–(6), p. 2), which is canonical because
`δf/δE = Γ`, i.e. `∫ E^a_i δΓ^i_a = 0`. This file proves the pointwise identity behind it,
`E^a_i δΓ^i_a = −½ ∂_a (ε_abc e^k_c δe^k_b)` (`E_dSpin_eq_div`), for every variation `(δe, δΓ)` satisfying the linearised
compatibility condition (the variation of Ashtekar–Lewandowski's (2.17)), and the integrated statement
`∫ E^a_i δΓ^i_a = 0` for compactly supported variations (`integral_E_dSpin_eq_zero`).
-/

open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

/-- **The variation of the spin connection contracted with the densitized triad is a divergence**: if the co-triad `e`
and the matrix `Γ` satisfy the compatibility condition at `x` and the variation `(δe, δΓ)` satisfies its linearisation,
then `Σ_{a,i} E^a_i δΓ^i_a = −½ Σ_a ∂_a (Σ_{bck} ε_abc e^k_c δe^k_b)` (for a positively oriented co-triad). -/
theorem E_dSpin_eq_div (e δe : CoTriad) (Γ δΓ : Matrix (Fin 3) (Fin 3) ℝ) {x : Fin 3 → ℝ}
    (hpos : 0 < (e x).det) (hde : ∀ k b, DifferentiableAt ℝ (fun y => e y k b) x)
    (hdl : ∀ k b, DifferentiableAt ℝ (fun y => δe y k b) x)
    (hC : ∀ k a b, Lightlike.pd a (fun y => e y k b) x - Lightlike.pd b (fun y => e y k a) x +
      ∑ i, ∑ j, eps3 k i j * (Γ a i * e x j b - Γ b i * e x j a) = 0)
    (hV : ∀ k a b, Lightlike.pd a (fun y => δe y k b) x - Lightlike.pd b (fun y => δe y k a) x +
      ∑ i, ∑ j, eps3 k i j * (δΓ a i * e x j b + Γ a i * δe x j b - δΓ b i * e x j a - Γ b i * δe x j a) = 0) :
    ∑ a, ∑ j, densTriad e x a j * δΓ a j =
      -(1 / 2) * ∑ a, Lightlike.pd a (fun y => ∑ b, ∑ c, ∑ k, eps3 a b c * (e y k c * δe y k b)) x := by
  have hE : ∀ a j, densTriad e x a j =
      ∑ j', ∑ k, ∑ b, ∑ c, (1 / 2) * (eps3 j j' k * eps3 a b c) * (e x j' b * e x k c) := fun a j =>
    densTriad_eq_poly hpos a j
  have hpd : ∀ a, Lightlike.pd a (fun y => ∑ b, ∑ c, ∑ k, eps3 a b c * (e y k c * δe y k b)) x =
      ∑ b, ∑ c, ∑ k, eps3 a b c * (Lightlike.pd a (fun y => e y k c) x * δe x k b +
        e x k c * Lightlike.pd a (fun y => δe y k b) x) := by
    intro a
    have d3 : ∀ b c k, DifferentiableAt ℝ (fun y => eps3 a b c * (e y k c * δe y k b)) x :=
      fun b c k => ((hde k c).mul (hdl k b)).const_mul _
    have d2 : ∀ b c, DifferentiableAt ℝ (fun y => ∑ k, eps3 a b c * (e y k c * δe y k b)) x :=
      fun b c => DifferentiableAt.fun_sum fun k _ => d3 b c k
    have d1 : ∀ b, DifferentiableAt ℝ (fun y => ∑ c, ∑ k, eps3 a b c * (e y k c * δe y k b)) x :=
      fun b => DifferentiableAt.fun_sum fun c _ => d2 b c
    rw [Lightlike.pd_sum (f := fun b y => ∑ c, ∑ k, eps3 a b c * (e y k c * δe y k b)) _ (fun b _ => d1 b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Lightlike.pd_sum (f := fun c y => ∑ k, eps3 a b c * (e y k c * δe y k b)) _ (fun c _ => d2 b c)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Lightlike.pd_sum (f := fun k y => eps3 a b c * (e y k c * δe y k b)) _ (fun k _ => d3 b c k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Lightlike.pd_const_mul (f := fun y => e y k c * δe y k b) _ ((hde k c).mul (hdl k b)),
      Lightlike.pd_mul (hde k c) (hdl k b)]
  have hVsum : ∑ k, ∑ a, ∑ b, (∑ c, eps3 a b c * e x k c) *
      (Lightlike.pd a (fun y => δe y k b) x - Lightlike.pd b (fun y => δe y k a) x +
        ∑ i, ∑ j, eps3 k i j * (δΓ a i * e x j b + Γ a i * δe x j b - δΓ b i * e x j a - Γ b i * δe x j a)) = 0 := by
    simp [hV]
  have hCsum : ∑ k, ∑ b, δe x k b * ∑ a, ∑ c, eps3 a b c *
      (Lightlike.pd a (fun y => e y k c) x - Lightlike.pd c (fun y => e y k a) x +
        ∑ i, ∑ j, eps3 k i j * (Γ a i * e x j c - Γ c i * e x j a)) = 0 := by
    simp [hC]
  simp only [hE, hpd]
  simp only [Fin.sum_univ_three, eps3_apply] at hVsum hCsum ⊢
  norm_num at hVsum hCsum ⊢
  linear_combination (1 / 4 : ℝ) * hVsum + (1 / 4 : ℝ) * hCsum

/-- **`∫ E^a_i δΓ^i_a = 0`** for a compactly supported variation `(δe, δΓ)` satisfying the linearised compatibility
condition of a positively oriented smooth co-triad: the functional derivative of `f[E] = ∫ Γ^i_a E^a_i` is `Γ`
(Holst (5)–(6)). -/
theorem integral_E_dSpin_eq_zero (e δe : CoTriad) (Γ δΓ : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (he : ∀ k b, ContDiff ℝ ∞ (fun y => e y k b)) (hδ : ∀ k b, ContDiff ℝ ∞ (fun y => δe y k b))
    (hδc : ∀ k b, HasCompactSupport (fun y => δe y k b)) (hpos : ∀ y, 0 < (e y).det)
    (hC : ∀ y k a b, Lightlike.pd a (fun z => e z k b) y - Lightlike.pd b (fun z => e z k a) y +
      ∑ i, ∑ j, eps3 k i j * (Γ y a i * e y j b - Γ y b i * e y j a) = 0)
    (hV : ∀ y k a b, Lightlike.pd a (fun z => δe z k b) y - Lightlike.pd b (fun z => δe z k a) y +
      ∑ i, ∑ j, eps3 k i j * (δΓ y a i * e y j b + Γ y a i * δe y j b - δΓ y b i * e y j a -
        Γ y b i * δe y j a) = 0) :
    ∫ y, ∑ a, ∑ j, densTriad e y a j * δΓ y a j = 0 := by
  set F : Fin 3 → (Fin 3 → ℝ) → ℝ := fun a y => ∑ b, ∑ c, ∑ k, eps3 a b c * (e y k c * δe y k b) with hF
  have hpt : (fun y => ∑ a, ∑ j, densTriad e y a j * δΓ y a j) = fun y => -(1 / 2) * ∑ a, Lightlike.pd a (F a) y :=
    funext fun y => E_dSpin_eq_div e δe (Γ y) (δΓ y) (hpos y)
      (fun k b => ((he k b).differentiable (by simp)) y) (fun k b => ((hδ k b).differentiable (by simp)) y)
      (hC y) (hV y)
  have hFs : ∀ a, ContDiff ℝ ∞ (F a) := fun a =>
    ContDiff.sum fun b _ => ContDiff.sum fun c _ => ContDiff.sum fun k _ =>
      contDiff_const.mul ((he k c).mul (hδ k b))
  have hFc : ∀ a, HasCompactSupport (F a) := fun a =>
    hcs_sum _ _ fun b _ => hcs_sum _ _ fun c _ => hcs_sum _ _ fun k _ =>
      ((hδc k b).mul_left (f := fun y => e y k c)).mul_left (f := fun _ => eps3 a b c)
  rw [hpt, integral_const_mul, (integral_sum_pd_eq_zero hFs hFc).2, mul_zero]

end Lightlike.Canonical
