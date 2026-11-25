import Lightlike.Spacetime.TraceAnomaly2D.Anomaly

/-!
# Existence of a conserved stress tensor with the 2D trace anomaly (row G1-063, SC7)

Uniqueness (`anomaly_unique`) is only meaningful if the system `trace = c R / (24 π)`,
`div T = 0` has a solution. This file exhibits one, of Polyakov type, for every smooth conformal
factor `ψ` (so every metric `e^{2ψ} η` on `ℝ²`):

`T_{ab} = κ (-∂_a ψ ∂_b ψ + ∂_a ∂_b ψ + η_{ab} (½ (∂ψ)² - □ψ))`, `κ = c / (12 π)`,

with `(∂ψ)² = η^{ab} ∂_a ψ ∂_b ψ`, `□ψ = -∂_t² ψ + ∂_x² ψ` (`stressPoly`; the components are written
out in `t, x`). `stressPoly_anomaly_conservation` shows that it is symmetric, has trace
`c R / (24 π)` and is divergence free (Birrell–Davies 1982: the conformal-gauge Polyakov stress
tensor, without the free traceless function `t_u(u) , t_v(v)`).
-/

noncomputable section

namespace Lightlike.Rows.G1_063

open Lightlike
open scoped ContDiff

/-- Partial derivatives of a `C^∞` function are `C^∞`. -/
lemma pd_smooth {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (k : Fin n) :
    ContDiff ℝ ∞ (pd k f) :=
  contDiffOn_univ.mp (contDiffOn_pd (U := Set.univ) hf.contDiffOn isOpen_univ k)

/-- The Polyakov-type stress tensor `T_{ab} = κ(-ψ_a ψ_b + ψ_{ab} + η_{ab}(½ (∂ψ)² - □ψ))` of the
conformal factor `ψ`, in components `(t, x)` (`T_{tx}` written via `∂_t ∂_x ψ`). -/
def stressPoly (ψ : (Fin 2 → ℝ) → ℝ) (κ : ℝ) :
    Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ
  | 0, 0 => fun y => κ * ((-(1 / 2)) * (pd 0 ψ y * pd 0 ψ y) +
      (-(1 / 2)) * (pd 1 ψ y * pd 1 ψ y) + pd 1 (pd 1 ψ) y)
  | 0, 1 => fun y => κ * (-(pd 0 ψ y * pd 1 ψ y) + pd 0 (pd 1 ψ) y)
  | 1, 0 => fun y => κ * (-(pd 0 ψ y * pd 1 ψ y) + pd 0 (pd 1 ψ) y)
  | 1, 1 => fun y => κ * ((-(1 / 2)) * (pd 0 ψ y * pd 0 ψ y) +
      (-(1 / 2)) * (pd 1 ψ y * pd 1 ψ y) + pd 0 (pd 0 ψ) y)

/-- Derivative of the shape of `T_tt`, `T_xx`. -/
lemma pd_shapeD {f g h : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (κ : ℝ) (k : Fin 2) :
    pd k (fun y => κ * ((-(1 / 2)) * (f y * f y) + (-(1 / 2)) * (g y * g y) + h y)) x =
      κ * (-(f x * pd k f x) - g x * pd k g x + pd k h x) := by
  rw [pd_const_mul, pd_add, pd_add, pd_const_mul, pd_const_mul, pd_mul, pd_mul]
  · ring
  all_goals fun_prop

/-- Derivative of the shape of `T_tx`. -/
lemma pd_shapeO {f g h : (Fin 2 → ℝ) → ℝ} {x : Fin 2 → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x) (κ : ℝ) (k : Fin 2) :
    pd k (fun y => κ * (-(f y * g y) + h y)) x =
      κ * (-(pd k f x * g x + f x * pd k g x) + pd k h x) := by
  have h1 : (fun y => -(f y * g y) + h y) = fun y => (-1) * (f y * g y) + h y := by
    funext y; ring
  rw [pd_const_mul, h1, pd_add, pd_const_mul, pd_mul]
  · ring
  all_goals fun_prop

/-- The flat-space form of the anomaly with conservation for `stressPoly`. -/
lemma stressPoly_flat {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (κ : ℝ) (x : Fin 2 → ℝ) :
    (-stressPoly ψ κ 0 0 x + stressPoly ψ κ 1 1 x =
      κ * (pd 0 (fun y => pd 0 ψ y) x - pd 1 (fun y => pd 1 ψ y) x)) ∧
    ∀ ν, -pd 0 (stressPoly ψ κ 0 ν) x + pd 1 (stressPoly ψ κ 1 ν) x =
      pd ν ψ x * (κ * (pd 0 (fun y => pd 0 ψ y) x - pd 1 (fun y => pd 1 ψ y) x)) := by
  have hA := pd_smooth hψ 0
  have hB := pd_smooth hψ 1
  have dA : DifferentiableAt ℝ (pd 0 ψ) x := (hA.differentiable (by simp)).differentiableAt
  have dB : DifferentiableAt ℝ (pd 1 ψ) x := (hB.differentiable (by simp)).differentiableAt
  have dAA : DifferentiableAt ℝ (pd 0 (pd 0 ψ)) x :=
    ((pd_smooth hA 0).differentiable (by simp)).differentiableAt
  have dAB : DifferentiableAt ℝ (pd 0 (pd 1 ψ)) x :=
    ((pd_smooth hB 0).differentiable (by simp)).differentiableAt
  have dBB : DifferentiableAt ℝ (pd 1 (pd 1 ψ)) x :=
    ((pd_smooth hB 1).differentiable (by simp)).differentiableAt
  have hc1 : pd 1 (pd 0 ψ) = pd 0 (pd 1 ψ) := by
    funext y
    exact pd_pd_comm hψ.contDiffOn isOpen_univ (Set.mem_univ y) 1 0
  have hc2 : pd 1 (pd 0 (pd 1 ψ)) x = pd 0 (pd 1 (pd 1 ψ)) x :=
    pd_pd_comm hB.contDiffOn isOpen_univ (Set.mem_univ x) 1 0
  have hc3 : pd 1 (pd 0 (pd 0 ψ)) x = pd 0 (pd 0 (pd 1 ψ)) x := by
    rw [pd_pd_comm (pd_smooth hψ 0).contDiffOn isOpen_univ (Set.mem_univ x) 1 0, hc1]
  have e00 : ∀ k, pd k (stressPoly ψ κ 0 0) x = κ * (-(pd 0 ψ x * pd k (pd 0 ψ) x) -
      pd 1 ψ x * pd k (pd 1 ψ) x + pd k (pd 1 (pd 1 ψ)) x) := fun k =>
    pd_shapeD dA dB dBB κ k
  have e11 : ∀ k, pd k (stressPoly ψ κ 1 1) x = κ * (-(pd 0 ψ x * pd k (pd 0 ψ) x) -
      pd 1 ψ x * pd k (pd 1 ψ) x + pd k (pd 0 (pd 0 ψ)) x) := fun k =>
    pd_shapeD dA dB dAA κ k
  have e01 : ∀ k, pd k (stressPoly ψ κ 0 1) x = κ * (-(pd k (pd 0 ψ) x * pd 1 ψ x +
      pd 0 ψ x * pd k (pd 1 ψ) x) + pd k (pd 0 (pd 1 ψ)) x) := fun k =>
    pd_shapeO dA dB dAB κ k
  have e10 : ∀ k, pd k (stressPoly ψ κ 1 0) x = κ * (-(pd k (pd 0 ψ) x * pd 1 ψ x +
      pd 0 ψ x * pd k (pd 1 ψ) x) + pd k (pd 0 (pd 1 ψ)) x) := fun k =>
    pd_shapeO dA dB dAB κ k
  refine ⟨?_, ?_⟩
  · show -(κ * _) + κ * _ = _
    ring
  · rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · show -pd 0 (stressPoly ψ κ 0 0) x + pd 1 (stressPoly ψ κ 1 0) x = _
      rw [e00, e10]
      simp only [hc1]
      rw [hc2]
      ring
    · show -pd 0 (stressPoly ψ κ 0 1) x + pd 1 (stressPoly ψ κ 1 1) x = _
      rw [e01, e11]
      simp only [hc1]
      rw [hc3]
      ring

/-- **Existence of a conserved stress tensor with the 2D trace anomaly.** For every smooth conformal
factor `ψ`, the Polyakov-type tensor `stressPoly ψ (c / (12 π))` is symmetric, has trace
`c R / (24 π)` and is divergence free for the metric `e^{2ψ} η` on `ℝ²` (Birrell–Davies 1982). -/
theorem stressPoly_anomaly_conservation {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (c : ℝ)
    (x : Fin 2 → ℝ) :
    trT (confEta2 ψ) (stressPoly ψ (c / (12 * Real.pi))) x =
        c * scalarCurvature (confEta2 ψ) x / (24 * Real.pi) ∧
      ∀ ν, divT (confEta2 ψ) (stressPoly ψ (c / (12 * Real.pi))) ν x = 0 :=
  (anomaly_conservation_iff hψ c _ x rfl).2 (stressPoly_flat hψ _ x)

end Lightlike.Rows.G1_063
