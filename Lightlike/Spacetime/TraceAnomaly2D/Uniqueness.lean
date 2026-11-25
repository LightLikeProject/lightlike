import Lightlike.Spacetime.TraceAnomaly2D.Anomaly

/-!
# Uniqueness of the anomalous stress tensor up to conserved traceless terms (row G1-063, SC7)

Wald's uniqueness statement ("`⟨T⟩` is unique up to local conserved terms") has, for the 2D trace
anomaly in conformal gauge, the following classical form (`anomaly_unique`): two symmetric tensor
fields `T`, `T'` on `(ℝ², e^{2ψ} η)` with the same trace anomaly `T^μ_μ = c R / (24 π)` that are
both conserved differ, at a point, by a traceless conserved tensor `D = T - T'`; in light-cone form
`(∂_t - ∂_x)(D_tt + D_tx) = 0` and `(∂_t + ∂_x)(D_tt - D_tx) = 0`, i.e. `D_{uu}` depends on `u`
only and `D_{vv}` on `v` only, and the conformal factor `ψ` has dropped out
(Birrell–Davies 1982).
-/

noncomputable section

namespace Lightlike.Rows.G1_063

open Lightlike
open scoped ContDiff

/-- **Uniqueness of the 2D anomalous stress tensor up to a traceless conserved tensor.**
Let `T, T'` be symmetric `(0,2)`-tensor fields differentiable at `x`, both with trace
`c R / (24 π)` everywhere and both divergence free at `x` on `(ℝ², e^{2ψ} η)`. Then `D = T - T'`
is traceless (`D_tt = D_xx` everywhere) and satisfies, at `x`, the light-cone equations
`(∂_t - ∂_x)(D_tt + D_tx) = 0`, `(∂_t + ∂_x)(D_tt - D_tx) = 0` at `x`. -/
theorem anomaly_unique {ψ : (Fin 2 → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (c : ℝ)
    (T T' : Fin 2 → Fin 2 → (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ)
    (hs : ∀ y, T 0 1 y = T 1 0 y) (hs' : ∀ y, T' 0 1 y = T' 1 0 y)
    (hd : ∀ i j, DifferentiableAt ℝ (T i j) x) (hd' : ∀ i j, DifferentiableAt ℝ (T' i j) x)
    (htr : ∀ y, trT (confEta2 ψ) T y = c * scalarCurvature (confEta2 ψ) y / (24 * Real.pi))
    (htr' : ∀ y, trT (confEta2 ψ) T' y = c * scalarCurvature (confEta2 ψ) y / (24 * Real.pi))
    (hdiv : ∀ ν, divT (confEta2 ψ) T ν x = 0) (hdiv' : ∀ ν, divT (confEta2 ψ) T' ν x = 0) :
    (∀ y, T 0 0 y - T' 0 0 y = T 1 1 y - T' 1 1 y) ∧
    (pd 0 (fun y => (T 0 0 y - T' 0 0 y) + (T 0 1 y - T' 0 1 y)) x
        - pd 1 (fun y => (T 0 0 y - T' 0 0 y) + (T 0 1 y - T' 0 1 y)) x = 0) ∧
    (pd 0 (fun y => (T 0 0 y - T' 0 0 y) - (T 0 1 y - T' 0 1 y)) x
        + pd 1 (fun y => (T 0 0 y - T' 0 0 y) - (T 0 1 y - T' 0 1 y)) x = 0) := by
  obtain ⟨h1, h2⟩ := (anomaly_conservation_iff hψ c T x (hs x)).1 ⟨htr x, hdiv⟩
  obtain ⟨h1', h2'⟩ := (anomaly_conservation_iff hψ c T' x (hs' x)).1 ⟨htr' x, hdiv'⟩
  have htl : ∀ y, T 0 0 y - T' 0 0 y = T 1 1 y - T' 1 1 y := by
    intro y
    have a := trT_confEta2 ψ T y
    have b := trT_confEta2 ψ T' y
    rw [htr y] at a
    rw [htr' y] at b
    have he : Real.exp (-(2 * ψ y)) ≠ 0 := (Real.exp_pos _).ne'
    have : Real.exp (-(2 * ψ y)) * (-T 0 0 y + T 1 1 y) =
        Real.exp (-(2 * ψ y)) * (-T' 0 0 y + T' 1 1 y) := by rw [← a, ← b]
    have := mul_left_cancel₀ he this
    linarith
  have key : pd 1 (T 1 1) x - pd 1 (T' 1 1) x = pd 1 (T 0 0) x - pd 1 (T' 0 0) x := by
    rw [← pd_sub (hd 1 1) (hd' 1 1), ← pd_sub (hd 0 0) (hd' 0 0)]
    exact congrArg (fun f => pd 1 f x) (funext fun y => (htl y).symm)
  have e0 := h2 0
  have e1 := h2 1
  have e0' := h2' 0
  have e1' := h2' 1
  have hT10 : T 1 0 = T 0 1 := funext fun y => (hs y).symm
  have hT10' : T' 1 0 = T' 0 1 := funext fun y => (hs' y).symm
  rw [hT10] at e0
  rw [hT10'] at e0'
  have dA : DifferentiableAt ℝ (fun y => T 0 0 y - T' 0 0 y) x := (hd 0 0).sub (hd' 0 0)
  have dB : DifferentiableAt ℝ (fun y => T 0 1 y - T' 0 1 y) x := (hd 0 1).sub (hd' 0 1)
  refine ⟨htl, ?_, ?_⟩
  · rw [pd_add dA dB, pd_add dA dB, pd_sub (hd 0 0) (hd' 0 0), pd_sub (hd 0 0) (hd' 0 0),
      pd_sub (hd 0 1) (hd' 0 1), pd_sub (hd 0 1) (hd' 0 1)]
    linarith
  · rw [pd_sub dA dB, pd_sub dA dB, pd_sub (hd 0 0) (hd' 0 0), pd_sub (hd 0 0) (hd' 0 0),
      pd_sub (hd 0 1) (hd' 0 1), pd_sub (hd 0 1) (hd' 0 1)]
    linarith

end Lightlike.Rows.G1_063
