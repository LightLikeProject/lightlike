import Mathlib
import Lightlike.GR.KerrFirstLaw.KerrArea

/-!
# First law of Kerr black-hole mechanics (G1-066)

For a differentiable one-parameter family of Kerr black holes `t ↦ (M t, a t)` with `0 < M t`
and `(a t)² < (M t)²` (non-extremal), the horizon area `A = kerrArea` and the angular momentum
`J = kerrJ` are differentiable and
`dM = κ/(8π) dA + Ω_H dJ`   (`kerr_first_law`).
Source: carlip-2014 (Section 2).
-/

noncomputable section

namespace Lightlike.Rows.G1_066

open Lightlike Real

/-- **First law for Kerr** (curve form): along a differentiable family of non-extremal Kerr
black holes, `dM/dt = κ/(8π) · dA/dt + Ω_H · dJ/dt`, with `A = kerrArea`, `J = kerrJ`. -/
theorem kerr_first_law {M a : ℝ → ℝ} {M' a' : ℝ} {t : ℝ}
    (hM : HasDerivAt M M' t) (ha : HasDerivAt a a' t)
    (hpos : 0 < M t) (hlt : a t ^ 2 < M t ^ 2) :
    ∃ A' J' : ℝ,
      HasDerivAt (fun u => kerrArea (M u) (a u)) A' t ∧
      HasDerivAt (fun u => kerrJ (M u) (a u)) J' t ∧
      M' = kerrKappa (M t) (a t) / (8 * π) * A' + kerrOmega (M t) (a t) * J' := by
  have hD : HasDerivAt (fun u => M u ^ 2 - a u ^ 2)
      (2 * M t * M' - 2 * a t * a') t := by
    have h1 := (hM.pow 2)
    have h2 := (ha.pow 2)
    convert h1.sub h2 using 1
    simp
  have hne : M t ^ 2 - a t ^ 2 ≠ 0 := by linarith
  have hS := hD.sqrt hne
  set s := √(M t ^ 2 - a t ^ 2) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs : s ^ 2 = M t ^ 2 - a t ^ 2 := Real.sq_sqrt (by linarith)
  set s' := (2 * M t * M' - 2 * a t * a') / (2 * s) with hs'def
  have hR : HasDerivAt (fun u => kerrRplus (M u) (a u)) (M' + s') t := hM.add hS
  have hA : HasDerivAt (fun u => kerrArea (M u) (a u))
      (4 * π * (2 * kerrRplus (M t) (a t) * (M' + s') + 2 * a t * a')) t := by
    have h := ((hR.mul hR).add (ha.mul ha)).const_mul (4 * π)
    have hf : (fun u => kerrArea (M u) (a u)) =
        fun u => 4 * π * (kerrRplus (M u) (a u) * kerrRplus (M u) (a u) + a u * a u) := by
      funext u
      unfold kerrArea
      ring
    rw [hf]
    exact h.congr_deriv (by ring)
  have hJ : HasDerivAt (fun u => kerrJ (M u) (a u)) (M' * a t + M t * a') t := by
    have h := hM.mul ha
    exact h
  refine ⟨_, _, hA, hJ, ?_⟩
  have hr : kerrRplus (M t) (a t) = M t + s := rfl
  rw [kerrKappa_eq _ _ hpos (by linarith), hr]
  unfold kerrOmega
  rw [hr, hs'def, ← hsdef]
  have hr0 : 0 < M t + s := by linarith
  field_simp
  linear_combination (-8 * M') * hs

end Lightlike.Rows.G1_066
