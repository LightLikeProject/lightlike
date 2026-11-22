import Mathlib
import Lightlike.GR.KerrHorizon

/-!
# Kerr horizon area, angular momentum and the Smarr formula (G1-066)

For `0 < M`, `a² ≤ M²` (geometric units `G = c = 1`) the event horizon of Kerr sits at `r = r₊`
(`kerrRplus`); its area is `A = 4π (r₊² + a²)` (`kerrArea`), the angular momentum is `J = M a`
(`kerrJ`).  With `Ω_H = a/(2 M r₊)` (`kerrOmega`) and `κ` (`kerrKappa`) of `GR/KerrHorizon.lean` we prove
the **Smarr formula** `M = 2 Ω_H J + κ A / (4π)` (`kerr_smarr`).  Source: carlip-2014 (Section 2).

Trust controls: with the wrong area `4π r₊²` the formula fails for `a ≠ 0` (`kerr_smarr_wrongArea_fails`
in `KerrControls.lean`).
-/

noncomputable section

namespace Lightlike.Rows.G1_066

open Lightlike Real

/-- Area of the Kerr event horizon, `A = 4π (r₊² + a²)`. -/
def kerrArea (M a : ℝ) : ℝ := 4 * π * (kerrRplus M a ^ 2 + a ^ 2)

/-- Angular momentum of Kerr, `J = M a`. -/
def kerrJ (M a : ℝ) : ℝ := M * a

lemma kerrRplus_pos {M a : ℝ} (hM : 0 < M) : 0 < kerrRplus M a := by
  unfold kerrRplus
  have := Real.sqrt_nonneg (M ^ 2 - a ^ 2)
  linarith

/-- The area in terms of `r₊`: `A = 8π M r₊`. -/
lemma kerrArea_eq {M a : ℝ} (h : a ^ 2 ≤ M ^ 2) : kerrArea M a = 8 * π * M * kerrRplus M a := by
  unfold kerrArea
  rw [rplus_sq_add M a h]
  ring

/-- `κ A / (4π) = √(M² - a²)`. -/
lemma kerr_kappa_area {M a : ℝ} (hM : 0 < M) (h : a ^ 2 ≤ M ^ 2) :
    kerrKappa M a * kerrArea M a / (4 * π) = √(M ^ 2 - a ^ 2) := by
  have hr := kerrRplus_pos (a := a) hM
  rw [kerrKappa_eq M a hM h, kerrArea_eq h]
  field_simp
  ring

/-- `2 Ω_H J = M - √(M² - a²)`. -/
lemma kerr_rotation_term {M a : ℝ} (hM : 0 < M) (h : a ^ 2 ≤ M ^ 2) :
    2 * kerrOmega M a * kerrJ M a = M - √(M ^ 2 - a ^ 2) := by
  have hr := kerrRplus_pos (a := a) hM
  have hs : √(M ^ 2 - a ^ 2) ^ 2 = M ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  have hrr : kerrRplus M a = M + √(M ^ 2 - a ^ 2) := rfl
  unfold kerrOmega kerrJ
  field_simp
  rw [hrr]
  nlinarith [hs]

/-- **Smarr formula for Kerr**: `M = 2 Ω_H J + κ A / (4π)`. -/
theorem kerr_smarr {M a : ℝ} (hM : 0 < M) (h : a ^ 2 ≤ M ^ 2) :
    M = 2 * kerrOmega M a * kerrJ M a + kerrKappa M a * kerrArea M a / (4 * π) := by
  rw [kerr_rotation_term hM h, kerr_kappa_area hM h]
  ring

end Lightlike.Rows.G1_066
