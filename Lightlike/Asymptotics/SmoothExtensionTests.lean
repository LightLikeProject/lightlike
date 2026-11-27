import Mathlib
import Lightlike.Asymptotics.SmoothExtension

/-!
# Tests: smooth extension

Non-vacuity: `y ↦ 1/y`, smooth on `(0, ∞)`, agrees near the compact `[1, 2]` with a smooth function on `ℝ`; the
extension takes the value `1/2` at `2` (it is the function itself there, not an arbitrary smooth function).
-/

open Set
open scoped ContDiff
noncomputable section
namespace Lightlike.SmoothExtensionTests

/-- The extension of `1/y` from `(0, ∞)` near `[1, 2]` takes the value `1/2` at `2`. -/
example : ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ F 2 = 1 / 2 := by
  obtain ⟨F, hF, W, -, hKW, hFW⟩ := exists_contDiff_eqOn_nhds (f := fun y : ℝ => y⁻¹) isOpen_Ioi
    (contDiffOn_inv ℝ |>.mono fun y (hy : (0 : ℝ) < y) => hy.ne') isCompact_Icc
    (fun y hy => lt_of_lt_of_le one_pos hy.1)
  exact ⟨F, hF, by rw [hFW 2 (hKW ⟨by norm_num, le_rfl⟩)]; norm_num⟩

end Lightlike.SmoothExtensionTests
