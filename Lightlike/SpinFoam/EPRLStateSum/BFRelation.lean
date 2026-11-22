import Lightlike.SpinFoam.EPRLStateSum.BFPoint
import Lightlike.SpinFoam.Ooguri

/-!
# The EPRL state sum at `γ = 1` and the Ooguri state sum: the cutoff-zero relation

At `γ = 1` the Spin(4) labels of a doubled spin `J` are `(J, 0)` (`eprlN_one`, `eprlM_one`), so the
face amplitude is `J + 1`, the face amplitude of the Ooguri (`SU(2)` BF) model
(`faceAmp_one`). This file records the relation that holds without recoupling: at cutoff `0`
both state sums are `1` on every closed 4-complex, and a face amplitude other than `J + 1`
(here `(J + 1)²`) is different from the one that `γ = 1` produces.

The per-simplex vertices differ by a change of intertwiner basis (the EPRL boundary states use
the channel `(01)(23)`, the Ooguri vertex `(02)(13)`), so the full equality of the two state sums
is not stated here.
-/

open Lightlike.FourD

namespace Lightlike.SpinFoam.EPRL

variable {V : Type*} [LinearOrder V]

/-- **Cutoff `0` at the BF point**: the EPRL state sum at `γ = 1` and the Ooguri state sum are both
`1` on every 4-complex, so they agree. -/
theorem amplitude_one_zero (K : Complex4 V) :
    amplitude 1 K 0 = ((Lightlike.SpinFoam.amplitude K 0 : ℝ) : ℂ) := by
  rw [Lightlike.SpinFoam.EPRL.amplitude_zero, Lightlike.SpinFoam.amplitude_zero]
  simp

/-- **A wrong face amplitude is detected**: `(J + 1)²` is not the face amplitude `J + 1` that
`γ = 1` gives, for every spin `J ≥ 1`. -/
theorem faceAmp_one_ne_sq {J : ℕ} (hJ : 1 ≤ J) : faceAmp 1 J ≠ (J + 1) ^ 2 := by
  rw [faceAmp_one]
  intro h
  nlinarith

end Lightlike.SpinFoam.EPRL
