import Lightlike.NCG.DiracDecomposition
import Lightlike.NCG.TestsBimodule

/-!
# Tests for `D = Δ + J Δ J`

* `Delta_of_D_eq_zero`: `D = 0` gives `Δ = 0`;
* `twoPoint_Delta`: on the two-point space with `D = 0`, `Δ = 0`.
-/

namespace Lightlike.NCG.TestsDiracDecomposition

/-- **`D = 0` gives `Δ = 0`.** -/
theorem Delta_of_D_eq_zero {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {T : FiniteSpectralTriple A H} (R : RealStructure T)
    (C : CentralPartition A ι) (hD : T.D = 0) : Delta R C = 0 := by
  ext x
  simp [Delta_apply, hD]

/-- On the two-point space with `D = 0`, `Δ = 0`. -/
theorem twoPoint_Delta : Delta TwoPoint.twoPointReal TwoPoint.twoPointPartition = 0 :=
  Delta_of_D_eq_zero _ _ rfl

end Lightlike.NCG.TestsDiracDecomposition
