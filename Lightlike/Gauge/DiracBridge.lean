import Lightlike.Gauge.DiracNonlinear
import Lightlike.Gauge.DiracTangent
import Lightlike.Gauge.DiracRegular

/-!
# The Dirac step through tangent cones equals the linear step, for regular tuples

`DiracNonlinear` states the step of the Dirac algorithm through Mathlib's `tangentConeAt` (no regularity), and
`DiracRegular`, `DiracStage`, `DiracWire` the same step through the linear condition `Φ'_i (V x + ∑ u_a W_a x) = 0`
for tuples of constraint functions. The implicit function theorem is what connects them
(`DiracTangent.mem_tangentCone_zeroSet_iff`): for a tuple with strict derivatives that are linearly independent at the
points of the surface, `dStep` of its zero set is exactly the set of points where some multiplier gives a velocity killed
by every `Φ'_i`.
-/

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The tangent-cone step equals the linear step on a regular zero set**. -/
theorem dStep_zeroSet_eq (V : E → E) (W : ι → E → E) (Φ : Fin n → E → ℝ) (Φ' : E → Fin n → E →L[ℝ] ℝ)
    (hΦ : ∀ x, (∀ i, Φ i x = 0) → ∀ i, HasStrictFDerivAt (Φ i) (Φ' x i) x)
    (hind : ∀ x, (∀ i, Φ i x = 0) → LinearIndependent ℝ (Φ' x)) :
    dStep V W (zeroSet Φ) =
      {x | (∀ i, Φ i x = 0) ∧ ∃ u : ι → ℝ, ∀ i, Φ' x i (V x + ∑ a, u a • W a x) = 0} := by
  ext x
  simp only [dStep, zeroSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, u, hu⟩
    exact ⟨hx, u, (mem_tangentCone_zeroSet_iff (hΦ x hx) (hind x hx) hx _).mp hu⟩
  · rintro ⟨hx, u, hu⟩
    exact ⟨hx, u, (mem_tangentCone_zeroSet_iff (hΦ x hx) (hind x hx) hx _).mpr hu⟩

end Lightlike.Gauge
