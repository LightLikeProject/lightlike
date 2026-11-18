import Lightlike.Gauge.DiracAlgorithm

/-!
# Trust check for the Dirac algorithm

On `ℝ²` with `A (x, y) = (y, 0)`, no multipliers (`U = ⊥`) and the primary constraint `x = 0`: the evolution
`x' = y` leaves `x = 0` only if `y = 0`, so the consistency condition gives the secondary constraint `y = 0`: the
first step strictly shrinks the surface (`C₁ ≠ C₀`), and `C₁ = ⊥` is then consistent. With `A = 0` there is no
secondary constraint.
-/

namespace Lightlike.Gauge

/-- `A (x, y) = (y, 0)`. -/
def shiftA : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ := (LinearMap.inl ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ ℝ)

/-- The primary constraint surface `x = 0`. -/
def xZero : Submodule ℝ (ℝ × ℝ) := LinearMap.ker (LinearMap.fst ℝ ℝ ℝ)

/-- **A secondary constraint**: the first step of the algorithm strictly shrinks the surface `x = 0`. -/
theorem diracStep_shiftA_ne : diracStep shiftA ⊥ xZero ≠ xZero := by
  intro h
  have h1 : ((0 : ℝ), (1 : ℝ)) ∈ xZero := by simp [xZero]
  rw [← h] at h1
  have := h1.2
  simp [shiftA, xZero] at this

/-- **No secondary constraint** when the evolution is trivial. -/
theorem diracStep_zero (C U : Submodule ℝ (ℝ × ℝ)) : diracStep 0 U C = C := by
  ext x
  simp only [diracStep, Submodule.mem_inf, Submodule.mem_comap, LinearMap.zero_apply]
  exact ⟨fun h => h.1, fun h => ⟨h, zero_mem _⟩⟩

end Lightlike.Gauge
