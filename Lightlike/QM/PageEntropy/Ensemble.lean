import Lightlike.QM.PageEntropy.PageValue
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Haar-random pure-state ensemble and its average entanglement entropy

A Haar-random pure state of `ℂ^m ⊗ ℂ^n` is a point of the unit sphere of `ℂ^(m n) = EuclideanSpace ℂ (Fin m × Fin n)`
drawn from the normalised surface measure (the unique unitarily invariant probability measure on that sphere).
This module defines

* `ketOfSphere`: a unit vector as a Physlib `Ket`;
* `sphereProb`: the normalised sphere measure `Measure.toSphere volume / total mass`;
* `avgEntropy m n`: the expectation of the reduced von Neumann entropy `Sᵥₙ (|ψ⟩⟨ψ|.traceRight)`;

and proves the first instance of Page's theorem, `avgEntropy_one_left`: for `m = 1` the average is `0 = pageValue 1 n`.
-/

namespace Lightlike.Rows.G1_069

open MeasureTheory Metric

/-- The Hilbert space `ℂ^m ⊗ ℂ^n`, as `ℂ^(m n)` with its Euclidean norm. -/
abbrev PageSpace (m n : ℕ) := EuclideanSpace ℂ (Fin m × Fin n)

/-- A unit vector of `EuclideanSpace ℂ d` as a Physlib `Ket`. -/
def ketOfSphere {d : Type*} [Fintype d] (x : sphere (0 : EuclideanSpace ℂ d) 1) : Ket d where
  vec := x.1
  normalized' := by
    have h := x.2
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
    simpa using h

/-- The normalised surface measure on the unit sphere of `ℂ^m ⊗ ℂ^n`: the Haar-random pure-state distribution. -/
noncomputable def sphereProb (m n : ℕ) : Measure (sphere (0 : PageSpace m n) 1) :=
  ((volume : Measure (PageSpace m n)).toSphere Set.univ)⁻¹ • (volume : Measure (PageSpace m n)).toSphere

/-- The normalised sphere measure is a probability measure (when the space is nontrivial). -/
instance sphereProb_isProbabilityMeasure (m n : ℕ) [NeZero m] [NeZero n] :
    IsProbabilityMeasure (sphereProb m n) := by
  have : Nontrivial (PageSpace m n) := by
    have : Nonempty (Fin m × Fin n) := ⟨(0, 0)⟩
    infer_instance
  refine ⟨?_⟩
  simp only [sphereProb, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (fun h => Measure.toSphere_ne_zero (volume : Measure (PageSpace m n))
      (Measure.measure_univ_eq_zero.mp h))
    (measure_ne_top _ _)

/-- The reduced von Neumann entropy of a unit vector of `ℂ^m ⊗ ℂ^n` (the entropy of the `ℂ^m` marginal). -/
noncomputable def sphereEntropy (m n : ℕ) (x : sphere (0 : PageSpace m n) 1) : ℝ :=
  Sᵥₙ (MState.pure (ketOfSphere x)).traceRight

/-- The average entanglement entropy of a Haar-random pure state of `ℂ^m ⊗ ℂ^n`. -/
noncomputable def avgEntropy (m n : ℕ) : ℝ :=
  ∫ x, sphereEntropy m n x ∂(sphereProb m n)

/-- For `m = 1` every state is a product state, so the entropy is identically `0`. -/
theorem sphereEntropy_one_left (n : ℕ) (x : sphere (0 : PageSpace 1 n) 1) : sphereEntropy 1 n x = 0 :=
  Sᵥₙ_unit_zero _

/-- **Page's theorem for `m = 1`**: the average entanglement entropy equals `pageValue 1 n = 0`. -/
theorem avgEntropy_one_left (n : ℕ) : avgEntropy 1 n = pageValue 1 n := by
  rw [pageValue_one_left]
  simp [avgEntropy, sphereEntropy_one_left]

end Lightlike.Rows.G1_069
