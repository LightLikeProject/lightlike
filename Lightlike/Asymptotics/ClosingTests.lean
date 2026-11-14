import Lightlike.Asymptotics.Closing
import Lightlike.Asymptotics.LandingTests

/-!
# Trust checks for the closing argument

* **Known value.** The leading term `ε u₀ √(π/(N‖b‖)) / 2` of `laplace_valley` is `ε u₀` times
  the full half-Gaussian `∫₀^∞ e^{−N‖b‖ t²} dt` (`lead_eq_half_gaussian`, from Mathlib's
  `integral_gaussian_Ioi`), so its normalisation is that of Laplace's method and not, say, of the
  whole-line Gaussian.
* **Wrong input fails.** If both descent paths start in the same valley, they can land at the
  same point: for the regular tetrahedron, with every other hypothesis of
  `IsEuclid.not_landing_eq` in force, one descent path from a valley end point serves as both
  `α₁` and `α₂` (`landing_eq_same_valley_regular`). So the hypothesis that the valleys are
  opposite (`ε = 1` and `ε = −1`) is needed; with one valley the two half-Gaussians cancel
  instead of adding.
* **Non-vacuity.** For the regular tetrahedron, descent paths from the end points of opposite
  valley rays exist, land at real points at or left of `3` or at or right of `4`, and land at
  different points (`exists_landing_ne_regular`). So the hypotheses of
  `IsEuclid.not_landing_eq`, apart from the common landing point, can all be met.
* **Junk values.** `cexp`, `phaseC` and the primitive are used only on the open upper half-plane
  and at the real landing point, where `phaseC` is the genuine boundary value of a continuous
  function (`continuousOn_phaseC`); `π / (N a / 2)` has `N a ≠ 0` (`Re a ≥ ‖b‖ > 0`), and the
  square root is the principal one with `Re > 0`, so no junk value of `/` or `cpow` enters.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: the leading term of `laplace_valley` (for `ε u₀ = 1`) is the half-Gaussian
`∫₀^∞ e^{−N‖b‖ t²} dt = √(π/(N‖b‖)) / 2`, for every `N ‖b‖`. -/
theorem lead_eq_half_gaussian (N β : ℝ) :
    Real.sqrt (π / (N * β)) / 2 = ∫ t in Ioi (0 : ℝ), Real.exp (-(N * β) * t ^ 2) :=
  (integral_gaussian_Ioi (N * β)).symm

/-- **Wrong input fails**: two descent paths from the end point of one valley ray (`ε = 1`
twice) do land at a common real point, for the regular tetrahedron and valley data satisfying
all the other hypotheses of `IsEuclid.not_landing_eq`. -/
theorem landing_eq_same_valley_regular : ∃ (b u₀ : ℂ) (K r : ℝ), b ≠ 0 ∧ ‖u₀‖ = 1 ∧
    b * u₀ ^ 2 = -‖b‖ ∧ 0 < r ∧
    (∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (saddle (fun _ => 1) + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1))
            (saddle (fun _ => 1) + t * valleyDir u₀ ε τ) -
          phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1)) -
          b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤ K * t ^ 3 ∧
      (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1))
          (saddle (fun _ => 1) + t * valleyDir u₀ ε τ)).re ≤
        (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).re -
          ‖b‖ / 4 * t ^ 2) ∧
    ∃ (T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (p : ℝ),
      IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
        (descentDomain (fun _ => 1)) (saddle (fun _ => 1) + r * valleyDir u₀ 1 0) T₁ α₁ ∧
      IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
        (descentDomain (fun _ => 1)) (saddle (fun _ => 1) + r * valleyDir u₀ 1 0) T₂ α₂ ∧
      Tendsto α₁ (𝓝[<] T₁) (𝓝 (p : ℂ)) ∧ Tendsto α₂ (𝓝[<] T₂) (𝓝 (p : ℂ)) := by
  obtain ⟨b, u₀, K, r, -, hb0, hu, hbu, hr, -, hray, -⟩ := isEuclid_regular.exists_valley
  have hrI : r ∈ Icc (0 : ℝ) r := ⟨hr.le, le_rfl⟩
  have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb0
  have hτ : |(0 : ℝ)| ≤ 1 / 2 := by norm_num
  have h1 := (hray 1 (by norm_num) 0 hτ r hrI).2.2
  have h2 : 0 < ‖b‖ / 4 * r ^ 2 := by positivity
  obtain ⟨T, α, x, hα, hx, -⟩ :=
    isEuclid_regular.exists_descent (hray 1 (by norm_num) 0 hτ r hrI).1 (by linarith)
  exact ⟨b, u₀, K, r, hb0, hu, hbu, hr, hray, T, T, α, α, x, hα, hα, hx, hx⟩

/-- **Non-vacuity**: for the regular tetrahedron, descent paths from the end points of two
opposite valley rays land at two different real points, each at or left of `3` (the face sum)
or at or right of `4` (the quadrilateral sum). -/
theorem exists_landing_ne_regular : ∃ (z₁ z₂ : ℂ) (T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (x₁ x₂ : ℝ),
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₁ T₁ α₁ ∧ Tendsto α₁ (𝓝[<] T₁) (𝓝 (x₁ : ℂ)) ∧
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₂ T₂ α₂ ∧ Tendsto α₂ (𝓝[<] T₂) (𝓝 (x₂ : ℂ)) ∧
    (x₁ ≤ 3 ∨ 4 ≤ x₁) ∧ (x₂ ≤ 3 ∨ 4 ≤ x₂) ∧ x₁ ≠ x₂ := by
  obtain ⟨b, u₀, K, r, -, hb0, hu, hbu, hr, -, hray, -⟩ := isEuclid_regular.exists_valley
  have hτ : |(0 : ℝ)| ≤ 1 / 2 := by norm_num
  obtain ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, -, -, ho₁, ho₂, hne⟩ :=
    isEuclid_regular.exists_landing_ne hb0 hu hbu hr hray hτ hτ
  refine ⟨_, _, T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, ?_, ?_, hne⟩
  · rw [faceSum_regular, quadSum_regular] at ho₁
    rcases ho₁ with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rw [faceSum_regular, quadSum_regular] at ho₂
    rcases ho₂ with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h

end Lightlike.Asymptotics
