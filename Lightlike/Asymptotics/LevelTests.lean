import Lightlike.Asymptotics.Level
import Lightlike.Asymptotics.ClosingTests

/-!
# Trust checks for the saddle level

For the regular tetrahedron with unit edges the face sums are `Aᵢ = 3` and the quadrilateral
sums `Bₖ = 4`.

* **Known value.** `IsEuclid.pi_faceSum_lt_level` gives `3π < Im ψ(s) < 4π` for the regular
  tetrahedron (`level_regular`), in agreement with the numerical value `Im ψ(s) = 11.4638`
  (`scripts/asymptotics/level_check.py`; `3π = 9.42`, `4π = 12.57`).
* **Wrong input fails.** A level inside `(π A_max, π B_min)` can be taken by `bdry` more than
  once: for the regular tetrahedron `bdry (17/6) = bdry (7/2) = 7π/2`
  (`bdry_regular_twice`). So the hypothesis of `eq_of_bdry_eq_of_not_mem` that the level is
  outside the middle range is needed, and the η-shift really uses that the two landing points
  differ.
* **Non-vacuity.** At the saddle level of the regular tetrahedron, the descent paths from the
  two valleys land one at or left of `3` and the other at or right of `4`
  (`landing_sides_regular`), so the hypotheses of `IsEuclid.landing_sides` can all be met;
  `IsEuclid.level_bounds` is applied to the data of `IsEuclid.exists_valley` in the proof of
  `IsEuclid.pi_faceSum_lt_level`, which needs only `IsEuclid`.
* **Junk values.** No division, logarithm or square root is taken outside its domain: the level
  is `Im ψ` at the saddle, which has `Im s > 0`, and `bdry` is a finite sum of `min`s.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: the saddle level of the regular unit tetrahedron lies in `(3π, 4π)`. -/
theorem level_regular :
    3 * π < (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).im ∧
    (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).im < 4 * π := by
  obtain ⟨h1, h2⟩ := isEuclid_regular.pi_faceSum_lt_level
  have e1 : faceSum (fun _ : Fin 6 => (1 : ℝ)) 0 = 3 := by
    rw [faceSum_regular]
  have e2 : quadSum (fun _ : Fin 6 => (1 : ℝ)) 0 = 4 := by
    rw [quadSum_regular]
  have a := h1 0
  have c := h2 0
  rw [e1] at a
  rw [e2] at c
  constructor <;> linarith

/-- **Wrong input fails**: the middle level `7π/2` is taken by `bdry` at the two different points
`17/6` and `7/2` for the regular tetrahedron, so `bdry` is not injective on a level inside
`(π A_max, π B_min)`. -/
theorem bdry_regular_twice :
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (17 / 6) =
      bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (7 / 2) ∧ (17 / 6 : ℝ) ≠ 7 / 2 := by
  refine ⟨?_, by norm_num⟩
  rw [bdry_regular_mid, faceSum_regular, quadSum_regular]
  simp only [bdry, Fin.sum_univ_four, Fin.sum_univ_three]
  norm_num [min_def]

/-- **Non-vacuity** of `IsEuclid.landing_sides`: for the regular tetrahedron, the descent paths
from the valley end points at the saddle level land one at or left of `3` and the other at or
right of `4`. -/
theorem landing_sides_regular : ∃ (z₁ z₂ : ℂ) (T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (x₁ x₂ : ℝ),
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₁ T₁ α₁ ∧ Tendsto α₁ (𝓝[<] T₁) (𝓝 (x₁ : ℂ)) ∧
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₂ T₂ α₂ ∧ Tendsto α₂ (𝓝[<] T₂) (𝓝 (x₂ : ℂ)) ∧
    ((x₁ ≤ 3 ∧ 4 ≤ x₂) ∨ (x₂ ≤ 3 ∧ 4 ≤ x₁)) := by
  obtain ⟨b, u₀, K, r, -, hb0, hu, hbu, hr, -, hray, hlev⟩ := isEuclid_regular.exists_valley
  have h0 : |(0 : ℝ)| ≤ ‖b‖ * r ^ 2 / 2 := by rw [abs_zero]; positivity
  obtain ⟨τ₁, hτ₁, hl₁⟩ := hlev 1 (by norm_num) 0 h0
  obtain ⟨τ₂, hτ₂, hl₂⟩ := hlev (-1) (by norm_num) 0 h0
  rw [add_zero] at hl₁ hl₂
  obtain ⟨hlo, hhi⟩ := isEuclid_regular.pi_faceSum_lt_level
  obtain ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, -, -, hs⟩ :=
    isEuclid_regular.landing_sides hb0 hu hbu hr hray hτ₁ hτ₂ hl₁ hl₂ hlo hhi
  refine ⟨_, _, T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, ?_⟩
  simpa only [faceSum_regular, quadSum_regular, exists_const] using hs

end Lightlike.Asymptotics
