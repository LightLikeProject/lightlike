import Lightlike.Asymptotics.UniformContour
import Lightlike.Asymptotics.Tests
import Lightlike.Asymptotics.ContourTests

/-!
# Trust checks for the strict landings and the continuity in the lengths

* **Known values.** For the regular unit tetrahedron (`Aᵢ = 3`, `Bₖ = 4`) the saddle level is
  `κ = 6 (π − arccos ⅓)`, and `bdry` is `π (12 − 3u)` on `[0, 3]` and `π (12 − 2u)` on `[4, ∞)`.
  So the two landing points are `x₁ = 2 + 2 arccos ⅓ / π ≈ 2.78`, inside `(0, 3)`, and
  `x₂ = 3 + 3 arccos ⅓ / π ≈ 4.18`, right of `4` (`landings_regular`), as
  `IsEuclid.landing_sides_strict` predicts. For `m_λ = (1 + 1/(2λ)) · 1` the saddle is
  `(1 + 1/(2λ)) s₁` by homogeneity, and its limit `s₁` agrees with `tendsto_saddle_lengthsDir`
  (`saddle_lengthsDir_ones`).
* **Wrong input fails.** Without `Σᵢ Aᵢ = Σₖ Bₖ` a landing can lie at `0`: for `Aᵢ = 1`,
  `Bₖ = 10` the level `4π` lies strictly between `π A_max = π` and `π B_min = 10π`, and `bdry`
  takes it at `u = 0` (`bdry_unbalanced_zero`), so `pos_lt_of_bdry_eq` needs the balance.
* **Non-vacuity.** At the saddle level of the regular tetrahedron the descent paths from the two
  valleys land one in `(0, 3)` and the other right of `4` (`landing_sides_strict_regular`). The
  closed ball of radius `Im s₁ / 2` about the saddle `s₁` of the regular tetrahedron is a compact
  subset of the upper half-plane, on which `ψ_{m_λ} → ψ_1` uniformly
  (`exists_uniform_ball_regular`).
* **Junk values.** At the zero lengths Lean's `x/0 = 0` gives `saddle 0 = 0`
  (`saddle_zero`), a junk value on the real axis; the zero lengths are not Euclidean
  (`not_isEuclid_zero`), so `continuousOn_saddle` does not see it. The continuity statements are
  within the closed upper half-plane, where the principal logarithm is continuous from above and
  `xlog 0 = 0` is the true limit (`continuousAt_xlog_zero`).
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- `bdry` of the regular tetrahedron on `[0, 3]`: `π (12 − 3u)`. -/
lemma bdry_regular_left {u : ℝ} (h0 : 0 ≤ u) (h3 : u ≤ 3) :
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) u = π * (12 - 3 * u) := by
  rw [faceSum_regular, quadSum_regular,
    bdry_of_le (B := fun _ => (4 : ℝ)) fun _ => (show u ≤ 4 by linarith)]
  simp only [Fin.sum_univ_four, min_eq_right h0, max_eq_left (by linarith : (0 : ℝ) ≤ 3 - u)]
  ring

/-- `bdry` of the regular tetrahedron on `[4, ∞)`: `π (12 − 2u)`. -/
lemma bdry_regular_right {u : ℝ} (h4 : 4 ≤ u) :
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) u = π * (12 - 2 * u) := by
  rw [faceSum_regular, quadSum_regular,
    bdry_of_ge (A := fun _ => (3 : ℝ)) (fun _ => (show (3 : ℝ) ≤ u by linarith)) (by linarith)]
  simp only [Fin.sum_univ_three, max_eq_right (by linarith : (4 : ℝ) - u ≤ 0)]
  ring

/-- The saddle level of the regular tetrahedron is `6 (π − arccos ⅓)`. -/
lemma level_regular_eq :
    (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).im =
      6 * (π - Real.arccos (1 / 3)) := by
  rw [← phase_eq_phaseC (fun _ => 1) isEuclid_regular.saddle_im_pos, im_phase_regular]

/-- **Known values**: for the regular tetrahedron the saddle level is taken at
`x₁ = 2 + 2 arccos ⅓ / π`, inside `(0, 3)`, and at `x₂ = 3 + 3 arccos ⅓ / π`, right of `4`. -/
theorem landings_regular :
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (2 + 2 * (Real.arccos (1 / 3) / π)) =
        (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).im ∧
      0 < 2 + 2 * (Real.arccos (1 / 3) / π) ∧ 2 + 2 * (Real.arccos (1 / 3) / π) < 3 ∧
      bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (3 + 3 * (Real.arccos (1 / 3) / π)) =
        (phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (saddle (fun _ => 1))).im ∧
      4 < 3 + 3 * (Real.arccos (1 / 3) / π) := by
  have ha0 : 0 < Real.arccos (1 / 3) := Real.arccos_pos.2 (by norm_num)
  have ha1 : Real.arccos (1 / 3) < π / 2 := Real.arccos_lt_pi_div_two.2 (by norm_num)
  have ht0 : 0 < Real.arccos (1 / 3) / π := div_pos ha0 Real.pi_pos
  have ht1 : Real.arccos (1 / 3) / π < 1 / 2 := by
    rw [div_lt_iff₀ Real.pi_pos]; linarith
  have hm : π * (Real.arccos (1 / 3) / π) = Real.arccos (1 / 3) :=
    mul_div_cancel₀ _ Real.pi_ne_zero
  have ha2 : π / 3 < Real.arccos (1 / 3) := by
    have h := Real.strictAntiOn_arccos (show (1 / 3 : ℝ) ∈ Icc (-1) 1 by constructor <;> norm_num)
      (show (1 / 2 : ℝ) ∈ Icc (-1) 1 by constructor <;> norm_num) (by norm_num : (1 / 3 : ℝ) < 1 / 2)
    rwa [← Real.cos_pi_div_three, Real.arccos_cos (by positivity) (by linarith)] at h
  have ht2 : 1 / 3 < Real.arccos (1 / 3) / π := by
    rw [lt_div_iff₀ Real.pi_pos]; linarith
  refine ⟨?_, by linarith, by linarith, ?_, by linarith⟩
  · rw [bdry_regular_left (by linarith) (by linarith), level_regular_eq]
    linear_combination (-6) * hm
  · rw [bdry_regular_right (by linarith), level_regular_eq]
    linear_combination (-6) * hm

/-- **Wrong input fails**: for `Aᵢ = 1` and `Bₖ = 10`, where `Σᵢ Aᵢ ≠ Σₖ Bₖ`, the level `4π`
lies strictly between `π A_max` and `π B_min` but is taken at `u = 0`, which is not positive. -/
theorem bdry_unbalanced_zero :
    bdry (fun _ => 1) (fun _ => 10) 0 = 4 * π ∧ π * 1 < 4 * π ∧ 4 * π < π * 10 := by
  have hπ := Real.pi_pos
  refine ⟨?_, by linarith, by linarith⟩
  rw [bdry_of_nonpos (A := fun _ => (1 : ℝ)) (B := fun _ => (10 : ℝ)) (fun _ => one_pos)
    (fun _ _ => by norm_num) le_rfl]
  simp only [Fin.sum_univ_four]
  ring

/-- **Non-vacuity** of `IsEuclid.landing_sides_strict`: for the regular tetrahedron, the descent
paths from the valley end points at the saddle level land one in `(0, 3)` and the other right
of `4`. -/
theorem landing_sides_strict_regular : ∃ (z₁ z₂ : ℂ) (T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (x₁ x₂ : ℝ),
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₁ T₁ α₁ ∧ Tendsto α₁ (𝓝[<] T₁) (𝓝 (x₁ : ℂ)) ∧
    IsLift (descentField (faceSum (fun _ => 1)) (quadSum (fun _ => 1)))
      (descentDomain (fun _ => 1)) z₂ T₂ α₂ ∧ Tendsto α₂ (𝓝[<] T₂) (𝓝 (x₂ : ℂ)) ∧
    (((0 < x₁ ∧ x₁ < 3) ∧ 4 < x₂) ∨ ((0 < x₂ ∧ x₂ < 3) ∧ 4 < x₁)) := by
  obtain ⟨b, u₀, K, r, -, hb0, hu, hbu, hr, -, hray, hlev⟩ := isEuclid_regular.exists_valley
  have h0 : |(0 : ℝ)| ≤ ‖b‖ * r ^ 2 / 2 := by rw [abs_zero]; positivity
  obtain ⟨τ₁, hτ₁, hl₁⟩ := hlev 1 (by norm_num) 0 h0
  obtain ⟨τ₂, hτ₂, hl₂⟩ := hlev (-1) (by norm_num) 0 h0
  rw [add_zero] at hl₁ hl₂
  obtain ⟨hlo, hhi⟩ := isEuclid_regular.pi_faceSum_lt_level
  obtain ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, -, -, hs⟩ :=
    isEuclid_regular.landing_sides_strict hb0 hu hbu hr hray hτ₁ hτ₂ hl₁ hl₂ hlo hhi
  refine ⟨_, _, T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, ?_⟩
  simpa only [faceSum_regular, quadSum_regular, exists_const] using hs

/-- `m_λ = (1 + 1/(2λ)) · 1` for the unit spins. -/
lemma lengthsDir_ones (lam : ℕ) :
    lengthsDir (fun _ => 1) lam = (1 + 1 / (2 * (lam : ℝ))) • fun _ : Fin 6 => (1 : ℝ) := by
  funext e
  simp [lengthsDir]

/-- **Known value**: for the unit spins the saddle of `m_λ` is `(1 + 1/(2λ)) s₁` by
homogeneity, whose limit `s₁` is the one given by `tendsto_saddle_lengthsDir`. -/
theorem saddle_lengthsDir_ones (lam : ℕ) :
    saddle (lengthsDir (fun _ => 1) lam) =
        ((1 + 1 / (2 * (lam : ℝ)) : ℝ) : ℂ) * saddle (fun _ => 1) ∧
      Tendsto (fun lam : ℕ => saddle (lengthsDir (fun _ => 1) lam)) atTop
        (𝓝 (saddle fun _ => 1)) := by
  refine ⟨?_, ?_⟩
  · rw [lengthsDir_ones, saddle_smul _ (by positivity)]
  · have h : IsEuclid fun e => (((fun _ => 1) : Fin 6 → ℕ) e : ℝ) := by
      simpa using isEuclid_regular
    simpa using tendsto_saddle_lengthsDir h

/-- The closed ball of radius `Im s / 2` about the saddle `s` of a Euclidean tetrahedron lies in
the upper half-plane. -/
lemma IsEuclid.closedBall_subset {l : Fin 6 → ℝ} (h : IsEuclid l) :
    Metric.closedBall (saddle l) ((saddle l).im / 2) ⊆ {z : ℂ | 0 ≤ z.im} := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 : |(z - saddle l).im| ≤ ‖z - saddle l‖ := abs_im_le_norm _
  have h2 := h.saddle_im_pos
  rw [sub_im] at h1
  simp only [mem_ofPred_eq]
  linarith [neg_abs_le (z.im - (saddle l).im)]

/-- **Non-vacuity** of `eventually_norm_phaseC_lengthsDir_sub_lt`: on the closed ball of radius
`Im s₁ / 2` about the saddle of the regular tetrahedron, `ψ_{m_λ}` is within `1` of `ψ_1` for
some `λ > 0`. -/
theorem exists_uniform_ball_regular :
    ∃ lam : ℕ, 0 < lam ∧
      ∀ z ∈ Metric.closedBall (saddle fun _ => 1) ((saddle fun _ => (1 : ℝ)).im / 2),
        ‖phaseC (faceSum (lengthsDir (fun _ => 1) lam)) (quadSum (lengthsDir (fun _ => 1) lam)) z -
          phaseC (faceSum fun _ => 1) (quadSum fun _ => 1) z‖ < 1 := by
  have h := eventually_norm_phaseC_lengthsDir_sub_lt (fun _ => 1) (isCompact_closedBall _ _)
    isEuclid_regular.closedBall_subset one_pos
  obtain ⟨lam, hlam, h0⟩ := (h.and (eventually_gt_atTop 0)).exists
  refine ⟨lam, h0, fun z hz => ?_⟩
  simpa using hlam z hz

/-- **Junk value**: Lean's `x/0 = 0` gives `saddle 0 = 0`. -/
theorem saddle_zero : saddle 0 = 0 := by
  apply Complex.ext <;> simp [qa]

/-- The zero lengths are not Euclidean, so `continuousOn_saddle` does not see the junk value
`saddle 0 = 0`. -/
theorem not_isEuclid_zero : ¬ IsEuclid 0 := fun h => by
  simpa [qa] using h.qa_pos

end Lightlike.Asymptotics
