import Lightlike.Asymptotics.Closing

/-!
# The saddle level lies between the face and quadrilateral sums

Let `ψ` be the continued phase of Racah's sum (`phaseC`), `s` the saddle point of a Euclidean
tetrahedron, `κ = Im ψ s` its level, and `A_max`, `B_min` the largest face sum and the smallest
quadrilateral sum. On the real axis `Im ψ = bdry`, a piecewise-linear function that equals `π u`
on `[A_max, B_min]` (`bdry_mid`), is strictly decreasing left of `A_max` above the level
`π A_max` and strictly decreasing right of `B_min` below the level `π B_min`. This file locates
the saddle level for the steepest-descent proof of `RacahSumAsymptotics`.

**Main theorem (`IsEuclid.pi_faceSum_lt_level`).** `π Aᵢ < κ < π Bₖ` for all `i`, `k`.

## Proof: the η-shift

For every `|η| ≤ η₀ = ‖b‖ r²/2`, the valley step (`exists_valley`) gives a valley-ray end point at
the level `κ + η` in each of the two valleys, and the descent paths from them land at two different
real points on that level (`IsEuclid.exists_landing_ne`). A level below `π A_max`
or above `π B_min` is taken by `bdry` at most once (`eq_of_bdry_eq_of_not_mem`), so
`π A_max ≤ κ + η ≤ π B_min` for all those `η`, and `κ` lies at distance at least `η₀ > 0` from
both ends (`IsEuclid.level_bounds`). No envelope argument (the derivative of the saddle in the
lengths) is needed.

At such a level both landing points, which lie outside the middle interval, cannot be on
the same side, so one lands at or left of `A_max` and the other at or right of `B_min`
(`IsEuclid.landing_sides`): the descent contour separates the poles of Racah's summand.
-/

open Set Filter Topology Complex
open scoped Real

namespace Lightlike.Asymptotics

/-- **A level outside `[π A_max, π B_min]` is taken by `bdry` at most once.** If two real points
have the same `bdry` level and it is below `π Aᵢ` for some `i` or above `π Bₖ` for some `k`, the
points coincide: below `π A_max` both lie right of `B_min`, above `π B_min` both lie left of
`A_max`, and `bdry` is strictly monotone there. -/
theorem eq_of_bdry_eq_of_not_mem {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hA : ∀ i, 0 < A i)
    (hAB : ∀ i k, A i < B k) {x₁ x₂ : ℝ} (h12 : bdry A B x₁ = bdry A B x₂)
    (hout : (∃ i, bdry A B x₁ < π * A i) ∨ ∃ k, π * B k < bdry A B x₁) : x₁ = x₂ := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max A
  obtain ⟨k₀, hk₀⟩ := Finite.exists_min B
  have hπ := Real.pi_pos
  rcases hout with ⟨i, hi⟩ | ⟨k, hk⟩
  · have hlev : bdry A B x₁ < π * A i₀ :=
      hi.trans_le (mul_le_mul_of_nonneg_left (hi₀ i) hπ.le)
    have hu := gt_of_bdry_lt hA hAB hi₀ hk₀ hlev
    have hlev₂ : bdry A B x₂ < π * A i₀ := h12 ▸ hlev
    have hv := gt_of_bdry_lt hA hAB hi₀ hk₀ hlev₂
    have hlev' : bdry A B x₁ < π * B k₀ :=
      hlev.trans (mul_lt_mul_of_pos_left (hAB i₀ k₀) hπ)
    exact bdry_injOn_right hA hAB hu.le hv.le hlev' h12
  · have hlev : π * B k₀ < bdry A B x₁ :=
      (mul_le_mul_of_nonneg_left (hk₀ k) hπ.le).trans_lt hk
    have hu := lt_of_bdry_gt hA hAB hi₀ hk₀ hlev
    have hlev₂ : π * B k₀ < bdry A B x₂ := h12 ▸ hlev
    have hv := lt_of_bdry_gt hA hAB hi₀ hk₀ hlev₂
    have hlev' : π * A i₀ < bdry A B x₁ :=
      (mul_lt_mul_of_pos_left (hAB i₀ k₀) hπ).trans hlev
    exact bdry_injOn_left hA hAB hu.le hv.le hlev' h12

/-- **The η-shift.** With the valley data of `IsEuclid.exists_valley` (rays with their bounds,
and in each valley an end point at every level `κ + η`, `|η| ≤ ‖b‖ r²/2`), the saddle level
`κ = Im ψ s` satisfies `π Aᵢ + ‖b‖ r²/2 ≤ κ` and `κ + ‖b‖ r²/2 ≤ π Bₖ` for all `i`, `k`. -/
theorem IsEuclid.level_bounds {l : Fin 6 → ℝ} (h : IsEuclid l)
    {b u₀ : ℂ} {K r : ℝ} (hb0 : b ≠ 0) (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖)
    (hr : 0 < r)
    (hray : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (saddle l + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ) -
          phaseC (faceSum l) (quadSum l) (saddle l) - b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤
        K * t ^ 3 ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖b‖ / 4 * t ^ 2)
    (hlev : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ η : ℝ, |η| ≤ ‖b‖ * r ^ 2 / 2 → ∃ τ : ℝ, |τ| ≤ 1 / 2 ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ ε τ)).im =
        (phaseC (faceSum l) (quadSum l) (saddle l)).im + η) :
    (∀ i, π * faceSum l i + ‖b‖ * r ^ 2 / 2 ≤ (phaseC (faceSum l) (quadSum l) (saddle l)).im) ∧
    ∀ k, (phaseC (faceSum l) (quadSum l) (saddle l)).im + ‖b‖ * r ^ 2 / 2 ≤ π * quadSum l k := by
  set κ := (phaseC (faceSum l) (quadSum l) (saddle l)).im with hκ
  set η₀ := ‖b‖ * r ^ 2 / 2 with hη₀def
  have hη₀ : 0 ≤ η₀ := by positivity
  have key : ∀ η : ℝ, |η| ≤ η₀ →
      (∀ i, π * faceSum l i ≤ κ + η) ∧ ∀ k, κ + η ≤ π * quadSum l k := by
    intro η hη
    obtain ⟨τ₁, hτ₁, hl₁⟩ := hlev 1 (by norm_num) η hη
    obtain ⟨τ₂, hτ₂, hl₂⟩ := hlev (-1) (by norm_num) η hη
    obtain ⟨-, -, -, -, x₁, x₂, -, -, -, -, hb₁, hb₂, -, -, hne⟩ :=
      h.exists_landing_ne hb0 hu hbu hr hray hτ₁ hτ₂
    rw [hl₁] at hb₁
    rw [hl₂] at hb₂
    by_contra hc
    simp only [not_and_or, not_forall, not_le] at hc
    refine hne (eq_of_bdry_eq_of_not_mem h.faceSum_pos h.lt (hb₁.trans hb₂.symm) ?_)
    rw [hb₁]
    exact hc
  refine ⟨fun i => ?_, fun k => ?_⟩
  · have := (key (-η₀) (by rw [abs_neg, abs_of_nonneg hη₀])).1 i
    linarith
  · have := (key η₀ (by rw [abs_of_nonneg hη₀])).2 k
    linarith

/-- **The saddle level lies strictly between the face and quadrilateral sums.** For a
Euclidean tetrahedron with face sums `Aᵢ`, quadrilateral sums `Bₖ` and saddle `s`,
`π Aᵢ < Im ψ s < π Bₖ` for all `i`, `k`. -/
theorem IsEuclid.pi_faceSum_lt_level {l : Fin 6 → ℝ} (h : IsEuclid l) :
    (∀ i, π * faceSum l i < (phaseC (faceSum l) (quadSum l) (saddle l)).im) ∧
    ∀ k, (phaseC (faceSum l) (quadSum l) (saddle l)).im < π * quadSum l k := by
  obtain ⟨b, u₀, K, r, -, hb0, hu, hbu, hr, -, hray, hlev⟩ := h.exists_valley
  have hpos : 0 < ‖b‖ * r ^ 2 / 2 := by
    have := norm_pos_iff.2 hb0
    positivity
  obtain ⟨h1, h2⟩ := h.level_bounds hb0 hu hbu hr hray hlev
  exact ⟨fun i => by linarith [h1 i], fun k => by linarith [h2 k]⟩

/-- **The two descent paths land on opposite sides.** With the valley data of
`IsEuclid.exists_valley`, let `z₁`, `z₂` be end points of valley rays in the valleys `ε = 1`
and `ε = −1` at one level `κ'` with `π Aᵢ < κ' < π Bₖ` for all `i`, `k` (for instance the
saddle level, by `IsEuclid.pi_faceSum_lt_level`). Then descent paths from them land at real
points `x₁`, `x₂` on that level, one at or left of the largest face sum and the other at or
right of the smallest quadrilateral sum. -/
theorem IsEuclid.landing_sides {l : Fin 6 → ℝ} (h : IsEuclid l)
    {b u₀ : ℂ} {K r : ℝ} (hb0 : b ≠ 0) (hu : ‖u₀‖ = 1) (hbu : b * u₀ ^ 2 = -‖b‖)
    (hr : 0 < r)
    (hray : ∀ ε : ℝ, ε ^ 2 = 1 → ∀ τ : ℝ, |τ| ≤ 1 / 2 → ∀ t ∈ Icc (0 : ℝ) r,
      0 < (saddle l + t * valleyDir u₀ ε τ).im ∧
      ‖phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ) -
          phaseC (faceSum l) (quadSum l) (saddle l) - b * valleyDir u₀ ε τ ^ 2 * t ^ 2‖ ≤
        K * t ^ 3 ∧
      (phaseC (faceSum l) (quadSum l) (saddle l + t * valleyDir u₀ ε τ)).re ≤
        (phaseC (faceSum l) (quadSum l) (saddle l)).re - ‖b‖ / 4 * t ^ 2)
    {τ₁ τ₂ κ' : ℝ} (hτ₁ : |τ₁| ≤ 1 / 2) (hτ₂ : |τ₂| ≤ 1 / 2)
    (hl₁ : (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ 1 τ₁)).im = κ')
    (hl₂ : (phaseC (faceSum l) (quadSum l) (saddle l + r * valleyDir u₀ (-1) τ₂)).im = κ')
    (hlo : ∀ i, π * faceSum l i < κ') (hhi : ∀ k, κ' < π * quadSum l k) :
    ∃ (T₁ T₂ : ℝ) (α₁ α₂ : ℝ → ℂ) (x₁ x₂ : ℝ),
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir u₀ 1 τ₁) T₁ α₁ ∧ Tendsto α₁ (𝓝[<] T₁) (𝓝 (x₁ : ℂ)) ∧
      IsLift (descentField (faceSum l) (quadSum l)) (descentDomain l)
        (saddle l + r * valleyDir u₀ (-1) τ₂) T₂ α₂ ∧ Tendsto α₂ (𝓝[<] T₂) (𝓝 (x₂ : ℂ)) ∧
      bdry (faceSum l) (quadSum l) x₁ = κ' ∧ bdry (faceSum l) (quadSum l) x₂ = κ' ∧
      (((∃ i, x₁ ≤ faceSum l i) ∧ ∃ k, quadSum l k ≤ x₂) ∨
        ((∃ i, x₂ ≤ faceSum l i) ∧ ∃ k, quadSum l k ≤ x₁)) := by
  obtain ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, hb₁, hb₂, ho₁, ho₂, hne⟩ :=
    h.exists_landing_ne hb0 hu hbu hr hray hτ₁ hτ₂
  rw [hl₁] at hb₁
  rw [hl₂] at hb₂
  refine ⟨T₁, T₂, α₁, α₂, x₁, x₂, hα₁, hx₁, hα₂, hx₂, hb₁, hb₂, ?_⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (faceSum l)
  obtain ⟨k₀, hk₀⟩ := Finite.exists_min (quadSum l)
  have hA := h.faceSum_pos
  have hAB := h.lt
  -- both on the left, or both on the right, would force `x₁ = x₂`
  have hleft : ∀ x, (∃ i, x ≤ faceSum l i) → x ≤ faceSum l i₀ := fun x ⟨i, hi⟩ =>
    hi.trans (hi₀ i)
  have hright : ∀ x, (∃ k, quadSum l k ≤ x) → quadSum l k₀ ≤ x := fun x ⟨k, hk⟩ =>
    (hk₀ k).trans hk
  rcases ho₁ with ho₁ | ho₁ <;> rcases ho₂ with ho₂ | ho₂
  · exact absurd (bdry_injOn_left hA hAB (hleft _ ho₁) (hleft _ ho₂)
      (by rw [hb₁]; exact hlo i₀) (hb₁.trans hb₂.symm)) hne
  · exact Or.inl ⟨ho₁, ho₂⟩
  · exact Or.inr ⟨ho₂, ho₁⟩
  · exact absurd (bdry_injOn_right hA hAB (hright _ ho₁) (hright _ ho₂)
      (by rw [hb₁]; exact hhi k₀) (hb₁.trans hb₂.symm)) hne

end Lightlike.Asymptotics
