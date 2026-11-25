import Mathlib
import Lightlike.PL.JordanCurve

/-!
# A point of zero winding about a Jordan curve is joined to infinity

Row G3-188 (PL5), step 3 of the pass-4 plan.  For a Jordan curve `f : Circle → ℂ`, a point `R` off the curve
whose global logarithm of `s ↦ f (exp s) - R` has period increment `0` (winding number `0`) is joined, off the
curve, to points of arbitrarily large norm.  This is the converse half of the index argument inside the proof of
`jordan_curve_theorem`, extracted: the index vanishes exactly on the component of `Ω`.
-/

open Complex Set unitInterval Real

namespace Lightlike.PL.Schoenflies

theorem jordan_index_zero_joined {f : Circle → ℂ} (hc : Continuous f) (hi : Function.Injective f)
    {R : ℂ} (hR : R ∉ range f) {F : ℝ → ℂ} (hFc : Continuous F)
    (hF : ∀ s, exp (F s) = f (Circle.exp s) - R) (h0 : F (2 * π) = F 0) (M : ℝ) :
    ∃ R' : ℂ, M < ‖R'‖ ∧ JoinedIn (range f)ᶜ R R' := by
  have hJo : IsOpen (range f)ᶜ := (isCompact_range hc).isClosed.isOpen_compl
  obtain ⟨T, hS, hU, a, b, hab, hb2, hγ₁, hγ₂⟩ := exists_theta_top hc hi
  have hcurve : T.curve = range f := hU
  have hΩJ : T.Ω ∉ range f := hcurve ▸ fun h => T.hΩ h
  -- every point of index zero is joined to `Ω`
  have hdich : ∀ R : ℂ, R ∉ range f → loopIndex T.ω₀ R = 0 → JoinedIn (range f)ᶜ R T.Ω := by
    intro R hR hidx
    by_cases hseg : R ∈ segment ℝ T.P T.Ω ∪ segment ℝ T.Q T.Ω
    · rcases T.segments_subset_component hseg with h | h
      · exact absurd (hcurve ▸ h) hR
      · rw [hcurve] at h
        exact (joinedIn_of_mem_connectedComponentIn hJo h).symm
    · by_contra hnj
      refine T.iota_ne_zero hS ?_ ?_ hidx
      · rintro ((h | h) | h)
        · exact hR (hcurve ▸ h)
        · exact hseg (Or.inl h)
        · exact hseg (Or.inr h)
      · rw [hcurve]; exact hnj
  have hav : ∀ (R : ℂ), R ∉ range f → ∀ t, T.ω₀ t ≠ R := by
    intro R hR t h
    apply hR
    rw [← hcurve, ← T.range_ω₀, ← h]
    exact ⟨t, rfl⟩
  have hR0 : loopIndex T.ω₀ R = 0 := by
    have h1 := loopIndex_spec T.ω₀ (hav R hR)
    rw [Theta.logInc_ω₀ T hFc hF hγ₁ hγ₂, h0, sub_self] at h1
    have h2 : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have h3 : ((loopIndex T.ω₀ R : ℤ) : ℂ) = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h h2
    exact_mod_cast h3
  -- far points have index zero
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ∀ t, ‖T.ω₀ t‖ ≤ ρ := by
    obtain ⟨ρ, hρ⟩ := (isCompact_range T.ω₀.continuous).isBounded.exists_norm_le
    exact ⟨ρ, fun t => hρ _ ⟨t, rfl⟩⟩
  set R' : ℂ := ((max M ρ + 1 : ℝ) : ℂ) with hR'
  have hnorm : ‖R'‖ = max M ρ + 1 := by
    rw [hR', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    have : ρ ≥ 0 := (norm_nonneg _).trans (hρ 0)
    linarith [le_max_right M ρ]
  have hρR' : ρ < ‖R'‖ := by rw [hnorm]; linarith [le_max_right M ρ]
  have hR'J : R' ∉ range f := by
    rintro ⟨w, hw⟩
    have : f w ∈ range T.ω₀ := by rw [T.range_ω₀, hcurve]; exact ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := this
    have := hρ t
    rw [ht, hw] at this
    linarith
  have hR'0 : loopIndex T.ω₀ R' = 0 := loopIndex_eq_zero_of_far T.ω₀ hρ hρR'
  refine ⟨R', by rw [hnorm]; linarith [le_max_left M ρ], ?_⟩
  exact (hdich R hR hR0).trans (hdich R' hR'J hR'0).symm

end Lightlike.PL.Schoenflies
