import Lightlike.Asymptotics.EPRL.Decay

/-!
# Localisation of the coherent 15j integral near the maximum set

The proof of the asymptotic formula for the coherent 15j integral splits the integral over
`SU(2)^5` into a part near the set where `|F_n| = 1` and a remainder. This file proves the
remainder bound: outside any open neighbourhood `U` of the set `{|F_n| = 1}`, the integrand
`F_{λn} = F_n^λ` is bounded by `q^λ` for a single `q < 1`, so the integral over the complement of
`U` is exponentially small (`norm_setIntegral_compl_le`). The remaining steps are the critical
points, the Hessian and the remainder bound of the stationary phase theorem near each critical
class.
-/

open Matrix MeasureTheory Complex

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- **A uniform gap off a neighbourhood of the maximum set.** If `U` is open and contains every
point of `SU(2)^5` with `|F_n| = 1`, then `|F_n| ≤ q` on the complement of `U`, for one `q < 1`
(compactness of the complement and continuity of `F_n`). -/
theorem exists_sup_lt_one (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    {U : Set (Fin 5 → SU2)} (hU : IsOpen U)
    (hmax : ∀ X, ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 → X ∈ U) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ X, X ∉ U →
      ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ ≤ q := by
  by_cases hne : Uᶜ.Nonempty
  · obtain ⟨X₀, hX₀, hmx⟩ := hU.isClosed_compl.isCompact.exists_isMaxOn hne
      (continuous_cohAmp n g).norm.continuousOn
    refine ⟨_, norm_nonneg _, ?_, fun X hX => hmx hX⟩
    refine lt_of_le_of_ne (norm_cohAmp_le n hg X₀) fun h1 => hX₀ (hmax X₀ h1)
  · refine ⟨0, le_rfl, one_pos, fun X hX => ?_⟩
    exact absurd ⟨X, hX⟩ hne

/-- **The remainder is exponentially small.** Under the hypotheses of `exists_sup_lt_one`, the
integral of `F_{λn}` over the complement of `U` has norm at most `q^λ`. -/
theorem norm_setIntegral_compl_le (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    {U : Set (Fin 5 → SU2)} (hU : IsOpen U)
    (hmax : ∀ X, ‖cohAmp n g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 → X ∈ U) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ,
      ‖∫ X in Uᶜ, cohAmp (lam • n) g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))
          ∂(haarN (N := 5))‖ ≤ q ^ lam := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_sup_lt_one n hg hU hmax
  refine ⟨q, hq0, hq1, fun lam => ?_⟩
  have hb : ∀ᵐ X ∂(haarN (N := 5)).restrict Uᶜ,
      ‖cohAmp (lam • n) g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ ≤ q ^ lam := by
    refine (ae_restrict_iff' hU.isClosed_compl.measurableSet).mpr (Filter.Eventually.of_forall
      fun X hX => ?_)
    rw [cohAmp_smul, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hq X hX) lam
  calc _ ≤ q ^ lam * ((haarN (N := 5)).restrict Uᶜ).real Set.univ :=
        norm_integral_le_of_norm_le_const hb
    _ ≤ q ^ lam * 1 := by
        gcongr
        simp only [Measure.restrict_apply_univ, measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    _ = q ^ lam := mul_one _

/-- **Wrong input**: the neighbourhood must contain the maximum set. With `U = ∅` and all spins
zero (`F = 1` everywhere) the hypothesis `hmax` fails, and indeed the integral over `Uᶜ` does not
decay. -/
theorem not_hmax_empty (g : BdryData) :
    ¬ ∀ X, ‖cohAmp (0 : Fin 10 → ℕ) g (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 →
      X ∈ (∅ : Set (Fin 5 → SU2)) := by
  intro h
  exact h 1 (by simp [cohAmp])

end Lightlike.Asymptotics.EPRL
