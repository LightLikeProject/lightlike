import Lightlike.Asymptotics.EPRL.GaugeFix

/-!
# Localisation of the gauge-fixed integral

The gauge-fixed integrand `Y ↦ F_n(Y, 1)` on `SU(2)^4` has modulus at most one. Outside an open
neighbourhood `U` of the set where the modulus is one, the integral of its `λ`-th power is
exponentially small: `‖∫_{Uᶜ} F_n^λ‖ ≤ q^λ` for one `q < 1`
(`norm_setIntegral_compl_le4`). The general statement for a continuous function of modulus at
most one on a compact probability space is `norm_setIntegral_pow_compl_le`.
-/

open MeasureTheory Complex

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4

/-- **Exponential smallness off a neighbourhood of the maximum set** (general form). -/
theorem norm_setIntegral_pow_compl_le {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (G : α → ℂ) (hG : Continuous G) (h1 : ∀ x, ‖G x‖ ≤ 1) {U : Set α} (hU : IsOpen U)
    (hmax : ∀ x, ‖G x‖ = 1 → x ∈ U) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ, ‖∫ x in Uᶜ, G x ^ lam ∂μ‖ ≤ q ^ lam := by
  have hq : ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ x, x ∉ U → ‖G x‖ ≤ q := by
    by_cases hne : Uᶜ.Nonempty
    · obtain ⟨x₀, hx₀, hmx⟩ := hU.isClosed_compl.isCompact.exists_isMaxOn hne hG.norm.continuousOn
      exact ⟨_, norm_nonneg _, lt_of_le_of_ne (h1 x₀) fun h => hx₀ (hmax x₀ h),
        fun x hx => hmx hx⟩
    · exact ⟨0, le_rfl, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  obtain ⟨q, hq0, hq1, hq⟩ := hq
  refine ⟨q, hq0, hq1, fun lam => ?_⟩
  have hb : ∀ᵐ x ∂μ.restrict Uᶜ, ‖G x ^ lam‖ ≤ q ^ lam := by
    refine (ae_restrict_iff' hU.isClosed_compl.measurableSet).mpr (Filter.Eventually.of_forall
      fun x hx => ?_)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hq x hx) lam
  calc _ ≤ q ^ lam * (μ.restrict Uᶜ).real Set.univ := norm_integral_le_of_norm_le_const hb
    _ ≤ q ^ lam * 1 := by
        gcongr
        simp only [Measure.restrict_apply_univ, measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    _ = q ^ lam := mul_one _

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.Subtype.secondCountableTopology _

lemma continuous_cohF4 (n : Fin 10 → ℕ) (g : BdryData) :
    Continuous fun Y : Fin 4 → SU2 => cohF n g (Fin.snoc Y 1) :=
  (continuous_cohAmp n g).comp (Continuous.finSnoc continuous_id continuous_const)

lemma cohF_smul (n : Fin 10 → ℕ) (g : BdryData) (lam : ℕ) (X : Fin 5 → SU2) :
    cohF (lam • n) g X = cohF n g X ^ lam := cohAmp_smul _ _ _ _

/-- **The gauge-fixed remainder is exponentially small**: if `U ⊆ SU(2)^4` is open and contains
every `Y` with `|F_n(Y,1)| = 1`, then `‖∫_{Uᶜ} F_{λn}(Y,1) dY‖ ≤ q^λ` for one `q < 1`. -/
theorem norm_setIntegral_compl_le4 (n : Fin 10 → ℕ) {g : BdryData} (hg : IsSU2Data g)
    {U : Set (Fin 4 → SU2)} (hU : IsOpen U)
    (hmax : ∀ Y, ‖cohF n g (Fin.snoc Y 1)‖ = 1 → Y ∈ U) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ lam : ℕ,
      ‖∫ Y in Uᶜ, cohF (lam • n) g (Fin.snoc Y 1) ∂(haarN (N := 4))‖ ≤ q ^ lam := by
  obtain ⟨q, hq0, hq1, h⟩ := norm_setIntegral_pow_compl_le (haarN (N := 4))
    (fun Y : Fin 4 → SU2 => cohF n g (Fin.snoc Y 1)) (continuous_cohF4 n g)
    (fun Y => norm_cohAmp_le n hg _) hU hmax
  exact ⟨q, hq0, hq1, fun lam => by simpa only [cohF_smul] using h lam⟩

end Lightlike.Asymptotics.EPRL
