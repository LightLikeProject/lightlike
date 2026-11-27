module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteSchurCoh

/-!
# The Plancherel norm of the coherent matrix coefficient

For `E_A = D_n(diag(A, 1/A)) e₀` and the `K`-weight vector `e_j`, the `K × K` Plancherel identity gives
`∫ |⟨e_j, D(g) E_A⟩|² dg = Σ_l |γ_A C_l (-t_A)^l|² ∫ |⟨e_j, D(g) e_l⟩|² dg` (`lintegral_norm_sq_coh`): the matrix
coefficient is a series of `K × K`-eigenfunctions with distinct right weights.
-/

@[expose] public section

open MeasureTheory Set Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma summable_sq_of_summable {f : ℕ → ℝ} (hf0 : ∀ l, 0 ≤ f l) (hf : Summable f) :
    Summable fun l => f l ^ 2 := by
  have hb : ∀ l, f l ≤ ∑' l, f l := fun l => hf.le_tsum l (fun i _ => hf0 i)
  refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_) (hf.mul_left (∑' l, f l))
  nlinarith [hb l, hf0 l]

/-- The `ℓ²`-sum of the `K × K`-components of the coherent matrix coefficient. -/
theorem tsum_norm_sq_kkCoeff_coh {n : ℕ} (hn : 2 ≤ n) (j : ℕ) {A : ℝ} (hA : 0 < A) (ξ : ℝ) :
    ∑' m : Fin 2 → ℤ, ‖kkCoeff (mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn))) m ξ‖ ^ 2 =
      ∑' l : ℕ, ‖cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2 := by
  set F := mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn)) with hF
  set c : ℕ → ℂ := fun l => cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ) with hc
  set φ : ℕ → (Fin 2 → ℤ) := fun l => -kkWeight n j l with hφdef
  have hφ : Function.Injective φ := kkWeight_injective n j
  have hval : ∀ l, kkCoeff F (φ l) ξ = c l := by
    intro l
    rw [kkCoeff_coh hn j hA ξ (φ l), tsum_eq_single l]
    · simp [hφdef, hc]
    · intro l' hl'
      have hne : ¬ (-kkWeight n j l + kkWeight n j l' = 0) := fun h =>
        hl' ((kkWeight_add_eq_zero n j l l').1 h).symm
      simp [hφdef, hne]
  have hzero : ∀ m, m ∉ Set.range φ → kkCoeff F m ξ = 0 := by
    intro m hm
    rw [kkCoeff_coh hn j hA ξ m]
    have : ∀ l, (if m + kkWeight n j l = 0 then c l else 0) = 0 := by
      intro l
      by_cases h : m + kkWeight n j l = 0
      · exfalso
        apply hm
        refine ⟨l, ?_⟩
        have : m = -kkWeight n j l := by
          have := congrArg (fun z => z - kkWeight n j l) h
          simpa [sub_eq_add_neg] using this
        simpa [hφdef] using this.symm
      · simp [h]
    refine (tsum_congr (fun l => ?_)).trans tsum_zero
    exact this l
  have hsupp : Function.support (fun m => ‖kkCoeff F m ξ‖ ^ 2) ⊆ Set.range φ := by
    intro m hm
    by_contra hmr
    apply hm
    simp [hzero m hmr]
  have h := hφ.tsum_eq hsupp
  rw [← h]
  refine tsum_congr (fun l => ?_)
  show ‖kkCoeff F (φ l) ξ‖ ^ 2 = ‖c l‖ ^ 2
  rw [hval]

/-- **The Plancherel norm of the coherent matrix coefficient**:
`∫ |⟨e_j, D(g) E_A⟩|² = Σ_l |γ_A C_l (-t_A)^l|² ∫ |⟨e_j, D(g) e_l⟩|²`. -/
theorem lintegral_norm_sq_coh {n : ℕ} (hn : 2 ≤ n) (j : ℕ) {A : ℝ} (hA : 0 < A) :
    ∫⁻ g, ENNReal.ofReal (‖mcoef n (kClass hn j) (discreteAction n (diagSL A hA.ne') (lowestClass hn)) g‖ ^ 2)
        ∂haarR =
      ∑' l : ℕ, ENNReal.ofReal (‖cohCoeff n A l‖ ^ 2) *
        ∫⁻ g, ENNReal.ofReal (‖mcoef n (kClass hn j) (kClass hn l) g‖ ^ 2) ∂haarR := by
  rw [lintegral_norm_sq_eq_kk (continuous_mcoef n _ _)]
  set c : ℕ → ℝ → ℂ := fun l ξ => cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ) with hc
  have hsumm : ∀ ξ, Summable fun l => ‖c l ξ‖ ^ 2 := by
    intro ξ
    have h0 := (hasSum_kkProfile_coh hn j hA ξ 0).summable
    have h1 : Summable fun l => ‖c l ξ‖ := by
      have := summable_norm_iff.2 h0
      refine this.congr (fun l => ?_)
      rw [norm_mul, norm_exp_char, one_mul]
    exact summable_sq_of_summable (fun l => norm_nonneg _) h1
  have hstep : ∀ ξ : ℝ, ENNReal.ofReal (Real.sinh ξ) * ENNReal.ofReal ((2 * π) ^ 2 *
      ∑' m : Fin 2 → ℤ, ‖kkCoeff (mcoef n (kClass hn j)
        (discreteAction n (diagSL A hA.ne') (lowestClass hn))) m ξ‖ ^ 2) =
      ∑' l : ℕ, ENNReal.ofReal (‖cohCoeff n A l‖ ^ 2) * (ENNReal.ofReal (Real.sinh ξ) *
        ENNReal.ofReal ((2 * π) ^ 2 * ‖mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2)) := by
    intro ξ
    rw [tsum_norm_sq_kkCoeff_coh hn j hA ξ]
    have hmul : (2 * π) ^ 2 * ∑' l : ℕ, ‖cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2 =
        ∑' l : ℕ, (2 * π) ^ 2 * ‖cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2 :=
      (tsum_mul_left).symm
    rw [hmul, ENNReal.ofReal_tsum_of_nonneg (fun l => by positivity) ((hsumm ξ).mul_left _),
      ← ENNReal.tsum_mul_left]
    refine tsum_congr (fun l => ?_)
    rw [show ‖cohCoeff n A l * mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2 =
        ‖cohCoeff n A l‖ ^ 2 * ‖mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2 by rw [norm_mul, mul_pow]]
    rw [show (2 * π) ^ 2 * (‖cohCoeff n A l‖ ^ 2 * ‖mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2) =
        ‖cohCoeff n A l‖ ^ 2 * ((2 * π) ^ 2 * ‖mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2) by ring,
      ENNReal.ofReal_mul (by positivity)]
    rw [mul_left_comm]
  have hmeas : ∀ l : ℕ, Measurable fun ξ : ℝ => ENNReal.ofReal (‖cohCoeff n A l‖ ^ 2) *
      (ENNReal.ofReal (Real.sinh ξ) *
        ENNReal.ofReal ((2 * π) ^ 2 * ‖mcoef n (kClass hn j) (kClass hn l) (aR ξ)‖ ^ 2)) := by
    intro l
    refine measurable_const.mul ((ENNReal.measurable_ofReal.comp Real.continuous_sinh.measurable).mul
      (ENNReal.measurable_ofReal.comp ?_))
    exact (continuous_const.mul (((continuous_mcoef n _ _).comp continuous_aR).norm.pow 2)).measurable
  rw [lintegral_congr (fun ξ => hstep ξ), lintegral_tsum (fun l => (hmeas l).aemeasurable)]
  refine tsum_congr (fun l => ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_norm_sq_mcoef hn j l]

end Lightlike.Lorentz.SL2RPlancherel
