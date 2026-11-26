module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileDecay

/-!
# Orthogonality of the radial profiles of distinct discrete series

For two holomorphic discrete series `D_n⁺`, `D_{n'}⁺` and `K`-weight vectors with the same `K × K`-weights, the
radial profiles `ψ^n_{jl}`, `ψ^{n'}_{j'l'}` satisfy `∫_0^∞ ψ conj χ sinh ξ dξ = 0` if `n ≠ n'`. The proof is by
induction on the ladder: integrating `(ψ^n_{jl} conj ψ^{n'}_{j'l'} sinh)'` over `(0, ∞)` and using the raising and
lowering equations of `DiscreteProfileODE`, `(n + l) ⟨ψ_{l+1}, χ_{l'+1}⟩ = (l' + 1) ⟨ψ_l, χ_{l'}⟩` and
`⟨ψ_{l+1}, χ_0⟩ = 0` (`profPair_step`, `profPair_step_zero`).
-/

@[expose] public section

open MeasureTheory Set Complex Metric Real Filter Topology Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The constant of the decay bound of the profile. -/
def profConst (n l j : ℕ) (κ : ℂ) : ℝ := ‖κ‖ * (2 ^ n * (2 ^ j * ((3 / 2) ^ l * 2 ^ (n + l))))

lemma integral_Ioi_deriv_eq_zero {F F' : ℝ → ℂ} (hF0 : ContinuousWithinAt F (Ici 0) 0) (hF00 : F 0 = 0)
    (hd : ∀ ξ ∈ Ioi (0 : ℝ), HasDerivAt F (F' ξ) ξ) (hint : IntegrableOn F' (Ioi 0))
    (hlim : Tendsto F atTop (𝓝 0)) : ∫ ξ in Ioi (0 : ℝ), F' ξ = 0 := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto hF0 hd hint hlim
  rw [this, hF00]; simp

lemma abs_sinh_le_exp {ξ : ℝ} (hξ : 0 ≤ ξ) : |Real.sinh ξ| ≤ Real.exp ξ := by
  rw [abs_of_nonneg (Real.sinh_nonneg_iff.2 hξ), Real.sinh_eq]
  have := Real.exp_pos (-ξ)
  have := Real.exp_pos ξ
  linarith

lemma integrableOn_of_decay {f : ℝ → ℂ} (hf : Continuous f) (C : ℝ)
    (h : ∀ ξ : ℝ, 0 ≤ ξ → ‖f ξ‖ ≤ C * Real.exp (-ξ)) : IntegrableOn f (Ioi 0) := by
  have hg : IntegrableOn (fun ξ : ℝ => C * Real.exp (-1 * ξ)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul C
  refine Integrable.mono' hg hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
  have := h ξ (le_of_lt hξ)
  simpa [neg_one_mul] using this

lemma tendsto_of_decay {f : ℝ → ℂ} (C : ℝ) (h : ∀ ξ : ℝ, 0 ≤ ξ → ‖f ξ‖ ≤ C * Real.exp (-ξ)) :
    Tendsto f atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ ?_ (f := f) (a := fun ξ => C * Real.exp (-ξ))
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with ξ hξ using h ξ hξ
  · simpa using (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul C

/-- **The decay of a product** of two profiles with `n + n' ≥ 4`. -/
lemma decay_prod {ψ χ : ℝ → ℂ} {a b : ℕ} (hab : 4 ≤ a + b) {Cψ Cχ : ℝ}
    (hψ : ∀ ξ : ℝ, 0 ≤ ξ → ‖ψ ξ‖ ≤ Cψ * Real.exp (-((a : ℝ) * ξ / 2)))
    (hχ : ∀ ξ : ℝ, 0 ≤ ξ → ‖χ ξ‖ ≤ Cχ * Real.exp (-((b : ℝ) * ξ / 2))) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    ‖ψ ξ * (starRingEnd ℂ) (χ ξ) * (Real.sinh ξ : ℂ)‖ ≤ Cψ * Cχ * Real.exp (-ξ) := by
  have h1 := hψ ξ hξ
  have h2 := hχ ξ hξ
  have h3 := abs_sinh_le_exp hξ
  have hCψ : 0 ≤ Cψ := by
    have := (norm_nonneg (ψ ξ)).trans h1
    have hp := Real.exp_pos (-((a : ℝ) * ξ / 2))
    by_contra hneg
    push Not at hneg
    nlinarith
  have hCχ : 0 ≤ Cχ := by
    have := (norm_nonneg (χ ξ)).trans h2
    have hp := Real.exp_pos (-((b : ℝ) * ξ / 2))
    by_contra hneg
    push Not at hneg
    nlinarith
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  calc ‖ψ ξ‖ * ‖χ ξ‖ * |Real.sinh ξ|
      ≤ (Cψ * Real.exp (-((a : ℝ) * ξ / 2))) * (Cχ * Real.exp (-((b : ℝ) * ξ / 2))) * Real.exp ξ := by
        gcongr
    _ = Cψ * Cχ * Real.exp (-((a : ℝ) * ξ / 2) + -((b : ℝ) * ξ / 2) + ξ) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ Cψ * Cχ * Real.exp (-ξ) := by
        gcongr
        have : (4 : ℝ) ≤ (a : ℝ) + b := by exact_mod_cast hab
        nlinarith

lemma ladB_sub_mul_sinh (n j l : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    (ladB n j l ξ - ladB n j (l + 1) ξ) * Real.sinh ξ = -Real.cosh ξ := by
  have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
  unfold ladB
  push_cast
  field_simp
  ring

/-- **The integration by parts** for the pairing of a profile `ψ_{jl}` (with the lowering equation) and a function
`χ` satisfying `χ' + b_{j,l+1} χ = c χ₁`: `(n + l) ∫ ψ_{l+1} conj χ sinh = c ∫ ψ_l conj χ₁ sinh`. -/
theorem pair_core (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {b : ℕ} (hb : 1 ≤ b) (hnb : 4 ≤ n + b)
    {χ χ₁ : ℝ → ℂ} (c : ℝ) {Cχ Cχ₁ : ℝ} (hχc : Continuous χ) (hχ₁c : Continuous χ₁)
    (hχd : ∀ ξ : ℝ, 0 < ξ → DifferentiableAt ℝ χ ξ)
    (hχrel : ∀ ξ : ℝ, 0 < ξ → deriv χ ξ + (ladB n j (l + 1) ξ : ℂ) * χ ξ = (c : ℂ) * χ₁ ξ)
    (hχb : ∀ ξ : ℝ, 0 ≤ ξ → ‖χ ξ‖ ≤ Cχ * Real.exp (-((b : ℝ) * ξ / 2)))
    (hχ₁b : ∀ ξ : ℝ, 0 ≤ ξ → ‖χ₁ ξ‖ ≤ Cχ₁ * Real.exp (-((b : ℝ) * ξ / 2))) :
    ((n + l : ℕ) : ℂ) * (∫ ξ in Ioi (0 : ℝ), profileFun n (l + 1) j κ ξ * (starRingEnd ℂ) (χ ξ) * (Real.sinh ξ : ℂ)) =
      (c : ℂ) * (∫ ξ in Ioi (0 : ℝ), profileFun n l j κ ξ * (starRingEnd ℂ) (χ₁ ξ) * (Real.sinh ξ : ℂ)) := by
  set ψ := profileFun n l j κ with hψ
  set ψ₁ := profileFun n (l + 1) j κ with hψ₁
  set F : ℝ → ℂ := fun ξ => ψ ξ * (starRingEnd ℂ) (χ ξ) * (Real.sinh ξ : ℂ) with hF
  set A : ℝ → ℂ := fun ξ => ψ₁ ξ * (starRingEnd ℂ) (χ ξ) * (Real.sinh ξ : ℂ) with hA
  set B : ℝ → ℂ := fun ξ => ψ ξ * (starRingEnd ℂ) (χ₁ ξ) * (Real.sinh ξ : ℂ) with hB
  have hψb : ∀ ξ : ℝ, 0 ≤ ξ → ‖ψ ξ‖ ≤ profConst n l j κ * Real.exp (-((n : ℝ) * ξ / 2)) :=
    fun ξ hξ => norm_profileFun_le n l j κ hξ
  have hψ₁b : ∀ ξ : ℝ, 0 ≤ ξ → ‖ψ₁ ξ‖ ≤ profConst n (l + 1) j κ * Real.exp (-((n : ℝ) * ξ / 2)) :=
    fun ξ hξ => norm_profileFun_le n (l + 1) j κ hξ
  have hψc : Continuous ψ := continuous_profileFun n l j hn κ
  have hψ₁c : Continuous ψ₁ := continuous_profileFun n (l + 1) j hn κ
  have hFc : Continuous F := (hψc.mul (Complex.continuous_conj.comp hχc)).mul
    (Complex.continuous_ofReal.comp Real.continuous_sinh)
  have hAc : Continuous A := (hψ₁c.mul (Complex.continuous_conj.comp hχc)).mul
    (Complex.continuous_ofReal.comp Real.continuous_sinh)
  have hBc : Continuous B := (hψc.mul (Complex.continuous_conj.comp hχ₁c)).mul
    (Complex.continuous_ofReal.comp Real.continuous_sinh)
  have hFd := fun ξ (hξ : 0 ≤ ξ) => decay_prod (a := n) (b := b) hnb hψb hχb hξ
  have hAd := fun ξ (hξ : 0 ≤ ξ) => decay_prod (a := n) (b := b) hnb hψ₁b hχb hξ
  have hBd := fun ξ (hξ : 0 ≤ ξ) => decay_prod (a := n) (b := b) hnb hψb hχ₁b hξ
  set F' : ℝ → ℂ := fun ξ => -((n + l : ℕ) : ℂ) * A ξ + (c : ℂ) * B ξ with hF'
  have hderiv : ∀ ξ ∈ Ioi (0 : ℝ), HasDerivAt F (F' ξ) ξ := by
    intro ξ hξ
    have hξ' : 0 < ξ := hξ
    have hψd : HasDerivAt ψ (deriv ψ ξ) ξ :=
      ((hasDerivAt_profileFun n l j hn κ ξ).differentiableAt).hasDerivAt
    have hχd' : HasDerivAt χ (deriv χ ξ) ξ := (hχd ξ hξ').hasDerivAt
    have hs : HasDerivAt (fun ξ : ℝ => ((Real.sinh ξ : ℝ) : ℂ)) (Real.cosh ξ : ℝ) ξ :=
      (Real.hasDerivAt_sinh ξ).ofReal_comp
    have hstar : HasDerivAt (fun ξ => (starRingEnd ℂ) (χ ξ)) ((starRingEnd ℂ) (deriv χ ξ)) ξ := by
      simpa [Complex.star_def] using hχd'.star
    have h := (hψd.mul hstar).mul hs
    refine h.congr_deriv ?_
    have hdown := profileFun_down n l j hn κ hξ'
    have hdown' : deriv ψ ξ = (ladB n j l ξ : ℂ) * ψ ξ - ((n + l : ℕ) : ℂ) * ψ₁ ξ := by
      have : deriv ψ ξ - (ladB n j l ξ : ℂ) * ψ ξ = -((n + l : ℕ) : ℂ) * ψ₁ ξ := hdown
      linear_combination this
    have hrel : deriv χ ξ = (c : ℂ) * χ₁ ξ - (ladB n j (l + 1) ξ : ℂ) * χ ξ := by
      linear_combination hχrel ξ hξ'
    have hsub := ladB_sub_mul_sinh n j l hξ'
    have hsubC : ((ladB n j l ξ : ℂ) - (ladB n j (l + 1) ξ : ℂ)) * (Real.sinh ξ : ℂ) = -(Real.cosh ξ : ℂ) := by
      exact_mod_cast hsub
    rw [hdown', hrel]
    simp only [hF', hA, hB, map_sub, map_mul, Complex.conj_ofReal, Pi.mul_apply]
    linear_combination (ψ ξ * (starRingEnd ℂ) (χ ξ)) * hsubC
  have hint : IntegrableOn F' (Ioi 0) := by
    have hA' := integrableOn_of_decay hAc _ hAd
    have hB' := integrableOn_of_decay hBc _ hBd
    exact (hA'.const_mul (-((n + l : ℕ) : ℂ))).add (hB'.const_mul (c : ℂ))
  have hlim := tendsto_of_decay _ hFd
  have h0 : F 0 = 0 := by simp [hF]
  have hzero := integral_Ioi_deriv_eq_zero hFc.continuousWithinAt h0 hderiv hint hlim
  have hAi := integrableOn_of_decay hAc _ hAd
  have hBi := integrableOn_of_decay hBc _ hBd
  have : ∫ ξ in Ioi (0 : ℝ), F' ξ =
      -((n + l : ℕ) : ℂ) * (∫ ξ in Ioi (0 : ℝ), A ξ) + (c : ℂ) * (∫ ξ in Ioi (0 : ℝ), B ξ) := by
    simp only [hF']
    rw [integral_add (hAi.const_mul _) (hBi.const_mul _), integral_const_mul, integral_const_mul]
  rw [this] at hzero
  try simp only [hA, hB] at hzero ⊢
  linear_combination (-1 : ℂ) * hzero

end Lightlike.Lorentz.SL2RPlancherel
