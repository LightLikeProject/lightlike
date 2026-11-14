module

public import Lightlike.Lorentz.LimitFormula
public import Lightlike.Lorentz.PlancherelTrace

/-!
# The Plancherel density as a Fourier transform of the orbital integral

Let `F` be smooth with compact support on `M₂(ℂ)` and invariant under conjugation by `SU(2)`, and
let `Φ_F(μ) = ∫_ℂ F([[μ, x], [0, μ⁻¹]]) d²x` be its orbital integral (`orbInt`). This file proves

    Σ_{n ∈ ℤ} ∫_ℝ (n² + 4ρ²) T_F(n, ρ) dρ = 16 π³ F(1),
    T_F(n, ρ) = ∫_{ℂ^×} m_{n,ρ}(λ) Φ_F(λ⁻¹) d²λ,

with `m_{n,ρ}(λ) = |λ|^{2iρ-2} (λ/|λ|)^n` the multiplier of the principal series (`mult`), each
`ρ`-integral absolutely convergent (`hasSum_density_orbInt`). By `integral_psKernel_diag`,
`π T_F(n, ρ)` is the integrated diagonal `∫ K^{n,ρ}_F(z, z) d²z` of the kernel of `π_{n,ρ}(F)`, so
this is the analytic core of the Plancherel formula of `SL(2, ℂ)`.

## Proof

* **Exponential coordinates.** In `λ = e^{s + iφ}` the measure `d²λ` is `e^{2s} ds dφ`
  (`integral_polar_exp`, from polar coordinates and `r = e^s`). With `Ψ_F(t, θ) = Φ_F(e^{t+iθ})`
  (`orbExp`) and its angular Fourier coefficients `c_n(t)` (`orbCoeff`) this gives
  `T_F(n, ρ) = 2π 𝓕c_n(ρ/π)` (`integral_mult_orbInt`), with Mathlib's
  `𝓕c(w) = ∫ e^{-2πitw} c(t) dt`.
* **Fourier inversion.** `c_n` is smooth with compact support, hence a Schwartz function. Inversion
  at `t = 0` for `c_n` and `c_n''` gives `∫ (n² + 4ρ²) 𝓕c_n(ρ/π) dρ = π (n² c_n(0) - c_n''(0))`
  (`integral_density_fourier`).
* **Fourier series.** The angular Fourier series of `θ ↦ ∂_θ²Ψ_F(0, θ)` and `θ ↦ ∂_t²Ψ_F(0, θ)` at
  `θ = 0` give `Σ n² c_n(0) = -∂_θ²Ψ_F(0, 0)` and `Σ c_n''(0) = ∂_t²Ψ_F(0, 0)`
  (`hasSum_fourierCoeffOn`; the coefficients are `O(n⁻²)` by two integrations by parts).
* **Limit formula.** `(∂_t² + ∂_θ²)Ψ_F(0, 0) = -8π F(1)` (`limit_formula`).

## References

* I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR 11 (1947).
* M. A. Naimark, *Linear representations of the Lorentz group*, Pergamon (1964), ch. III.
* Harish-Chandra, *The Plancherel formula for complex semisimple Lie groups*, Trans. AMS 76 (1954).
-/

@[expose] public section

open MeasureTheory Complex Metric Set Filter Topology
open scoped Matrix ComplexConjugate ContDiff FourierTransform

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-! ## Exponential coordinates on the orbital integral -/

/-- Smoothness of a `2 × 2` array-valued map, entry by entry. -/
lemma contDiff_mat2 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : WithTop ℕ∞}
    {a b c d : X → ℂ} (ha : ContDiff ℝ k a) (hb : ContDiff ℝ k b) (hc : ContDiff ℝ k c)
    (hd : ContDiff ℝ k d) : ContDiff ℝ k fun x => mat2 (a x) (b x) (c x) (d x) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa [mat2]

/-- The orbital integral at `e^s`: `Φ_F(e^s) = ∫ F([[e^s, x], [0, e^{-s}]]) d²x`. -/
lemma orbInt_cexp (F : P2 → ℂ) (s : ℂ) :
    orbInt F (cexp s) = ∫ x : ℂ, F (mat2 (cexp s) x 0 (cexp (-s))) := by
  simp only [orbInt, triMat, Complex.exp_neg]

/-- **Smoothness of the orbital integral in exponential coordinates.** For `F` smooth with
compact support, `s ↦ Φ_F(e^s)` is smooth on `ℂ`. -/
theorem contDiff_orbInt_cexp {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ContDiff ℝ ∞ fun s : ℂ => orbInt F (cexp s) := by
  obtain ⟨C, -, hCF⟩ := exists_bound_support hs
  simp_rw [orbInt_cexp]
  have hΦ : ContDiff ℝ ∞ (Function.uncurry fun (x : ℂ) (s : ℂ) =>
      F (mat2 (cexp s) x 0 (cexp (-s)))) :=
    hF.comp (contDiff_mat2 contDiff_snd.cexp contDiff_fst contDiff_const contDiff_snd.neg.cexp)
  refine contDiff_parametric_integral_infty hΦ (p := fun x : ℂ => x) aestronglyMeasurable_id
    measurableSet_closedBall measure_closedBall_lt_top.ne (R := C)
    (Eventually.of_forall fun x hx => mem_closedBall_zero_iff.1 hx)
    (Eventually.of_forall fun x hx s => hCF _ ?_)
  rw [mem_closedBall_zero_iff, not_le] at hx
  exact hx.le.trans (by simpa [mat2] using norm_apply_le (mat2 (cexp s) x 0 (cexp (-s))) 0 1)

/-- **The orbital integral in exponential coordinates**, `Ψ_F(t, θ) = Φ_F(e^{t + iθ})`. -/
noncomputable def orbExp (F : P2 → ℂ) (t θ : ℝ) : ℂ := orbInt F (cexp (t + θ * I))

/-- `Ψ_F` is jointly smooth in `(t, θ)`. -/
theorem contDiff_orbExp {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ContDiff ℝ ∞ (Function.uncurry (orbExp F)) := by
  have hl : ContDiff ℝ ∞ fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I :=
    (ofRealCLM.contDiff.comp contDiff_fst).add
      ((ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  exact (contDiff_orbInt_cexp hF hs).comp hl

/-- `Ψ_F(t, ·)` has period `2π`. -/
lemma orbExp_periodic (F : P2 → ℂ) (t : ℝ) : Function.Periodic (orbExp F t) (2 * Real.pi) := by
  intro θ
  simp only [orbExp]
  rw [show (t : ℂ) + ((θ + 2 * Real.pi : ℝ) : ℂ) * I = (t + θ * I) + 2 * Real.pi * I by
    push_cast; ring, Complex.exp_periodic]

/-- `Φ_F(μ) = 0` once `|μ| ≥ C` or `|μ⁻¹| ≥ C`, for `C` beyond the support of `F`. -/
lemma orbInt_eq_zero {F : P2 → ℂ} {C : ℝ} (hCF : ∀ X : P2, C ≤ ‖X‖ → F X = 0) {μ : ℂ}
    (h : C ≤ ‖μ‖ ∨ C ≤ ‖μ⁻¹‖) : orbInt F μ = 0 := by
  have h0 : ∀ x, F (triMat μ x) = 0 := fun x => hCF _ (by
    rcases h with h | h
    · exact h.trans (by simpa [triMat, mat2] using norm_apply_le (triMat μ x) 0 0)
    · exact h.trans (by simpa [triMat, mat2] using norm_apply_le (triMat μ x) 1 1))
  simp [orbInt, h0]

/-- `Ψ_F(t, θ) = 0` once `|t| ≥ log C`. -/
lemma orbExp_eq_zero {F : P2 → ℂ} {C : ℝ} (hC : 0 < C) (hCF : ∀ X : P2, C ≤ ‖X‖ → F X = 0)
    {t : ℝ} (ht : Real.log C ≤ |t|) (θ : ℝ) : orbExp F t θ = 0 := by
  refine orbInt_eq_zero hCF ?_
  rw [norm_inv, Complex.norm_exp]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_self,
    add_zero]
  rcases le_abs'.1 ht with h | h
  · right
    rw [← Real.exp_neg]
    exact (Real.log_le_iff_le_exp hC).1 (by linarith)
  · left
    exact (Real.log_le_iff_le_exp hC).1 h

/-- A bound for the orbital integral: `|Φ_F(μ)| ≤ B · vol(B(0, C))` when `|F| ≤ B` and `F`
vanishes beyond `C`. -/
lemma norm_orbInt_le {F : P2 → ℂ} {B C : ℝ} (hB : ∀ X, ‖F X‖ ≤ B)
    (hCF : ∀ X : P2, C ≤ ‖X‖ → F X = 0) (μ : ℂ) :
    ‖orbInt F μ‖ ≤ ∫ x : ℂ, (closedBall 0 C).indicator (fun _ => B) x := by
  refine norm_integral_le_of_norm_le
    ((integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
      measurableSet_closedBall)
    (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall (0 : ℂ) C
  · rw [indicator_of_mem hx]
    exact hB _
  · rw [indicator_of_notMem hx]
    rw [mem_closedBall_zero_iff, not_le] at hx
    rw [hCF _ (hx.le.trans (by simpa [triMat, mat2] using norm_apply_le (triMat μ x) 0 1)),
      norm_zero]

/-- The orbital integral of a continuous `F` is strongly measurable. -/
lemma stronglyMeasurable_orbInt {F : P2 → ℂ} (hF : Continuous F) :
    StronglyMeasurable (orbInt F) := by
  have hm : Measurable fun q : ℂ × ℂ => F (triMat q.1 q.2) :=
    hF.measurable.comp (measurable_mat2 measurable_fst measurable_snd measurable_const
      measurable_fst.inv)
  exact hm.stronglyMeasurable.integral_prod_right'

/-! ## Angular Fourier coefficients -/

/-- `-π < π`. -/
lemma neg_pi_lt_pi : -Real.pi < Real.pi := by linarith [Real.pi_pos]

/-- The Fourier coefficient on `(-π, π]` as an integral,
`ĝ(n) = (2π)⁻¹ ∫_{(-π, π]} e^{-inθ} g(θ) dθ`. -/
lemma fourierCoeffOn_pi (g : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn neg_pi_lt_pi g n =
      (2 * Real.pi : ℂ)⁻¹ * ∫ θ in Ioc (-Real.pi) Real.pi, cexp (-(n * θ * I)) * g θ := by
  rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le neg_pi_lt_pi.le,
    Complex.real_smul]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  congr 1
  · push_cast
    field_simp
    ring
  · refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    field_simp
    ring

/-- **The angular Fourier coefficients** `c_n(t) = (2π)⁻¹ ∫_{-π}^{π} e^{-inθ} Ψ_F(t, θ) dθ`. -/
noncomputable def orbCoeff (F : P2 → ℂ) (n : ℤ) (t : ℝ) : ℂ :=
  fourierCoeffOn neg_pi_lt_pi (orbExp F t) n

/-- `c_n` as a parametric integral over `(-π, π]`. -/
lemma orbCoeff_eq (F : P2 → ℂ) (n : ℤ) :
    orbCoeff F n = fun t => ∫ θ in Ioc (-Real.pi) Real.pi,
      (2 * Real.pi : ℂ)⁻¹ * cexp (-(n * θ * I)) * orbExp F t θ := by
  funext t
  rw [orbCoeff, fourierCoeffOn_pi, ← integral_const_mul]
  simp_rw [mul_assoc]

/-- Smoothness of the integrand of `c_n`. -/
lemma contDiff_orbCoeff_integrand {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F)
    (n : ℤ) : ContDiff ℝ ∞ (Function.uncurry fun (θ t : ℝ) =>
      (2 * Real.pi : ℂ)⁻¹ * cexp (-(n * θ * I)) * orbExp F t θ) := by
  have he : ContDiff ℝ ∞ fun p : ℝ × ℝ => cexp (-(n * (p.1 : ℂ) * I)) :=
    ((contDiff_const.mul (ofRealCLM.contDiff.comp contDiff_fst)).mul contDiff_const).neg.cexp
  exact (contDiff_const.mul he).mul
    ((contDiff_orbExp hF hs).comp (contDiff_snd.prodMk contDiff_fst))

/-- The parametric-integral hypotheses for `c_n`. -/
lemma orbCoeff_param :
    (volume.restrict (Ioc (-Real.pi) Real.pi)) (Ioc (-Real.pi) Real.pi) ≠ ⊤ ∧
    (∀ᵐ θ ∂volume.restrict (Ioc (-Real.pi) Real.pi), θ ∈ Ioc (-Real.pi) Real.pi →
      ‖θ‖ ≤ Real.pi) := by
  refine ⟨by rw [Measure.restrict_apply_self]; exact measure_Ioc_lt_top.ne,
    Eventually.of_forall fun θ hθ => ?_⟩
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hθ.1.le, hθ.2⟩

/-- The `c_n` integrand vanishes off `(-π, π]` almost everywhere for the restricted measure. -/
lemma orbCoeff_param_zero (Φ : ℝ → ℝ → ℂ) :
    ∀ᵐ θ ∂volume.restrict (Ioc (-Real.pi) Real.pi), θ ∉ Ioc (-Real.pi) Real.pi →
      ∀ t, Φ θ t = 0 :=
  (ae_restrict_mem measurableSet_Ioc).mono fun _ h h' => absurd h h'

/-- `c_n` is smooth. -/
theorem contDiff_orbCoeff {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) (n : ℤ) :
    ContDiff ℝ ∞ (orbCoeff F n) := by
  rw [orbCoeff_eq]
  exact contDiff_parametric_integral_infty (contDiff_orbCoeff_integrand hF hs n)
    (p := fun θ : ℝ => θ) aestronglyMeasurable_id measurableSet_Ioc orbCoeff_param.1
    orbCoeff_param.2 (orbCoeff_param_zero _)

/-- `c_n` has compact support: it vanishes for `|t| ≥ log C`. -/
theorem hasCompactSupport_orbCoeff {F : P2 → ℂ} (hs : HasCompactSupport F) (n : ℤ) :
    HasCompactSupport (orbCoeff F n) := by
  obtain ⟨C, hC, hCF⟩ := exists_bound_support hs
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (Real.log C)) fun t ht => ?_
  rw [mem_closedBall_zero_iff, Real.norm_eq_abs, not_le] at ht
  have h0 : orbExp F t = fun _ => 0 := funext fun θ => orbExp_eq_zero hC hCF ht.le θ
  simp [orbCoeff, fourierCoeffOn_pi, h0]

/-- **The second derivative of `c_n`** is the Fourier coefficient of `∂_t²Ψ_F(t, ·)`. -/
theorem deriv_deriv_orbCoeff {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F)
    (n : ℤ) (t : ℝ) :
    deriv (deriv (orbCoeff F n)) t =
      fourierCoeffOn neg_pi_lt_pi (fun θ => deriv (deriv fun t => orbExp F t θ) t) n := by
  rw [orbCoeff_eq, deriv_deriv_parametric_integral
    ((contDiff_orbCoeff_integrand hF hs n).of_le (by simp))
    (p := fun θ : ℝ => θ) aestronglyMeasurable_id measurableSet_Ioc orbCoeff_param.1
    orbCoeff_param.2 (orbCoeff_param_zero _), fourierCoeffOn_pi, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  simp only [deriv_const_mul_field']
  ring

/-! ## Fourier inversion at the origin -/

/-- A smooth compactly supported function on `ℝ` has an integrable Fourier transform (it is a
Schwartz function). -/
lemma integrable_fourier_of_hasCompactSupport {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) : Integrable (𝓕 c) := by
  have h := (𝓕 (hcs.toSchwartzMap hc)).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe] at h
  exact h

/-- **Fourier inversion at the origin**: `∫ 𝓕c = c(0)`. -/
lemma integral_fourier_eq {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c) :
    ∫ w, 𝓕 c w = c 0 := by
  have h := congr_fun (hc.continuous.fourierInv_fourier_eq
    (hc.continuous.integrable_of_hasCompactSupport hcs)
    (integrable_fourier_of_hasCompactSupport hc hcs)) 0
  rw [Real.fourierInv_eq] at h
  simpa using h

/-- Iterated derivatives of a compactly supported function have compact support. -/
lemma hasCompactSupport_iterate_deriv {c : ℝ → ℂ} (hcs : HasCompactSupport c) (k : ℕ) :
    HasCompactSupport (deriv^[k] c) := by
  induction k with
  | zero => exact hcs
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.deriv

/-- The Fourier transform of `c''` is `-4π²w² 𝓕c(w)`. -/
lemma fourier_deriv_deriv {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c) :
    𝓕 (deriv (deriv c)) = fun w : ℝ => -(4 * (Real.pi : ℂ) ^ 2 * (w : ℂ) ^ 2) * 𝓕 c w := by
  have h := Real.fourier_iteratedDeriv (N := 2) (n := 2)
    (hc.of_le (by simp)) (fun k _ => by
      rw [iteratedDeriv_eq_iterate]
      exact (hc.iterate_deriv k).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_iterate_deriv hcs k)) le_rfl
  rw [iteratedDeriv_eq_iterate] at h
  funext w
  rw [show deriv (deriv c) = deriv^[2] c from rfl, h]
  simp only [smul_eq_mul]
  congr 1
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * (w : ℂ) ^ 2) * I_sq

/-- **The Plancherel density against a Fourier transform.** For `c` smooth with compact support,
`ρ ↦ (n² + 4ρ²) 𝓕c(ρ/π)` is integrable with integral `π (n² c(0) - c''(0))`. -/
theorem integral_density_fourier {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hcs : HasCompactSupport c)
    (n : ℤ) :
    Integrable (fun ρ : ℝ => ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * 𝓕 c (ρ / Real.pi)) ∧
    ∫ ρ : ℝ, ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * 𝓕 c (ρ / Real.pi) =
      Real.pi * ((n : ℂ) ^ 2 * c 0 - deriv (deriv c) 0) := by
  have hc2 : ContDiff ℝ ∞ (deriv (deriv c)) := hc.iterate_deriv 2
  have hcs2 : HasCompactSupport (deriv (deriv c)) := hcs.deriv.deriv
  have hi1 := integrable_fourier_of_hasCompactSupport hc hcs
  have hi2 := integrable_fourier_of_hasCompactSupport hc2 hcs2
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℂ, g = fun w => (n : ℂ) ^ 2 * 𝓕 c w - 𝓕 (deriv (deriv c)) w :=
    ⟨_, rfl⟩
  have hgi : Integrable g := hg ▸ (hi1.const_mul _).sub hi2
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have heq : (fun ρ : ℝ => ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * 𝓕 c (ρ / Real.pi)) =
      fun ρ => g (ρ / Real.pi) := by
    funext ρ
    rw [hg, fourier_deriv_deriv hc hcs]
    push_cast
    field_simp
    ring
  rw [heq]
  refine ⟨hgi.comp_div Real.pi_ne_zero, ?_⟩
  rw [Measure.integral_comp_div g, abs_of_pos Real.pi_pos, hg, integral_sub (hi1.const_mul _) hi2,
    integral_const_mul, integral_fourier_eq hc hcs, integral_fourier_eq hc2 hcs2,
    Complex.real_smul]

/-! ## Fourier series of smooth periodic functions -/

/-- A periodic function has a periodic derivative. -/
lemma periodic_deriv {g : ℝ → ℂ} {T : ℝ} (hg : Function.Periodic g T) :
    Function.Periodic (deriv g) T := by
  intro x
  rw [← deriv_comp_add_const, show (fun y => g (y + T)) = g from funext hg]

/-- Moving the right endpoint of `fourierCoeffOn` along an equality. -/
lemma fourierCoeffOn_endpoint {a b b' : ℝ} (hab : a < b) (hab' : a < b') (hb : b = b')
    (g : ℝ → ℂ) : fourierCoeffOn hab g = fourierCoeffOn hab' g := by
  subst hb
  rfl

/-- **Fourier coefficients of a derivative**: `ĝ'(n) = i n ĝ(n)` for a smooth function of period
`2π`. -/
theorem fourierCoeffOn_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2 * Real.pi)) (n : ℤ) :
    fourierCoeffOn neg_pi_lt_pi (deriv g) n = n * I * fourierCoeffOn neg_pi_lt_pi g n := by
  have hd : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    ((hg.differentiable (by simp)) x).hasDerivAt
  have hdi : IntervalIntegrable (deriv g) volume (-Real.pi) Real.pi :=
    (hg.continuous_deriv (by simp)).intervalIntegrable _ _
  have hend : g Real.pi = g (-Real.pi) := by
    have h := hp (-Real.pi)
    rwa [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rcases eq_or_ne n 0 with rfl | hn
  · rw [fourierCoeffOn_eq_integral, neg_zero]
    simp only [fourier_zero, one_smul, Int.cast_zero, zero_mul]
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => (hd x).differentiableAt) hdi, hend,
      sub_self, smul_zero]
  · have h := fourierCoeffOn_of_hasDerivAt neg_pi_lt_pi hn (fun x _ => hd x) hdi
    rw [hend, sub_self, mul_zero, zero_sub] at h
    have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
    rw [h]
    push_cast
    field_simp
    ring

/-- `ĝ''(n) = -n² ĝ(n)` for a smooth function of period `2π`. -/
theorem fourierCoeffOn_deriv_deriv {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2 * Real.pi)) (n : ℤ) :
    fourierCoeffOn neg_pi_lt_pi (deriv (deriv g)) n =
      -((n : ℂ) ^ 2) * fourierCoeffOn neg_pi_lt_pi g n := by
  rw [fourierCoeffOn_deriv (g := deriv g) (hg.iterate_deriv 1) (periodic_deriv hp),
    fourierCoeffOn_deriv hg hp]
  linear_combination ((n : ℂ) ^ 2 * fourierCoeffOn neg_pi_lt_pi g n) * I_sq

/-- The Fourier coefficients are bounded by the sup norm on `[-π, π]`. -/
lemma norm_fourierCoeffOn_le {g : ℝ → ℂ} {M : ℝ}
    (hM : ∀ θ ∈ Icc (-Real.pi) Real.pi, ‖g θ‖ ≤ M) (n : ℤ) :
    ‖fourierCoeffOn neg_pi_lt_pi g n‖ ≤ M := by
  rw [fourierCoeffOn_pi, norm_mul]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (-Real.pi) Real.pi)
    (f := fun θ : ℝ => cexp (-(n * θ * I)) * g θ) measure_Ioc_lt_top (fun θ hθ => by
      rw [norm_mul, Complex.norm_exp]
      simpa using hM θ ⟨hθ.1.le, hθ.2⟩)
  rw [Real.volume_real_Ioc_of_le neg_pi_lt_pi.le] at h
  have h2 : ‖(2 * Real.pi : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h2]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in Ioc (-Real.pi) Real.pi, cexp (-(n * θ * I)) * g θ‖
      ≤ (2 * Real.pi)⁻¹ * (M * (Real.pi - -Real.pi)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = M := by field_simp; ring

/-- The Fourier coefficients of a smooth function of period `2π` are summable: they are
`O(n⁻²)`. -/
theorem summable_fourierCoeffOn {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2 * Real.pi)) :
    Summable (fourierCoeffOn neg_pi_lt_pi g) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).exists_bound_of_continuousOn
    (hg.iterate_deriv 2).continuous.continuousOn
  refine Summable.of_norm_bounded_eventually (g := fun n : ℤ => M * (1 / (n : ℝ) ^ 2))
    ((Real.summable_one_div_int_pow.2 one_lt_two).mul_left M) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn
  have hn' : (0 : ℝ) < (n : ℝ) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hn0).symm
  have hb := norm_fourierCoeffOn_le (g := deriv (deriv g)) hM n
  rw [fourierCoeffOn_deriv_deriv hg hp, norm_mul, norm_neg, norm_pow, Complex.norm_intCast,
    sq_abs] at hb
  rw [mul_one_div, le_div_iff₀ hn', mul_comm]
  exact hb

/-- **Pointwise Fourier inversion** at `θ = 0` for a smooth function of period `2π`:
`Σ_n ĝ(n) = g(0)`. -/
theorem hasSum_fourierCoeffOn {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hp : Function.Periodic g (2 * Real.pi)) :
    HasSum (fourierCoeffOn neg_pi_lt_pi g) (g 0) := by
  have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hend : g (-Real.pi) = g (-Real.pi + 2 * Real.pi) := (hp _).symm
  let G : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨AddCircle.liftIoc (2 * Real.pi) (-Real.pi) g,
      AddCircle.liftIoc_continuous hend hg.continuous.continuousOn⟩
  have hfun : fourierCoeff G = fourierCoeffOn neg_pi_lt_pi g := by
    funext n
    rw [show fourierCoeff G n = fourierCoeff (AddCircle.liftIoc (2 * Real.pi) (-Real.pi) g) n
      from rfl, fourierCoeff_liftIoc_eq]
    exact congrFun (fourierCoeffOn_endpoint _ neg_pi_lt_pi (by ring) g) n
  have hs : Summable (fourierCoeff G) := by
    rw [hfun]
    exact summable_fourierCoeffOn hg hp
  have h := has_pointwise_sum_fourier_series_of_summable hs ((0 : ℝ) : AddCircle (2 * Real.pi))
  have hG0 : G ((0 : ℝ) : AddCircle (2 * Real.pi)) = g 0 :=
    AddCircle.liftIoc_coe_apply ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [hG0, hfun] at h
  simpa [fourier_coe_apply] using h

/-! ## Summation over `n` -/

/-- `θ ↦ Ψ_F(t, θ)` is smooth. -/
lemma contDiff_orbExp_right {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F)
    (t : ℝ) : ContDiff ℝ ∞ (orbExp F t) :=
  (contDiff_orbExp hF hs).comp (contDiff_const.prodMk contDiff_id)

/-- The `t`-derivative of a jointly smooth function of two real variables is jointly smooth. -/
lemma contDiff_uncurry_deriv_infty {Φ : ℝ → ℝ → ℂ} (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) :
    ContDiff ℝ ∞ (Function.uncurry fun q t => deriv (Φ q) t) := by
  refine contDiff_infty.2 fun k => ?_
  have hd : ContDiff ℝ k (fun y : ℝ × ℝ => fderiv ℝ (Φ y.1) y.2) :=
    ContDiff.fderiv (f := fun (y : ℝ × ℝ) (x : ℝ) => Φ y.1 x) (g := Prod.snd)
      (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
      (by simp)
  exact hd.clm_apply contDiff_const

/-- `θ ↦ ∂_t²Ψ_F(0, θ)` is smooth. -/
lemma contDiff_orbExp_tt {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    ContDiff ℝ ∞ fun θ => deriv (deriv fun t => orbExp F t θ) 0 := by
  have h1 : ContDiff ℝ ∞ (Function.uncurry fun (θ t : ℝ) => orbExp F t θ) :=
    (contDiff_orbExp hF hs).comp (contDiff_snd.prodMk contDiff_fst)
  have h2 : ContDiff ℝ ∞ (Function.uncurry fun (θ t : ℝ) => deriv (fun t => orbExp F t θ) t) :=
    contDiff_uncurry_deriv_infty (Φ := fun θ t => orbExp F t θ) h1
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (θ t : ℝ) =>
      deriv (fun t => deriv (fun t => orbExp F t θ) t) t) :=
    contDiff_uncurry_deriv_infty (Φ := fun θ t => deriv (fun t => orbExp F t θ) t) h2
  have h4 : ContDiff ℝ ∞ fun θ : ℝ => (θ, (0 : ℝ)) := contDiff_id.prodMk contDiff_const
  have h5 := h3.comp h4
  exact h5

/-- `Σ_n n² c_n(0) = -∂_θ²Ψ_F(0, 0)`. -/
theorem hasSum_sq_orbCoeff {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F) :
    HasSum (fun n : ℤ => (n : ℂ) ^ 2 * orbCoeff F n 0) (-deriv (deriv (orbExp F 0)) 0) := by
  have hg := contDiff_orbExp_right hF hs 0
  have hp := orbExp_periodic F 0
  have h : HasSum (fourierCoeffOn neg_pi_lt_pi (deriv (deriv (orbExp F 0))))
      (deriv (deriv (orbExp F 0)) 0) :=
    hasSum_fourierCoeffOn (hg.iterate_deriv 2) (periodic_deriv (periodic_deriv hp))
  convert h.neg using 1
  funext n
  rw [fourierCoeffOn_deriv_deriv hg hp, orbCoeff]
  ring

/-- `Σ_n c_n''(0) = ∂_t²Ψ_F(0, 0)`. -/
theorem hasSum_deriv_deriv_orbCoeff {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F)
    (hs : HasCompactSupport F) :
    HasSum (fun n : ℤ => deriv (deriv (orbCoeff F n)) 0)
      (deriv (deriv fun t => orbExp F t 0) 0) := by
  have hp : Function.Periodic (fun θ => deriv (deriv fun t => orbExp F t θ) 0)
      (2 * Real.pi) := fun θ => by
    have h : ∀ t, orbExp F t (θ + 2 * Real.pi) = orbExp F t θ := fun t => orbExp_periodic F t θ
    simp only [h]
  have h := hasSum_fourierCoeffOn (contDiff_orbExp_tt hF hs) hp
  simp_rw [deriv_deriv_orbCoeff hF hs]
  exact h

/-- The limit formula in exponential coordinates: `(∂_t² + ∂_θ²)Ψ_F(0, 0) = -8π F(1)`. -/
theorem orbExp_laplacian {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F)
    (hK : IsSU2ConjInvariant F) :
    deriv (deriv fun t => orbExp F t 0) 0 + deriv (deriv (orbExp F 0)) 0 =
      -(8 * Real.pi) * F (mat2 1 0 0 1) := by
  have h1 : (fun t : ℝ => orbExp F t 0) = fun t : ℝ => orbInt F (cexp t) := by
    funext t
    simp [orbExp]
  have h2 : orbExp F 0 = fun t : ℝ => orbInt F (cexp (t * I)) := by
    funext t
    simp [orbExp]
  rw [h1, h2]
  exact limit_formula (hF.of_le (by simp)) hs hK

/-! ## The trace in exponential coordinates -/

/-- **Exponential coordinates on `ℂ^×`**: `∫ H(λ) d²λ = ∫∫ e^{2t} H(e^{t + iθ}) dθ dt`, for `H`
whose polar-coordinate integrand is integrable. -/
theorem integral_polar_exp (H : ℂ → ℂ)
    (hH : IntegrableOn (fun p : ℝ × ℝ => p.1 • H (Complex.polarCoord.symm p))
      Complex.polarCoord.target) :
    ∫ l, H l = ∫ t : ℝ, ∫ θ in Ioo (-Real.pi) Real.pi,
      (Real.exp (2 * t) : ℂ) * H (cexp (t + θ * I)) := by
  have hH' : IntegrableOn (fun p : ℝ × ℝ => p.1 • H (Complex.polarCoord.symm p))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) ((volume : Measure ℝ).prod volume) := hH
  rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target,
    show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    setIntegral_prod _ hH', ← integral_comp_exp]
  congr 1
  funext t
  rw [← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  simp only [Complex.polarCoord_symm_apply, smul_smul]
  rw [Complex.real_smul, ← Real.exp_add, ← two_mul, Complex.exp_add, Complex.exp_mul_I,
    ← ofReal_cos, ← ofReal_sin]
  simp only [ofReal_exp]

/-- The multiplier vanishes at `0` (a junk value; `ℂ^×` has full measure). -/
lemma mult_at_zero (n : ℤ) (ρ : ℝ) : mult n ρ 0 = 0 := by
  have h : (2 * I * (ρ : ℂ) - 2) ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
  rw [mult, norm_zero, ofReal_zero, Complex.zero_cpow h, zero_mul]

/-- The multiplier in exponential coordinates: `m_{n,ρ}(e^{t+iθ}) = e^{(2iρ-2)t} e^{inθ}`. -/
lemma mult_cexp (n : ℤ) (ρ t θ : ℝ) :
    mult n ρ (cexp (t + θ * I)) = cexp (t * (2 * I * ρ - 2)) * cexp (n * (θ * I)) := by
  have hnorm : ‖cexp (t + θ * I)‖ = Real.exp t := by
    rw [Complex.norm_exp]
    simp
  have hph : cexp (t + θ * I) / ((Real.exp t : ℝ) : ℂ) = cexp (θ * I) := by
    rw [ofReal_exp, Complex.exp_add, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  rw [mult, hnorm, hph, Complex.cpow_def_of_ne_zero (ofReal_ne_zero.2 (Real.exp_pos t).ne'),
    ← ofReal_log (Real.exp_pos t).le, Real.log_exp, Complex.exp_int_mul]

/-- `(e^{t + iθ})⁻¹ = e^{-t - iθ}`. -/
lemma cexp_inv (t θ : ℝ) : (cexp (t + θ * I))⁻¹ = cexp ((-t : ℝ) + (-θ : ℝ) * I) := by
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- The reflection `θ ↦ -θ` preserves integrals over `(-π, π)`. -/
lemma setIntegral_Ioo_comp_neg (f : ℝ → ℂ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, f (-θ) = ∫ θ in Ioo (-Real.pi) Real.pi, f θ := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le neg_pi_lt_pi.le,
    ← intervalIntegral.integral_of_le neg_pi_lt_pi.le, intervalIntegral.integral_comp_neg, neg_neg]

/-- The angular integral in the trace is a Fourier coefficient:
`∫_{-π}^{π} e^{inθ} Ψ_F(t, -θ) dθ = 2π c_n(t)`. -/
lemma integral_Ioo_orbExp (F : P2 → ℂ) (n : ℤ) (t : ℝ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, cexp (n * (θ * I)) * orbExp F t (-θ) =
      2 * Real.pi * orbCoeff F n t := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    have := ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  rw [show (∫ θ in Ioo (-Real.pi) Real.pi, cexp (n * (θ * I)) * orbExp F t (-θ)) =
      ∫ θ in Ioo (-Real.pi) Real.pi,
        (fun φ : ℝ => cexp (-(n * φ * I)) * orbExp F t φ) (-θ) from
      setIntegral_congr_fun measurableSet_Ioo fun θ _ => by
        simp only [ofReal_neg, mul_neg, neg_mul, neg_neg, mul_assoc],
    setIntegral_Ioo_comp_neg (fun φ : ℝ => cexp (-(n * φ * I)) * orbExp F t φ),
    orbCoeff, fourierCoeffOn_pi, ← integral_Ioc_eq_integral_Ioo,
    ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]

/-- Integrability in polar coordinates of a bounded measurable function vanishing outside a
ball. -/
lemma integrableOn_polar {H : ℂ → ℂ} (hm : Measurable H) {B R : ℝ} (hR : 0 ≤ R)
    (hB : ∀ l, ‖H l‖ ≤ B) (hRH : ∀ l, H l ≠ 0 → ‖l‖ ≤ R) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • H (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hT : MeasurableSet Complex.polarCoord.target := by
    rw [Complex.polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  have hsymm : Measurable fun p : ℝ × ℝ => Complex.polarCoord.symm p := by
    have : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * I) := by
      fun_prop
    simpa only [Complex.polarCoord_symm_apply] using this.measurable
  rw [← integrable_indicator_iff hT]
  refine integrable_of_bound_ball (B := R * B) (R := max R Real.pi)
    ((measurable_fst.smul (hm.comp hsymm)).indicator hT).aestronglyMeasurable
    (fun p => ?_) (fun p hp => ?_)
  · by_cases hp : p ∈ Complex.polarCoord.target
    · rw [indicator_of_mem hp, norm_smul]
      by_cases h0 : H (Complex.polarCoord.symm p) = 0
      · rw [h0, norm_zero, mul_zero]
        positivity
      · have h1 := hRH _ h0
        rw [Complex.norm_polarCoord_symm] at h1
        exact mul_le_mul (by rw [Real.norm_eq_abs]; exact h1) (hB _) (norm_nonneg _) hR
    · rw [indicator_of_notMem hp, norm_zero]
      positivity
  · have hmem : p ∈ Complex.polarCoord.target := by
      by_contra h
      exact hp (indicator_of_notMem h _)
    rw [indicator_of_mem hmem] at hp
    have h0 : H (Complex.polarCoord.symm p) ≠ 0 := fun h => hp (by rw [h, smul_zero])
    have h1 := hRH _ h0
    rw [Complex.norm_polarCoord_symm] at h1
    rw [Complex.polarCoord_target] at hmem
    refine norm_prod_le_iff.2 ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs]
      exact h1.trans (le_max_left _ _)
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hmem.2.1, hmem.2.2, le_max_right R Real.pi]

/-- The trace integrand `m_{n,ρ}(λ) Φ_F(λ⁻¹)` is integrable in polar coordinates. -/
lemma integrableOn_polar_mult_orbInt {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F)
    (hs : HasCompactSupport F) (n : ℤ) (ρ : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ =>
      p.1 • (mult n ρ (Complex.polarCoord.symm p) * orbInt F (Complex.polarCoord.symm p)⁻¹))
      Complex.polarCoord.target := by
  obtain ⟨C, hC, hCF⟩ := exists_bound_support hs
  obtain ⟨BF, hBF⟩ := hF.continuous.bounded_above_of_compact_support hs
  have hBF0 : 0 ≤ BF := (norm_nonneg _).trans (hBF 0)
  obtain ⟨M, hM⟩ : ∃ M, M = ∫ x : ℂ, (closedBall 0 C).indicator (fun _ => BF) x := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ integral_nonneg fun x => indicator_nonneg (fun _ _ => hBF0) x
  have key : ∀ l : ℂ, mult n ρ l * orbInt F l⁻¹ ≠ 0 → ‖l‖ < C ∧ ‖l⁻¹‖ < C := by
    intro l hl
    have ho : orbInt F l⁻¹ ≠ 0 := right_ne_zero_of_mul hl
    refine ⟨?_, ?_⟩
    · by_contra h
      exact ho (orbInt_eq_zero hCF (Or.inr (by rw [inv_inv]; exact not_lt.1 h)))
    · by_contra h
      exact ho (orbInt_eq_zero hCF (Or.inl (not_lt.1 h)))
  refine integrableOn_polar (H := fun l => mult n ρ l * orbInt F l⁻¹)
    ((measurable_mult n ρ).mul ((stronglyMeasurable_orbInt hF.continuous).measurable.comp
      measurable_inv)) hC.le (B := C ^ 2 * M) (fun l => ?_) (fun l hl => (key l hl).1.le)
  by_cases hl : mult n ρ l * orbInt F l⁻¹ = 0
  · rw [hl, norm_zero]
    positivity
  · have hl0 : l ≠ 0 := by
      rintro rfl
      exact hl (by rw [mult_at_zero, zero_mul])
    rw [norm_mul, norm_mult n ρ hl0]
    refine mul_le_mul ?_ (hM ▸ norm_orbInt_le hBF hCF _) (norm_nonneg _) (by positivity)
    rw [← inv_pow, ← norm_inv]
    exact pow_le_pow_left₀ (norm_nonneg _) (key l hl).2.le 2

/-- **The trace as a Fourier transform**: `T_F(n, ρ) = 2π 𝓕c_n(ρ/π)`. -/
theorem integral_mult_orbInt {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F)
    (n : ℤ) (ρ : ℝ) :
    ∫ l, mult n ρ l * orbInt F l⁻¹ = 2 * Real.pi * 𝓕 (orbCoeff F n) (ρ / Real.pi) := by
  rw [integral_polar_exp (fun l => mult n ρ l * orbInt F l⁻¹)
    (integrableOn_polar_mult_orbInt hF hs n ρ)]
  have h1 : ∀ t θ : ℝ, (Real.exp (2 * t) : ℂ) *
      (mult n ρ (cexp (t + θ * I)) * orbInt F (cexp (t + θ * I))⁻¹) =
      cexp (2 * I * ρ * t) * (cexp (n * (θ * I)) * orbExp F (-t) (-θ)) := by
    intro t θ
    have he : cexp ((2 * t : ℝ) : ℂ) * cexp (t * (2 * I * ρ - 2)) = cexp (2 * I * ρ * t) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [mult_cexp, cexp_inv, ofReal_exp, ← he]
    unfold orbExp
    ring
  simp_rw [h1, integral_const_mul, integral_Ioo_orbExp]
  have hflip := integral_neg_eq_self
    (fun t : ℝ => cexp (-(2 * I * ρ * t)) * (2 * Real.pi * orbCoeff F n t)) volume
  simp only [ofReal_neg, mul_neg, neg_neg] at hflip
  rw [hflip, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  congr 1
  funext v
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have hv : (((-2 * Real.pi * v * (ρ / Real.pi) : ℝ)) : ℂ) * I = -(2 * I * ρ * v) := by
    push_cast
    field_simp
  rw [smul_eq_mul, hv]
  ring

/-! ## The Plancherel density -/

/-- **The Plancherel density of the orbital integral.** For `F` smooth with compact support on
`M₂(ℂ)` and invariant under `SU(2)` conjugation, with `T_F(n, ρ) = ∫ m_{n,ρ}(λ) Φ_F(λ⁻¹) d²λ`:
each `ρ ↦ (n² + 4ρ²) T_F(n, ρ)` is integrable, and
`Σ_{n ∈ ℤ} ∫ (n² + 4ρ²) T_F(n, ρ) dρ = 16 π³ F(1)`. -/
theorem hasSum_density_orbInt {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) (hs : HasCompactSupport F)
    (hK : IsSU2ConjInvariant F) :
    (∀ n : ℤ, Integrable fun ρ : ℝ =>
      ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ l, mult n ρ l * orbInt F l⁻¹) ∧
    HasSum (fun n : ℤ => ∫ ρ : ℝ,
      ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ l, mult n ρ l * orbInt F l⁻¹)
      (16 * Real.pi ^ 3 * F (mat2 1 0 0 1)) := by
  have hT : ∀ n : ℤ, (fun ρ : ℝ =>
      ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ l, mult n ρ l * orbInt F l⁻¹) =
      fun ρ : ℝ => 2 * Real.pi *
        (((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * 𝓕 (orbCoeff F n) (ρ / Real.pi : ℝ)) :=
    fun n => by
      funext ρ
      rw [integral_mult_orbInt hF hs n ρ]
      ring
  have hD := fun n : ℤ =>
    integral_density_fourier (contDiff_orbCoeff hF hs n) (hasCompactSupport_orbCoeff hs n) n
  refine ⟨fun n => by rw [hT n]; exact (hD n).1.const_mul _, ?_⟩
  have hterm : ∀ n : ℤ, (∫ ρ : ℝ,
      ((n : ℂ) ^ 2 + 4 * (ρ : ℂ) ^ 2) * ∫ l, mult n ρ l * orbInt F l⁻¹) =
      2 * (Real.pi : ℂ) ^ 2 * ((n : ℂ) ^ 2 * orbCoeff F n 0) -
        2 * (Real.pi : ℂ) ^ 2 * deriv (deriv (orbCoeff F n)) 0 := fun n => by
    rw [hT n, integral_const_mul, (hD n).2]
    ring
  simp_rw [hterm]
  convert ((hasSum_sq_orbCoeff hF hs).mul_left (2 * (Real.pi : ℂ) ^ 2)).sub
    ((hasSum_deriv_deriv_orbCoeff hF hs).mul_left (2 * (Real.pi : ℂ) ^ 2)) using 1
  linear_combination (2 * (Real.pi : ℂ) ^ 2) * orbExp_laplacian hF hs hK

end Lightlike.Lorentz
