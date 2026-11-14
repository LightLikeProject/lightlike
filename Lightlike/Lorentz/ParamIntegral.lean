module

public import Mathlib

/-!
# Smoothness of parametric integrals

Let `Φ : P → E → G` be jointly `C^k` on finite-dimensional real spaces `P, E`, and let `p : α → P`
be a measurable parameter that is (a.e.) bounded on a set `S` of finite measure, with
`Φ (p a) = 0` for (a.e.) `a ∉ S`. Then `x ↦ ∫ Φ (p a) x dμ(a)` is `C^k`
(`contDiff_parametric_integral`), and its derivative is the integral of the derivatives
(`hasFDerivAt_parametric_integral`; in one real variable `hasDerivAt_parametric_integral` and
`deriv_deriv_parametric_integral`).

The parameter space `α` carries no topology, so the lemma covers integrals over `SL(2, ℂ)`, over
`ℂ²` and over `ℂ` alike, and the a.e. hypotheses cover `μ = volume.restrict S`. A measurable
weight `w : α → 𝕜` with support in `S` is handled by taking `p a = (w a, q a)` and
`Φ (c, q) x = c • Ψ q x`.

The proof is an induction on `k`: the derivative `x ↦ fderiv ℝ (Φ q) x` is again jointly
`C^(k-1)` in `(q, x)` (`ContDiff.fderiv`), and differentiation under the integral sign is
`hasFDerivAt_integral_of_dominated_of_fderiv_le`, with the bound `C · 1_S`.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., Wiley 1999, Theorem 2.27 (differentiation under
  the integral sign).
-/

@[expose] public section

open MeasureTheory Metric
open scoped ContDiff

namespace Lightlike.Lorentz

universe u

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {P : Type*} {E G : Type u}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ G] in
/-- A jointly continuous `Ψ` is bounded on `{‖q‖ ≤ R} × ball x₀ 1`. -/
lemma exists_bound_ball_of_continuous {Ψ : P → E → G} (hΨ : Continuous (Function.uncurry Ψ))
    (R : ℝ) (x₀ : E) : ∃ C, ∀ q x, ‖q‖ ≤ R → x ∈ ball x₀ 1 → ‖Ψ q x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : P) R).prod (isCompact_closedBall x₀ 1))
    |>.exists_bound_of_continuousOn hΨ.continuousOn
  exact ⟨C, fun q x hq hx =>
    hC (q, x) ⟨mem_closedBall_zero_iff.2 hq, ball_subset_closedBall hx⟩⟩

/-- The bound `C · 1_S` of the parametric integrand is integrable. -/
lemma integrable_indicator_const_of_ne_top {S : Set α} (hSm : MeasurableSet S) (hS : μ S ≠ ⊤)
    (C : ℝ) : Integrable (S.indicator fun _ => C) μ :=
  (integrable_indicator_iff hSm).2 (integrableOn_const hS)

omit [NormedSpace ℝ G] in
/-- The parametric integrand is dominated by `C · 1_S` near `x₀`. -/
lemma parametric_bound {Ψ : P → E → G} (hΨ : Continuous (Function.uncurry Ψ))
    {p : α → P} {S : Set α} {R : ℝ} (hpR : ∀ᵐ a ∂μ, a ∈ S → ‖p a‖ ≤ R)
    (h0 : ∀ᵐ a ∂μ, a ∉ S → ∀ x, Ψ (p a) x = 0) (x₀ : E) :
    ∃ C, ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ 1, ‖Ψ (p a) x‖ ≤ S.indicator (fun _ => C) a := by
  obtain ⟨C, hC⟩ := exists_bound_ball_of_continuous hΨ R x₀
  refine ⟨C, ?_⟩
  filter_upwards [hpR, h0] with a hpa h0a x hx
  by_cases ha : a ∈ S
  · rw [Set.indicator_of_mem ha]; exact hC _ _ (hpa ha) hx
  · rw [Set.indicator_of_notMem ha, h0a ha x, norm_zero]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ G] in
/-- The parametric integrand is a.e. strongly measurable for each fixed `x`. -/
lemma aestronglyMeasurable_parametric {Ψ : P → E → G} (hΨ : Continuous (Function.uncurry Ψ))
    {p : α → P} (hp : AEStronglyMeasurable p μ) (x : E) :
    AEStronglyMeasurable (fun a => Ψ (p a) x) μ :=
  (hΨ.comp (continuous_id.prodMk continuous_const)).comp_aestronglyMeasurable hp

omit [NormedSpace ℝ G] in
/-- The parametric integrand is integrable for each fixed `x`. -/
lemma integrable_parametric {Ψ : P → E → G} (hΨ : Continuous (Function.uncurry Ψ))
    {p : α → P} (hp : AEStronglyMeasurable p μ) {S : Set α} (hSm : MeasurableSet S)
    (hS : μ S ≠ ⊤) {R : ℝ} (hpR : ∀ᵐ a ∂μ, a ∈ S → ‖p a‖ ≤ R)
    (h0 : ∀ᵐ a ∂μ, a ∉ S → ∀ x, Ψ (p a) x = 0) (x : E) :
    Integrable (fun a => Ψ (p a) x) μ := by
  obtain ⟨C, hC⟩ := parametric_bound hΨ hpR h0 x
  exact (integrable_indicator_const_of_ne_top hSm hS C).mono'
    (aestronglyMeasurable_parametric hΨ hp x) (hC.mono fun a ha => ha x (mem_ball_self one_pos))

omit [MeasurableSpace α] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] in
/-- The derivative of a parametric integrand vanishes where the integrand does. -/
lemma fderiv_parametric_eq_zero {Φ : P → E → G} {p : α → P} {S : Set α} {a : α}
    (h0 : a ∉ S → ∀ x, Φ (p a) x = 0) (ha : a ∉ S) (x : E) : fderiv ℝ (Φ (p a)) x = 0 := by
  have : Φ (p a) = fun _ => 0 := funext (h0 ha)
  rw [this, fderiv_const_apply]

/-- Differentiation under the integral sign for the parametric integrals of this file. -/
theorem hasFDerivAt_parametric_integral {Φ : P → E → G}
    (hΦ : ContDiff ℝ 1 (Function.uncurry Φ)) {p : α → P} (hp : AEStronglyMeasurable p μ)
    {S : Set α} (hSm : MeasurableSet S) (hS : μ S ≠ ⊤) {R : ℝ}
    (hpR : ∀ᵐ a ∂μ, a ∈ S → ‖p a‖ ≤ R) (h0 : ∀ᵐ a ∂μ, a ∉ S → ∀ x, Φ (p a) x = 0) (x₀ : E) :
    HasFDerivAt (fun x => ∫ a, Φ (p a) x ∂μ) (∫ a, fderiv ℝ (Φ (p a)) x₀ ∂μ) x₀ := by
  have hd : ContDiff ℝ 0 (fun y : P × E => fderiv ℝ (Φ y.1) y.2) :=
    ContDiff.fderiv (f := fun (y : P × E) (x : E) => Φ y.1 x) (g := Prod.snd)
      (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  have hd' : Continuous (Function.uncurry fun q x => fderiv ℝ (Φ q) x) := hd.continuous
  have h0' : ∀ᵐ a ∂μ, a ∉ S → ∀ x, fderiv ℝ (Φ (p a)) x = 0 :=
    h0.mono fun a h0a ha x => fderiv_parametric_eq_zero h0a ha x
  obtain ⟨C', hC'⟩ := parametric_bound hd' hpR h0' x₀
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x₀ one_pos)
    (Filter.Eventually.of_forall fun x => aestronglyMeasurable_parametric hΦ.continuous hp x)
    (integrable_parametric hΦ.continuous hp hSm hS hpR h0 x₀)
    (aestronglyMeasurable_parametric hd' hp x₀) hC'
    (integrable_indicator_const_of_ne_top hSm hS C')
    (Filter.Eventually.of_forall fun a x _ => ?_)
  have : ContDiff ℝ 1 (Φ (p a)) := hΦ.comp (contDiff_const.prodMk contDiff_id)
  exact (this.differentiable one_ne_zero x).hasFDerivAt

/-- **Smoothness of parametric integrals.** If `Φ` is jointly `C^k`, the parameter `p` is
measurable and a.e. bounded on `S`, `μ S < ∞`, and `Φ (p a) = 0` for a.e. `a ∉ S`, then
`x ↦ ∫ Φ (p a) x dμ(a)` is `C^k`. -/
theorem contDiff_parametric_integral (k : ℕ) {Φ : P → E → G}
    (hΦ : ContDiff ℝ k (Function.uncurry Φ)) {p : α → P} (hp : AEStronglyMeasurable p μ)
    {S : Set α} (hSm : MeasurableSet S) (hS : μ S ≠ ⊤) {R : ℝ}
    (hpR : ∀ᵐ a ∂μ, a ∈ S → ‖p a‖ ≤ R) (h0 : ∀ᵐ a ∂μ, a ∉ S → ∀ x, Φ (p a) x = 0) :
    ContDiff ℝ k (fun x => ∫ a, Φ (p a) x ∂μ) := by
  induction k generalizing G with
  | zero =>
    refine contDiff_zero.2 (continuous_iff_continuousAt.2 fun x₀ => ?_)
    obtain ⟨C, hC⟩ := parametric_bound hΦ.continuous hpR h0 x₀
    refine continuousAt_of_dominated
      (Filter.Eventually.of_forall fun x => aestronglyMeasurable_parametric hΦ.continuous hp x)
      (Filter.eventually_of_mem (ball_mem_nhds x₀ one_pos) fun x hx =>
        hC.mono fun a ha => ha x hx)
      (integrable_indicator_const_of_ne_top hSm hS C)
      (Filter.Eventually.of_forall fun a => ?_)
    exact (hΦ.continuous.comp (continuous_const.prodMk continuous_id)).continuousAt
  | succ k ih =>
    have hd : ContDiff ℝ k (fun y : P × E => fderiv ℝ (Φ y.1) y.2) :=
      ContDiff.fderiv (f := fun (y : P × E) (x : E) => Φ y.1 x) (g := Prod.snd)
        (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by push_cast; rfl)
    have h0' : ∀ᵐ a ∂μ, a ∉ S → ∀ x, fderiv ℝ (Φ (p a)) x = 0 :=
      h0.mono fun a h0a ha x => fderiv_parametric_eq_zero h0a ha x
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    exact ⟨_, ih (Φ := fun q x => fderiv ℝ (Φ q) x) hd h0', fun x₀ =>
      hasFDerivAt_parametric_integral (hΦ.of_le (by norm_cast; omega)) hp hSm hS hpR h0 x₀⟩

/-- The `C^∞` version of `contDiff_parametric_integral`. -/
theorem contDiff_parametric_integral_infty {Φ : P → E → G}
    (hΦ : ContDiff ℝ ∞ (Function.uncurry Φ)) {p : α → P} (hp : AEStronglyMeasurable p μ)
    {S : Set α} (hSm : MeasurableSet S) (hS : μ S ≠ ⊤) {R : ℝ}
    (hpR : ∀ᵐ a ∂μ, a ∈ S → ‖p a‖ ≤ R) (h0 : ∀ᵐ a ∂μ, a ∉ S → ∀ x, Φ (p a) x = 0) :
    ContDiff ℝ ∞ (fun x => ∫ a, Φ (p a) x ∂μ) :=
  contDiff_infty.2 fun k =>
    contDiff_parametric_integral k (hΦ.of_le (by exact_mod_cast le_top)) hp hSm hS hpR h0

/-! ### One real variable -/

section OneVar

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [FiniteDimensional ℝ P] in
/-- The derivative in the real variable of a jointly `C²` family is jointly `C¹`. -/
lemma contDiff_uncurry_deriv {Φ : P → ℝ → H} (hΦ : ContDiff ℝ 2 (Function.uncurry Φ)) :
    ContDiff ℝ 1 (Function.uncurry fun q t => deriv (Φ q) t) := by
  have hd : ContDiff ℝ 1 (fun y : P × ℝ => fderiv ℝ (Φ y.1) y.2) :=
    ContDiff.fderiv (f := fun (y : P × ℝ) (x : ℝ) => Φ y.1 x) (g := Prod.snd)
      (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  exact hd.clm_apply contDiff_const

/-- **Differentiation under the integral sign, one real variable**: the derivative of
`t ↦ ∫ Φ (p a) t dμ(a)` is `∫ ∂ₜΦ (p a) t dμ(a)`. -/
theorem hasDerivAt_parametric_integral {Φ : P → ℝ → H}
    (hΦ : ContDiff ℝ 1 (Function.uncurry Φ)) {p : α → P} (hp : AEStronglyMeasurable p μ)
    {S : Set α} (hSm : MeasurableSet S) (hS : μ S ≠ ⊤) {R : ℝ}
    (hpR : ∀ᵐ a ∂μ, a ∈ S → ‖p a‖ ≤ R) (h0 : ∀ᵐ a ∂μ, a ∉ S → ∀ x, Φ (p a) x = 0) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ a, Φ (p a) t ∂μ) (∫ a, deriv (Φ (p a)) t₀ ∂μ) t₀ := by
  have hd : ContDiff ℝ 0 (fun y : P × ℝ => fderiv ℝ (Φ y.1) y.2) :=
    ContDiff.fderiv (f := fun (y : P × ℝ) (x : ℝ) => Φ y.1 x) (g := Prod.snd)
      (hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  have h0' : ∀ᵐ a ∂μ, a ∉ S → ∀ x, fderiv ℝ (Φ (p a)) x = 0 :=
    h0.mono fun a h0a ha x => fderiv_parametric_eq_zero h0a ha x
  have hint := integrable_parametric (Ψ := fun q x => fderiv ℝ (Φ q) x) hd.continuous hp hSm hS
    hpR h0' t₀
  have h := (hasFDerivAt_parametric_integral hΦ hp hSm hS hpR h0 t₀).hasDerivAt
  rw [ContinuousLinearMap.integral_apply hint] at h
  exact h

/-- The second derivative of a parametric integral in one real variable. -/
theorem deriv_deriv_parametric_integral {Φ : P → ℝ → H}
    (hΦ : ContDiff ℝ 2 (Function.uncurry Φ)) {p : α → P} (hp : AEStronglyMeasurable p μ)
    {S : Set α} (hSm : MeasurableSet S) (hS : μ S ≠ ⊤) {R : ℝ}
    (hpR : ∀ᵐ a ∂μ, a ∈ S → ‖p a‖ ≤ R) (h0 : ∀ᵐ a ∂μ, a ∉ S → ∀ x, Φ (p a) x = 0) (t₀ : ℝ) :
    deriv (deriv fun t => ∫ a, Φ (p a) t ∂μ) t₀ = ∫ a, deriv (deriv (Φ (p a))) t₀ ∂μ := by
  have h1 : deriv (fun t => ∫ a, Φ (p a) t ∂μ) = fun t => ∫ a, deriv (Φ (p a)) t ∂μ :=
    funext fun t => (hasDerivAt_parametric_integral (hΦ.of_le (by norm_num)) hp hSm hS hpR h0
      t).deriv
  have h0' : ∀ᵐ a ∂μ, a ∉ S → ∀ x, deriv (Φ (p a)) x = 0 := by
    filter_upwards [h0] with a h0a ha x
    have : Φ (p a) = fun _ => 0 := funext (h0a ha)
    rw [this, deriv_const]
  rw [h1]
  exact (hasDerivAt_parametric_integral (Φ := fun q t => deriv (Φ q) t)
    (contDiff_uncurry_deriv hΦ) hp hSm hS hpR h0' t₀).deriv

end OneVar

end Lightlike.Lorentz
