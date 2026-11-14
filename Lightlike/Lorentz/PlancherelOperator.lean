module

public import Lightlike.Lorentz.Plancherel
public import Lightlike.Lorentz.Continuity

/-!
# The operator `π_{n,ρ}(f)` and its integral kernel

For `f : SL(2,ℂ) → ℂ` continuous with compact support, the operator of the principal series
`π_{n,ρ}` (`PrincipalSeries.lean`) integrated against `f` is the Bochner integral in `L²(ℂ)`

    π_{n,ρ}(f) φ = ∫ f(g) π_{n,ρ}(g) φ dg      (`piOp`, Haar measure `haarC`),

which exists because `g ↦ π(g) φ` is continuous (`continuous_principalSeries`). This file proves
that `psKernel` (`PlancherelKernel.lean`), the kernel in the Plancherel formula
(`Plancherel.lean`), is the integral kernel of this operator.

## Main results

* `inner_piOp`: `⟪ψ, π(f) φ⟫ = ∫ conj ψ(z) ∫ K_f(z, w) φ(w) d²w d²z` for all `ψ, φ ∈ L²(ℂ)`,
  with the outer integrand integrable.
* `coeFn_piOp`: `(π(f) φ)(z) = ∫ K_f(z, w) φ(w) d²w` for almost every `z`.
* `plancherel_piOp`: the Plancherel formula (`plancherel`) stated for the operators `piOp`: their
  kernels are `psKernel`, and the weighted sum of the squared kernel norms is `16π⁴ ‖f‖²`.

## Proof

1. `⟪ψ, π(f) φ⟫ = ∫ f(g) ⟪ψ, π(g) φ⟫ dg` (`integral_inner`), and
   `⟪ψ, π(g) φ⟫ = ∫ conj ψ(z) m(den g z) φ(mob g z) d²z` (`coeFn_principalSeries`).
2. The integrand `(g, z) ↦ f(g) conj ψ(z) m(den g z) φ(mob g z)` is integrable on
   `SL(2,ℂ) × ℂ`: by `|ab| ≤ |a|² + |b|²` and the `L²` identity of the principal series
   (`lintegral_act`), its `z`-integral is at most `|f(g)| (‖ψ‖² + ‖φ‖²)`.
3. Fubini, then for fixed `z` the chart at `z` (`haarC_eq_map_prod`), in which `den g z = λ` and
   `mob g z = w` (`den_fixChart`, `mob_fixChart`), turns `∫ f(g) m(den g z) φ(mob g z) dg` into
   `∫ K_f(z, w) φ(w) d²w`.
4. Testing against the indicators of the sets of finite measure gives the identity almost
   everywhere (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`).

## Scope

The theorems identify the kernel of `π(f)`. That `π(f)` is Hilbert–Schmidt with
`‖π(f)‖²_HS = ∫∫ |K_f(z', z)|² d²z' d²z` (the left side of `plancherel`) is the standard formula
for the Hilbert–Schmidt norm of an integral operator with square-integrable kernel; it is not
formalised here, so in `plancherel_piOp` the Hilbert–Schmidt norm is the double integral of the
kernel.

## References

* I. M. Gel'fand, M. I. Graev, N. Ya. Vilenkin, *Generalized Functions*, Vol. 5 (Academic Press,
  1966), Ch. IV (the operators `T(f)` of the principal series and their kernels).
* A. Perez, C. Rovelli, *Spin foam model for Lorentzian general relativity*, arXiv:gr-qc/0011037
  (2000), App. A, (A12)–(A14).
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace Lightlike.Lorentz

/-- **The operator `π_{n,ρ}(f) = ∫ f(g) π_{n,ρ}(g) dg`** on `L²(ℂ)`, as a Bochner integral for the
Haar measure `haarC`. For `f` continuous with compact support the integrand is integrable
(`integrable_piOp_integrand`). -/
noncomputable def piOp (n : ℤ) (ρ : ℝ) (f : SL2C → ℂ) (φ : L2C) : L2C :=
  ∫ g, f g • principalSeries n ρ g φ ∂haarC

/-- For `f` continuous with compact support, `g ↦ f(g) π(g) φ` is Bochner integrable. -/
lemma integrable_piOp_integrand (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (φ : L2C) :
    Integrable (fun g => f g • principalSeries n ρ g φ) haarC :=
  (hf.smul (continuous_principalSeries n ρ φ)).integrable_of_hasCompactSupport
    (hfc.smul_right (f' := fun g => principalSeries n ρ g φ))

/-- The integrand `f(g) conj ψ(z) m(den g z) φ(mob g z)` of `⟪ψ, π(f) φ⟫`. -/
noncomputable def opIntegrand (n : ℤ) (ρ : ℝ) (f : SL2C → ℂ) (ψ φ : ℂ → ℂ) (g : SL2C) (z : ℂ) :
    ℂ :=
  f g * (conj (ψ z) * (mult n ρ (den g z) * φ (mob g z)))

lemma continuous_den₂ : Continuous fun p : SL2C × ℂ => den p.1 p.2 :=
  (((continuous_entry 0 1).comp continuous_fst).mul continuous_snd).add
    ((continuous_entry 1 1).comp continuous_fst)

lemma continuous_num₂ : Continuous fun p : SL2C × ℂ => num p.1 p.2 :=
  (((continuous_entry 0 0).comp continuous_fst).mul continuous_snd).add
    ((continuous_entry 1 0).comp continuous_fst)

lemma measurable_mob₂ : Measurable fun p : SL2C × ℂ => mob p.1 p.2 :=
  continuous_num₂.measurable.div continuous_den₂.measurable

/-- `ab ≤ a² + b²` in `[0, ∞]`. -/
lemma ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ (2 : ℝ) + b ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.rpow_two]
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/-- `∫⁻ |ψ|² < ∞` for `ψ ∈ L²(ℂ)`. -/
lemma lintegral_sq_lt_top (ψ : L2C) : ∫⁻ z, ‖ψ z‖ₑ ^ (2 : ℝ) < ⊤ := by
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    (Lp.eLpNorm_lt_top ψ)
  simpa using this

/-- **Integrability of the integrand of `⟪ψ, π(f) φ⟫`** on `SL(2,ℂ) × ℂ`, for `f` continuous with
compact support. -/
theorem integrable_opIntegrand (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ψ φ : L2C) :
    Integrable (Function.uncurry (opIntegrand n ρ f ψ φ)) (haarC.prod volume) := by
  have hfm : Measurable f := hf.measurable
  have hψm : Measurable ψ := (Lp.stronglyMeasurable ψ).measurable
  have hφm : Measurable φ := (Lp.stronglyMeasurable φ).measurable
  have hm : Measurable (Function.uncurry (opIntegrand n ρ f ψ φ)) :=
    (hfm.comp measurable_fst).mul ((Complex.continuous_conj.measurable.comp
      (hψm.comp measurable_snd)).mul (((measurable_mult n ρ).comp continuous_den₂.measurable).mul
      (hφm.comp measurable_mob₂)))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set A := ∫⁻ z, ‖ψ z‖ₑ ^ (2 : ℝ)
  set B := ∫⁻ w, ‖φ w‖ₑ ^ (2 : ℝ)
  have hinner : ∀ g : SL2C, ∫⁻ z, ‖opIntegrand n ρ f ψ φ g z‖ₑ ≤ ‖f g‖ₑ * (A + B) := by
    intro g
    calc ∫⁻ z, ‖opIntegrand n ρ f ψ φ g z‖ₑ
        ≤ ∫⁻ z, ‖f g‖ₑ * (‖ψ z‖ₑ ^ (2 : ℝ) +
            ‖mult n ρ (den g z) * φ (mob g z)‖ₑ ^ (2 : ℝ)) := by
          refine lintegral_mono fun z => ?_
          rw [opIntegrand, enorm_mul, enorm_mul, ← ofReal_norm (conj _), Complex.norm_conj,
            ofReal_norm]
          gcongr ‖f g‖ₑ * ?_
          exact ennreal_mul_le_sq_add_sq _ _
      _ = ‖f g‖ₑ * (A + B) := by
          rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_add_left
            (hψm.enorm.pow_const _), lintegral_act n ρ g φ]
  have hfi : ∫⁻ g, ‖f g‖ₑ ∂haarC < ⊤ :=
    hasFiniteIntegral_iff_enorm.1 (hf.integrable_of_hasCompactSupport hfc).2
  calc ∫⁻ p, ‖Function.uncurry (opIntegrand n ρ f ψ φ) p‖ₑ ∂(haarC.prod volume)
      ≤ ∫⁻ g, ∫⁻ z, ‖opIntegrand n ρ f ψ φ g z‖ₑ ∂volume ∂haarC := lintegral_prod_le _
    _ ≤ ∫⁻ g, ‖f g‖ₑ * (A + B) ∂haarC := lintegral_mono hinner
    _ = (∫⁻ g, ‖f g‖ₑ ∂haarC) * (A + B) := lintegral_mul_const _ hfm.enorm
    _ < ⊤ := ENNReal.mul_lt_top hfi
        (ENNReal.add_lt_top.2 ⟨lintegral_sq_lt_top ψ, lintegral_sq_lt_top φ⟩)

/-- **The chart at `z` evaluates the `g`-integral**: if `g ↦ f(g) m(den g z) φ(mob g z)` is
`haarC`-integrable, its integral is `∫ K_f(z, w) φ(w) d²w`. -/
theorem integral_haarC_eq_psKernel (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Measurable f)
    {φ : ℂ → ℂ} (hφ : Measurable φ) (z : ℂ)
    (hi : Integrable (fun g => f g * (mult n ρ (den g z) * φ (mob g z))) haarC) :
    ∫ g, f g * (mult n ρ (den g z) * φ (mob g z)) ∂haarC = ∫ w, psKernel n ρ f z w * φ w := by
  have hGm : Measurable fun g => f g * (mult n ρ (den g z) * φ (mob g z)) :=
    hf.mul (((measurable_mult n ρ).comp (continuous_den_left z).measurable).mul
      (hφ.comp ((continuous_num_left z).measurable.div (continuous_den_left z).measurable)))
  have hT : Measurable fun p : ℂ × ℂ × ℂ => fixChart z (tripleOf p) :=
    (measurable_fixChart z).comp measurePreserving_tripleOf.measurable
  have hsnd : ∀ᵐ p : ℂ × ℂ × ℂ, p.2.2 ≠ 0 := Measure.quasiMeasurePreserving_snd.ae ae_snd_ne_zero
  have e : (fun p : ℂ × ℂ × ℂ => (fun g => f g * (mult n ρ (den g z) * φ (mob g z)))
      (fixChart z (tripleOf p))) =ᵐ[volume]
      fun p => f (chartPt z p.1 p.2) * mult n ρ p.2.2 * φ p.1 := by
    filter_upwards [hsnd] with p hp
    have h2 : tripleOf p 2 ≠ 0 := hp
    show f (fixChart z (tripleOf p)) * (mult n ρ (den (fixChart z (tripleOf p)) z) *
      φ (mob (fixChart z (tripleOf p)) z)) = f (chartPt z p.1 p.2) * mult n ρ p.2.2 * φ p.1
    rw [den_fixChart z h2, mob_fixChart z h2, mul_assoc]
    rfl
  rw [haarC_eq_map_prod z] at hi ⊢
  rw [integral_map hT.aemeasurable hGm.aestronglyMeasurable]
  have hi' := ((integrable_map_measure hGm.aestronglyMeasurable hT.aemeasurable).1 hi).congr e
  refine (integral_congr_ae e).trans ?_
  rw [Measure.volume_eq_prod, integral_prod _ hi']
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [psKernel]
  exact integral_mul_const _ _

/-- **The kernel of `π(f)`, weak form**: for `f` continuous with compact support and
`ψ, φ ∈ L²(ℂ)`, `z ↦ conj ψ(z) ∫ K_f(z, w) φ(w) d²w` is integrable and
`⟪ψ, π_{n,ρ}(f) φ⟫ = ∫ conj ψ(z) ∫ K_f(z, w) φ(w) d²w d²z`. -/
theorem inner_piOp (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ψ φ : L2C) :
    Integrable (fun z => conj (ψ z) * ∫ w, psKernel n ρ f z w * φ w) ∧
    ⟪ψ, piOp n ρ f φ⟫_ℂ = ∫ z, conj (ψ z) * ∫ w, psKernel n ρ f z w * φ w := by
  have hfm : Measurable f := hf.measurable
  have hφm : Measurable φ := (Lp.stronglyMeasurable φ).measurable
  have hH := integrable_opIntegrand n ρ hf hfc ψ φ
  -- the `g`-integral at fixed `z`
  have hz : ∀ᵐ z : ℂ, ∫ g, opIntegrand n ρ f ψ φ g z ∂haarC =
      conj (ψ z) * ∫ w, psKernel n ρ f z w * φ w := by
    filter_upwards [hH.prod_left_ae] with z hzi
    have e1 : ∫ g, opIntegrand n ρ f ψ φ g z ∂haarC =
        conj (ψ z) * ∫ g, f g * (mult n ρ (den g z) * φ (mob g z)) ∂haarC := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [opIntegrand]
      ring
    rw [e1]
    by_cases h0 : ψ z = 0
    · simp [h0]
    have hc : conj (ψ z) ≠ 0 := (map_ne_zero _).2 h0
    have hG : Integrable (fun g => f g * (mult n ρ (den g z) * φ (mob g z))) haarC := by
      refine (hzi.const_mul (conj (ψ z))⁻¹).congr (Eventually.of_forall fun g => ?_)
      simp only [Function.uncurry_apply_pair, opIntegrand]
      rw [← mul_assoc (conj (ψ z))⁻¹, mul_comm (conj (ψ z))⁻¹ (f g), mul_assoc,
        inv_mul_cancel_left₀ hc]
    rw [integral_haarC_eq_psKernel n ρ hfm hφm z hG]
  refine ⟨hH.integral_prod_right.congr hz, ?_⟩
  have step1 : ⟪ψ, piOp n ρ f φ⟫_ℂ = ∫ g, ∫ z, opIntegrand n ρ f ψ φ g z ∂volume ∂haarC := by
    rw [piOp, ← integral_inner (𝕜 := ℂ) (integrable_piOp_integrand n ρ hf hfc φ) ψ]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    beta_reduce
    rw [inner_smul_right, L2.inner_def, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_principalSeries n ρ g φ] with z hz'
    rw [RCLike.inner_apply', hz', opIntegrand]
  rw [step1, integral_integral_swap hH]
  exact integral_congr_ae hz

/-- **`psKernel` is the integral kernel of `π_{n,ρ}(f) = ∫ f(g) π_{n,ρ}(g) dg`**: for `f`
continuous with compact support and `φ ∈ L²(ℂ)`,
`(π_{n,ρ}(f) φ)(z) = ∫ K_f(z, w) φ(w) d²w` for almost every `z`. -/
theorem coeFn_piOp (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (φ : L2C) :
    piOp n ρ f φ =ᵐ[volume] fun z => ∫ w, psKernel n ρ f z w * φ w := by
  have hind : ∀ s : Set ℂ, ∀ hs : MeasurableSet s, ∀ hμs : volume s ≠ ⊤,
      (fun z => conj (indicatorConstLp 2 hs hμs (1 : ℂ) z) *
        ∫ w, psKernel n ρ f z w * φ w) =ᵐ[volume]
      s.indicator fun z => ∫ w, psKernel n ρ f z w * φ w := by
    intro s hs hμs
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℂ))]
      with z hz
    rw [hz]
    by_cases h : z ∈ s <;> simp [h]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ one_le_two hμs.ne
  · intro s hs hμs
    exact (integrable_indicator_iff hs).1
      ((inner_piOp n ρ hf hfc (indicatorConstLp 2 hs hμs.ne (1 : ℂ)) φ).1.congr
        (hind s hs hμs.ne))
  · intro s hs hμs
    rw [← L2.inner_indicatorConstLp_one hs hμs.ne,
      (inner_piOp n ρ hf hfc (indicatorConstLp 2 hs hμs.ne (1 : ℂ)) φ).2,
      ← integral_indicator hs]
    exact integral_congr_ae (hind s hs hμs.ne)

/-- **The Plancherel formula for the operators `π_{n,ρ}(f)`**: for `f = F|_{SL(2,ℂ)}` with `F`
smooth and compactly supported on `2 × 2` arrays, the kernel of `π_{n,ρ}(f) = ∫ f(g) π_{n,ρ}(g) dg`
is `K_f = psKernel n ρ f` (`coeFn_piOp`), and
`Σ_n ∫ (n² + 4ρ²) ∫∫ |K_f(z', z)|² d²z' d²z dρ = 16π⁴ ∫ |f|² dg` (`plancherel`). -/
theorem plancherel_piOp {f : SL2C → ℂ} {F : (Fin 2 → Fin 2 → ℂ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (hs : HasCompactSupport F) (hfF : ∀ g : SL2C, f g = F (toArr g)) :
    (∀ (n : ℤ) (ρ : ℝ) (φ : L2C),
      piOp n ρ f φ =ᵐ[volume] fun z => ∫ w, psKernel n ρ f z w * φ w) ∧
    HasSum (fun n : ℤ => ∫ ρ : ℝ,
      ((n : ℝ) ^ 2 + 4 * ρ ^ 2) * ∫ z, ∫ z', ‖psKernel n ρ f z' z‖ ^ 2)
      (16 * Real.pi ^ 4 * ∫ g, ‖f g‖ ^ 2 ∂haarC) := by
  have hfe : f = fun g => F (toArr g) := funext hfF
  have hf : Continuous f := by
    rw [hfe]; exact hF.continuous.comp isClosedEmbedding_toArr.continuous
  have hfc : HasCompactSupport f := by
    rw [hfe]; exact hasCompactSupport_restrict hs
  exact ⟨fun n ρ φ => coeFn_piOp n ρ hf hfc φ, (plancherel hF hs hfF).2.2.2⟩

end Lightlike.Lorentz
