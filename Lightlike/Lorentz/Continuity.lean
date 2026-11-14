module

public import Lightlike.Lorentz.PrincipalSeries

/-!
# Continuity of the principal series

**Theorem (`continuous_principalSeries`).** For every `f ∈ L²(ℂ)` the orbit map `g ↦ π(g) f` is
continuous on `SL(2,ℂ)`: the principal series is a strongly continuous unitary representation.
**Theorem (`continuous_principalSeries_action`).** The action map `(g, f) ↦ π(g) f` is jointly
continuous on `SL(2,ℂ) × L²(ℂ)`.

Proof.
1. For a continuous compactly supported `φ`, the matrix coefficient `g ↦ ⟪π(g) φ, φ⟫` is
   continuous at `1` by dominated convergence (`continuousAt_inner_one`): near `1` the
   denominator `b z + d` stays at distance `≤ 1/2` from `1` on the support of `φ`, so the
   integrand is bounded by `4 · sup|φ| · |φ|`.
2. Unitarity gives `‖π(g) φ - φ‖² = 2‖φ‖² - 2 Re ⟪π(g) φ, φ⟫ → 0` (`tendsto_one_of_compactSupport`).
3. Continuous compactly supported functions are dense in `L²(ℂ)`, and every `π(g)` is an
   isometry; an `ε/3` argument gives `π(g) f → f` as `g → 1` for all `f` (`tendsto_one`).
4. `π(g) f = π(g₀) π(g₀⁻¹ g) f` moves continuity from `1` to any `g₀`.

References: G. B. Folland, *A Course in Abstract Harmonic Analysis* (CRC Press, 1995),
Chapter 3 (strong continuity of unitary representations); A. W. Knapp, *Representation Theory of
Semisimple Groups* (Princeton, 1986), Chapter II.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology Metric
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace Lightlike.Lorentz

variable (n : ℤ) (ρ : ℝ)

lemma continuous_entry (i j : Fin 2) :
    Continuous fun g : SL2C => (g : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  continuous_subtype_val.matrix_elem i j

lemma continuous_den_left (z : ℂ) : Continuous fun g : SL2C => den g z :=
  ((continuous_entry 0 1).mul continuous_const).add (continuous_entry 1 1)

lemma continuous_num_left (z : ℂ) : Continuous fun g : SL2C => num g z :=
  ((continuous_entry 0 0).mul continuous_const).add (continuous_entry 1 0)

/-- The integrand of the matrix coefficient `⟪π(g) φ, φ⟫`. -/
noncomputable def coeffIntegrand (φ : ℂ → ℂ) (g : SL2C) (z : ℂ) : ℂ :=
  conj (mult n ρ (den g z) * φ (mob g z)) * φ z

/-- The matrix coefficient of a function in `L²` as an explicit integral. -/
lemma inner_eq_integral (φ : ℂ → ℂ) (hφ : MemLp φ 2 volume) (g : SL2C) :
    ⟪principalSeries n ρ g (hφ.toLp φ), hφ.toLp φ⟫_ℂ = ∫ z, coeffIntegrand n ρ φ g z := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have h1 := coeFn_principalSeries n ρ g (hφ.toLp φ)
  have h2 := MemLp.coeFn_toLp hφ
  have h3 := ae_eq_comp_mob g h2
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  simp only [Function.comp_apply] at hz3
  rw [hz1, hz2, hz3, coeffIntegrand, RCLike.inner_apply, mul_comm]

/-- **Step 1.** For continuous compactly supported `φ`, `g ↦ ⟪π(g) φ, φ⟫` is continuous at `1`. -/
theorem continuousAt_inner_one (φ : ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ContinuousAt (fun g => ∫ z, coeffIntegrand n ρ φ g z) 1 := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  set δ : ℝ := 1 / (4 * (|R| + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  -- Near the identity, `|b| < δ` and `|d - 1| < 1/4`.
  have hb : ∀ᶠ g : SL2C in 𝓝 1, ‖g 0 1‖ < δ :=
    ((continuous_entry 0 1).norm.continuousAt).eventually_lt
      (continuousAt_const (y := δ)) (by simpa using hδpos)
  have hd : ∀ᶠ g : SL2C in 𝓝 1, ‖g 1 1 - 1‖ < 1 / 4 :=
    (((continuous_entry 1 1).sub continuous_const).norm.continuousAt).eventually_lt
      (continuousAt_const (y := (1 / 4 : ℝ))) (by norm_num)
  refine continuousAt_of_dominated (bound := fun z => 4 * C * ‖φ z‖) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun g => ?_
    refine (Continuous.measurable (by fun_prop : Continuous fun w : ℂ => conj w)).comp_aemeasurable
      ?_ |>.aestronglyMeasurable.mul hφ.aestronglyMeasurable
    exact ((measurable_mult n ρ).comp (continuous_den g).measurable).aemeasurable.mul
      (hφ.measurable.comp (measurable_mob g)).aemeasurable
  · filter_upwards [hb, hd] with g hbg hdg
    refine Eventually.of_forall fun z => ?_
    by_cases hz : φ z = 0
    · simp [coeffIntegrand, hz]
    · have hzK : z ∈ Metric.closedBall (0 : ℂ) R := hR (subset_tsupport _ hz)
      have hzR : ‖z‖ ≤ |R| := by
        have := mem_closedBall_zero_iff.mp hzK; exact this.trans (le_abs_self R)
      have hden : ‖den g z - 1‖ ≤ 1 / 2 := by
        have e : den g z - 1 = g 0 1 * z + (g 1 1 - 1) := by simp only [den]; ring
        rw [e]
        calc ‖g 0 1 * z + (g 1 1 - 1)‖ ≤ ‖g 0 1‖ * ‖z‖ + ‖g 1 1 - 1‖ :=
              (norm_add_le _ _).trans (by rw [norm_mul])
          _ ≤ δ * (|R| + 1) + 1 / 4 :=
              add_le_add (mul_le_mul hbg.le (by linarith) (norm_nonneg _) hδpos.le) hdg.le
          _ = 1 / 2 := by rw [hδ]; field_simp; norm_num
      have hden' : 1 / 2 ≤ ‖den g z‖ := by
        have := norm_sub_le (den g z) (den g z - 1)
        rw [sub_sub_cancel, norm_one] at this
        linarith
      have hne : den g z ≠ 0 := by
        intro h0; rw [h0, norm_zero] at hden'; norm_num at hden'
      have hm : ‖mult n ρ (den g z)‖ ≤ 4 := by
        rw [norm_mult n ρ hne]
        have : (1 / 2 : ℝ) ^ 2 ≤ ‖den g z‖ ^ 2 := by gcongr
        calc (‖den g z‖ ^ 2)⁻¹ ≤ ((1 / 2 : ℝ) ^ 2)⁻¹ := by gcongr
          _ = 4 := by norm_num
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z)
      rw [coeffIntegrand, norm_mul, RCLike.norm_conj, norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hm (hC _) (norm_nonneg _) (by norm_num))
        (norm_nonneg _)
  · exact ((hφ.integrable_of_hasCompactSupport hφc).norm.const_mul (4 * C))
  · refine Eventually.of_forall fun z => ?_
    have h1 : den (1 : SL2C) z ≠ 0 := by simp
    have hd : ContinuousAt (fun g : SL2C => den g z) 1 := (continuous_den_left z).continuousAt
    have hm : ContinuousAt (fun g : SL2C => mult n ρ (den g z)) 1 :=
      ContinuousAt.comp (f := fun g : SL2C => den g z) (continuousAt_mult n ρ h1) hd
    have hmob : ContinuousAt (fun g : SL2C => mob g z) 1 :=
      ((continuous_num_left z).continuousAt).div hd h1
    have hφm : ContinuousAt (fun g : SL2C => φ (mob g z)) 1 :=
      hφ.continuousAt.comp hmob
    exact ((Complex.continuous_conj.continuousAt).comp (hm.mul hφm)).mul continuousAt_const

/-- **Step 2.** For continuous compactly supported `φ`, `π(g) φ → φ` as `g → 1`. -/
theorem tendsto_one_of_compactSupport (φ : ℂ → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ2 : MemLp φ 2 volume) :
    Tendsto (fun g => principalSeries n ρ g (hφ2.toLp φ)) (𝓝 1) (𝓝 (hφ2.toLp φ)) := by
  set F := hφ2.toLp φ
  have hcoef : ContinuousAt (fun g => ⟪principalSeries n ρ g F, F⟫_ℂ) 1 := by
    have := continuousAt_inner_one n ρ φ hφ hφc
    simpa only [← inner_eq_integral n ρ φ hφ2] using this
  have hval : ⟪principalSeries n ρ 1 F, F⟫_ℂ = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [principalSeries_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K]; norm_cast
  have hre : Tendsto (fun g => RCLike.re ⟪principalSeries n ρ g F, F⟫_ℂ) (𝓝 1)
      (𝓝 (‖F‖ ^ 2)) := by
    have := (RCLike.continuous_re.tendsto _).comp hcoef.tendsto
    rw [hval, RCLike.re_to_complex, Complex.ofReal_re] at this
    exact this
  have hsq : Tendsto (fun g => ‖principalSeries n ρ g F - F‖ ^ 2) (𝓝 1) (𝓝 0) := by
    have e : ∀ g, ‖principalSeries n ρ g F - F‖ ^ 2 =
        2 * ‖F‖ ^ 2 - 2 * RCLike.re ⟪principalSeries n ρ g F, F⟫_ℂ := fun g => by
      rw [@norm_sub_sq ℂ, principalSeries_norm]; ring
    simp only [e]
    have := (tendsto_const_nhds (x := 2 * ‖F‖ ^ 2)).sub (hre.const_mul 2)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun g => ?_
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- **Step 3.** For every `f ∈ L²(ℂ)`, `π(g) f → f` as `g → 1`. -/
theorem tendsto_one (f : L2C) : Tendsto (fun g => principalSeries n ρ g f) (𝓝 1) (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨φ, hφc, hφnorm, hφ, hφ2⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top
      (ENNReal.ofReal_pos.mpr hε3).ne'
  set F := hφ2.toLp φ
  have hfF : ‖f - F‖ ≤ ε / 3 := by
    rw [Lp.norm_def]
    have : eLpNorm (⇑(f - F)) 2 volume = eLpNorm (⇑f - φ) 2 volume := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub f F, MemLp.coeFn_toLp hφ2] with z hz1 hz2
      rw [hz1, Pi.sub_apply, hz2, Pi.sub_apply]
    rw [this]
    have hfin : eLpNorm (⇑f - φ) 2 volume ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hφnorm
    calc (eLpNorm (⇑f - φ) 2 volume).toReal ≤ (ENNReal.ofReal (ε / 3)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hφnorm
      _ = ε / 3 := ENNReal.toReal_ofReal hε3.le
  have hev := (Metric.tendsto_nhds.mp (tendsto_one_of_compactSupport n ρ φ hφ hφc hφ2)) _ hε3
  filter_upwards [hev] with g hg
  rw [dist_eq_norm] at hg ⊢
  have e : principalSeries n ρ g f - f =
      principalSeries n ρ g (f - F) + (principalSeries n ρ g F - F) + (F - f) := by
    rw [map_sub]; abel
  rw [e]
  calc ‖principalSeries n ρ g (f - F) + (principalSeries n ρ g F - F) + (F - f)‖
      ≤ ‖principalSeries n ρ g (f - F)‖ + ‖principalSeries n ρ g F - F‖ + ‖F - f‖ :=
        norm_add₃_le
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [principalSeries_norm, norm_sub_rev F f]
        linarith
    _ = ε := by ring

/-- **Strong continuity of the principal series**: `g ↦ π(g) f` is continuous for every
`f ∈ L²(ℂ)`. -/
theorem continuous_principalSeries (f : L2C) :
    Continuous fun g => principalSeries n ρ g f := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have e : (fun g => principalSeries n ρ g f) =
      (fun h => principalSeries n ρ g₀ (principalSeries n ρ h f)) ∘ (fun g => g₀⁻¹ * g) := by
    funext g
    simp only [Function.comp_apply, ← mul_apply_eq_comp,
      ← principalSeries_mul, mul_inv_cancel_left]
  rw [e]
  have h1 : ContinuousAt (fun h => principalSeries n ρ h f) 1 := by
    have := tendsto_one n ρ f
    rwa [ContinuousAt, principalSeries_one, one_apply_eq_self]
  have h2 : ContinuousAt (fun h => principalSeries n ρ g₀ (principalSeries n ρ h f)) 1 :=
    (principalSeries n ρ g₀).continuous.continuousAt.comp h1
  refine ContinuousAt.comp (f := fun g => g₀⁻¹ * g) ?_ (by fun_prop)
  simpa using h2

/-- **Joint continuity of the action** `(g, f) ↦ π(g) f` on `SL(2,ℂ) × L²(ℂ)`. -/
theorem continuous_principalSeries_action :
    Continuous fun p : SL2C × L2C => principalSeries n ρ p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, f₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ p : SL2C × L2C, ‖principalSeries n ρ p.1 p.2 - principalSeries n ρ g₀ f₀‖ ≤
      ‖p.2 - f₀‖ + ‖principalSeries n ρ p.1 f₀ - principalSeries n ρ g₀ f₀‖ := fun p => by
    have e : principalSeries n ρ p.1 p.2 - principalSeries n ρ g₀ f₀ =
        principalSeries n ρ p.1 (p.2 - f₀) +
          (principalSeries n ρ p.1 f₀ - principalSeries n ρ g₀ f₀) := by
      rw [map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (by rw [principalSeries_norm])
  refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
  have h1 : Tendsto (fun p : SL2C × L2C => ‖p.2 - f₀‖) (𝓝 (g₀, f₀)) (𝓝 0) := by
    have := ((continuous_snd.sub (continuous_const (y := f₀))).norm).tendsto (g₀, f₀)
    simpa using this
  have h2 : Tendsto (fun p : SL2C × L2C =>
      ‖principalSeries n ρ p.1 f₀ - principalSeries n ρ g₀ f₀‖) (𝓝 (g₀, f₀)) (𝓝 0) := by
    have := ((((continuous_principalSeries n ρ f₀).comp continuous_fst).sub
      (continuous_const (y := principalSeries n ρ g₀ f₀))).norm).tendsto (g₀, f₀)
    simpa using this
  simpa using h1.add h2

end Lightlike.Lorentz
