module

public import Mathlib

/-!
# Weighted composition operators on `L²(μ)` and unitary representations

Two general constructions used by the representations of `SL(2,ℝ)` (milestone HA3); the
`SL(2,ℂ)` file `PrincipalSeries.lean` has the special case `L²(ℂ)`.

* `weightedCompL2 μ c T …`: if `T : X → X` is quasi-measure-preserving and
  `∫⁻ |c|² |f ∘ T|² dμ = ∫⁻ |f|² dμ` for every measurable `f`, then `f ↦ c · (f ∘ T)` is a linear
  isometry of `L²(μ)`.
* `mem_unitary_of_inner`: in a representation by inner-product-preserving operators on a complex
  Hilbert space, every `π(g)` is a unitary operator, with inverse and adjoint `π(g⁻¹)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Lightlike.Lorentz

section WeightedComp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  (c : X → ℂ) (T : X → X) (hc : AEStronglyMeasurable c μ) (hT : QuasiMeasurePreserving T μ μ)
  (hiso : ∀ f : X → ℂ, Measurable f →
    ∫⁻ x, ‖c x * f (T x)‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂μ)

include hc hT in
lemma aestronglyMeasurable_weightedCompL2 {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => c x * f (T x)) μ :=
  hc.mul (hf.comp_quasiMeasurePreserving hT)

include hc hT hiso in
lemma eLpNorm_weightedCompL2 {f : X → ℂ} (hf : Measurable f) :
    eLpNorm (fun x => c x * f (T x)) 2 μ = eLpNorm f 2 μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (aestronglyMeasurable_weightedCompL2 μ c T hc hT hf.aestronglyMeasurable),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  rw [hiso f hf]

include hc hT hiso in
lemma memLp_weightedCompL2 (f : Lp ℂ 2 μ) : MemLp (fun x => c x * f (T x)) 2 μ := by
  rw [memLp_iff, eLpNorm_weightedCompL2 μ c T hc hT hiso (Lp.stronglyMeasurable f).measurable]
  exact Lp.eLpNorm_lt_top f

/-- **Weighted composition** `f ↦ c · (f ∘ T)` as a linear isometry of `L²(μ)`. -/
def weightedCompL2 : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_weightedCompL2 μ c T hc hT hiso f).toLp _
  map_add' f f' := by
    rw [Lp.ext_iff]
    refine (MemLp.coeFn_toLp _).trans ?_
    refine EventuallyEq.symm ((Lp.coeFn_add _ _).trans ?_)
    have h1 := MemLp.coeFn_toLp (memLp_weightedCompL2 μ c T hc hT hiso f)
    have h2 := MemLp.coeFn_toLp (memLp_weightedCompL2 μ c T hc hT hiso f')
    have h3 := hT.ae_eq_comp (Lp.coeFn_add f f')
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    simp only [Pi.add_apply, Function.comp_apply] at hz1 hz2 hz3 ⊢
    rw [hz1, hz2, hz3, mul_add]
  map_smul' a f := by
    rw [Lp.ext_iff]
    refine (MemLp.coeFn_toLp _).trans ?_
    refine EventuallyEq.symm ((Lp.coeFn_smul _ _).trans ?_)
    have h1 := MemLp.coeFn_toLp (memLp_weightedCompL2 μ c T hc hT hiso f)
    have h3 := hT.ae_eq_comp (Lp.coeFn_smul a f)
    filter_upwards [h1, h3] with z hz1 hz3
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, RingHom.id_apply] at hz1 hz3 ⊢
    rw [hz1, hz3]; ring
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp, Lp.norm_def,
      eLpNorm_weightedCompL2 μ c T hc hT hiso (Lp.stronglyMeasurable f).measurable]

lemma coeFn_weightedCompL2 (f : Lp ℂ 2 μ) :
    weightedCompL2 μ c T hc hT hiso f =ᵐ[μ] fun x => c x * f (T x) :=
  MemLp.coeFn_toLp (memLp_weightedCompL2 μ c T hc hT hiso f)

end WeightedComp

/-- **Unitarity from isometry**: in a representation of a group by operators that preserve the
inner product of a complex Hilbert space, each `π(g)` is a unitary operator. -/
theorem mem_unitary_of_inner {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : ContRepresentation ℂ G H)
    (hπ : ∀ g f f', ⟪π g f, π g f'⟫_ℂ = ⟪f, f'⟫_ℂ) (g : G) :
    π g ∈ unitary (H →L[ℂ] H) := by
  have hinv : π g * π g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : π g⁻¹ * π g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hstar : ContinuousLinearMap.adjoint (π g) * π g = 1 := by
    ext1 f
    refine ext_inner_left ℂ fun f' => ?_
    rw [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,
      one_apply_eq_self, hπ]
  have hadj : ContinuousLinearMap.adjoint (π g) = π g⁻¹ := by
    calc ContinuousLinearMap.adjoint (π g)
        = ContinuousLinearMap.adjoint (π g) * (π g * π g⁻¹) := by rw [hinv, mul_one]
      _ = π g⁻¹ := by rw [← mul_assoc, hstar, one_mul]
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, hadj]
  exact ⟨hinv', hinv⟩

/-! ### Strong continuity from continuous matrix coefficients -/

section StrongContinuity

variable {G H : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : ContRepresentation ℂ G H)
  (hnorm : ∀ g f, ‖π g f‖ = ‖f‖)

include hnorm in
/-- In an isometric representation, `π(g) φ → φ` as `g → 1` as soon as the diagonal matrix
coefficient `g ↦ ⟪π(g) φ, φ⟫` is continuous at `1`, since
`‖π(g) φ - φ‖² = 2‖φ‖² - 2 Re ⟪π(g) φ, φ⟫`. -/
theorem tendsto_one_of_coeff {φ : H} (hcoef : ContinuousAt (fun g => ⟪π g φ, φ⟫_ℂ) 1) :
    Tendsto (fun g => π g φ) (𝓝 1) (𝓝 φ) := by
  have hval : ⟪π 1 φ, φ⟫_ℂ = ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K]; norm_cast
  have hre : Tendsto (fun g => RCLike.re ⟪π g φ, φ⟫_ℂ) (𝓝 1) (𝓝 (‖φ‖ ^ 2)) := by
    have := (RCLike.continuous_re.tendsto _).comp hcoef.tendsto
    rw [hval, RCLike.re_to_complex, Complex.ofReal_re] at this
    exact this
  have hsq : Tendsto (fun g => ‖π g φ - φ‖ ^ 2) (𝓝 1) (𝓝 0) := by
    have e : ∀ g, ‖π g φ - φ‖ ^ 2 = 2 * ‖φ‖ ^ 2 - 2 * RCLike.re ⟪π g φ, φ⟫_ℂ := fun g => by
      rw [@norm_sub_sq ℂ, hnorm]; ring
    simp only [e]
    have := (tendsto_const_nhds (x := 2 * ‖φ‖ ^ 2)).sub (hre.const_mul 2)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun g => ?_
  simp [Real.sqrt_sq (norm_nonneg _)]

include hnorm in
/-- **Strong continuity from a dense set of continuous coefficients**: if `π` is isometric and
`g ↦ ⟪π(g) φ, φ⟫` is continuous at `1` for all `φ` in a dense set, then `g ↦ π(g) f` is
continuous for every `f` (an `ε/3` argument, then translation). -/
theorem continuous_of_dense_coeff [IsTopologicalGroup G] {D : Set H} (hD : Dense D)
    (hcoef : ∀ φ ∈ D, ContinuousAt (fun g => ⟪π g φ, φ⟫_ℂ) 1) (f : H) :
    Continuous fun g => π g f := by
  have h1 : Tendsto (fun g => π g f) (𝓝 1) (𝓝 f) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    have hη3 : 0 < η / 3 := by positivity
    obtain ⟨φ, hφD, hfφ⟩ := hD.exists_dist_lt f hη3
    rw [dist_eq_norm] at hfφ
    have hev := (Metric.tendsto_nhds.mp (tendsto_one_of_coeff π hnorm (hcoef φ hφD))) _ hη3
    filter_upwards [hev] with g hg
    rw [dist_eq_norm] at hg ⊢
    have e : π g f - f = π g (f - φ) + (π g φ - φ) + (φ - f) := by rw [map_sub]; abel
    rw [e]
    calc ‖π g (f - φ) + (π g φ - φ) + (φ - f)‖
        ≤ ‖π g (f - φ)‖ + ‖π g φ - φ‖ + ‖φ - f‖ := norm_add₃_le
      _ < η / 3 + η / 3 + η / 3 := by
          rw [hnorm, norm_sub_rev φ f]
          linarith
      _ = η := by ring
  rw [continuous_iff_continuousAt]
  intro g₀
  have e : (fun g => π g f) = (fun h => π g₀ (π h f)) ∘ (fun g => g₀⁻¹ * g) := by
    funext g
    simp only [Function.comp_apply, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left]
  rw [e]
  have h1' : ContinuousAt (fun h => π h f) 1 := by
    rwa [ContinuousAt, map_one, one_apply_eq_self]
  have h2 : ContinuousAt (fun h => π g₀ (π h f)) 1 :=
    (π g₀).continuous.continuousAt.comp h1'
  refine ContinuousAt.comp (f := fun g => g₀⁻¹ * g) ?_ (by fun_prop)
  simpa using h2

include hnorm in
/-- **Joint continuity**: an isometric, strongly continuous representation has a jointly
continuous action `(g, f) ↦ π(g) f`. -/
theorem continuous_action_of_norm (hc : ∀ f, Continuous fun g => π g f) :
    Continuous fun p : G × H => π p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g₀, f₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ p : G × H, ‖π p.1 p.2 - π g₀ f₀‖ ≤ ‖p.2 - f₀‖ + ‖π p.1 f₀ - π g₀ f₀‖ := fun p => by
    have e : π p.1 p.2 - π g₀ f₀ = π p.1 (p.2 - f₀) + (π p.1 f₀ - π g₀ f₀) := by
      rw [map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (by rw [hnorm])
  refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
  have h1 : Tendsto (fun p : G × H => ‖p.2 - f₀‖) (𝓝 (g₀, f₀)) (𝓝 0) := by
    have := ((continuous_snd.sub (continuous_const (y := f₀))).norm).tendsto (g₀, f₀)
    simpa using this
  have h2 : Tendsto (fun p : G × H => ‖π p.1 f₀ - π g₀ f₀‖) (𝓝 (g₀, f₀)) (𝓝 0) := by
    have := ((((hc f₀).comp continuous_fst).sub
      (continuous_const (y := π g₀ f₀))).norm).tendsto (g₀, f₀)
    simpa using this
  simpa using h1.add h2

end StrongContinuity

/-- **Density of continuous compactly supported functions** in `L²(μ)` for a regular measure on a
locally compact space, as a set of classes. -/
theorem dense_hasCompactSupport_L2 {X : Type*} [TopologicalSpace X] [NormalSpace X] [R1Space X]
    [WeaklyLocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [μ.Regular] :
    Dense {F : Lp ℂ 2 μ | ∃ φ : X → ℂ, Continuous φ ∧ HasCompactSupport φ ∧ F =ᵐ[μ] φ} := by
  rw [Metric.dense_iff]
  intro f r hr
  have hr2 : 0 < r / 2 := by positivity
  obtain ⟨φ, hφc, hφnorm, hφ, hφ2⟩ :=
    (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top
      (ENNReal.ofReal_pos.mpr hr2).ne'
  refine ⟨hφ2.toLp φ, ?_, φ, hφ, hφc, MemLp.coeFn_toLp hφ2⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm, Lp.norm_def]
  have : eLpNorm (⇑(f - hφ2.toLp φ)) 2 μ = eLpNorm (⇑f - φ) 2 μ := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub f (hφ2.toLp φ), MemLp.coeFn_toLp hφ2] with x hx1 hx2
    rw [hx1, Pi.sub_apply, hx2, Pi.sub_apply]
  rw [this]
  calc (eLpNorm (⇑f - φ) 2 μ).toReal ≤ (ENNReal.ofReal (r / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hφnorm
    _ = r / 2 := ENNReal.toReal_ofReal hr2.le
    _ < r := by linarith

end Lightlike.Lorentz
