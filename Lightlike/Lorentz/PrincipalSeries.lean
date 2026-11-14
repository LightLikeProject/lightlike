module

public import Lightlike.Lorentz.Mobius

/-!
# The unitary principal series of SL(2,ℂ) on L²(ℂ)

For `k ∈ ½ℤ` (we use `n = 2k ∈ ℤ`) and `ρ ∈ ℝ` the principal-series representation `(k, ρ)`
acts on functions on `ℂ` by

  `(π(g) f)(z) = m(b z + d) · f((a z + c) / (b z + d))`,   `g = [[a, b], [c, d]]`,

with the multiplier `m(λ) = |λ|^{2iρ - 2} (λ / |λ|)^{2k}`, i.e. `m(λ) = λ^{-1+iρ+k} λ̄^{-1+iρ-k}`.
This is the affine chart `z ↦ (z, 1)` of the action `F ↦ F ∘ gᵀ` on functions on `ℂ²` that are
homogeneous of degree `(-1+iρ+k, -1+iρ-k)` (the convention of Rühl, *The Lorentz group and
harmonic analysis*, 1970, and Barrett–Dowdall–Fairbairn–Hellmann–Pereira, *Class. Quantum Grav.*
27 (2010) 165009); see `Homogeneous.lean`.

## Main results

* `mult_mul`, `mult_one`: `m` is a character of `ℂ^×`; `norm_mult`: `‖m(λ)‖ = ‖λ‖^{-2}` for real
  `ρ`, and `norm_mult_complex`: `‖m(λ)‖ = ‖λ‖^{-2 - 2 Im ρ}` in general.
* `weightedComp`: a general construction. If `T` is quasi-measure-preserving and
  `∫⁻ |c|² |f ∘ T|² = ∫⁻ |f|²` for every `f`, then `f ↦ c · (f ∘ T)` is a linear isometry of
  `L²(ℂ)`.
* `principalSeries n ρ : ContRepresentation ℂ SL2C (L²(ℂ))`, a homomorphism
  `SL(2,ℂ) → (L²(ℂ) →L[ℂ] L²(ℂ))` (`principalSeries_mul`, `principalSeries_one`).
* **Unitarity:** `principalSeries_norm` (`‖π(g) f‖ = ‖f‖`), `principalSeries_inner`
  (`⟪π(g) f, π(g) f'⟫ = ⟪f, f'⟫`) and `principalSeries_mem_unitary` (each `π(g)` is a unitary
  operator, with inverse `π(g⁻¹)`).
* **Continuity:** `continuous_principalSeries` (`g ↦ π(g) f` is continuous for every `f`, i.e. the
  representation is strongly continuous). The proof is the standard one: matrix coefficients of
  continuous compactly supported functions are continuous by dominated convergence, which gives
  continuity on a dense subspace; unitarity then extends it to all of `L²`.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace Lightlike.Lorentz

/-! ## The multiplier -/

/-- **The multiplier** `m(λ) = |λ|^{2iρ - 2} (λ / |λ|)^n` of the principal series `(k, ρ)`,
`n = 2k`. Defined for every complex `ρ` so that non-unitary parameters can be tested; the
principal series uses real `ρ`. -/
noncomputable def mult (n : ℤ) (ρ : ℂ) (w : ℂ) : ℂ :=
  ((‖w‖ : ℝ) : ℂ) ^ (2 * I * ρ - 2) * (w / ((‖w‖ : ℝ) : ℂ)) ^ n

/-- The phase `λ / |λ|` has norm one. -/
lemma norm_phase {w : ℂ} (hw : w ≠ 0) : ‖w / ((‖w‖ : ℝ) : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr hw)]

@[simp] lemma mult_one (n : ℤ) (ρ : ℂ) : mult n ρ 1 = 1 := by
  simp [mult]

/-- **The multiplier is a character** of `ℂ^×`: `m(λ μ) = m(λ) m(μ)`. -/
theorem mult_mul (n : ℤ) (ρ : ℂ) {w z : ℂ} (hw : w ≠ 0) (hz : z ≠ 0) :
    mult n ρ (w * z) = mult n ρ w * mult n ρ z := by
  have hw' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have hz' : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  simp only [mult, norm_mul, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    mul_div_mul_comm, mul_zpow]
  ring

/-- For real `ρ`, `‖m(λ)‖ = ‖λ‖⁻²`. -/
theorem norm_mult (n : ℤ) (ρ : ℝ) {w : ℂ} (hw : w ≠ 0) :
    ‖mult n ρ w‖ = (‖w‖ ^ 2)⁻¹ := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [mult, norm_mul, norm_zpow, norm_phase hw, _root_.one_zpow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have : (2 * I * (ρ : ℂ) - 2).re = -2 := by simp
  rw [this, Real.rpow_neg hpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- For complex `ρ`, `‖m(λ)‖ = ‖λ‖^{-2 - 2 Im ρ}`: unitarity fails when `Im ρ ≠ 0`. -/
theorem norm_mult_complex (n : ℤ) (ρ : ℂ) {w : ℂ} (hw : w ≠ 0) :
    ‖mult n ρ w‖ = ‖w‖ ^ (-2 - 2 * ρ.im) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [mult, norm_mul, norm_zpow, norm_phase hw, _root_.one_zpow, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 1; simp; ring

/-- The multiplier is continuous on `ℂ^×`. -/
lemma continuousAt_mult (n : ℤ) (ρ : ℂ) {w : ℂ} (hw : w ≠ 0) : ContinuousAt (mult n ρ) w := by
  have hw' : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have hnorm : Continuous fun w : ℂ => ((‖w‖ : ℝ) : ℂ) := by fun_prop
  have h1 : ContinuousAt (fun w : ℂ => ((‖w‖ : ℝ) : ℂ) ^ (2 * I * ρ - 2)) w :=
    ContinuousAt.cpow (f := fun w : ℂ => ((‖w‖ : ℝ) : ℂ)) hnorm.continuousAt continuousAt_const
      (Complex.ofReal_mem_slitPlane.mpr (norm_pos_iff.mpr hw))
  have h2 : ContinuousAt (fun w : ℂ => w / ((‖w‖ : ℝ) : ℂ)) w :=
    continuousAt_id.div hnorm.continuousAt hw'
  have h3 : ContinuousAt (fun w : ℂ => (w / ((‖w‖ : ℝ) : ℂ)) ^ n) w := by
    refine h2.zpow₀ n (Or.inl ?_)
    exact div_ne_zero hw hw'
  exact h1.mul h3

lemma measurable_mult (n : ℤ) (ρ : ℂ) : Measurable (mult n ρ) := by
  unfold mult; fun_prop

/-! ## Weighted composition operators on L²(ℂ) -/

/-- The Hilbert space `L²(ℂ)` of the principal series (Lebesgue measure on `ℂ = ℝ²`). -/
noncomputable abbrev L2C := Lp ℂ 2 (volume : Measure ℂ)

section WeightedComp

variable (c T : ℂ → ℂ) (hc : AEStronglyMeasurable c volume)
  (hT : QuasiMeasurePreserving T volume volume)
  (hiso : ∀ f : ℂ → ℂ, ∫⁻ z, ‖c z * f (T z)‖ₑ ^ (2 : ℝ) = ∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ))

include hc hT in
lemma aestronglyMeasurable_weightedComp {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun z => c z * f (T z)) volume :=
  hc.mul (hf.comp_quasiMeasurePreserving hT)

include hc hT hiso in
lemma eLpNorm_weightedComp {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun z => c z * f (T z)) 2 volume = eLpNorm f 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (aestronglyMeasurable_weightedComp c T hc hT hf),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat]
  rw [hiso f]

include hc hT hiso in
lemma memLp_weightedComp (f : L2C) : MemLp (fun z => c z * f (T z)) 2 volume := by
  rw [memLp_iff, eLpNorm_weightedComp c T hc hT hiso (Lp.aestronglyMeasurable f)]
  exact Lp.eLpNorm_lt_top f

/-- **Weighted composition** `f ↦ c · (f ∘ T)` as a linear isometry of `L²(ℂ)`. -/
noncomputable def weightedComp : L2C →ₗᵢ[ℂ] L2C where
  toFun f := (memLp_weightedComp c T hc hT hiso f).toLp _
  map_add' f f' := by
    rw [Lp.ext_iff]
    refine (MemLp.coeFn_toLp _).trans ?_
    refine EventuallyEq.symm ((Lp.coeFn_add _ _).trans ?_)
    have h1 := MemLp.coeFn_toLp (memLp_weightedComp c T hc hT hiso f)
    have h2 := MemLp.coeFn_toLp (memLp_weightedComp c T hc hT hiso f')
    have h3 := hT.ae_eq_comp (Lp.coeFn_add f f')
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    simp only [Pi.add_apply, Function.comp_apply] at hz1 hz2 hz3 ⊢
    rw [hz1, hz2, hz3, mul_add]
  map_smul' a f := by
    rw [Lp.ext_iff]
    refine (MemLp.coeFn_toLp _).trans ?_
    refine EventuallyEq.symm ((Lp.coeFn_smul _ _).trans ?_)
    have h1 := MemLp.coeFn_toLp (memLp_weightedComp c T hc hT hiso f)
    have h3 := hT.ae_eq_comp (Lp.coeFn_smul a f)
    filter_upwards [h1, h3] with z hz1 hz3
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, RingHom.id_apply] at hz1 hz3 ⊢
    rw [hz1, hz3]; ring
  norm_map' f := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp, Lp.norm_def,
      eLpNorm_weightedComp c T hc hT hiso (Lp.aestronglyMeasurable f)]

lemma coeFn_weightedComp (f : L2C) :
    weightedComp c T hc hT hiso f =ᵐ[volume] fun z => c z * f (T z) :=
  MemLp.coeFn_toLp (memLp_weightedComp c T hc hT hiso f)

end WeightedComp

/-! ## The principal series -/

/-- **The principal-series action on functions**: `(act g f)(z) = m(den g z) · f(mob g z)`. -/
noncomputable def act (n : ℤ) (ρ : ℂ) (g : SL2C) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => mult n ρ (den g z) * f (mob g z)

/-- `‖m(den g z)‖ₑ² = ‖den g z‖⁻⁴` off the pole. -/
lemma enorm_mult_den_sq (n : ℤ) (ρ : ℝ) (g : SL2C) {z : ℂ} (hz : den g z ≠ 0) :
    ‖mult n ρ (den g z)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((‖den g z‖ ^ 4)⁻¹) := by
  rw [← ofReal_norm, norm_mult n ρ hz, ENNReal.ofReal_rpow_of_nonneg (by positivity)
    zero_le_two]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring

/-- **The L² identity** behind unitarity: `∫⁻ |act g f|² = ∫⁻ |f|²` for every `f`. -/
theorem lintegral_act (n : ℤ) (ρ : ℝ) (g : SL2C) (f : ℂ → ℂ) :
    ∫⁻ z, ‖mult n ρ (den g z) * f (mob g z)‖ₑ ^ (2 : ℝ) = ∫⁻ w, ‖f w‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_mob g (fun w => ‖f w‖ₑ ^ (2 : ℝ))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_den_ne_zero g] with z hz
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, enorm_mult_den_sq n ρ g hz]

lemma aestronglyMeasurable_mult_den (n : ℤ) (ρ : ℂ) (g : SL2C) :
    AEStronglyMeasurable (fun z => mult n ρ (den g z)) volume :=
  ((measurable_mult n ρ).comp (continuous_den g).measurable).aestronglyMeasurable

/-- The operator `π(g)` as a linear isometry of `L²(ℂ)`. -/
noncomputable def piIso (n : ℤ) (ρ : ℝ) (g : SL2C) : L2C →ₗᵢ[ℂ] L2C :=
  weightedComp (fun z => mult n ρ (den g z)) (mob g) (aestronglyMeasurable_mult_den n ρ g)
    (quasiMeasurePreserving_mob g) (lintegral_act n ρ g)

lemma coeFn_piIso (n : ℤ) (ρ : ℝ) (g : SL2C) (f : L2C) :
    piIso n ρ g f =ᵐ[volume] act n ρ g f :=
  coeFn_weightedComp _ _ _ _ _ f

lemma piIso_one (n : ℤ) (ρ : ℝ) (f : L2C) : piIso n ρ 1 f = f := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_piIso n ρ 1 f] with z hz
  rw [hz]; simp [act]

lemma piIso_mul (n : ℤ) (ρ : ℝ) (g h : SL2C) (f : L2C) :
    piIso n ρ (g * h) f = piIso n ρ g (piIso n ρ h f) := by
  rw [Lp.ext_iff]
  have h1 := coeFn_piIso n ρ (g * h) f
  have h2 := coeFn_piIso n ρ g (piIso n ρ h f)
  have h3 := ae_eq_comp_mob g (coeFn_piIso n ρ h f)
  filter_upwards [h1, h2, h3, ae_den_ne_zero g, ae_den_ne_zero (g * h)] with z hz1 hz2 hz3 hg hgh
  rw [hz1, hz2]
  simp only [Function.comp_apply] at hz3
  simp only [act]
  rw [hz3]
  have hh : den h (mob g z) ≠ 0 := by
    intro h0; apply hgh; rw [den_mul g h hg, h0, mul_zero]
  simp only [act]
  rw [den_mul g h hg, mult_mul n ρ hg hh, mob_mul g h hg]; ring

/-- **The unitary principal series** `(k, ρ)` of `SL(2,ℂ)`, `n = 2k`, on `L²(ℂ)`. -/
noncomputable def principalSeries (n : ℤ) (ρ : ℝ) : ContRepresentation ℂ SL2C L2C :=
  .ofMonoidHom
    { toFun := fun g => (piIso n ρ g).toContinuousLinearMap
      map_one' := by ext1 f; exact piIso_one n ρ f
      map_mul' := fun g h => by ext1 f; exact piIso_mul n ρ g h f }

lemma principalSeries_apply (n : ℤ) (ρ : ℝ) (g : SL2C) (f : L2C) :
    principalSeries n ρ g f = piIso n ρ g f := rfl

/-- The principal series acts by the explicit formula, almost everywhere. -/
theorem coeFn_principalSeries (n : ℤ) (ρ : ℝ) (g : SL2C) (f : L2C) :
    principalSeries n ρ g f =ᵐ[volume] fun z => mult n ρ (den g z) * f (mob g z) :=
  coeFn_piIso n ρ g f

/-- `π(g h) = π(g) π(h)`. -/
theorem principalSeries_mul (n : ℤ) (ρ : ℝ) (g h : SL2C) :
    principalSeries n ρ (g * h) = principalSeries n ρ g * principalSeries n ρ h :=
  map_mul _ g h

/-- `π(1) = 1`. -/
theorem principalSeries_one (n : ℤ) (ρ : ℝ) : principalSeries n ρ 1 = 1 :=
  map_one _

/-- **Unitarity (norm form):** `‖π(g) f‖ = ‖f‖`. -/
theorem principalSeries_norm (n : ℤ) (ρ : ℝ) (g : SL2C) (f : L2C) :
    ‖principalSeries n ρ g f‖ = ‖f‖ :=
  (piIso n ρ g).norm_map f

/-- **Unitarity:** `π(g)` preserves the inner product of `L²(ℂ)`. -/
theorem principalSeries_inner (n : ℤ) (ρ : ℝ) (g : SL2C) (f f' : L2C) :
    ⟪principalSeries n ρ g f, principalSeries n ρ g f'⟫_ℂ = ⟪f, f'⟫_ℂ :=
  (piIso n ρ g).inner_map_map f f'

/-- **Each `π(g)` is a unitary operator** (an invertible isometry, inverse `π(g⁻¹)`). -/
theorem principalSeries_mem_unitary (n : ℤ) (ρ : ℝ) (g : SL2C) :
    principalSeries n ρ g ∈ unitary (L2C →L[ℂ] L2C) := by
  have hinv : principalSeries n ρ g * principalSeries n ρ g⁻¹ = 1 := by
    rw [← principalSeries_mul, mul_inv_cancel, principalSeries_one]
  have hinv' : principalSeries n ρ g⁻¹ * principalSeries n ρ g = 1 := by
    rw [← principalSeries_mul, inv_mul_cancel, principalSeries_one]
  have hstar : ContinuousLinearMap.adjoint (principalSeries n ρ g) * principalSeries n ρ g = 1 := by
    ext1 f
    refine ext_inner_left ℂ fun f' => ?_
    rw [mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,
      one_apply_eq_self, principalSeries_inner]
  have hadj : ContinuousLinearMap.adjoint (principalSeries n ρ g) = principalSeries n ρ g⁻¹ := by
    calc ContinuousLinearMap.adjoint (principalSeries n ρ g)
        = ContinuousLinearMap.adjoint (principalSeries n ρ g) *
            (principalSeries n ρ g * principalSeries n ρ g⁻¹) := by rw [hinv, mul_one]
      _ = principalSeries n ρ g⁻¹ := by rw [← mul_assoc, hstar, one_mul]
  rw [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, hadj]
  exact ⟨hinv', hinv⟩

end Lightlike.Lorentz
