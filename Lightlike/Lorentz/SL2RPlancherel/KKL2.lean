import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.KKParseval
import Lightlike.Lorentz.SL2RPlancherel.SphericalL2

/-!
# The `K × K` decomposition of `L²(SL(2,ℝ))`

The `K × K`-Fourier components `kkCoeff f m` of a continuous square-integrable `f` lie in
`L²((0, ∞), sinh ξ dξ)`, presented as `√(sinh ξ) f_m(ξ)` in `L²(0, ∞)` (`kkSrc`), and
`‖f‖² = (2π)² ∑_m ‖f_m‖²` (`lintegral_norm_sq_eq_kk`).  This file builds the extension of
`f ↦ (f_m)_m` to all of `L²(SL(2,ℝ))`: the linear isometry `kkIso` into the Hilbert sum
`ℓ²(ℤ², L²(0, ∞))` and its components `kkL2 F m`, with `kkL2 (toLp f) m = √(sinh ξ) f_m(ξ)` for
continuous square-integrable `f` (`kkL2_toLp_ae`), Parseval `‖F‖² = (2π)² ∑_m ‖kkL2 F m‖²`
(`norm_sq_eq_tsum_kkL2`) and its polarisation (`inner_eq_tsum_kkL2`).  The continuous
square-integrable functions are dense (`denseRange_kkE`, from the regularity of the Haar measure).
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (the
first step of the assembly), milestone HA3.
-/

open MeasureTheory Set Real Filter Topology Lightlike.Lorentz.SL2R
open scoped ContDiff ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The box `(0, 1]²` is almost everywhere the closed box `[0, 1]²`. -/
lemma box_ae_eq_Icc : box =ᵐ[volume] Icc (0 : Fin 2 → ℝ) 1 := by
  have h : box = Set.pi univ fun _ : Fin 2 => Ioc (0 : ℝ) 1 := by
    ext x; simp [box, Set.mem_pi]
  rw [h, volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ => (volume : Measure ℝ))
    (f := fun _ => (0 : ℝ)) (g := fun _ => (1 : ℝ))

/-- The `K × K` components of a continuous function are continuous in the radius. -/
lemma continuous_kkCoeff {f : SL2R → ℂ} (hf : Continuous f) (n : Fin 2 → ℤ) :
    Continuous (kkCoeff f n) := by
  have hfun : kkCoeff f n = fun ξ => ∫ x in Icc (0 : Fin 2 → ℝ) 1,
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) * kkProfile f ξ x :=
    funext fun ξ => setIntegral_congr_set box_ae_eq_Icc
  rw [hfun]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  have h1 : Continuous fun p : ℝ × (Fin 2 → ℝ) =>
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * ((p.2 i : ℝ) : ℂ))) := by fun_prop
  have h2 : Continuous fun p : ℝ × (Fin 2 → ℝ) =>
      f (rot (2 * π * p.2 0) * aR p.1 * rot (2 * π * p.2 1)) := by
    refine hf.comp (((continuous_rot.comp ?_).mul (continuous_aR.comp continuous_fst)).mul
      (continuous_rot.comp ?_)) <;> fun_prop
  exact h1.mul h2

/-- The `K × K` component as a vector of `L²(0, ∞)`: `√(sinh ξ) f_m(ξ)`. -/
def kkSrc (f : SL2R → ℂ) (m : Fin 2 → ℤ) (ξ : ℝ) : ℂ :=
  ((Real.sqrt (Real.sinh ξ) : ℝ) : ℂ) * kkCoeff f m ξ

lemma summable_kkCoeff {f : SL2R → ℂ} (hf : Continuous f) (ξ : ℝ) :
    Summable fun n : Fin 2 → ℤ => ‖kkCoeff f n ξ‖ ^ 2 :=
  (hasSum_sq_box (continuous_kkProfile hf ξ)).summable

lemma norm_sq_kkSrc (f : SL2R → ℂ) (m : Fin 2 → ℤ) {ξ : ℝ} (hξ : 0 < ξ) :
    ‖kkSrc f m ξ‖ ^ 2 = Real.sinh ξ * ‖kkCoeff f m ξ‖ ^ 2 := by
  rw [kkSrc, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (Real.sinh_pos_iff.2 hξ).le]

lemma continuous_kkSrc {f : SL2R → ℂ} (hf : Continuous f) (m : Fin 2 → ℤ) :
    Continuous (kkSrc f m) :=
  (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_sinh)).mul
    (continuous_kkCoeff hf m)

/-- The square integral of a square-integrable function as an `ENNReal` integral. -/
lemma lintegral_norm_sq_lt_top {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) :
    ∫⁻ g, ENNReal.ofReal (‖f g‖ ^ 2) ∂haarR < ⊤ := by
  have hi := (memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).1 hf
  have := hi.2
  rw [HasFiniteIntegral] at this
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun g => ?_)) this
  rw [Real.enorm_of_nonneg (by positivity)]

/-- **The summed components**: `∫₀^∞ sinh ξ · ∑_m |f_m(ξ)|²` is finite and
`(2π)² ∫₀^∞ sinh ξ ∑_m |f_m(ξ)|² dξ = ∫ |f|² d haarR`, in `ENNReal`. -/
lemma lintegral_tsum_kkSrc {f : SL2R → ℂ} (hfc : Continuous f) :
    ENNReal.ofReal ((2 * π) ^ 2) *
      ∑' m : Fin 2 → ℤ, ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) =
      ∫⁻ g, ENNReal.ofReal (‖f g‖ ^ 2) ∂haarR := by
  have hm : ∀ m, Measurable fun ξ => ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) := fun m =>
    ((continuous_kkSrc hfc m).norm.pow 2).measurable.ennreal_ofReal
  have hmt : Measurable fun ξ => ∑' m, ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) :=
    Measurable.ennreal_tsum hm
  rw [lintegral_norm_sq_eq_kk hfc, ← lintegral_tsum fun m => (hm m).aemeasurable,
    ← lintegral_const_mul _ hmt]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
  simp only [norm_sq_kkSrc f _ hξ]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (Real.sinh_pos_iff.2 hξ).le (sq_nonneg _))
    ((summable_kkCoeff hfc ξ).mul_left _), tsum_mul_left, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (Real.sinh_pos_iff.2 hξ).le]
  congr 1
  ring

/-- The continuous square-integrable functions on `SL(2,ℝ)`. -/
def contL2 : Submodule ℂ (SL2R → ℂ) where
  carrier := {f | Continuous f ∧ MemLp f 2 haarR}
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨continuous_const, MemLp.zero⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, hf.2.const_smul c⟩

lemma integrableOn_box_kk {f : SL2R → ℂ} (hf : Continuous f) (n : Fin 2 → ℤ) (ξ : ℝ) :
    IntegrableOn (fun x : Fin 2 → ℝ => Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) *
      kkProfile f ξ x) box := by
  have hc : Continuous fun x : Fin 2 → ℝ =>
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ))) * kkProfile f ξ x :=
    (by fun_prop : Continuous fun x : Fin 2 → ℝ =>
      Complex.exp (-(2 * π * Complex.I * ∑ i, (n i : ℂ) * (x i : ℂ)))).mul (continuous_kkProfile hf ξ)
  refine (hc.continuousOn.integrableOn_compact isCompact_Icc (μ := volume)
    (K := Icc (0 : Fin 2 → ℝ) 1)).mono_set ?_
  intro x hx
  exact ⟨fun i => (hx i).1.le, fun i => by simpa using (hx i).2⟩

lemma kkCoeff_add {f g : SL2R → ℂ} (hf : Continuous f) (hg : Continuous g) (n : Fin 2 → ℤ) (ξ : ℝ) :
    kkCoeff (f + g) n ξ = kkCoeff f n ξ + kkCoeff g n ξ := by
  simp only [kkCoeff, kkProfile, Pi.add_apply, mul_add]
  exact integral_add (integrableOn_box_kk hf n ξ) (integrableOn_box_kk hg n ξ)

lemma kkCoeff_smul (c : ℂ) (f : SL2R → ℂ) (n : Fin 2 → ℤ) (ξ : ℝ) :
    kkCoeff (c • f) n ξ = c * kkCoeff f n ξ := by
  simp only [kkCoeff, kkProfile, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

/-- The summed components are finite for a square-integrable continuous function. -/
lemma tsum_lintegral_kkSrc_lt_top {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) :
    ∑' m : Fin 2 → ℤ, ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) < ⊤ := by
  have h := lintegral_tsum_kkSrc hfc
  have hlt := lintegral_norm_sq_lt_top hfc hf
  rw [← h] at hlt
  have hne : ENNReal.ofReal ((2 * π) ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]; positivity
  exact ENNReal.lt_top_of_mul_ne_top_right hlt.ne hne

theorem memLp_kkSrc {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) (m : Fin 2 → ℤ) :
    MemLp (kkSrc f m) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_kkSrc hfc m).aestronglyMeasurable]
  refine ⟨((continuous_kkSrc hfc m).norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ ξ in Ioi (0 : ℝ), ‖‖kkSrc f m ξ‖ ^ 2‖ₑ
      = ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) :=
        lintegral_congr fun ξ => Real.enorm_of_nonneg (by positivity)
    _ ≤ ∑' m' : Fin 2 → ℤ, ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m' ξ‖ ^ 2) :=
        ENNReal.le_tsum (f := fun m' => ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m' ξ‖ ^ 2)) m
    _ < ⊤ := tsum_lintegral_kkSrc_lt_top hfc hf

/-- `L²(0, ∞)`. -/
abbrev L2Ioi := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- The Hilbert sum `ℓ²(ℤ², L²(0, ∞))` of the `K × K` blocks. -/
abbrev KKSpace := lp (fun _ : Fin 2 → ℤ => L2Ioi) 2

lemma norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℂ} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ ξ, ‖g ξ‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp, hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  norm_num

lemma kkSrc_add {f g : SL2R → ℂ} (hf : Continuous f) (hg : Continuous g) (m : Fin 2 → ℤ) :
    kkSrc (f + g) m = kkSrc f m + kkSrc g m := by
  funext ξ; simp only [kkSrc, Pi.add_apply, kkCoeff_add hf hg, mul_add]

lemma kkSrc_smul (c : ℂ) (f : SL2R → ℂ) (m : Fin 2 → ℤ) :
    kkSrc (c • f) m = c • kkSrc f m := by
  funext ξ; simp only [kkSrc, Pi.smul_apply, smul_eq_mul, kkCoeff_smul]; ring

/-- The block vector `2π (√(sinh ξ) f_m(ξ))_m` of a continuous square-integrable `f`. -/
def kkVecFun (f : contL2) : ∀ _ : Fin 2 → ℤ, L2Ioi := fun m =>
  ((2 * π : ℝ) : ℂ) • (memLp_kkSrc f.2.1 f.2.2 m).toLp (kkSrc f m)

lemma norm_sq_kkVecFun (f : contL2) (m : Fin 2 → ℤ) :
    ‖kkVecFun f m‖ ^ 2 = (2 * π) ^ 2 *
      (∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2)).toReal := by
  have hm : AEStronglyMeasurable (fun ξ => ‖kkSrc f m ξ‖ ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
    ((continuous_kkSrc f.2.1 m).norm.pow 2).aestronglyMeasurable
  rw [kkVecFun, norm_smul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    norm_toLp_sq, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => by positivity) hm]

lemma memℓp_kkVecFun (f : contL2) : Memℓp (kkVecFun f) 2 := by
  refine memℓp_gen ?_
  have h : ∀ m, ‖kkVecFun f m‖ ^ (2 : ℝ≥0∞).toReal = (2 * π) ^ 2 *
      (∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2)).toReal := fun m => by
    rw [ENNReal.toReal_ofNat, Real.rpow_two, norm_sq_kkVecFun]
  simp_rw [h]
  exact (ENNReal.summable_toReal (tsum_lintegral_kkSrc_lt_top f.2.1 f.2.2).ne).mul_left _

lemma kkVecFun_add (f g : contL2) : kkVecFun (f + g) = kkVecFun f + kkVecFun g := by
  funext m
  have e : (memLp_kkSrc (f + g).2.1 (f + g).2.2 m).toLp (kkSrc ((f + g : contL2) : SL2R → ℂ) m) =
      (memLp_kkSrc f.2.1 f.2.2 m).toLp (kkSrc f m) + (memLp_kkSrc g.2.1 g.2.2 m).toLp (kkSrc g m) := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (kkSrc_add f.2.1 g.2.1 m))
  simp only [kkVecFun, Pi.add_apply]
  rw [e, smul_add]

lemma kkVecFun_smul (c : ℂ) (f : contL2) : kkVecFun (c • f) = c • kkVecFun f := by
  funext m
  have e : (memLp_kkSrc (c • f).2.1 (c • f).2.2 m).toLp (kkSrc ((c • f : contL2) : SL2R → ℂ) m) =
      c • (memLp_kkSrc f.2.1 f.2.2 m).toLp (kkSrc f m) := by
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (kkSrc_smul c f m))
  simp only [kkVecFun, Pi.smul_apply]
  rw [e, smul_comm]

/-- The block map on continuous square-integrable functions. -/
def kkF : contL2 →ₗ[ℂ] KKSpace where
  toFun f := ⟨kkVecFun f, memℓp_kkVecFun f⟩
  map_add' f g := lp.ext (kkVecFun_add f g)
  map_smul' c f := lp.ext (kkVecFun_smul c f)

lemma kkF_apply (f : contL2) (m : Fin 2 → ℤ) : (kkF f : ∀ _ : Fin 2 → ℤ, L2Ioi) m = kkVecFun f m := rfl

/-- The embedding of the continuous square-integrable functions into `L²(SL(2,ℝ))`. -/
def kkE : contL2 →ₗ[ℂ] Lp ℂ 2 haarR where
  toFun f := f.2.2.toLp f
  map_add' f g := (MemLp.toLp_add f.2.2 g.2.2).symm ▸ rfl
  map_smul' c f := MemLp.toLp_const_smul c f.2.2

/-- **The block map is isometric** (`lintegral_norm_sq_eq_kk`). -/
lemma kkE_apply (f : contL2) : kkE f = f.2.2.toLp f := rfl

theorem norm_kkF (f : contL2) : ‖kkF f‖ = ‖kkE f‖ := by
  have hn : ‖kkF f‖ ^ 2 = ∑' m, ‖kkVecFun f m‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (kkF f)
    rw [ENNReal.toReal_ofNat] at h
    simp only [Real.rpow_two, kkF_apply] at h
    exact h
  have hfin : ∀ m, ∫⁻ ξ in Ioi (0 : ℝ), ENNReal.ofReal (‖kkSrc f m ξ‖ ^ 2) ≠ ⊤ := fun m =>
    (lt_of_le_of_lt (ENNReal.le_tsum (f := fun m' => ∫⁻ ξ in Ioi (0 : ℝ),
      ENNReal.ofReal (‖kkSrc f m' ξ‖ ^ 2)) m) (tsum_lintegral_kkSrc_lt_top f.2.1 f.2.2)).ne
  have he : ‖kkE f‖ ^ 2 = ∫ g, ‖(f : SL2R → ℂ) g‖ ^ 2 ∂haarR := by
    rw [kkE_apply, norm_toLp_sq]
  have hmf : AEStronglyMeasurable (fun g => ‖(f : SL2R → ℂ) g‖ ^ 2) haarR :=
    (f.2.1.norm.pow 2).aestronglyMeasurable
  have hpos : (0 : ℝ) ≤ (2 * π) ^ 2 := by positivity
  have h1 : ‖kkF f‖ ^ 2 = ‖kkE f‖ ^ 2 := by
    rw [hn, tsum_congr (norm_sq_kkVecFun f), tsum_mul_left, ← ENNReal.tsum_toReal_eq hfin, he,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => by positivity) hmf,
      ← lintegral_tsum_kkSrc f.2.1, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- The continuous square-integrable functions are dense in `L²(SL(2,ℝ))`. -/
theorem denseRange_kkE : DenseRange kkE := by
  have hd := MeasureTheory.Lp.boundedContinuousFunction_dense ℂ haarR (p := 2) (by norm_num)
  refine hd.mono ?_
  intro F hF
  obtain ⟨g, hg⟩ := MeasureTheory.Lp.mem_boundedContinuousFunction_iff.1 hF
  have hae : (F : SL2R → ℂ) =ᵐ[haarR] g := by
    have h1 := ContinuousMap.coeFn_toAEEqFun haarR g.toContinuousMap
    rw [hg] at h1
    exact h1
  have hmem : MemLp (g : SL2R → ℂ) 2 haarR := (Lp.memLp F).ae_eq hae
  refine ⟨⟨g, g.continuous, hmem⟩, ?_⟩
  show hmem.toLp g = F
  rw [← Lp.toLp_coeFn F (Lp.memLp F)]
  exact MemLp.toLp_congr _ _ hae.symm

/-- **The `K × K` isometry** `L²(SL(2,ℝ)) → ℓ²(ℤ², L²(0, ∞))`: the extension of
`f ↦ 2π (√(sinh ξ) f_m(ξ))_m`. -/
def kkIso : Lp ℂ 2 haarR →ₗᵢ[ℂ] KKSpace :=
  LinearMap.extendOfIsometry kkF denseRange_kkE norm_kkF

/-- On continuous square-integrable functions, `kkIso` is the block map. -/
theorem kkIso_apply (f : contL2) : kkIso (kkE f) = kkF f :=
  LinearMap.extendOfIsometry_eq kkF denseRange_kkE norm_kkF f

/-- **The `K × K` components of an `L²` function**: `kkL2 F m ∈ L²(0, ∞)`, the class of
`√(sinh ξ) F_m(ξ)`. -/
def kkL2 : Lp ℂ 2 haarR →ₗ[ℂ] (Fin 2 → ℤ) → L2Ioi where
  toFun F m := (((2 * π : ℝ) : ℂ))⁻¹ • (kkIso F : ∀ _ : Fin 2 → ℤ, L2Ioi) m
  map_add' F G := by funext m; simp [map_add, smul_add]
  map_smul' c F := by funext m; simp [map_smul, smul_comm c]

/-- **Agreement**: on a continuous square-integrable `f`, `kkL2` is the class of
`√(sinh ξ) f_m(ξ)`. -/
theorem kkL2_toLp {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) (m : Fin 2 → ℤ) :
    kkL2 (hf.toLp f) m = (memLp_kkSrc hfc hf m).toLp (kkSrc f m) := by
  have h := kkIso_apply ⟨f, hfc, hf⟩
  show (((2 * π : ℝ) : ℂ))⁻¹ • (kkIso (kkE ⟨f, hfc, hf⟩) : ∀ _ : Fin 2 → ℤ, L2Ioi) m = _
  rw [h]
  show (((2 * π : ℝ) : ℂ))⁻¹ • kkVecFun ⟨f, hfc, hf⟩ m = _
  rw [kkVecFun, smul_smul, inv_mul_cancel₀ (by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)),
    one_smul]

/-- **Agreement**, almost everywhere: `kkL2 (toLp f) m = √(sinh ξ) f_m(ξ)` for almost every
`ξ > 0`. -/
theorem kkL2_toLp_ae {f : SL2R → ℂ} (hfc : Continuous f) (hf : MemLp f 2 haarR) (m : Fin 2 → ℤ) :
    (kkL2 (hf.toLp f) m : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] kkSrc f m := by
  rw [kkL2_toLp hfc hf m]
  exact MemLp.coeFn_toLp _

/-- **Parseval for the `K × K` decomposition of `L²(SL(2,ℝ))`**:
`‖F‖² = (2π)² ∑_m ‖kkL2 F m‖²`. -/
theorem norm_sq_eq_tsum_kkL2 (F : Lp ℂ 2 haarR) :
    ‖F‖ ^ 2 = (2 * π) ^ 2 * ∑' m : Fin 2 → ℤ, ‖kkL2 F m‖ ^ 2 := by
  have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (kkIso F)
  rw [ENNReal.toReal_ofNat, Real.rpow_two, kkIso.norm_map] at hn
  rw [hn, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  show ‖(kkIso F : ∀ _ : Fin 2 → ℤ, L2Ioi) m‖ ^ (2 : ℝ) =
    (2 * π) ^ 2 * ‖(((2 * π : ℝ) : ℂ))⁻¹ • (kkIso F : ∀ _ : Fin 2 → ℤ, L2Ioi) m‖ ^ 2
  rw [Real.rpow_two, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    mul_pow]
  field_simp

/-- **Polarised Parseval**: `⟪G, F⟫ = (2π)² ∑_m ⟪kkL2 G m, kkL2 F m⟫`. -/
theorem inner_eq_tsum_kkL2 (G F : Lp ℂ 2 haarR) :
    inner ℂ G F = ((2 * π : ℝ) : ℂ) ^ 2 * ∑' m : Fin 2 → ℤ, inner ℂ (kkL2 G m) (kkL2 F m) := by
  rw [← kkIso.inner_map_map, lp.inner_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  show inner ℂ ((kkIso G : ∀ _ : Fin 2 → ℤ, L2Ioi) m) ((kkIso F : ∀ _ : Fin 2 → ℤ, L2Ioi) m) =
    ((2 * π : ℝ) : ℂ) ^ 2 * inner ℂ ((((2 * π : ℝ) : ℂ))⁻¹ • (kkIso G : ∀ _ : Fin 2 → ℤ, L2Ioi) m)
      ((((2 * π : ℝ) : ℂ))⁻¹ • (kkIso F : ∀ _ : Fin 2 → ℤ, L2Ioi) m)
  rw [inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal]
  have hne : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  field_simp

/-- Non-vacuity: Parseval for the zero class. -/
example : ‖(0 : Lp ℂ 2 haarR)‖ ^ 2 = (2 * π) ^ 2 * ∑' m : Fin 2 → ℤ, ‖kkL2 0 m‖ ^ 2 :=
  norm_sq_eq_tsum_kkL2 0

end Lightlike.Lorentz.SL2RPlancherel
