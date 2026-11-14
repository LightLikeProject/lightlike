module

public import Lightlike.Lorentz.HaarChart

/-!
# The radial formula for the Haar measure of SL(2,ℂ)

For `g ∈ SL(2,ℂ)` let `coshDist g = ‖g‖²_F / 2`, half the sum of the squared moduli of its
entries. In the Cartan decomposition `g = u · diag(e^{r/2}, e^{-r/2}) · v` with `u, v ∈ SU(2)` it
equals `cosh r`. The main result, `lintegral_coshDist`, integrates every function of `coshDist`
against the Haar measure `haarC` of `HaarChart.lean`:

`∫_G Φ(coshDist g) dg = 4π³ ∫₁^∞ Φ(t) √(t² − 1) dt`.

The proof works in the Bruhat chart `g = [[(1+bc)/d, b], [c, d]]` and needs no Cartan
decomposition. For fixed `(b, d)` with `d ≠ 0` and `N = |b|² + |d|²`,
`coshDist = (N / 2|d|²) |c + b̄/N|² + (N + 1/N)/2` (`coshDist_bruhat`). The integral over `c`
is then a Gaussian-type integral (`lintegral_comp_quadratic`), the factor `|d|²` cancels the
density `|d|⁻²`, and what remains depends on `(b, d)` only through `N`. Two radial integrals
over `b` and `d` (`lintegral_comp_normSq`, `lintegral_Ioi_add`) and the length of the set
`{s > 0 : (s + 1/s)/2 < t}` (`lintegral_Ioi_cosh`) give the constant `4π³`.

With `t = cosh r` the formula reads `4π³ ∫₀^∞ Φ(cosh r) sinh² r dr` (`lintegral_coshDist_sinh`).
As a check against a known value, the set `{g : d(o, g·o) < R}` has measure `π³ (sinh 2R − 2R)`,
proportional to the volume `π (sinh 2R − 2R)` of a ball of radius `R` in hyperbolic 3-space
(`haarC_coshDist_lt`).

## References

* W. Rühl, *The Lorentz Group and Harmonic Analysis*, Benjamin 1970, ch. 2.
* A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton 1986, ch. II and V.
-/

@[expose] public section

open MeasureTheory Set Real
open scoped ENNReal
namespace Lightlike.Lorentz

/-- The substitution `u = r²` on `(0, ∞)`. -/
lemma lintegral_Ioi_sq (h : ℝ → ℝ≥0∞) :
    ∫⁻ u in Ioi (0 : ℝ), h u = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (2 * r) * h (r ^ 2) := by
  have himg : (fun r : ℝ => r ^ 2) '' Ioi 0 = Ioi 0 := by
    ext u; constructor
    · rintro ⟨r, hr, rfl⟩; exact pow_pos (show (0 : ℝ) < r from hr) 2
    · intro hu; exact ⟨√u, Real.sqrt_pos.2 hu, Real.sq_sqrt (le_of_lt hu)⟩
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f := fun r : ℝ => r ^ 2) (f' := fun r => 2 * r)
    (fun r _ => by simpa using (hasDerivAt_pow 2 r).hasDerivWithinAt)
    (fun r hr s hs hrs => (pow_left_inj₀ (le_of_lt hr) (le_of_lt hs) two_ne_zero).1 hrs) h
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [abs_of_pos (by have : (0:ℝ) < r := hr; positivity)]

/-- **Radial integrals on `ℂ`**: `∫ h(|z|²) d²z = π ∫₀^∞ h(u) du`. -/
lemma lintegral_comp_normSq (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ z : ℂ, h (‖z‖ ^ 2) = ENNReal.ofReal π * ∫⁻ u in Ioi (0 : ℝ), h u := by
  have m1 : Measurable fun r : ℝ => ENNReal.ofReal (2 * r) * h (r ^ 2) := by fun_prop
  rw [← Complex.lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul]
  rw [lintegral_prod _ (by fun_prop), lintegral_Ioi_sq h, ← lintegral_const_mul _ m1]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  dsimp only
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioo,
    mul_comm _ (ENNReal.ofReal _), ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (by linarith [Real.pi_pos]), ← ENNReal.ofReal_mul Real.pi_pos.le]
  congr 2; ring

/-- The affine substitution `t = αu + β` on `(0, ∞)`. -/
lemma lintegral_Ioi_affine {α : ℝ} (hα : 0 < α) (β : ℝ) (h : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi β, h t = ENNReal.ofReal α * ∫⁻ u in Ioi (0 : ℝ), h (α * u + β) := by
  have himg : (fun u : ℝ => α * u + β) '' Ioi 0 = Ioi β := by
    ext t; constructor
    · rintro ⟨u, hu, rfl⟩
      have : (0 : ℝ) < u := hu
      show β < α * u + β; nlinarith
    · intro ht
      have ht' : β < t := ht
      refine ⟨(t - β) / α, ?_, ?_⟩
      · show (0 : ℝ) < (t - β) / α; exact div_pos (by linarith) hα
      · show α * ((t - β) / α) + β = t; field_simp; ring
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ioi (a := (0 : ℝ)))
    (f := fun u : ℝ => α * u + β) (f' := fun _ => α)
    (fun u _ => by
      simpa using (((hasDerivAt_id u).const_mul α).add_const β).hasDerivWithinAt)
    (fun u _ v _ huv => by
      have : α * u = α * v := by simpa using huv
      exact mul_left_cancel₀ hα.ne' this) h
  rw [himg] at key
  rw [key, abs_of_pos hα, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **A Gaussian-type integral on `ℂ`**: `∫ Φ(α|c + w|² + β) d²c = (π/α) ∫_β^∞ Φ`. -/
lemma lintegral_comp_quadratic {α : ℝ} (hα : 0 < α) (w : ℂ) (β : ℝ) {Φ : ℝ → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ c : ℂ, Φ (α * ‖c + w‖ ^ 2 + β) = ENNReal.ofReal (π / α) * ∫⁻ t in Ioi β, Φ t := by
  rw [lintegral_add_right_eq_self (fun c : ℂ => Φ (α * ‖c‖ ^ 2 + β)) w,
    lintegral_comp_normSq (fun u => Φ (α * u + β)) (by fun_prop), lintegral_Ioi_affine hα β Φ,
    ← mul_assoc, ← ENNReal.ofReal_mul (div_pos Real.pi_pos hα).le]
  congr 2; field_simp

/-- A tail integral `∫_{s>v}` as an integral over `(0, ∞)` with a cut-off, for `v ≥ 0`. -/
lemma setLIntegral_Ioi_eq_indicator {v : ℝ} (hv : 0 ≤ v) (H : ℝ → ℝ≥0∞) :
    ∫⁻ s in Ioi v, H s = ∫⁻ s in Ioi (0 : ℝ), if v < s then H s else 0 := by
  have : (fun s => if v < s then H s else 0) = (Ioi v).indicator H := by
    ext s; simp [Set.indicator_apply]
  rw [this, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left hv]

/-- **Sums of two positive variables**: `∫_{v>0} ∫_{u>0} H(u+v) = ∫_{s>0} s H(s)`. -/
lemma lintegral_Ioi_add {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ v in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), H (u + v) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s * H s := by
  have h1 : ∀ v ∈ Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), H (u + v) =
      ∫⁻ s in Ioi (0 : ℝ), if v < s then H s else 0 := by
    intro v hv
    rw [← setLIntegral_Ioi_eq_indicator (le_of_lt hv), lintegral_Ioi_affine one_pos v H,
      ENNReal.ofReal_one, one_mul]
    simp only [one_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi h1, lintegral_lintegral_swap]
  · refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs' : (0 : ℝ) < s := hs
    have : (fun v => if v < s then H s else 0) = (Iio s).indicator (fun _ => H s) := by
      ext v; simp [Set.indicator_apply]
    rw [this, lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Iio_inter_Ioi, Real.volume_Ioo, sub_zero, mul_comm]
  · exact (Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (hH.comp measurable_snd) measurable_const).aemeasurable

/-- For `s > 0`, `(s + s⁻¹)/2 < t` iff `s² + 1 < 2ts`. -/
lemma half_add_inv_lt_iff {s t : ℝ} (hs : 0 < s) : (s + s⁻¹) / 2 < t ↔ s ^ 2 + 1 < 2 * t * s := by
  have : (s + s⁻¹) / 2 = (s ^ 2 + 1) / (2 * s) := by field_simp
  rw [this, div_lt_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

/-- The set `{s > 0 : (s + s⁻¹)/2 < t}` for `t > 1`. -/
lemma Ioi_inter_half_add_inv_lt {t : ℝ} (ht : 1 < t) (s : ℝ) :
    (0 < s ∧ (s + s⁻¹) / 2 < t) ↔ s ∈ Ioo (t - √(t ^ 2 - 1)) (t + √(t ^ 2 - 1)) := by
  have hr0 : 0 ≤ √(t ^ 2 - 1) := Real.sqrt_nonneg _
  have hr2 : √(t ^ 2 - 1) ^ 2 = t ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hrt : √(t ^ 2 - 1) < t := by nlinarith
  constructor
  · rintro ⟨hs, h⟩
    rw [half_add_inv_lt_iff hs] at h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have hs : 0 < s := by linarith
    refine ⟨hs, (half_add_inv_lt_iff hs).2 ?_⟩
    nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]

/-- **The length integral for `cosh`**:
`∫_{s>0} ∫_{t>(s+s⁻¹)/2} Φ(t) dt ds = ∫_{t>1} 2√(t²−1) Φ(t) dt`. -/
lemma lintegral_Ioi_cosh {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi ((s + s⁻¹) / 2), Φ t =
      ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (2 * √(t ^ 2 - 1)) * Φ t := by
  have h1 : ∀ s : ℝ, ∫⁻ t in Ioi ((s + s⁻¹) / 2), Φ t =
      ∫⁻ t, if (s + s⁻¹) / 2 < t then Φ t else 0 := by
    intro s
    have : (fun t => if (s + s⁻¹) / 2 < t then Φ t else 0) = (Ioi ((s + s⁻¹) / 2)).indicator Φ := by
      ext t; simp [Set.indicator_apply]
    rw [this, lintegral_indicator measurableSet_Ioi]
  simp only [h1]
  rw [lintegral_lintegral_swap, ← lintegral_indicator measurableSet_Ioi]
  · congr 1; ext t
    by_cases ht : 1 < t
    · rw [indicator_of_mem (show t ∈ Ioi 1 from ht)]
      have : ∀ s ∈ Ioi (0 : ℝ), (if (s + s⁻¹) / 2 < t then Φ t else 0) =
          (Ioo (t - √(t ^ 2 - 1)) (t + √(t ^ 2 - 1))).indicator (fun _ => Φ t) s := by
        intro s hs
        have hs' : (0 : ℝ) < s := hs
        by_cases h : (s + s⁻¹) / 2 < t
        · rw [ite_eq_left h, indicator_of_mem ((Ioi_inter_half_add_inv_lt ht s).1 ⟨hs', h⟩)]
        · rw [ite_eq_right h,
            indicator_of_notMem fun hm => h ((Ioi_inter_half_add_inv_lt ht s).2 hm).2]
      have hrt : √(t ^ 2 - 1) ≤ t := by
        have := Real.sq_sqrt (show (0:ℝ) ≤ t ^ 2 - 1 by nlinarith)
        nlinarith [Real.sqrt_nonneg (t ^ 2 - 1)]
      rw [setLIntegral_congr_fun measurableSet_Ioi this,
        lintegral_indicator_const measurableSet_Ioo, Measure.restrict_apply measurableSet_Ioo,
        Ioo_inter_Ioi, max_eq_left (by linarith),
        Real.volume_Ioo, mul_comm]
      congr 2; ring
    · rw [indicator_of_notMem (show t ∉ Ioi 1 from ht)]
      refine (setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_).trans (lintegral_zero)
      have hs' : (0 : ℝ) < s := hs
      have ht' : t ≤ 1 := not_lt.1 ht
      refine ite_eq_right fun h => ?_
      rw [half_add_inv_lt_iff hs'] at h
      nlinarith [sq_nonneg (s - 1)]
  · refine (Measurable.ite (measurableSet_lt ?_ measurable_snd) (hΦ.comp measurable_snd)
      measurable_const).aemeasurable
    fun_prop

/-- **Fubini on the chart**: `∫ f(x) d⁶x = ∫ d²b ∫ d²d ∫ d²c f(b, c, d)`. -/
lemma lintegral_fin_three {f : (Fin 3 → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ b : ℂ, ∫⁻ d : ℂ, ∫⁻ c : ℂ, f ![b, c, d] := by
  have e1 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℂ) 1).symm
  have hf1 : Measurable fun p =>
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℂ) 1).symm p) :=
    hf.comp (MeasurableEquiv.measurable _)
  rw [← e1.lintegral_comp hf, Measure.volume_eq_prod, lintegral_prod_symm _ hf1.aemeasurable]
  have hK := hf1.lintegral_prod_left' (μ := (volume : Measure ℂ))
  have e2 := (volume_preserving_finTwoArrow ℂ).symm
  rw [← e2.lintegral_comp hK, Measure.volume_eq_prod]
  refine (lintegral_prod _ (hK.comp (MeasurableEquiv.measurable _)).aemeasurable).trans ?_
  refine lintegral_congr fun b => lintegral_congr fun d => lintegral_congr fun c => ?_
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ## The radial formula -/


/-- Half the squared Frobenius norm of a group element. For the Cartan decomposition
`g = u · diag(e^{r/2}, e^{-r/2}) · v` it equals `cosh r`, where `r` is the hyperbolic distance
from the origin to `g · o` in hyperbolic 3-space. -/
noncomputable def coshDist (g : SL2C) : ℝ :=
  (‖g 0 0‖ ^ 2 + ‖g 0 1‖ ^ 2 + ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2) / 2

/-- `|1 + bc|² = 1 + 2 Re(bc) + |b|²|c|²`. -/
lemma normSq_one_add_mul (b c : ℂ) :
    ‖1 + b * c‖ ^ 2 = 1 + 2 * (b.re * c.re - b.im * c.im) + ‖b‖ ^ 2 * ‖c‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im]
  ring

/-- `|c + b̄/N|² = |c|² + 2 Re(bc)/N + |b|²/N²` for real `N ≠ 0`. -/
lemma normSq_add_conj_div (b c : ℂ) {N : ℝ} (hN : N ≠ 0) :
    ‖c + starRingEnd ℂ b / (N : ℂ)‖ ^ 2 =
      ‖c‖ ^ 2 + 2 * (b.re * c.re - b.im * c.im) / N + ‖b‖ ^ 2 / N ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-- **Completing the square in the chart**: for `d ≠ 0` and `N = |b|² + |d|²`,
`coshDist = (N / 2|d|²) |c + b̄/N|² + (N + 1/N)/2`. -/
lemma coshDist_bruhat {b c d : ℂ} (hd : d ≠ 0) :
    coshDist (bruhat ![b, c, d]) =
      (‖b‖ ^ 2 + ‖d‖ ^ 2) / (2 * ‖d‖ ^ 2) *
          ‖c + starRingEnd ℂ b / ((‖b‖ ^ 2 + ‖d‖ ^ 2 : ℝ) : ℂ)‖ ^ 2 +
        ((‖b‖ ^ 2 + ‖d‖ ^ 2) + (‖b‖ ^ 2 + ‖d‖ ^ 2)⁻¹) / 2 := by
  have hx : (![b, c, d] : Fin 3 → ℂ) 2 ≠ 0 := hd
  have hd2 : 0 < ‖d‖ ^ 2 := by positivity
  have hN : 0 < ‖b‖ ^ 2 + ‖d‖ ^ 2 := by positivity
  have e : ∀ i j, (bruhat ![b, c, d]) i j = (!![(1 + b * c) / d, b; c, d] : Matrix _ _ ℂ) i j := by
    intro i j; rw [bruhat_apply hx]; rfl
  simp only [coshDist, e]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, norm_div, div_pow]
  rw [normSq_one_add_mul, normSq_add_conj_div b c hN.ne']
  generalize ‖b‖ ^ 2 = B at *
  generalize ‖d‖ ^ 2 = D at *
  field_simp
  ring

/-- `coshDist` is continuous. -/
lemma continuous_coshDist : Continuous coshDist := by
  unfold coshDist
  have := continuous_entry
  fun_prop

/-- A tail integral as an integral over the whole line with a cut-off. -/
lemma setLIntegral_Ioi_eq_ite (β : ℝ) (Φ : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi β, Φ t = ∫⁻ t, if β < t then Φ t else 0 := by
  have : (fun t => if β < t then Φ t else 0) = (Ioi β).indicator Φ := by
    ext t; simp [Set.indicator_apply]
  rw [this, lintegral_indicator measurableSet_Ioi]

/-- Tail integrals depend measurably on the cut-off. -/
lemma measurable_setLIntegral_Ioi {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
    {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) : Measurable fun a => ∫⁻ t in Ioi (f a), Φ t := by
  simp only [setLIntegral_Ioi_eq_ite]
  exact (Measurable.ite (measurableSet_lt (hf.comp measurable_fst) measurable_snd)
    (hΦ.comp measurable_snd) measurable_const).lintegral_prod_right'

/-- **The radial formula for the Haar measure** `haarC`: for every measurable `Φ ≥ 0`,
`∫_G Φ(‖g‖²_F / 2) dg = 4π³ ∫₁^∞ Φ(t) √(t² − 1) dt`. With `t = cosh r` this is
`4π³ ∫₀^∞ Φ(cosh r) sinh² r dr`. -/
theorem lintegral_coshDist {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ g, Φ (coshDist g) ∂haarC =
      ENNReal.ofReal (4 * π ^ 3) * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal √(t ^ 2 - 1) * Φ t := by
  set Ψ : ℝ → ℝ≥0∞ := fun s => ∫⁻ t in Ioi ((s + s⁻¹) / 2), Φ t with hΨdef
  set K : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (2 * π / s) * Ψ s with hKdef
  have hΨ : Measurable Ψ := measurable_setLIntegral_Ioi (by fun_prop) hΦ
  have hK : Measurable K := (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hΨ
  have hf : Measurable fun x => bruhatDensity x * Φ (coshDist (bruhat x)) :=
    measurable_bruhatDensity.mul (hΦ.comp (continuous_coshDist.measurable.comp measurable_bruhat))
  rw [lintegral_haarC (F := fun g => Φ (coshDist g)) (hΦ.comp continuous_coshDist.measurable),
    lintegral_fin_three hf]
  -- the integral over `c`
  have hc : ∀ b d : ℂ, d ≠ 0 →
      ∫⁻ c, bruhatDensity ![b, c, d] * Φ (coshDist (bruhat ![b, c, d])) =
        K (‖b‖ ^ 2 + ‖d‖ ^ 2) := by
    intro b d hd
    have hd2 : 0 < ‖d‖ ^ 2 := by positivity
    have hN : 0 < ‖b‖ ^ 2 + ‖d‖ ^ 2 := by positivity
    have hα : 0 < (‖b‖ ^ 2 + ‖d‖ ^ 2) / (2 * ‖d‖ ^ 2) := by positivity
    simp only [bruhatDensity, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      coshDist_bruhat hd]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_comp_quadratic hα _ _ hΦ,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    simp only [hKdef, hΨdef]
    congr 2
    field_simp
  -- the integral over `d`
  have hd : ∀ b : ℂ, ∫⁻ d, ∫⁻ c, bruhatDensity ![b, c, d] * Φ (coshDist (bruhat ![b, c, d])) =
      ∫⁻ d : ℂ, K (‖b‖ ^ 2 + ‖d‖ ^ 2) := by
    intro b
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with d hd0
    exact hc b d hd0
  simp only [hd]
  -- the radial integrals over `b` and `d`
  have hH2 : Measurable fun p : ℝ × ℂ => K (p.1 + ‖p.2‖ ^ 2) := hK.comp (by fun_prop)
  have hH : Measurable fun u : ℝ => ∫⁻ d : ℂ, K (u + ‖d‖ ^ 2) := hH2.lintegral_prod_right'
  rw [lintegral_comp_normSq (fun u => ∫⁻ d : ℂ, K (u + ‖d‖ ^ 2)) hH]
  have h2 : ∀ u : ℝ, ∫⁻ d : ℂ, K (u + ‖d‖ ^ 2) =
      ENNReal.ofReal π * ∫⁻ v in Ioi (0 : ℝ), K (v + u) := by
    intro u
    rw [lintegral_comp_normSq (fun v => K (u + v)) (hK.comp (measurable_const_add u))]
    simp only [add_comm u]
  simp only [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioi_add hK]
  -- the integral over `N = |b|² + |d|²`
  have h3 : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal s * K s = ENNReal.ofReal (2 * π) * Ψ s := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    simp only [hKdef]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hs'.le]
    congr 2
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi h3, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simp only [hΨdef]
  rw [lintegral_Ioi_cosh hΦ]
  -- constants
  have h4 : ∀ t ∈ Ioi (1 : ℝ), ENNReal.ofReal (2 * √(t ^ 2 - 1)) * Φ t =
      ENNReal.ofReal 2 * (ENNReal.ofReal √(t ^ 2 - 1) * Φ t) := by
    intro t _
    rw [ENNReal.ofReal_mul (by norm_num), mul_assoc]
  have h5 : ENNReal.ofReal (4 * π ^ 3) =
      ENNReal.ofReal π * ENNReal.ofReal π * ENNReal.ofReal (2 * π) * ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi h4, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    h5]
  ring

/-! ## The hyperbolic distance and the volume of balls -/

/-- The substitution `t = cosh r` on `(1, ∞)`. -/
lemma lintegral_Ioi_one_cosh (h : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi (1 : ℝ), h t = ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (sinh r) * h (cosh r) := by
  have himg : cosh '' Ioi 0 = Ioi 1 := by
    ext t; constructor
    · rintro ⟨r, hr, rfl⟩; exact Real.one_lt_cosh.2 (ne_of_gt hr)
    · intro ht
      exact ⟨arcosh t, arcosh_pos ht, cosh_arcosh (le_of_lt ht)⟩
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ioi (a := (0 : ℝ)))
    (f := cosh) (f' := sinh) (fun r _ => (Real.hasDerivAt_cosh r).hasDerivWithinAt)
    (cosh_injOn.mono Ioi_subset_Ici_self) h
  rw [himg] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [abs_of_pos (Real.sinh_pos_iff.2 hr)]

/-- **The radial formula in the hyperbolic distance**: `∫_G Φ(cosh r(g)) dg = 4π³ ∫₀^∞ Φ(cosh r)
sinh² r dr`, where `cosh r(g) = coshDist g`. -/
theorem lintegral_coshDist_sinh {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ g, Φ (coshDist g) ∂haarC =
      ENNReal.ofReal (4 * π ^ 3) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (sinh r ^ 2) * Φ (cosh r) := by
  rw [lintegral_coshDist hΦ, lintegral_Ioi_one_cosh]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hs : 0 < sinh r := Real.sinh_pos_iff.2 hr
  rw [show cosh r ^ 2 - 1 = sinh r ^ 2 by rw [Real.cosh_sq]; ring, Real.sqrt_sq hs.le, ← mul_assoc,
    ← ENNReal.ofReal_mul hs.le, sq]

/-- `(sinh 2r − 2r)/4` is a primitive of `sinh² r`. -/
lemma hasDerivAt_sinh_two_mul_sub (r : ℝ) :
    HasDerivAt (fun r => (sinh (2 * r) - 2 * r) / 4) (sinh r ^ 2) r := by
  have h1 : HasDerivAt (fun r => 2 * r) 2 r := by simpa using (hasDerivAt_id r).const_mul 2
  have h2 := ((Real.hasDerivAt_sinh (2 * r)).comp r h1).sub h1
  convert h2.div_const 4 using 1
  · rfl
  · rw [Real.cosh_two_mul, Real.cosh_sq]; ring

/-- **Volume of a hyperbolic ball** (known value): the set of `g` with `d(o, g·o) < R` in
hyperbolic 3-space has measure `π³ (sinh 2R − 2R)`, which is `π²` times the hyperbolic volume
`π (sinh 2R − 2R)` of a ball of radius `R`. -/
theorem haarC_coshDist_lt {R : ℝ} (hR : 0 ≤ R) :
    haarC {g | coshDist g < cosh R} = ENNReal.ofReal (π ^ 3 * (sinh (2 * R) - 2 * R)) := by
  have hm : MeasurableSet {g | coshDist g < cosh R} :=
    measurableSet_lt continuous_coshDist.measurable measurable_const
  rw [← lintegral_indicator_one hm]
  have e : {g | coshDist g < cosh R}.indicator (1 : SL2C → ℝ≥0∞) =
      fun g => (Iio (cosh R)).indicator 1 (coshDist g) := by
    ext g; simp [indicator_apply]
  rw [e, lintegral_coshDist_sinh ((measurable_one).indicator measurableSet_Iio)]
  have h2 : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (sinh r ^ 2) * (Iio (cosh R)).indicator 1 (cosh r) =
      (Iio R).indicator (fun r => ENNReal.ofReal (sinh r ^ 2)) r := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have hiff : cosh r < cosh R ↔ r < R := by
      rw [Real.cosh_lt_cosh, abs_of_pos hr', abs_of_nonneg hR]
    by_cases h : r < R
    · rw [indicator_of_mem (show cosh r ∈ Iio (cosh R) from hiff.2 h),
        indicator_of_mem (show r ∈ Iio R from h), Pi.one_apply, mul_one]
    · rw [indicator_of_notMem (show cosh r ∉ Iio (cosh R) from fun h' => h (hiff.1 h')),
        indicator_of_notMem (show r ∉ Iio R from h), mul_zero]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  have hc : Continuous fun r => sinh r ^ 2 := Real.continuous_sinh.pow 2
  rw [← ofReal_integral_eq_lintegral_ofReal
      ((hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
      (Filter.Eventually.of_forall fun r => sq_nonneg _),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hasDerivAt_sinh_two_mul_sub r)
      (hc.intervalIntegrable _ _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [mul_zero, Real.sinh_zero, sub_zero, zero_div]
  ring

end Lightlike.Lorentz
