module

public import Lightlike.Lorentz.Cartan
public import Lightlike.Lorentz.PrincipalSeries

/-!
# The spherical function of the principal series of SL(2,ℂ)

For the principal series `π_{0,ρ}` (`k = 0`) on `L²(ℂ)` the function
`e₀(z) = π^{-1/2} (1 + |z|²)^{iρ - 1}` is a unit vector fixed by `SU(2)`. Its matrix coefficient
is the spherical function

  `⟨e₀, π_{0,ρ}(g) e₀⟩ = sin(ρ r) / (ρ sinh r)`,   `r = arcosh(‖g‖²_F / 2)`,

the hyperbolic distance from `g·o` to the base point of `H³ = SL(2,ℂ)/SU(2)` (Gel'fand–Naimark
1950; Rühl, *The Lorentz group and harmonic analysis*, 1970, ch. 4). For `ρ = 0` it is
`r / sinh r`, which gives the kernel `I(g) = ∫_ℂ d²z / ((1 + |z|²) ‖gᵀ(z, 1)‖²) = π r / sinh r`
used for the finiteness of the Lorentzian EPRL amplitude.

## Main results

* `principalSeries_ofSU2_sphVec`: `π(u) e₀ = e₀` for `u ∈ SU(2)`; `norm_sphVec`: `‖e₀‖ = 1`.
* `inner_sphVec_diagR`: `⟨e₀, π(a_r) e₀⟩ = sphericalFn ρ r` on the diagonal.
* `inner_sphVec_cartan`, `inner_sphVec_eq_sphericalFn`: the same for `u a_r v` and for all `g`,
  through the Cartan decomposition (`Cartan.lean`).
* `kernelI_eq`: `I(g) = π · sphericalFn 0 r`.

## Method

`π(g) e₀ = π^{-1/2} ‖gᵀ(z, 1)‖^{2(iρ - 1)}`, so `⟨e₀, π(a_r) e₀⟩` is a radial integral over `ℂ`.
In the variable `s = log((e^r y² + e^{-r})/(1 + y²))`, which runs from `-r` to `r`, the integrand
`2y (1 + y²)^{-iρ-1} (e^r y² + e^{-r})^{iρ-1}` is `e^{iρ s} ds / (2 sinh r)`. The proof applies
the fundamental theorem of calculus on `(0, ∞)` to `y ↦ E_ρ(s(y)) / (2 sinh r)`, where `E_ρ` is a
primitive of `e^{iρs}`.

## References

* Harish-Chandra, *The Plancherel formula for complex semisimple Lie groups*, Trans. AMS 76
  (1954).
* S. Helgason, *Groups and Geometric Analysis*, Academic Press 1984, ch. IV.
* A. W. Knapp, *Representation Theory of Semisimple Groups*, Princeton 1986, ch. II and V.
-/

@[expose] public section

open MeasureTheory Complex
open scoped ComplexConjugate InnerProductSpace

namespace Lightlike.Lorentz

/-- `N^{iρ - 1} = N⁻¹ e^{iρ log N}` for `N > 0`. -/
noncomputable def kerPow (ρ N : ℝ) : ℂ := ((N⁻¹ : ℝ) : ℂ) * exp (I * ρ * Real.log N)

/-- `kerPow` is the complex power `N^{iρ - 1}` for `N > 0`. -/
lemma ofReal_cpow_eq_kerPow (ρ : ℝ) {N : ℝ} (hN : 0 < N) :
    ((N : ℂ)) ^ (I * ρ - 1) = kerPow ρ N := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hN.ne'), ← ofReal_log hN.le, kerPow,
    show (Real.log N : ℂ) * (I * ρ - 1) = I * ρ * Real.log N + (-(Real.log N : ℂ)) by ring,
    exp_add, mul_comm, ← ofReal_neg, ← ofReal_exp, Real.exp_neg, Real.exp_log hN]

/-- `kerPow` is multiplicative on positive reals. -/
lemma kerPow_mul (ρ : ℝ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    kerPow ρ (A * B) = kerPow ρ A * kerPow ρ B := by
  simp only [kerPow, Real.log_mul hA.ne' hB.ne', mul_inv, ofReal_mul, ofReal_add, mul_add, exp_add]
  ring

/-- `|N^{iρ - 1}| = N⁻¹` for `N > 0`. -/
lemma norm_kerPow (ρ : ℝ) {N : ℝ} (hN : 0 < N) : ‖kerPow ρ N‖ = N⁻¹ := by
  rw [kerPow, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN),
    show I * ρ * Real.log N = ((ρ * Real.log N : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]

/-- Complex conjugation flips the sign of `ρ`. -/
lemma conj_kerPow (ρ N : ℝ) : conj (kerPow ρ N) = kerPow (-ρ) N := by
  simp only [kerPow, map_mul, conj_ofReal, ← exp_conj, map_mul, conj_I, ofReal_neg]
  ring_nf

/-- The multiplier of the `k = 0` principal series is `|w|^{2(iρ - 1)}`. -/
lemma mult_zero_eq (ρ : ℝ) {w : ℂ} (hw : w ≠ 0) : mult 0 ρ w = kerPow ρ (‖w‖ ^ 2) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hn2 : 0 < ‖w‖ ^ 2 := by positivity
  rw [mult, zpow_zero, mul_one, ← ofReal_cpow_eq_kerPow ρ hn2,
    cpow_def_of_ne_zero (by exact_mod_cast hn.ne'),
    cpow_def_of_ne_zero (by exact_mod_cast hn2.ne'), ← ofReal_log hn.le, ← ofReal_log hn2.le,
    Real.log_pow]
  push_cast; ring_nf


/-- `z ↦ kerPow ρ (f z)` is continuous for continuous positive `f`. -/
lemma continuous_kerPow_comp {α : Type*} [TopologicalSpace α] (ρ : ℝ) {f : α → ℝ}
    (hf : Continuous f) (hpos : ∀ z, 0 < f z) :
    Continuous fun z => kerPow ρ (f z) := by
  unfold kerPow
  have h1 : Continuous fun z => (f z)⁻¹ := hf.inv₀ fun z => (hpos z).ne'
  have h2 : Continuous fun z => Real.log (f z) := hf.log fun z => (hpos z).ne'
  fun_prop

/-- The `SU(2)`-invariant unit vector of the principal series `(0, ρ)`:
`e₀(z) = π^{-1/2} (1 + |z|²)^{iρ - 1}`. -/
noncomputable def sphFun (ρ : ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt Real.pi)⁻¹ : ℝ) * kerPow ρ (1 + ‖z‖ ^ 2)

/-- The spherical vector is continuous. -/
lemma continuous_sphFun (ρ : ℝ) : Continuous (sphFun ρ) := by
  unfold sphFun
  have := continuous_kerPow_comp ρ (f := fun z : ℂ => 1 + ‖z‖ ^ 2) (by fun_prop)
    (fun z => by positivity)
  fun_prop

/-- `|e₀(z)| = π^{-1/2} (1 + |z|²)⁻¹`. -/
lemma norm_sphFun (ρ : ℝ) (z : ℂ) :
    ‖sphFun ρ z‖ = (Real.sqrt Real.pi)⁻¹ * (1 + ‖z‖ ^ 2)⁻¹ := by
  rw [sphFun, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos)), norm_kerPow ρ (by positivity)]

/-- The spherical vector is square integrable. -/
lemma memLp_sphFun (ρ : ℝ) : MemLp (sphFun ρ) 2 (volume : Measure ℂ) := by
  refine (memLp_two_iff_integrable_sq_norm (continuous_sphFun ρ).aestronglyMeasurable).mpr ?_
  have hint := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)
  refine (hint.const_mul (Real.pi)⁻¹).congr (Filter.Eventually.of_forall fun z => ?_)
  have hp : 0 < 1 + ‖z‖ ^ 2 := by positivity
  simp only [norm_sphFun, mul_pow, inv_pow, Real.sq_sqrt Real.pi_pos.le]
  rw [show (-(4 : ℝ) / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hp.le, Real.rpow_natCast]

/-- The vector `e₀ ∈ L²(ℂ)`. -/
noncomputable def sphVec (ρ : ℝ) : L2C := (memLp_sphFun ρ).toLp _

/-- The `L²` class `sphVec ρ` is represented by `sphFun ρ`. -/
lemma coeFn_sphVec (ρ : ℝ) : sphVec ρ =ᵐ[volume] sphFun ρ := MemLp.coeFn_toLp _

/-- The action on `e₀`: `(π(g) e₀)(z) = π^{-1/2} (|num|² + |den|²)^{iρ - 1}`, where
`|num|² + |den|² = ‖gᵀ (z, 1)‖²`. -/
lemma mult_mul_sphFun (ρ : ℝ) (g : SL2C) {z : ℂ} (hz : den g z ≠ 0) :
    mult 0 ρ (den g z) * sphFun ρ (mob g z) =
      ((Real.sqrt Real.pi)⁻¹ : ℝ) * kerPow ρ (‖num g z‖ ^ 2 + ‖den g z‖ ^ 2) := by
  have hd : 0 < ‖den g z‖ ^ 2 := by positivity
  rw [mult_zero_eq ρ hz, sphFun, mul_left_comm, ← kerPow_mul ρ hd (by positivity), mob_def,
    norm_div]
  congr 2
  field_simp
  ring


/-- `‖gᵀ (z, 1)‖² = |num g z|² + |den g z|²`. -/
noncomputable def normT (g : SL2C) (z : ℂ) : ℝ := ‖num g z‖ ^ 2 + ‖den g z‖ ^ 2

/-- `(π(g) e₀)(z) = π^{-1/2} ‖gᵀ(z, 1)‖^{2(iρ - 1)}` almost everywhere. -/
lemma coeFn_principalSeries_sphVec (ρ : ℝ) (g : SL2C) :
    principalSeries 0 ρ g (sphVec ρ) =ᵐ[volume]
      fun z => ((Real.sqrt Real.pi)⁻¹ : ℝ) * kerPow ρ (normT g z) := by
  have h1 := coeFn_principalSeries 0 ρ g (sphVec ρ)
  have h2 := ae_eq_comp_mob g (coeFn_sphVec ρ)
  filter_upwards [h1, h2, ae_den_ne_zero g] with z hz1 hz2 hz3
  rw [hz1]
  simp only [Function.comp] at hz2
  rw [hz2, mult_mul_sphFun ρ g hz3, normT]

/-- For `u ∈ SU(2)`, `‖uᵀ(z, 1)‖² = 1 + |z|²`. -/
lemma normT_ofSU2 (u : Lightlike.SU2) (z : ℂ) : normT (SL2C.ofSU2 u) z = 1 + ‖z‖ ^ 2 := by
  have hu := SU2_mul_star u
  have e : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) ℂ) * star (u : Matrix (Fin 2) (Fin 2) ℂ)) i j =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => by rw [hu]
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  have key : ((normT (SL2C.ofSU2 u) z : ℝ) : ℂ) = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    simp only [normT, num, den, SL2C.coe_ofSU2]
    push_cast
    rw [← mul_conj', ← mul_conj', ← mul_conj']
    simp only [map_add, map_mul, RCLike.star_def] at h00 h01 h10 h11 ⊢
    linear_combination (z * conj z) * h00 + z * h01 + conj z * h10 + h11
  exact_mod_cast key

/-- **`e₀` is `SU(2)`-invariant**: `π(u) e₀ = e₀`. -/
theorem principalSeries_ofSU2_sphVec (ρ : ℝ) (u : Lightlike.SU2) :
    principalSeries 0 ρ (SL2C.ofSU2 u) (sphVec ρ) = sphVec ρ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_principalSeries_sphVec ρ (SL2C.ofSU2 u), coeFn_sphVec ρ] with z h1 h2
  rw [h1, h2, normT_ofSU2, sphFun]


/-- The matrix coefficient `⟨e₀, π(g) e₀⟩` as an integral over `ℂ`. -/
theorem inner_sphVec_principalSeries (ρ : ℝ) (g : SL2C) :
    ⟪sphVec ρ, principalSeries 0 ρ g (sphVec ρ)⟫_ℂ =
      ((Real.pi)⁻¹ : ℝ) * ∫ z, kerPow (-ρ) (1 + ‖z‖ ^ 2) * kerPow ρ (normT g z) := by
  rw [L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_sphVec ρ, coeFn_principalSeries_sphVec ρ g] with z h1 h2
  rw [h1, h2, RCLike.inner_apply', sphFun, map_mul, conj_ofReal, conj_kerPow]
  have hc : ((Real.sqrt Real.pi)⁻¹ : ℝ) * (Real.sqrt Real.pi)⁻¹ = (Real.pi)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
  rw [← hc]; push_cast; ring

/-- Radial integrals over `ℂ`: `∫_ℂ F(|z|) dz = 2π ∫₀^∞ y F(y) dy`. -/
lemma integral_comp_norm_complex (F : ℝ → ℂ) :
    ∫ z : ℂ, F ‖z‖ = 2 * Real.pi * ∫ y in Set.Ioi (0 : ℝ), (y : ℂ) * F y := by
  rw [integral_fun_norm_addHaar volume F, Complex.finrank_real_complex]
  have hv : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [hv]
  simp only [Nat.add_one_sub_one, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
  simp only [Complex.real_smul]
  ring


/-- The product `A^{-iρ-1} B^{iρ-1} = (AB)⁻¹ e^{iρ (log B - log A)}`. -/
lemma kerPow_neg_mul_kerPow (ρ : ℝ) {A B : ℝ} :
    kerPow (-ρ) A * kerPow ρ B =
      (((A * B)⁻¹ : ℝ) : ℂ) * exp (I * ρ * ((Real.log B - Real.log A : ℝ) : ℂ)) := by
  simp only [kerPow]
  rw [mul_mul_mul_comm, ← exp_add, mul_inv]
  push_cast; ring_nf

/-! ## The radial integral -/

/-- A primitive of `s ↦ e^{iρs}`: `(e^{iρs} - 1)/(iρ)`, and `s` for `ρ = 0`. -/
noncomputable def expPrim (ρ s : ℝ) : ℂ :=
  if ρ = 0 then (s : ℂ) else (exp (I * ρ * s) - 1) / (I * ρ)

/-- `expPrim ρ` is a primitive of `s ↦ e^{iρs}`. -/
lemma hasDerivAt_expPrim (ρ s : ℝ) : HasDerivAt (expPrim ρ) (exp (I * ρ * s)) s := by
  by_cases hρ : ρ = 0
  · have he : expPrim ρ = fun s : ℝ => (s : ℂ) := by funext s; simp [expPrim, hρ]
    rw [he, hρ]
    simpa using (hasDerivAt_id s).ofReal_comp
  · have hIρ : (I * ρ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hρ)
    have he : expPrim ρ = fun s : ℝ => (exp (I * ρ * s) - 1) / (I * ρ) := by
      funext s; simp [expPrim, hρ]
    have h : HasDerivAt (fun w : ℂ => (exp (I * ρ * w) - 1) / (I * ρ)) (exp (I * ρ * s))
        (s : ℂ) := by
      have := ((((hasDerivAt_id (s : ℂ)).const_mul (I * ρ)).cexp).sub_const 1).div_const (I * ρ)
      simp only [id] at this
      have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
      exact this.congr_deriv (by field_simp)
    rw [he]
    exact h.comp_ofReal

/-- `expPrim ρ` is continuous. -/
lemma continuous_expPrim (ρ : ℝ) : Continuous (expPrim ρ) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_expPrim ρ s).continuousAt

section Radial
variable (r : ℝ)

/-- `log (e^r y² + e^{-r}) - log (1 + y²)`. -/
noncomputable def logRatio (y : ℝ) : ℝ :=
  Real.log (Real.exp r * y ^ 2 + Real.exp (-r)) - Real.log (1 + y ^ 2)

/-- The derivative of `logRatio r`. -/
lemma hasDerivAt_logRatio (y : ℝ) :
    HasDerivAt (logRatio r)
      (2 * y * Real.exp r / (Real.exp r * y ^ 2 + Real.exp (-r)) - 2 * y / (1 + y ^ 2)) y := by
  have hB : Real.exp r * y ^ 2 + Real.exp (-r) ≠ 0 := by positivity
  have hA : 1 + y ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => Real.exp r * y ^ 2 + Real.exp (-r))
      (Real.exp r * (2 * y)) y := by
    have := ((hasDerivAt_pow 2 y).const_mul (Real.exp r)).add_const (Real.exp (-r))
    convert this using 1; push_cast; ring
  have h2 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
    have := (hasDerivAt_pow 2 y).const_add 1
    convert this using 1; push_cast; ring
  have := (h1.log hB).sub (h2.log hA)
  exact this.congr_deriv (by ring)

/-- `logRatio r 0 = -r`. -/
lemma logRatio_zero : logRatio r 0 = -r := by
  simp [logRatio, Real.log_exp]

/-- `logRatio r y → r` as `y → ∞`. -/
lemma tendsto_logRatio : Filter.Tendsto (logRatio r) Filter.atTop (nhds r) := by
  have hA : Filter.Tendsto (fun y : ℝ => 1 + y ^ 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop two_ne_zero)
  have h : Filter.Tendsto
      (fun y : ℝ => Real.exp r + (Real.exp (-r) - Real.exp r) * (1 + y ^ 2)⁻¹)
      Filter.atTop (nhds (Real.exp r + (Real.exp (-r) - Real.exp r) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hA))
  rw [mul_zero, add_zero] at h
  have hl := ((Real.continuousAt_log (Real.exp_pos r).ne').tendsto.comp h)
  rw [Real.log_exp] at hl
  refine hl.congr fun y => ?_
  have hA0 : 1 + y ^ 2 ≠ 0 := by positivity
  simp only [Function.comp, logRatio]
  rw [← Real.log_div (by positivity) hA0]
  congr 1
  field_simp
  ring

/-- The radial integrand `(1 + y²)^{-iρ-1} (e^r y² + e^{-r})^{iρ-1}`. -/
noncomputable def radInt (ρ y : ℝ) : ℂ :=
  kerPow (-ρ) (1 + y ^ 2) * kerPow ρ (Real.exp r * y ^ 2 + Real.exp (-r))

/-- The radial integrand is continuous. -/
lemma continuous_radInt (ρ : ℝ) : Continuous (radInt r ρ) := by
  unfold radInt
  have h1 := continuous_kerPow_comp (-ρ) (f := fun y : ℝ => 1 + y ^ 2) (by fun_prop)
    (fun y => by positivity)
  have h2 := continuous_kerPow_comp ρ (f := fun y : ℝ => Real.exp r * y ^ 2 + Real.exp (-r))
    (by fun_prop) (fun y => by positivity)
  exact h1.mul h2

/-- `|radInt r ρ y| = ((1 + y²)(e^r y² + e^{-r}))⁻¹`. -/
lemma norm_radInt (ρ y : ℝ) :
    ‖radInt r ρ y‖ = ((1 + y ^ 2) * (Real.exp r * y ^ 2 + Real.exp (-r)))⁻¹ := by
  rw [radInt, norm_mul, norm_kerPow _ (by positivity), norm_kerPow _ (by positivity), mul_inv]

/-- The bound `|radInt r ρ y| ≤ e^{|r|} (1 + y²)⁻²`. -/
lemma norm_radInt_le (ρ y : ℝ) :
    ‖radInt r ρ y‖ ≤ Real.exp |r| * ((1 + y ^ 2) ^ 2)⁻¹ := by
  have hA : 0 < 1 + y ^ 2 := by positivity
  have h1 : Real.exp (-|r|) ≤ Real.exp r := Real.exp_le_exp.2 (neg_abs_le r)
  have h2 : Real.exp (-|r|) ≤ Real.exp (-r) := Real.exp_le_exp.2 (neg_le_neg (le_abs_self r))
  have hB : Real.exp (-|r|) * (1 + y ^ 2) ≤ Real.exp r * y ^ 2 + Real.exp (-r) := by
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg y)]
  rw [norm_radInt]
  calc ((1 + y ^ 2) * (Real.exp r * y ^ 2 + Real.exp (-r)))⁻¹
      ≤ ((1 + y ^ 2) * (Real.exp (-|r|) * (1 + y ^ 2)))⁻¹ :=
        inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hB hA.le)
    _ = Real.exp |r| * ((1 + y ^ 2) ^ 2)⁻¹ := by
        rw [Real.exp_neg]; field_simp

/-- For `r ≠ 0`, `E_ρ(logRatio r y)/(2 sinh r)` is a primitive of `2y · radInt r ρ y`. -/
lemma hasDerivAt_radPrim (ρ : ℝ) (hr : r ≠ 0) (y : ℝ) :
    HasDerivAt (fun y => expPrim ρ (logRatio r y) / ((2 * Real.sinh r : ℝ) : ℂ))
      (2 * y * radInt r ρ y) y := by
  have h := ((hasDerivAt_expPrim ρ (logRatio r y)).scomp y (hasDerivAt_logRatio r y)).div_const
    ((2 * Real.sinh r : ℝ) : ℂ)
  refine h.congr_deriv ?_
  have hA : 0 < 1 + y ^ 2 := by positivity
  have hB : 0 < Real.exp r * y ^ 2 + Real.exp (-r) := by positivity
  have hs : Real.sinh r ≠ 0 := fun h => hr (Real.sinh_eq_zero.mp h)
  set E := exp (I * ρ * ((logRatio r y : ℝ) : ℂ))
  have key : (2 * y * Real.exp r / (Real.exp r * y ^ 2 + Real.exp (-r)) - 2 * y / (1 + y ^ 2)) /
      (2 * Real.sinh r) = 2 * y * ((1 + y ^ 2) * (Real.exp r * y ^ 2 + Real.exp (-r)))⁻¹ := by
    have hs' : Real.exp r - Real.exp (-r) ≠ 0 := by
      intro h0; apply hs; rw [Real.sinh_eq]; rw [h0]; ring
    rw [Real.sinh_eq]
    field_simp
    ring_nf
  rw [radInt, kerPow_neg_mul_kerPow, Complex.real_smul]
  have hE : exp (I * ρ * ((Real.log (Real.exp r * y ^ 2 + Real.exp (-r)) -
      Real.log (1 + y ^ 2) : ℝ) : ℂ)) = E := rfl
  rw [hE]
  calc ((2 * y * Real.exp r / (Real.exp r * y ^ 2 + Real.exp (-r)) - 2 * y / (1 + y ^ 2) : ℝ)
        : ℂ) * E / ((2 * Real.sinh r : ℝ) : ℂ)
      = (((2 * y * Real.exp r / (Real.exp r * y ^ 2 + Real.exp (-r)) - 2 * y / (1 + y ^ 2)) /
          (2 * Real.sinh r) : ℝ) : ℂ) * E := by push_cast; ring
    _ = 2 * y * ((((1 + y ^ 2) * (Real.exp r * y ^ 2 + Real.exp (-r)))⁻¹ : ℝ) * E) := by
        rw [key]; push_cast; ring

/-- `-(1 + y²)⁻¹` is a primitive of `2y (1 + y²)⁻²`. -/
lemma hasDerivAt_negInv (y : ℝ) :
    HasDerivAt (fun y : ℝ => -(1 + y ^ 2)⁻¹) (2 * y * ((1 + y ^ 2) ^ 2)⁻¹) y := by
  have hA : (1 + y ^ 2) ≠ 0 := by positivity
  have h0 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * y) y := by
    simpa using ((hasDerivAt_id y).pow 2).const_add 1
  refine (h0.inv hA).neg.congr_deriv ?_
  field_simp

/-- `-(1 + y²)⁻¹ → 0` as `y → ∞`. -/
lemma tendsto_negInv : Filter.Tendsto (fun y : ℝ => -(1 + y ^ 2)⁻¹) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_left _ 1 (Filter.tendsto_pow_atTop two_ne_zero))
  simpa using h.neg

/-- `2y (1 + y²)⁻²` is integrable on `(0, ∞)`. -/
lemma integrableOn_bound :
    IntegrableOn (fun y : ℝ => 2 * y * ((1 + y ^ 2) ^ 2)⁻¹) (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun y _ => hasDerivAt_negInv y)
    (fun y hy => by have : 0 < y := hy; positivity) tendsto_negInv

/-- `2y · radInt r ρ y` is integrable on `(0, ∞)`. -/
lemma integrableOn_radInt (ρ : ℝ) :
    IntegrableOn (fun y : ℝ => 2 * (y : ℂ) * radInt r ρ y) (Set.Ioi 0) := by
  refine Integrable.mono' ((integrableOn_bound).const_mul (Real.exp |r|)) ?_ ?_
  · exact ((continuous_const.mul continuous_ofReal).mul
      (continuous_radInt r ρ)).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy : 0 < y := hy
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
    calc 2 * y * ‖radInt r ρ y‖ ≤ 2 * y * (Real.exp |r| * ((1 + y ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (norm_radInt_le r ρ y) (by positivity)
      _ = Real.exp |r| * (2 * y * ((1 + y ^ 2) ^ 2)⁻¹) := by ring

/-- For `r ≠ 0`, `∫₀^∞ 2y · radInt r ρ y dy = (E_ρ(r) - E_ρ(-r))/(2 sinh r)`. -/
lemma integral_radInt (ρ : ℝ) (hr : r ≠ 0) :
    ∫ y in Set.Ioi (0 : ℝ), 2 * (y : ℂ) * radInt r ρ y =
      (expPrim ρ r - expPrim ρ (-r)) / ((2 * Real.sinh r : ℝ) : ℂ) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _ => hasDerivAt_radPrim r ρ hr y)
    (integrableOn_radInt r ρ)
    ((((continuous_expPrim ρ).tendsto r).comp (tendsto_logRatio r)).div_const _)]
  simp only [logRatio_zero]
  ring

/-- At `r = 0` the radial integrand is `(1 + y²)⁻²`. -/
lemma radInt_zero (ρ y : ℝ) : radInt 0 ρ y = ((((1 + y ^ 2) ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [radInt, kerPow_neg_mul_kerPow]
  simp only [neg_zero, Real.exp_zero, one_mul]
  rw [add_comm (y ^ 2) 1, sub_self]
  simp [sq]

/-- At `r = 0`, `∫₀^∞ 2y (1 + y²)⁻² dy = 1`. -/
lemma integral_radInt_zero (ρ : ℝ) :
    ∫ y in Set.Ioi (0 : ℝ), 2 * (y : ℂ) * radInt 0 ρ y = 1 := by
  have hd : ∀ y ∈ Set.Ici (0 : ℝ), HasDerivAt (fun y : ℝ => ((-(1 + y ^ 2)⁻¹ : ℝ) : ℂ))
      (2 * (y : ℂ) * radInt 0 ρ y) y := fun y _ => by
    refine (hasDerivAt_negInv y).ofReal_comp.congr_deriv ?_
    rw [radInt_zero]; push_cast; ring
  have ht : Filter.Tendsto (fun y : ℝ => ((-(1 + y ^ 2)⁻¹ : ℝ) : ℂ)) Filter.atTop
      (nhds ((0 : ℝ) : ℂ)) := (continuous_ofReal.tendsto 0).comp tendsto_negInv
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_radInt 0 ρ) ht]
  norm_num

end Radial

/-! ## The spherical function -/

/-- The difference `E(r) - E(-r)` of the primitive. -/
lemma expPrim_sub_neg (ρ r : ℝ) :
    expPrim ρ r - expPrim ρ (-r) =
      ((2 * (if ρ = 0 then r else Real.sin (ρ * r) / ρ) : ℝ) : ℂ) := by
  unfold expPrim
  split_ifs with hρ
  · push_cast; ring
  · have hρ' : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ
    have e1 : exp (I * ρ * (r : ℂ)) = Complex.cos (ρ * r) + Complex.sin (ρ * r) * I := by
      rw [← Complex.exp_mul_I]; ring_nf
    have e2 : exp (I * ρ * ((-r : ℝ) : ℂ)) = Complex.cos (ρ * r) - Complex.sin (ρ * r) * I := by
      rw [show I * ρ * ((-r : ℝ) : ℂ) = -(ρ * r) * I by push_cast; ring, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg]
      ring
    rw [e1, e2]
    push_cast
    field_simp
    ring_nf

/-- **The spherical function** of the principal series `(k, ρ) = (0, ρ)` on `a_r`:
`sin(ρr)/(ρ sinh r)`, with the values `r / sinh r` at `ρ = 0` and `1` at `r = 0`. -/
noncomputable def sphericalFn (ρ r : ℝ) : ℝ :=
  if r = 0 then 1 else if ρ = 0 then r / Real.sinh r else Real.sin (ρ * r) / (ρ * Real.sinh r)

/-- `‖a_r gᵀ(z,1)‖² = e^r |z|² + e^{-r}`. -/
lemma normT_diagR (r : ℝ) (z : ℂ) :
    normT (diagR r) z = Real.exp r * ‖z‖ ^ 2 + Real.exp (-r) := by
  have h1 : Real.exp (r / 2) ^ 2 = Real.exp r := by
    rw [sq, ← Real.exp_add, add_halves]
  have h2 : Real.exp (-(r / 2)) ^ 2 = Real.exp (-r) := by
    rw [sq, ← Real.exp_add]; ring_nf
  simp only [normT, num, den, coe_diagR]
  simp [-Complex.ofReal_exp, mul_pow, Complex.norm_real, h1, h2]

/-- The matrix coefficient on the diagonal: `⟨e₀, π(a_r) e₀⟩ = sphericalFn ρ r`. -/
theorem inner_sphVec_diagR (ρ r : ℝ) :
    ⟪sphVec ρ, principalSeries 0 ρ (diagR r) (sphVec ρ)⟫_ℂ = (sphericalFn ρ r : ℂ) := by
  rw [inner_sphVec_principalSeries]
  have hf : (fun z : ℂ => kerPow (-ρ) (1 + ‖z‖ ^ 2) * kerPow ρ (normT (diagR r) z)) =
      fun z => radInt r ρ ‖z‖ := by
    funext z; rw [normT_diagR, radInt]
  have h2 : ∫ y in Set.Ioi (0 : ℝ), (y : ℂ) * radInt r ρ y =
      (1 / 2 : ℂ) * ∫ y in Set.Ioi (0 : ℝ), 2 * (y : ℂ) * radInt r ρ y := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  rw [hf, integral_comp_norm_complex (radInt r ρ), h2]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold sphericalFn
  by_cases hr : r = 0
  · subst hr
    rw [integral_radInt_zero]
    simp only [ite_true]
    push_cast
    field_simp
  · have hs : Real.sinh r ≠ 0 := fun h => hr (Real.sinh_eq_zero.mp h)
    have hs' : (Real.sinh r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
    rw [integral_radInt r ρ hr, expPrim_sub_neg]
    split_ifs with hρ
    · push_cast; field_simp
    · have hρ' : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ
      push_cast; field_simp

/-- **The matrix coefficient in Cartan form**:
`⟨e₀, π_{0,ρ}(u a_r v) e₀⟩ = sphericalFn ρ r` for `u, v ∈ SU(2)`. -/
theorem inner_sphVec_cartan (ρ : ℝ) (u v : Lightlike.SU2) (r : ℝ) :
    ⟪sphVec ρ, principalSeries 0 ρ (SL2C.ofSU2 u * diagR r * SL2C.ofSU2 v) (sphVec ρ)⟫_ℂ =
      (sphericalFn ρ r : ℂ) := by
  rw [principalSeries_mul, principalSeries_mul, mul_apply_eq_comp, mul_apply_eq_comp,
    principalSeries_ofSU2_sphVec]
  have h := principalSeries_inner 0 ρ (SL2C.ofSU2 u) (sphVec ρ)
    (principalSeries 0 ρ (diagR r) (sphVec ρ))
  rw [principalSeries_ofSU2_sphVec] at h
  rw [h, inner_sphVec_diagR]

/-- The spherical function is even in `r`. -/
lemma sphericalFn_neg (ρ r : ℝ) : sphericalFn ρ (-r) = sphericalFn ρ r := by
  unfold sphericalFn
  simp only [neg_eq_zero, Real.sinh_neg, mul_neg, Real.sin_neg, neg_div_neg_eq]

/-- `sphericalFn ρ |r| = sphericalFn ρ r`. -/
lemma sphericalFn_abs (ρ r : ℝ) : sphericalFn ρ |r| = sphericalFn ρ r := by
  rcases abs_choice r with h | h <;> rw [h]
  exact sphericalFn_neg ρ r

/-- **The spherical function as a function of the hyperbolic distance**:
`⟨e₀, π_{0,ρ}(g) e₀⟩ = sphericalFn ρ (arcosh (coshDist g))`, where `arcosh (coshDist g)` is the
distance from `g·o` to the base point `o` of hyperbolic 3-space. -/
theorem inner_sphVec_eq_sphericalFn (ρ : ℝ) (g : SL2C) :
    ⟪sphVec ρ, principalSeries 0 ρ g (sphVec ρ)⟫_ℂ =
      (sphericalFn ρ (Real.arcosh (coshDist g)) : ℂ) := by
  obtain ⟨u, v, r, rfl⟩ := exists_cartan g
  rw [inner_sphVec_cartan, coshDist_cartan, ← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg r),
    sphericalFn_abs]

/-- The spherical vector is a unit vector. -/
theorem norm_sphVec (ρ : ℝ) : ‖sphVec ρ‖ = 1 := by
  have h := inner_sphVec_diagR ρ 0
  have h0 : diagR 0 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [coe_diagR]
  rw [h0, principalSeries_one, one_apply_eq_self] at h
  have h2 : ‖sphVec ρ‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h]; simp [sphericalFn]
  have h3 : 0 ≤ ‖sphVec ρ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖sphVec ρ‖ - 1)]

/-- The kernel `I(g) = ∫_ℂ d²z / ((1 + |z|²) ‖gᵀ(z, 1)‖²)` that bounds the matrix coefficients of
the EPRL boundary states. -/
noncomputable def kernelI (g : SL2C) : ℝ := ∫ z : ℂ, ((1 + ‖z‖ ^ 2) * normT g z)⁻¹

/-- **`I(g) = π r / sinh r`** with `r` the hyperbolic distance (`I(g) = π` at `r = 0`). -/
theorem kernelI_eq (g : SL2C) :
    kernelI g = Real.pi * sphericalFn 0 (Real.arcosh (coshDist g)) := by
  have h := inner_sphVec_eq_sphericalFn 0 g
  rw [inner_sphVec_principalSeries] at h
  have hk : ∀ N : ℝ, kerPow 0 N = ((N⁻¹ : ℝ) : ℂ) := fun N => by simp [kerPow]
  have hint : ∫ z : ℂ, kerPow (-0) (1 + ‖z‖ ^ 2) * kerPow 0 (normT g z) =
      ((kernelI g : ℝ) : ℂ) := by
    rw [kernelI, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [neg_zero, hk, ← ofReal_mul, ← mul_inv]
  rw [hint] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h' : ((kernelI g : ℝ) : ℂ) =
      ((Real.pi * sphericalFn 0 (Real.arcosh (coshDist g)) : ℝ) : ℂ) := by
    rw [ofReal_mul, ← h]; push_cast; field_simp
  exact_mod_cast h'

end Lightlike.Lorentz
