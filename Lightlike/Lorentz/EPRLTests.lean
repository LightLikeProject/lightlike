module

public import Lightlike.Lorentz.EPRL
public import Lightlike.Lorentz.SmoothVectors
public import Lightlike.SU2.Completeness

/-!
# Trust checks for the Lorentzian EPRL vertex amplitude

* **Known value, spin zero** (`eprlCoeff_spin_zero`, `eprlVertex_spinZero`): for `j = 0` the EPRL
  vector is a unit multiple of the spherical vector, so the matrix coefficient is the spherical
  function `sin(γr)/(γ sinh r)` of the hyperbolic distance `r`, and the vertex amplitude is the
  integral of the product of the ten spherical functions, the kernel of the Lorentzian
  Barrett–Crane model.
* **Non-vacuity** (`eprlVertex_spinZero_ne_zero`): for `γ = 0` and all spins zero the amplitude
  is a positive real number, so the definition is not trivially zero.
* **Non-vacuity at `γ ≠ 0`** (`continuousAt_integral_sphLinks`,
  `eventually_eprlVertex_spinZero_ne_zero`, `exists_pos_eprlVertex_spinZero_ne_zero`): since
  `|sin(γr)/(γ sinh r)| ≤ r / sinh r`, dominated convergence makes the spin-zero amplitude
  continuous in `γ` at `0`, so it is nonzero for all `γ` near `0`, in particular for some `γ > 0`.
* **Wrong model: no gauge fixing** (`lintegral_linkProd_ungauged_eq_top`): integrating the
  dominating kernel `∏ I(V_a⁻¹ V_b)` over all five copies of SL(2,ℂ) instead of four gives `∞`,
  because it is invariant under `V_a ↦ W V_a`. This is a statement about the dominating integral,
  not about `|integrand|`: without the gauge fixing `V₄ = 1` the finiteness proof does not apply.
* **Label check** (`casimir2_eprlVec_fun`, `casimir2_hvec_eq_iff`, `casimir2_wrong_label_ne`): on
  the functions that define the EPRL vectors (`eprlVec_eq`) the second Casimir `kρ` is `γ j(j+1)`,
  `γ` times the SU(2) Casimir, for `ρ = eprlRho γ J = γ(j+1)`, and for no other `ρ` when `j ≠ 0`.
  The label `ρ = γj` (Engle and Pereira's `2γj` in their normalisation) therefore gives a
  different Casimir, checked through `casimir2` at a point where the function is nonzero.

## References

* J. W. Barrett and L. Crane, *A Lorentzian signature model for quantum general relativity*,
  Class. Quantum Grav. 17 (2000) 3101, arXiv:gr-qc/9904025.
* J. Engle and R. Pereira, *Regularization and finiteness of the Lorentzian loop quantum gravity
  vertices*, Phys. Rev. D 79 (2009) 084034, arXiv:0805.4696, eqs. (22)–(23).
* Y. Ding and C. Rovelli, *Physical boundary Hilbert space and volume operator in the Lorentzian
  new spin-foam theory*, arXiv:1006.1294, eq. (24).
-/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace Lightlike.Lorentz

/-! ## Spin zero -/

lemma eprlRho_zero (γ : ℝ) : eprlRho γ 0 = γ := by simp [eprlRho]

/-- The spin-0 vector of the decomposition is a unit multiple of the spherical vector. -/
lemma exists_sphVec_eq_smul (ρ : ℝ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ sphVec ρ = c • suV 0 ρ 0 (EuclideanSpace.single 0 1) := by
  let S : (Fin (dsp 0 0 + 1) → ℂ) →ₗ[ℂ] L2C := (LinearMap.proj 0).smulRight (sphVec ρ)
  have hS : IsPSIntertwiner 0 ρ S := by
    intro u x
    have h1 : Lightlike.SU2.spinMat (dsp 0 0) (u : Matrix (Fin 2) (Fin 2) ℂ) = 1 := Lightlike.SU2.spinMat_zero' _
    simp only [S, LinearMap.smulRight_apply, LinearMap.proj_apply, map_smul,
      principalSeries_ofSU2_sphVec, h1, Matrix.one_mulVec]
  obtain ⟨c, hc⟩ := intertwiner_eq_smul 0 ρ 0 hS
  have h1 := hc (Pi.single 0 1)
  simp only [S, LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.single_eq_same,
    one_smul, PiLp.toLp_single] at h1
  refine ⟨c, ?_, h1⟩
  have h2 := congrArg norm h1
  rwa [norm_sphVec, norm_smul, LinearIsometry.norm_map, PiLp.norm_single, norm_one, mul_one,
    eq_comm] at h2

/-- **Spin-zero coefficient**: `D^{(γ, 0)}_{00,00}(g) = φ_γ(r)`, the spherical function
`sin(γr)/(γ sinh r)` of `r = d(g · o, o)`. -/
theorem eprlCoeff_spin_zero (γ : ℝ) (g : SL2C) :
    eprlCoeff γ 0 0 0 g = (sphericalFn γ (Real.arcosh (coshDist g)) : ℂ) := by
  obtain ⟨c, hc1, hc⟩ := exists_sphVec_eq_smul γ
  have hv : eprlVec γ 0 0 = suV 0 γ 0 (EuclideanSpace.single 0 1) := by
    simp only [eprlVec, Nat.lt_add_one_iff, zero_le, ↓reduceDIte, eprlRho_zero]
    rfl
  have key : ⟪sphVec γ, principalSeries 0 γ g (sphVec γ)⟫_ℂ =
      ⟪suV 0 γ 0 (EuclideanSpace.single 0 1),
        principalSeries 0 γ g (suV 0 γ 0 (EuclideanSpace.single 0 1))⟫_ℂ := by
    rw [hc, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc1]
    simp
  rw [eprlCoeff, hv, eprlRho_zero, Nat.cast_zero, ← key, inner_sphVec_eq_sphericalFn]

lemma magBox_spinZero : magBox (fun _ => 0) = {fun _ _ => 0} := by
  ext m
  simp only [magBox, Fintype.mem_piFinset, mem_singleton, funext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  split_ifs <;> simp

/-- The spin-zero integrand: the product of the ten spherical functions `φ_γ(r_{ab})`. -/
noncomputable def sphLinks (γ : ℝ) (x : Fin 4 → SL2C) : ℝ :=
  linkProd fun a b => sphericalFn γ (Real.arcosh (coshDist ((gauge x a)⁻¹ * gauge x b)))

lemma eprlLinks_spinZero (γ : ℝ) (x : Fin 4 → SL2C) :
    eprlLinks γ (fun _ => 0) (fun _ _ => 0) x = (sphLinks γ x : ℂ) := by
  simp only [eprlLinks, eprlCoeff_spin_zero, sphLinks, linkProd, Complex.ofReal_prod]

/-- **The spin-zero EPRL amplitude** is the integral of the product of the ten spherical
functions. -/
theorem eprlVertex_spinZero (γ : ℝ) :
    eprlVertex γ (fun _ => 0) (fun _ _ => 1) = ((∫ x, sphLinks γ x ∂haar4 : ℝ) : ℂ) := by
  rw [eprlVertex, magBox_spinZero, sum_singleton, intwCoeff]
  simp only [prod_const_one, one_mul, eprlLinks_spinZero]
  exact integral_ofReal

lemma integrable_sphLinks (γ : ℝ) : Integrable (sphLinks γ) haar4 := by
  refine (integrable_eprlLinks γ (fun _ => 0) (fun _ _ => 0)).re.congr
    (Eventually.of_forall fun x => ?_)
  simp [eprlLinks_spinZero]

lemma sphLinks_zero_pos (x : Fin 4 → SL2C) : 0 < sphLinks 0 x := by
  unfold sphLinks linkProd
  exact prod_pos fun a _ => prod_pos fun b _ => sphericalFn_zero_pos _

lemma haar4_univ_ne_zero : haar4 Set.univ ≠ 0 := by
  rw [Measure.pi_univ, Finset.prod_ne_zero_iff]
  exact fun _ _ => Measure.measure_univ_ne_zero.2 haarC_ne_zero

/-- **Non-vacuity**: for `γ = 0` the spin-zero amplitude is a positive real number. -/
theorem integral_sphLinks_zero_pos : 0 < ∫ x, sphLinks 0 x ∂haar4 := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (sphLinks_zero_pos x).le)
    (integrable_sphLinks 0)]
  have : Function.support (sphLinks 0) = Set.univ :=
    Set.eq_univ_of_forall fun x => (sphLinks_zero_pos x).ne'
  rw [this]
  exact pos_iff_ne_zero.2 haar4_univ_ne_zero

/-- **Non-vacuity**: the EPRL amplitude with `γ = 0`, all spins `0` and unit intertwiner
coefficients is not zero. -/
theorem eprlVertex_spinZero_ne_zero : eprlVertex 0 (fun _ => 0) (fun _ _ => 1) ≠ 0 := by
  rw [eprlVertex_spinZero]
  exact_mod_cast integral_sphLinks_zero_pos.ne'

/-! ## Non-vacuity for a nonzero Barbero–Immirzi parameter -/

/-- `φ_ρ(r) = r sinc(ρ r) / sinh r` for `r ≠ 0`, uniformly in `ρ` (including `ρ = 0`). -/
lemma sphericalFn_eq_sinc (ρ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    sphericalFn ρ r = r * Real.sinc (ρ * r) / Real.sinh r := by
  by_cases hρ : ρ = 0
  · simp [sphericalFn, hr, hρ]
  · have hs : Real.sinh r ≠ 0 := Real.sinh_ne_zero.2 hr
    simp only [sphericalFn, hr, hρ, ↓reduceIte, Real.sinc_of_ne_zero (mul_ne_zero hρ hr)]
    field_simp

/-- For fixed `r`, the spherical function is continuous in the label `ρ`. -/
lemma continuous_sphericalFn_label (r : ℝ) : Continuous fun ρ => sphericalFn ρ r := by
  by_cases hr : r = 0
  · simp only [sphericalFn, hr, ↓reduceIte]
    exact continuous_const
  · simp_rw [sphericalFn_eq_sinc _ hr]
    exact (continuous_const.mul (Real.continuous_sinc.comp
      (continuous_id.mul continuous_const))).div_const _

/-- `|φ_ρ(r)| ≤ φ_0(r) = r / sinh r` for `r ≥ 0`, since `|sinc| ≤ 1`. -/
lemma abs_sphericalFn_le (ρ : ℝ) {r : ℝ} (hr : 0 ≤ r) : |sphericalFn ρ r| ≤ sphericalFn 0 r := by
  rcases hr.eq_or_lt with h | h
  · subst h
    simp [sphericalFn]
  · have hs : 0 < Real.sinh r := Real.sinh_pos_iff.2 h
    rw [sphericalFn_eq_sinc ρ h.ne', sphericalFn_eq_sinc 0 h.ne', zero_mul, Real.sinc_zero,
      mul_one, abs_div, abs_mul, abs_of_pos h, abs_of_pos hs]
    calc r * |Real.sinc (ρ * r)| / Real.sinh r ≤ r * 1 / Real.sinh r := by
          gcongr
          exact Real.abs_sinc_le_one _
      _ = r / Real.sinh r := by rw [mul_one]

/-- The spin-zero integrand is dominated by its value at `γ = 0`. -/
lemma abs_sphLinks_le (γ : ℝ) (x : Fin 4 → SL2C) : |sphLinks γ x| ≤ sphLinks 0 x := by
  unfold sphLinks linkProd
  rw [Finset.abs_prod]
  refine prod_le_prod₀ (fun a _ => abs_nonneg _) fun a _ => ?_
  rw [Finset.abs_prod]
  exact prod_le_prod₀ (fun b _ => abs_nonneg _) fun b _ =>
    abs_sphericalFn_le γ (Real.arcosh_nonneg (one_le_coshDist _))

/-- **The spin-zero amplitude is continuous in `γ` at `γ = 0`**, by dominated convergence with
the dominating function `∏ r_ab / sinh r_ab`. -/
theorem continuousAt_integral_sphLinks :
    ContinuousAt (fun γ => ∫ x, sphLinks γ x ∂haar4) 0 := by
  refine continuousAt_of_dominated (bound := sphLinks 0)
    (Eventually.of_forall fun γ => (integrable_sphLinks γ).aestronglyMeasurable)
    (Eventually.of_forall fun γ => Eventually.of_forall fun x => ?_) (integrable_sphLinks 0)
    (Eventually.of_forall fun x => ?_)
  · rw [Real.norm_eq_abs]
    exact abs_sphLinks_le γ x
  · unfold sphLinks linkProd
    exact (continuous_finsetProd _ fun a _ => continuous_finsetProd _ fun b _ =>
      continuous_sphericalFn_label _).continuousAt

/-- **Non-vacuity near `γ = 0`**: for all `γ` in some (unquantified) neighbourhood of `0`,
including `γ ≠ 0`, the spin-zero EPRL amplitude is not zero. -/
theorem eventually_eprlVertex_spinZero_ne_zero :
    ∀ᶠ γ in nhds 0, eprlVertex γ (fun _ => 0) (fun _ _ => 1) ≠ 0 := by
  filter_upwards [continuousAt_integral_sphLinks.eventually (lt_mem_nhds
    integral_sphLinks_zero_pos)] with γ hγ
  rw [eprlVertex_spinZero]
  exact_mod_cast hγ.ne'

/-- **Non-vacuity**: some `γ > 0` gives a nonzero spin-zero EPRL amplitude. -/
theorem exists_pos_eprlVertex_spinZero_ne_zero :
    ∃ γ > 0, eprlVertex γ (fun _ => 0) (fun _ _ => 1) ≠ 0 := by
  obtain ⟨γ, hA, hγ⟩ := ((eventually_eprlVertex_spinZero_ne_zero.filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  exact ⟨γ, hγ, hA⟩

/-! ## Wrong model: no gauge fixing -/

/-- The Haar measure on all five vertex variables. -/
noncomputable abbrev haar5 : Measure (Fin 5 → SL2C) := Measure.pi fun _ => haarC

/-- `V₀, …, V₃, V₄ = (y, z) ↦ y · gauge (y⁻¹ z)`: the gauge orbit of a configuration. -/
lemma snoc_eq_mul_gauge (y : SL2C) (z : Fin 4 → SL2C) (a : Fin 5) :
    (Fin.snoc (α := fun _ => SL2C) z y : Fin 5 → SL2C) a = y * gauge (fun i => y⁻¹ * z i) a := by
  induction a using Fin.lastCases with
  | last => rw [Fin.snoc_last (α := fun _ => SL2C), gauge_last, mul_one]
  | cast i => rw [Fin.snoc_castSucc (α := fun _ => SL2C), gauge_castSucc, mul_inv_cancel_left]

/-- **Wrong model: without gauge fixing the dominating integral diverges.** Integrating the
product of the ten kernels `I(V_a⁻¹ V_b)` over all five copies of SL(2,ℂ) gives `∞`: the product
is invariant under `V_a ↦ W V_a` and SL(2,ℂ) has infinite volume. -/
theorem lintegral_linkProd_ungauged_eq_top :
    ∫⁻ V, linkProd (fun a b => kernelE ((V a)⁻¹ * V b)) ∂haar5 = ∞ := by
  set F : (Fin 5 → SL2C) → ℝ≥0∞ := fun V => linkProd fun a b => kernelE ((V a)⁻¹ * V b) with hF
  set Φ : (Fin 4 → SL2C) → ℝ≥0∞ :=
    fun x => linkProd fun a b => kernelE ((gauge x a)⁻¹ * gauge x b) with hΦ
  have hFm : Measurable F := by
    simp only [hF, linkProd]
    exact Finset.measurable_prod _ fun a _ => Finset.measurable_prod _ fun b _ =>
      measurable_kernelE.comp ((measurable_pi_apply a).inv.mul (measurable_pi_apply b))
  have hΦm : Measurable Φ := by
    simp only [hΦ, linkProd]
    exact Finset.measurable_prod _ fun a _ => Finset.measurable_prod _ fun b _ =>
      measurable_kernelE.comp ((measurable_gauge_apply a).inv.mul (measurable_gauge_apply b))
  have hc : ∫⁻ x, Φ x ∂haar4 ≠ 0 := by
    refine ((lintegral_pos_iff_support hΦm).2 ?_).ne'
    have : Function.support Φ = Set.univ := Set.eq_univ_of_forall fun x => by
      simp only [Function.mem_support, hΦ, linkProd, Finset.prod_ne_zero_iff]
      exact fun a _ b _ => (kernelE_pos _).ne'
    rw [this]
    exact pos_iff_ne_zero.2 haar4_univ_ne_zero
  set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => SL2C) (Fin.last 4)
  have e : MeasurePreserving E haar5 (haarC.prod haar4) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin 5 => haarC) (Fin.last 4)
  have hz : ∀ (y : SL2C) (z : Fin 4 → SL2C), F (E.symm (y, z)) = Φ ((fun _ => y⁻¹) * z) := by
    intro y z
    simp only [E, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.insertNth_last', hF, hΦ, snoc_eq_mul_gauge, mul_inv_rev, mul_assoc,
      inv_mul_cancel_left]
    rfl
  have inner : ∀ y : SL2C, ∫⁻ z, F (E.symm (y, z)) ∂haar4 = ∫⁻ x, Φ x ∂haar4 := by
    intro y
    simp_rw [hz]
    exact lintegral_mul_left_eq_self Φ (fun _ => y⁻¹)
  calc ∫⁻ V, F V ∂haar5
      = ∫⁻ p, F (E.symm p) ∂(haarC.prod haar4) :=
        (e.symm.lintegral_comp_emb E.symm.measurableEmbedding F).symm
    _ = ∫⁻ y, ∫⁻ z, F (E.symm (y, z)) ∂haar4 ∂haarC :=
        lintegral_prod _ (hFm.comp E.symm.measurable).aemeasurable
    _ = ∞ := by
        simp_rw [inner]
        rw [lintegral_const, measure_univ_of_isMulLeftInvariant, ENNReal.mul_top hc]

/-! ## The labels: the second Casimir -/

/-- The EPRL vector `Y e_m` is the normalised `L²` class of `tlin (p₀ J) (q₀ J) ρ e_m`, the chart
of the function `hvec (p₀ J) (q₀ J) ρ e_m` on `ℂ²`, with `ρ = γ(J/2 + 1)`. -/
theorem eprlVec_eq (γ : ℝ) (J m : ℕ) (h : m < dsp (J : ℤ) 0 + 1) :
    eprlVec γ J m = ((nrmA (tlin (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) (eprlRho γ J)))⁻¹ : ℂ) •
      tlin (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) (eprlRho γ J) (Pi.single ⟨m, h⟩ 1) := by
  simp only [eprlVec, h, ↓reduceDIte]
  rfl

/-- **Label check**: on the functions `hvec (p₀ J) (q₀ J) ρ x` that define the EPRL vectors
(`eprlVec_eq`), the second Casimir `C₂ = kρ` equals `γ j(j+1)` for `k = j = J/2` and
`ρ = γ(j + 1)`: `γ` times the SU(2) Casimir. -/
theorem casimir2_eprlVec_fun (γ : ℝ) (J : ℕ)
    (x : Fin (0 + p0 (J : ℤ) + (0 + q0 (J : ℤ)) + 1) → ℂ) {ζ : C2} (hζ : ζ ≠ 0) :
    casimir2 (hvec (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) (eprlRho γ J) x) ζ =
      (γ * ((J / 2 : ℂ) * (J / 2 + 1))) *
        hvec (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) (eprlRho γ J) x ζ := by
  have hpq : ((0 + p0 (J : ℤ) : ℕ) : ℤ) - ((0 + q0 (J : ℤ) : ℕ) : ℤ) = J := by
    simp only [p0, q0]; omega
  rw [casimir2_hvec hpq (eprlRho γ J) x hζ, eprlRho]
  push_cast
  ring

/-- **A nonzero value**: `hvec p q ρ x⋆ (0, 1) = nrm (p + q) p ≠ 0` for the weight vector
`x⋆ = xstar p q`, so the functions defining the SU(2)-finite vectors are not identically zero. -/
lemma hvec_xstar_ne_zero (p q : ℕ) (ρ : ℝ) : hvec p q ρ (xstar p q) ![0, 1] ≠ 0 := by
  have h : hvec p q ρ (xstar p q) ![0, 1] = Lightlike.SU2.nrm (p + q) p := tfun_xstar_zero p q ρ
  rw [h]
  exact Lightlike.SU2.nrm_ne_zero (by omega)

/-- **The second Casimir fixes the label**: for `J ≠ 0`, at a point `ζ ≠ 0` where the function
`hvec (p₀ J) (q₀ J) ρ x` of the lowest SU(2) subspace of `π_{J,ρ}` is nonzero, `casimir2` has the
eigenvalue `γ j(j+1)` (with `j = J/2`) exactly when `ρ = eprlRho γ J`. -/
theorem casimir2_hvec_eq_iff (γ ρ : ℝ) {J : ℕ} (hJ : J ≠ 0)
    (x : Fin (0 + p0 (J : ℤ) + (0 + q0 (J : ℤ)) + 1) → ℂ) {ζ : C2} (hζ : ζ ≠ 0)
    (hx : hvec (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) ρ x ζ ≠ 0) :
    casimir2 (hvec (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) ρ x) ζ =
        (γ * ((J / 2 : ℂ) * (J / 2 + 1))) * hvec (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) ρ x ζ ↔
      ρ = eprlRho γ J := by
  have hpq : ((0 + p0 (J : ℤ) : ℕ) : ℤ) - ((0 + q0 (J : ℤ) : ℕ) : ℤ) = J := by
    simp only [p0, q0]; omega
  have hJ' : (J : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hJ
  rw [casimir2_hvec hpq ρ x hζ, mul_left_inj' hx, eprlRho]
  constructor
  · intro h
    apply Complex.ofReal_injective
    apply mul_left_cancel₀ (div_ne_zero hJ' (two_ne_zero (α := ℂ)))
    push_cast at h ⊢
    linear_combination h
  · intro h
    rw [h]
    push_cast
    ring

/-- **Wrong-label control**: the label `ρ = γj` (Engle and Pereira's `2γj` in their
normalisation, see `EPRL.lean`) in place of `eprlRho γ J = γ(j+1)` gives, by
`casimir2_hvec_eq_iff`, a second Casimir different from `γ j(j+1)` on the function `hvec … x⋆`
defining a vector of `π_{J,γj}`, at the point `(0, 1)` where it is nonzero
(`hvec_xstar_ne_zero`). -/
theorem casimir2_wrong_label_ne {γ : ℝ} (hγ : γ ≠ 0) {J : ℕ} (hJ : J ≠ 0) :
    casimir2 (hvec (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) (γ * (J / 2))
        (xstar (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)))) ![0, 1] ≠
      (γ * ((J / 2 : ℂ) * (J / 2 + 1))) * hvec (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ)) (γ * (J / 2))
        (xstar (0 + p0 (J : ℤ)) (0 + q0 (J : ℤ))) ![0, 1] := by
  have hζ : (![0, 1] : C2) ≠ 0 := fun h => by simpa using congrFun h 1
  rw [Ne, casimir2_hvec_eq_iff γ _ hJ _ hζ (hvec_xstar_ne_zero _ _ _), eprlRho]
  intro h
  exact hγ (by linear_combination -h)

end Lightlike.Lorentz
