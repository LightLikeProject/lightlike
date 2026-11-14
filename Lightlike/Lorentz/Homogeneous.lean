module

public import Lightlike.Lorentz.PrincipalSeries

/-!
# The homogeneous model, the Lie algebra action and the two Casimirs

The principal series `(k, ρ)`, `n = 2k`, is the action `(g · F)(ζ) = F(gᵀ ζ)` of `SL(2,ℂ)` on
functions on `ℂ² ∖ 0` that are **homogeneous of degree `(-1+iρ+k, -1+iρ-k)`**:
`F(λ ζ) = m(λ) F(ζ)` for `λ ∈ ℂ^×`, with the multiplier `m` of `PrincipalSeries.lean`
(`IsHomog`). The space `L²(ℂ)` of `PrincipalSeries.lean` is its affine chart `f(z) = F(z, 1)`:
`chart_actH` shows that the chart turns `F ↦ F ∘ gᵀ` into the operator `π(g)` of that file.

## The Lie algebra and the Casimirs

For `X ∈ sl(2,ℂ)` (as a real Lie algebra) the generator acts on differentiable `F` by
`dπ(X) F (ζ) = DF_ζ (Xᵀ ζ)` (`lie`), the derivative of `t ↦ F(γ(t)ᵀ ζ)` at `t = 0` along any curve
`γ` in `SL(2,ℂ)` with `γ(0) = 1`, `γ'(0) = X` (`hasDerivAt_actH`). With the rotation generators
`J_a = (i/2) σ_a` and the boost generators `K_a = σ_a / 2` the two Casimirs are

  `C₁ = Σ_a dπ(K_a)² - dπ(J_a)²`,   `C₂ = - Σ_a dπ(J_a) dπ(K_a)`,

i.e. `C₁ = L² - K²` and `C₂ = L · K` for the Hermitian generators `L_a = i dπ(J_a)`,
`K_a = i dπ(K_a)`.

**Theorem (`casimir1_eq`, `casimir2_eq`).** On every `F` that is homogeneous of degree
`(-1+iρ+k, -1+iρ-k)` and twice differentiable at `ζ ≠ 0`,

  `C₁ F (ζ) = (k² - ρ² - 1) F(ζ)`,   `C₂ F (ζ) = k ρ F(ζ)`.

These are the standard values (Rühl 1970; Barrett et al., *Class. Quantum Grav.* 27 (2010)
165009, eq. (2.6)). The statement holds for every complex `ρ`.

Proof. Differentiating the homogeneity along `t ↦ (1 + t) ζ` and `t ↦ e^{it} ζ` gives the Euler
identities `DF_ζ(ζ) = (2iρ - 2) F(ζ)` and `DF_ζ(iζ) = i n F(ζ)` (`fderiv_euler_radial`,
`fderiv_euler_phase`). Differentiating them once more gives the second derivatives
`D²F(ζ, ζ)`, `D²F(iζ, iζ)` and `D²F(iζ, ζ)`. The Casimirs involve `D²F` only through
`Σ_a D²F(v_a, v_a) - D²F(i v_a, i v_a)` and `Σ_a D²F(i v_a, v_a)` with `v_a = σ_aᵀ ζ`, and the
Fierz identity `Σ_a v_a ⊗ v_a = ζ ⊗ ζ` reduces these to the same expressions at `v = ζ`
(`fierz_sq`, `fierz_mixed`, valid for every symmetric real-bilinear form).
-/

@[expose] public section

open Matrix Complex Filter Topology
open scoped ComplexConjugate

namespace Lightlike.Lorentz

/-- The space `ℂ²` on which the homogeneous model lives. -/
abbrev C2 := Fin 2 → ℂ

/-- **Homogeneity of degree `(-1+iρ+k, -1+iρ-k)`**, `n = 2k`: `F(λ ζ) = m(λ) F(ζ)` for all
`λ ≠ 0` and `ζ ≠ 0`. -/
def IsHomog (n : ℤ) (ρ : ℂ) (F : C2 → ℂ) : Prop :=
  ∀ (w : ℂ) (ζ : C2), w ≠ 0 → ζ ≠ 0 → F (w • ζ) = mult n ρ w * F ζ

/-! ## The group action and the affine chart -/

/-- **The principal-series action on functions on `ℂ²`**: `(g · F)(ζ) = F(gᵀ ζ)`. -/
def actH (g : SL2C) (F : C2 → ℂ) : C2 → ℂ :=
  fun ζ => F ((g : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ)

/-- `actH` is a left action: `(g h) · F = g · (h · F)`. -/
theorem actH_mul (g h : SL2C) (F : C2 → ℂ) : actH (g * h) F = actH g (actH h F) := by
  funext ζ
  simp only [actH, Matrix.SpecialLinearGroup.coe_mul, transpose_mul, mulVec_mulVec]

@[simp] theorem actH_one (F : C2 → ℂ) : actH 1 F = F := by
  funext ζ; simp [actH]

lemma transpose_mulVec_ne_zero (g : SL2C) {ζ : C2} (hζ : ζ ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ ≠ 0 := by
  intro h
  apply hζ
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℂ)ᵀ).det = 1 := by rw [det_transpose]; exact g.2
  have hu : IsUnit ((g : Matrix (Fin 2) (Fin 2) ℂ)ᵀ).det := by rw [hdet]; exact isUnit_one
  have := congrArg (fun v => ((g : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)⁻¹ *ᵥ v) h
  simp only [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec, mulVec_zero] at this
  exact this

/-- The action preserves homogeneity. -/
theorem isHomog_actH {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) (g : SL2C) :
    IsHomog n ρ (actH g F) := by
  intro w ζ hw hζ
  simp only [actH, mulVec_smul]
  exact hF w _ hw (transpose_mulVec_ne_zero g hζ)

/-- The affine chart `f(z) = F(z, 1)`. -/
def chart (F : C2 → ℂ) : ℂ → ℂ := fun z => F ![z, 1]

/-- **The chart intertwines the two models**: `(g · F)(z, 1) = m(den g z) F(mob g z, 1)`, i.e.
`chart (g · F) = act g (chart F)` off the pole. So the action on homogeneous functions is the
operator `π(g)` of `PrincipalSeries.lean`. -/
theorem chart_actH {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) (g : SL2C) {z : ℂ}
    (hz : den g z ≠ 0) : chart (actH g F) z = act n ρ g (chart F) z := by
  have hne : (![mob g z, 1] : C2) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  simp only [chart, actH, act]
  rw [transpose_mulVec_chart g hz, hF _ _ hz hne]

/-- A homogeneous function is determined by its chart: `F(ζ₀, ζ₁) = m(ζ₁) F(ζ₀/ζ₁, 1)`. -/
theorem eq_mult_chart {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) {ζ : C2}
    (h1 : ζ 1 ≠ 0) : F ζ = mult n ρ (ζ 1) * chart F (ζ 0 / ζ 1) := by
  have hne : (![ζ 0 / ζ 1, 1] : C2) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  have e : ζ = ζ 1 • (![ζ 0 / ζ 1, 1] : C2) := by
    ext i; fin_cases i <;> simp; field_simp
  conv_lhs => rw [e]
  rw [hF _ _ h1 hne]; rfl

/-! ## The Lie algebra action -/

/-- **The generator of `X ∈ sl(2,ℂ)`** on differentiable functions: `dπ(X) F (ζ) = DF_ζ(Xᵀ ζ)`. -/
noncomputable def lie (X : Matrix (Fin 2) (Fin 2) ℂ) (F : C2 → ℂ) : C2 → ℂ :=
  fun ζ => fderiv ℝ F ζ (Xᵀ *ᵥ ζ)

/-- **`dπ(X)` is the derivative of the group action**: along any curve `γ` in `SL(2,ℂ)` with
`γ(0) = 1` and `γ'(0) = X` (entrywise), `d/dt|₀ F(γ(t)ᵀ ζ) = dπ(X) F (ζ)`. -/
theorem hasDerivAt_actH (γ : ℝ → SL2C) (X : Matrix (Fin 2) (Fin 2) ℂ) (hγ0 : γ 0 = 1)
    (hγ : ∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ) i j) (X i j) 0)
    {F : C2 → ℂ} {ζ : C2} (hF : DifferentiableAt ℝ F ζ) :
    HasDerivAt (fun t => actH (γ t) F ζ) (lie X F ζ) 0 := by
  have hc : HasDerivAt (fun t => (γ t : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ) (Xᵀ *ᵥ ζ) 0 := by
    rw [hasDerivAt_pi]
    intro i
    have : HasDerivAt (fun t => ∑ j, (γ t : Matrix (Fin 2) (Fin 2) ℂ) j i * ζ j)
        (∑ j, X j i * ζ j) 0 :=
      HasDerivAt.fun_sum fun j _ => (hγ j i).mul_const (ζ j)
    simpa [mulVec, dotProduct, transpose_apply] using this
  have h0 : (γ 0 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ = ζ := by simp [hγ0]
  have hF' : HasFDerivAt F (fderiv ℝ F ζ) ((γ 0 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ *ᵥ ζ) := by
    rw [h0]; exact hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hc

/-- `ζ ↦ Xᵀ ζ` as a real-linear continuous map. -/
noncomputable def mulVecCLM (X : Matrix (Fin 2) (Fin 2) ℂ) : C2 →L[ℝ] C2 :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin Xᵀ).restrictScalars ℝ)

@[simp] lemma mulVecCLM_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (v : C2) :
    mulVecCLM X v = Xᵀ *ᵥ v := rfl

/-- The derivative of `ζ ↦ DF_ζ(A ζ)` for a real-linear `A`: `D²F_ζ(v, Aζ) + DF_ζ(A v)`. -/
lemma fderiv_fderiv_apply_clm {F : C2 → ℂ} {ζ : C2} (hF : ContDiffAt ℝ 2 F ζ) (A : C2 →L[ℝ] C2)
    (v : C2) :
    fderiv ℝ (fun ζ' => fderiv ℝ F ζ' (A ζ')) ζ v =
      fderiv ℝ (fderiv ℝ F) ζ v (A ζ) + fderiv ℝ F ζ (A v) := by
  have h2 : DifferentiableAt ℝ (fderiv ℝ F) ζ :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have := h2.hasFDerivAt.clm_apply A.hasFDerivAt
  rw [this.fderiv]
  simp [add_comm]

/-- **Second-order formula**: `dπ(X) dπ(Y) F (ζ) = D²F_ζ(Xᵀζ, Yᵀζ) + DF_ζ(Yᵀ Xᵀ ζ)`. -/
theorem lie_lie {F : C2 → ℂ} {ζ : C2} (hF : ContDiffAt ℝ 2 F ζ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    lie X (lie Y F) ζ =
      fderiv ℝ (fderiv ℝ F) ζ (Xᵀ *ᵥ ζ) (Yᵀ *ᵥ ζ) + fderiv ℝ F ζ (Yᵀ *ᵥ (Xᵀ *ᵥ ζ)) := by
  exact fderiv_fderiv_apply_clm hF (mulVecCLM Y) (Xᵀ *ᵥ ζ)

/-! ## Euler identities -/

/-- `m(r) = r^{2iρ - 2}` for real `r > 0`. -/
lemma mult_ofReal_pos (n : ℤ) (ρ : ℂ) {r : ℝ} (hr : 0 < r) :
    mult n ρ (r : ℂ) = (r : ℂ) ^ (2 * I * ρ - 2) := by
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [mult, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr']

/-- `m(e^{iθ}) = e^{inθ}`. -/
lemma mult_exp (n : ℤ) (ρ : ℂ) (θ : ℝ) :
    mult n ρ (cexp (θ * I)) = cexp (n * (θ * I)) := by
  have h1 : ‖cexp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  simp only [mult, h1, Complex.ofReal_one, Complex.one_cpow, one_mul, div_one]
  rw [← Complex.exp_int_mul]

/-- **Radial Euler identity** `DF_ζ(ζ) = (2iρ - 2) F(ζ)`. -/
theorem fderiv_euler_radial {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) {ζ : C2}
    (hζ : ζ ≠ 0) (hd : DifferentiableAt ℝ F ζ) :
    fderiv ℝ F ζ ζ = (2 * I * ρ - 2) * F ζ := by
  -- the curve `t ↦ (1 + t) ζ`
  have hc : HasDerivAt (fun t : ℝ => ((1 + t : ℝ) : ℂ) • ζ) ζ 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ((1 + t : ℝ) : ℂ)) 1 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_add 1).ofReal_comp
      simpa using this
    simpa using h1.smul_const ζ
  have hL : HasDerivAt (fun t : ℝ => F (((1 + t : ℝ) : ℂ) • ζ)) (fderiv ℝ F ζ ζ) 0 := by
    have hF' : HasFDerivAt F (fderiv ℝ F ζ) (((1 + 0 : ℝ) : ℂ) • ζ) := by
      simpa using hd.hasFDerivAt
    exact hF'.comp_hasDerivAt (0 : ℝ) hc
  have hR : HasDerivAt (fun t : ℝ => ((1 + t : ℝ) : ℂ) ^ (2 * I * ρ - 2) * F ζ)
      ((2 * I * ρ - 2) * F ζ) 0 := by
    by_cases hs : (2 * I * ρ - 2) = 0
    · simpa [hs] using hasDerivAt_const (0 : ℝ) (F ζ)
    · have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (2 * I * ρ - 2)) (2 * I * ρ - 2) (1 + 0) := by
        simpa using hasDerivAt_ofReal_cpow_const (x := (1 : ℝ)) one_ne_zero hs
      have := (h1.comp_const_add 1 0).mul_const (F ζ)
      simpa using this
  have heq : (fun t : ℝ => F (((1 + t : ℝ) : ℂ) • ζ)) =ᶠ[𝓝 0]
      fun t : ℝ => ((1 + t : ℝ) : ℂ) ^ (2 * I * ρ - 2) * F ζ := by
    have : ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t := by
      filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
        with t ht
      linarith [ht.1]
    filter_upwards [this] with t ht
    have hne : ((1 + t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [hF _ _ hne hζ, mult_ofReal_pos n ρ ht]
  exact (hL.congr_of_eventuallyEq heq.symm).unique hR |>.symm.trans rfl |>.symm

/-- **Phase Euler identity** `DF_ζ(iζ) = i n F(ζ)`. -/
theorem fderiv_euler_phase {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) {ζ : C2}
    (hζ : ζ ≠ 0) (hd : DifferentiableAt ℝ F ζ) :
    fderiv ℝ F ζ (I • ζ) = (I * n) * F ζ := by
  have he : HasDerivAt (fun t : ℝ => cexp (t * I)) I 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I
    simpa using h1.cexp
  have hc : HasDerivAt (fun t : ℝ => cexp (t * I) • ζ) (I • ζ) 0 := he.smul_const ζ
  have hL : HasDerivAt (fun t : ℝ => F (cexp (t * I) • ζ)) (fderiv ℝ F ζ (I • ζ)) 0 := by
    have hF' : HasFDerivAt F (fderiv ℝ F ζ) (cexp (((0 : ℝ) : ℂ) * I) • ζ) := by
      simpa using hd.hasFDerivAt
    exact hF'.comp_hasDerivAt (0 : ℝ) hc
  have hR : HasDerivAt (fun t : ℝ => cexp (n * ((t : ℂ) * I)) * F ζ) ((I * n) * F ζ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (n : ℂ) * ((t : ℂ) * I)) (n * I) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_mul (n : ℂ)
    have := h1.cexp.mul_const (F ζ)
    simpa [mul_comm] using this
  have heq : (fun t : ℝ => F (cexp (t * I) • ζ)) = fun t : ℝ => cexp (n * ((t : ℂ) * I)) * F ζ := by
    funext t
    rw [hF _ _ (Complex.exp_ne_zero _) hζ, mult_exp]
  rw [heq] at hL
  exact hL.unique hR

/-! ## The Fierz identity for real-bilinear forms -/

/-- The Pauli matrices `σ₁, σ₂, σ₃`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -I; I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The boost generators `K_a = σ_a / 2`. -/
noncomputable def boostGen (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • pauli a
/-- The rotation generators `J_a = (i/2) σ_a` (they generate `SU(2)`). -/
noncomputable def rotGen (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ := (I / 2) • pauli a

/-- The vectors `v_a = σ_aᵀ ζ`. -/
def pv (a : Fin 3) (ζ : C2) : C2 := (pauli a)ᵀ *ᵥ ζ

/-- The real basis `e₀, i e₀, e₁, i e₁` of `ℂ²`. -/
def rb : Fin 4 → C2
  | 0 => ![1, 0]
  | 1 => ![I, 0]
  | 2 => ![0, 1]
  | 3 => ![0, I]

/-- The real coordinates of a vector of `ℂ²` in the basis `rb`. -/
def realCoord (u : C2) : Fin 4 → ℝ
  | 0 => (u 0).re
  | 1 => (u 0).im
  | 2 => (u 1).re
  | 3 => (u 1).im

/-- Every vector of `ℂ²` in the real basis. -/
lemma eq_rb (u : C2) : u = ∑ i, realCoord u i • rb i := by
  ext j; fin_cases j <;> simp [realCoord, rb, Fin.sum_univ_four]

/-- The coefficients `B(e_i, e_j)` of a real-bilinear form in the real basis. -/
def bco (B : C2 →L[ℝ] C2 →L[ℝ] ℂ) (i j : Fin 4) : ℂ := B (rb i) (rb j)

/-- A real-bilinear form in the real basis. -/
lemma bilin_rb (B : C2 →L[ℝ] C2 →L[ℝ] ℂ) (u w : C2) :
    B u w = ∑ i, ∑ j, ((realCoord u i * realCoord w j : ℝ) : ℂ) * bco B i j := by
  conv_lhs => rw [eq_rb u, eq_rb w]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, Finset.smul_sum, Complex.real_smul,
    Complex.ofReal_mul, bco]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma pv_zero (ζ : C2) : pv 0 ζ = ![ζ 1, ζ 0] := by
  ext i; fin_cases i <;> simp [pv, pauli, mulVec, dotProduct, Fin.sum_univ_two]
lemma pv_one (ζ : C2) : pv 1 ζ = ![I * ζ 1, -(I * ζ 0)] := by
  ext i; fin_cases i <;> simp [pv, pauli, mulVec, dotProduct, Fin.sum_univ_two]
lemma pv_two (ζ : C2) : pv 2 ζ = ![ζ 0, -ζ 1] := by
  ext i; fin_cases i <;> simp [pv, pauli, mulVec, dotProduct, Fin.sum_univ_two]

/-- Symmetry of the coefficients. -/
lemma bco_symm (B : C2 →L[ℝ] C2 →L[ℝ] ℂ) (hB : ∀ u w, B u w = B w u) (i j : Fin 4) :
    bco B i j = bco B j i := hB _ _

/-- **Fierz identity, quadratic part**: for a symmetric real-bilinear form `B` on `ℂ²`,
`Σ_a B(v_a, v_a) - B(i v_a, i v_a) = B(ζ, ζ) - B(iζ, iζ)` with `v_a = σ_aᵀ ζ`. -/
theorem fierz_sq (B : C2 →L[ℝ] C2 →L[ℝ] ℂ) (hB : ∀ u w, B u w = B w u) (ζ : C2) :
    ∑ a, (B (pv a ζ) (pv a ζ) - B (I • pv a ζ) (I • pv a ζ)) = B ζ ζ - B (I • ζ) (I • ζ) := by
  rw [Fin.sum_univ_three, pv_zero, pv_one, pv_two]
  simp only [bilin_rb B, Fin.sum_univ_four, realCoord, Matrix.smul_cons, smul_eq_mul,
    Matrix.smul_empty, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  rw [bco_symm B hB 1 0, bco_symm B hB 2 0, bco_symm B hB 3 0, bco_symm B hB 2 1,
    bco_symm B hB 3 1, bco_symm B hB 3 2]
  push_cast
  ring

/-- **Fierz identity, mixed part**: `Σ_a B(i v_a, v_a) = B(iζ, ζ)` for symmetric `B`. -/
theorem fierz_mixed (B : C2 →L[ℝ] C2 →L[ℝ] ℂ) (hB : ∀ u w, B u w = B w u) (ζ : C2) :
    ∑ a, B (I • pv a ζ) (pv a ζ) = B (I • ζ) ζ := by
  rw [Fin.sum_univ_three, pv_zero, pv_one, pv_two]
  simp only [bilin_rb B, Fin.sum_univ_four, realCoord, Matrix.smul_cons, smul_eq_mul,
    Matrix.smul_empty, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  rw [bco_symm B hB 1 0, bco_symm B hB 2 0, bco_symm B hB 3 0, bco_symm B hB 2 1,
    bco_symm B hB 3 1, bco_symm B hB 3 2]
  push_cast
  ring

/-! ## The Casimirs -/

/-- **The first Casimir** `C₁ = Σ_a dπ(K_a)² - dπ(J_a)²` (`= L² - K²` in Hermitian form). -/
noncomputable def casimir1 (F : C2 → ℂ) : C2 → ℂ :=
  fun ζ => ∑ a, (lie (boostGen a) (lie (boostGen a) F) ζ - lie (rotGen a) (lie (rotGen a) F) ζ)

/-- **The second Casimir** `C₂ = - Σ_a dπ(J_a) dπ(K_a)` (`= L · K` in Hermitian form). -/
noncomputable def casimir2 (F : C2 → ℂ) : C2 → ℂ :=
  fun ζ => -∑ a, lie (rotGen a) (lie (boostGen a) F) ζ

lemma I_cube : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
lemma I_four : I ^ 4 = 1 := by rw [show 4 = 2 + 2 from rfl, pow_add, I_sq]; norm_num

lemma boostGen_mulVec (a : Fin 3) (ζ : C2) : (boostGen a)ᵀ *ᵥ ζ = (1 / 2 : ℝ) • pv a ζ := by
  ext i; fin_cases a <;> fin_cases i <;>
    simp [boostGen, pv, pauli, mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff]

lemma rotGen_mulVec (a : Fin 3) (ζ : C2) : (rotGen a)ᵀ *ᵥ ζ = (1 / 2 : ℝ) • (I • pv a ζ) := by
  ext i; fin_cases a <;> fin_cases i <;>
    simp [rotGen, pv, pauli, mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff]

lemma boostGen_sq (a : Fin 3) (ζ : C2) :
    (boostGen a)ᵀ *ᵥ ((boostGen a)ᵀ *ᵥ ζ) = (1 / 4 : ℝ) • ζ := by
  ext i; fin_cases a <;> fin_cases i <;>
    simp [boostGen, pauli, mulVec, dotProduct, Fin.sum_univ_two, Complex.real_smul] <;> ring_nf <;>
    simp only [I_sq] <;> ring

lemma rotGen_sq (a : Fin 3) (ζ : C2) :
    (rotGen a)ᵀ *ᵥ ((rotGen a)ᵀ *ᵥ ζ) = (-(1 / 4) : ℝ) • ζ := by
  ext i; fin_cases a <;> fin_cases i <;>
    simp [rotGen, pauli, mulVec, dotProduct, Fin.sum_univ_two, Complex.real_smul] <;> ring_nf <;>
    simp only [I_sq, I_four] <;> ring

lemma boostGen_rotGen (a : Fin 3) (ζ : C2) :
    (boostGen a)ᵀ *ᵥ ((rotGen a)ᵀ *ᵥ ζ) = (1 / 4 : ℝ) • (I • ζ) := by
  ext i; fin_cases a <;> fin_cases i <;>
    simp [boostGen, rotGen, pauli, mulVec, dotProduct, Fin.sum_univ_two, Complex.real_smul] <;>
    ring_nf <;> simp only [I_cube] <;> ring

/-- The second derivatives forced by homogeneity. -/
lemma second_derivs {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) {ζ : C2} (hζ : ζ ≠ 0)
    (hc : ContDiffAt ℝ 2 F ζ) :
    fderiv ℝ (fderiv ℝ F) ζ ζ ζ = (2 * I * ρ - 2 - 1) * (2 * I * ρ - 2) * F ζ ∧
    fderiv ℝ (fderiv ℝ F) ζ (I • ζ) (I • ζ) = ((2 * I * ρ - 2) - n ^ 2) * F ζ ∧
    fderiv ℝ (fderiv ℝ F) ζ (I • ζ) ζ = (2 * I * ρ - 2 - 1) * (I * n) * F ζ := by
  set σ : ℂ := 2 * I * ρ - 2
  have hd : DifferentiableAt ℝ F ζ := hc.differentiableAt (by norm_num)
  -- Euler identities near ζ
  have hnear : ∀ᶠ ζ' in 𝓝 ζ, ζ' ≠ 0 ∧ DifferentiableAt ℝ F ζ' := by
    filter_upwards [isOpen_ne.mem_nhds hζ, hc.eventually (by simp)] with ζ' h1 h2
    exact ⟨h1, h2.differentiableAt (by norm_num)⟩
  have hE1 : (fun ζ' => fderiv ℝ F ζ' (ContinuousLinearMap.id ℝ C2 ζ')) =ᶠ[𝓝 ζ]
      fun ζ' => σ * F ζ' := by
    filter_upwards [hnear] with ζ' ⟨h1, h2⟩
    exact fderiv_euler_radial hF h1 h2
  have hE2 : (fun ζ' => fderiv ℝ F ζ' ((I • ContinuousLinearMap.id ℝ C2) ζ')) =ᶠ[𝓝 ζ]
      fun ζ' => (I * n) * F ζ' := by
    filter_upwards [hnear] with ζ' ⟨h1, h2⟩
    exact fderiv_euler_phase hF h1 h2
  have hR1 : ∀ v, fderiv ℝ (fderiv ℝ F) ζ v ζ + fderiv ℝ F ζ v = σ * fderiv ℝ F ζ v := by
    intro v
    have := fderiv_fderiv_apply_clm hc (ContinuousLinearMap.id ℝ C2) v
    rw [hE1.fderiv_eq] at this
    simp only [ContinuousLinearMap.id_apply] at this
    rw [← this, fderiv_const_mul hd]; rfl
  have hR2 : ∀ v, fderiv ℝ (fderiv ℝ F) ζ v (I • ζ) + fderiv ℝ F ζ (I • v) =
      (I * n) * fderiv ℝ F ζ v := by
    intro v
    have := fderiv_fderiv_apply_clm hc (I • ContinuousLinearMap.id ℝ C2) v
    rw [hE2.fderiv_eq] at this
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply] at this
    rw [← this, fderiv_const_mul hd]; rfl
  have e1 := fderiv_euler_radial hF hζ hd
  have e2 := fderiv_euler_phase hF hζ hd
  have hII : I • I • ζ = -ζ := by rw [smul_smul, I_mul_I, neg_one_smul]
  refine ⟨?_, ?_, ?_⟩
  · have := hR1 ζ; rw [e1] at this; linear_combination this
  · have := hR2 (I • ζ); rw [hII, map_neg, e1, e2] at this
    linear_combination this + ((n : ℂ) ^ 2 * F ζ) * Complex.I_sq
  · have := hR1 (I • ζ); rw [e2] at this; linear_combination this

/-- **The first Casimir**: `C₁ F = (k² - ρ² - 1) F` on homogeneous `F` of degree
`(-1+iρ+k, -1+iρ-k)`, `k = n/2`, at every point `ζ ≠ 0` where `F` is `C²`. -/
theorem casimir1_eq {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) {ζ : C2} (hζ : ζ ≠ 0)
    (hc : ContDiffAt ℝ 2 F ζ) :
    casimir1 F ζ = ((n / 2 : ℂ) ^ 2 - ρ ^ 2 - 1) * F ζ := by
  have hd : DifferentiableAt ℝ F ζ := hc.differentiableAt (by norm_num)
  have hsym := hc.isSymmSndFDerivAt (by simp)
  obtain ⟨h1, h2, -⟩ := second_derivs hF hζ hc
  have hf := fierz_sq (fderiv ℝ (fderiv ℝ F) ζ) (fun u w => hsym u w) ζ
  have e1 := fderiv_euler_radial hF hζ hd
  have hterm : ∀ a, lie (boostGen a) (lie (boostGen a) F) ζ - lie (rotGen a) (lie (rotGen a) F) ζ
      = (1 / 4 : ℂ) * (fderiv ℝ (fderiv ℝ F) ζ (pv a ζ) (pv a ζ) -
          fderiv ℝ (fderiv ℝ F) ζ (I • pv a ζ) (I • pv a ζ)) +
        (1 / 2 : ℂ) * fderiv ℝ F ζ ζ := by
    intro a
    rw [lie_lie hc, lie_lie hc, boostGen_sq, rotGen_sq, boostGen_mulVec, rotGen_mulVec]
    simp only [map_smul, _root_.smul_apply, Complex.real_smul]
    push_cast; ring
  simp only [casimir1, hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hf, h1, h2, e1,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linear_combination (ρ ^ 2 * F ζ) * Complex.I_sq

/-- **The second Casimir**: `C₂ F = k ρ F` on homogeneous `F` of degree `(-1+iρ+k, -1+iρ-k)`,
`k = n/2`, at every point `ζ ≠ 0` where `F` is `C²`. -/
theorem casimir2_eq {n : ℤ} {ρ : ℂ} {F : C2 → ℂ} (hF : IsHomog n ρ F) {ζ : C2} (hζ : ζ ≠ 0)
    (hc : ContDiffAt ℝ 2 F ζ) :
    casimir2 F ζ = ((n / 2 : ℂ) * ρ) * F ζ := by
  have hd : DifferentiableAt ℝ F ζ := hc.differentiableAt (by norm_num)
  have hsym := hc.isSymmSndFDerivAt (by simp)
  obtain ⟨-, -, h3⟩ := second_derivs hF hζ hc
  have hf := fierz_mixed (fderiv ℝ (fderiv ℝ F) ζ) (fun u w => hsym u w) ζ
  have e2 := fderiv_euler_phase hF hζ hd
  have hterm : ∀ a, lie (rotGen a) (lie (boostGen a) F) ζ =
      (1 / 4 : ℂ) * fderiv ℝ (fderiv ℝ F) ζ (I • pv a ζ) (pv a ζ) +
        (1 / 4 : ℂ) * fderiv ℝ F ζ (I • ζ) := by
    intro a
    rw [lie_lie hc, boostGen_rotGen, rotGen_mulVec, boostGen_mulVec]
    simp only [map_smul, _root_.smul_apply, Complex.real_smul]
    push_cast; ring
  simp only [casimir2, hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hf, h3, e2,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  linear_combination (-(n : ℂ) * ρ / 2 * F ζ) * Complex.I_sq

end Lightlike.Lorentz
