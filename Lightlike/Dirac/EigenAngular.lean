import Mathlib
import Lightlike.Dirac.EigenGeneralK

/-!
# Angular modes of the flat Dirac operator on the plane

For a Clifford module `V` of `Cl₂` the operator `J = γ₀γ₁` satisfies `J² = -1` and `γ₁ = -γ₀ J`.
It makes `V` a complex vector space, and `γ₀` is antilinear.  Every `V`-valued function of the form
`g = Lv(c₁) + γ₀ Lv(c₂)`, with `c₁, c₂ : ℝ² → ℂ` and `Lv c = Re c • v + Im c • J v`,
has flat Dirac operator
`D₀ g = γ₀ Lv(∂₀c₁ − i ∂₁c₁) − Lv(∂₀c₂ + i ∂₁c₂)`
(`dirac_angular`): the two Wirtinger derivatives `2∂_z c₁`, `2∂_{z̄} c₂` appear.
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The complex structure `J = γ₀γ₁` on a `Cl₂`-module. -/
noncomputable def Jop (ρ : CliffordRep 2 V) : V →L[ℝ] V := (gam ρ 0).comp (gam ρ 1)

/-- `J² = -1`. -/
lemma Jop_sq (ρ : CliffordRep 2 V) (w : V) : Jop ρ (Jop ρ w) = -w := by
  have h01 : ∀ u, gam ρ 1 (gam ρ 0 u) = -gam ρ 0 (gam ρ 1 u) := fun u =>
    eq_neg_of_add_eq_zero_left (by
      have := gam_anticomm ρ (i := 1) (j := 0) (by decide) u
      exact this)
  simp only [Jop, ContinuousLinearMap.comp_apply]
  rw [h01, map_neg, gam_sq, ← neg_neg (gam ρ 1 w)]
  simp [gam_sq]

/-- `γ₀ J = -γ₁`. -/
lemma gam0_Jop (ρ : CliffordRep 2 V) (w : V) : gam ρ 0 (Jop ρ w) = -gam ρ 1 w := by
  simp [Jop, gam_sq]

/-- `γ₁ w = -γ₀ (J w)`. -/
lemma gam1_eq (ρ : CliffordRep 2 V) (w : V) : gam ρ 1 w = -gam ρ 0 (Jop ρ w) := by
  rw [gam0_Jop, neg_neg]

/-- `J γ₀ = γ₁ ` on vectors: `J (γ₀ w) = γ₁ w`... stated as `γ₀ J = -J γ₀`. -/
lemma gam0_Jop_comm (ρ : CliffordRep 2 V) (w : V) : gam ρ 0 (Jop ρ w) = -Jop ρ (gam ρ 0 w) := by
  have h : ∀ u, gam ρ 1 (gam ρ 0 u) = -gam ρ 0 (gam ρ 1 u) := fun u =>
    eq_neg_of_add_eq_zero_left (gam_anticomm ρ (i := 1) (j := 0) (by decide) u)
  simp [Jop, gam_sq, h]

/-- The real-linear map `c ↦ Re c • v + Im c • J v` from `ℂ` to `V`. -/
noncomputable def Lv (ρ : CliffordRep 2 V) (v : V) : ℂ →L[ℝ] V :=
  Complex.reCLM.smulRight v + Complex.imCLM.smulRight (Jop ρ v)

lemma Lv_apply (ρ : CliffordRep 2 V) (v : V) (c : ℂ) : Lv ρ v c = c.re • v + c.im • Jop ρ v := by
  simp [Lv]

/-- Multiplication by `i` on `ℂ` is `J` on `V`. -/
lemma Lv_I_mul (ρ : CliffordRep 2 V) (v : V) (c : ℂ) : Lv ρ v (Complex.I * c) = Jop ρ (Lv ρ v c) := by
  simp [Lv_apply, Jop_sq, map_add, map_smul]
  abel

/-- The spinor `Lv(c₁) + γ₀ Lv(c₂)`. -/
noncomputable def angSpinor (ρ : CliffordRep 2 V) (v : V) (c₁ c₂ : E 2 → ℂ) : E 2 → V :=
  fun y => Lv ρ v (c₁ y) + gam ρ 0 (Lv ρ v (c₂ y))

/-- The derivative of an angular spinor. -/
lemma hasFDerivAt_angSpinor (ρ : CliffordRep 2 V) (v : V) {c₁ c₂ : E 2 → ℂ} {c₁' c₂' : E 2 →L[ℝ] ℂ}
    {x : E 2} (h₁ : HasFDerivAt c₁ c₁' x) (h₂ : HasFDerivAt c₂ c₂' x) :
    HasFDerivAt (angSpinor ρ v c₁ c₂)
      ((Lv ρ v).comp c₁' + (gam ρ 0).comp ((Lv ρ v).comp c₂')) x :=
  ((Lv ρ v).hasFDerivAt.comp x h₁).add ((gam ρ 0).hasFDerivAt.comp x ((Lv ρ v).hasFDerivAt.comp x h₂))

/-- **Flat Dirac operator of an angular spinor.** -/
theorem dirac_angular (ρ : CliffordRep 2 V) (v : V) {c₁ c₂ : E 2 → ℂ} {c₁' c₂' : E 2 →L[ℝ] ℂ}
    {x : E 2} (h₁ : HasFDerivAt c₁ c₁' x) (h₂ : HasFDerivAt c₂ c₂' x) :
    dirac ρ (angSpinor ρ v c₁ c₂) x =
      gam ρ 0 (Lv ρ v (c₁' (e 0) - Complex.I * c₁' (e 1))) -
        Lv ρ v (c₂' (e 0) + Complex.I * c₂' (e 1)) := by
  have hd := hasFDerivAt_angSpinor ρ v h₁ h₂
  simp only [dirac, Fin.sum_univ_two, hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add, map_sub]
  have hI : ∀ c : ℂ, Lv ρ v (Complex.I * c) = Jop ρ (Lv ρ v c) := Lv_I_mul ρ v
  have k1 : ∀ X, gam ρ 1 (gam ρ 0 X) = -Jop ρ X := by
    intro X
    have := gam_anticomm ρ (i := 1) (j := 0) (by decide) X
    simp only [Jop, ContinuousLinearMap.comp_apply]
    exact eq_neg_of_add_eq_zero_left this
  rw [hI, hI, gam1_eq ρ (Lv ρ v (c₁' (e 1))), k1, gam_sq]
  abel

/-- The complex coordinate `z = y₀ + i y₁` as a real-linear map. -/
noncomputable def zcL : E 2 →L[ℝ] ℂ :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (1 : ℂ) + (EuclideanSpace.proj (1 : Fin 2)).smulRight Complex.I

lemma zcL_apply (y : E 2) : zcL y = (y 0 : ℂ) + (y 1 : ℂ) * Complex.I := by
  simp [zcL]

/-- A radial profile times a power of `z`: `y ↦ φ(‖y‖²) z^m`. -/
noncomputable def angProfile (φ : ℝ → ℝ) (m : ℕ) : E 2 → ℂ :=
  fun y => ((φ (‖y‖ ^ 2) : ℝ) : ℂ) * (zcL y) ^ m

/-- The two Wirtinger-type combinations of the derivative of `φ(‖y‖²) z^m`. -/
theorem angProfile_deriv (φ : ℝ → ℝ) (m : ℕ) {φ' : ℝ} (x : E 2)
    (hφ : HasDerivAt φ φ' (‖x‖ ^ 2)) :
    ∃ Ψ' : E 2 →L[ℝ] ℂ, HasFDerivAt (angProfile φ m) Ψ' x ∧
      Ψ' (e 0) - Complex.I * Ψ' (e 1) =
        2 * (φ' : ℂ) * (starRingEnd ℂ (zcL x)) * (zcL x) ^ m + 2 * m * (φ (‖x‖ ^ 2) : ℂ) * (zcL x) ^ (m - 1) ∧
      Ψ' (e 0) + Complex.I * Ψ' (e 1) = 2 * (φ' : ℂ) * (zcL x) ^ (m + 1) := by
  have ht : HasFDerivAt (fun y : E 2 => ‖y‖ ^ 2) ((2 : ℝ) • innerSL ℝ x) x := by
    have := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have e2 : ((2 : ℕ) • (innerSL ℝ x) : E 2 →L[ℝ] ℝ) = (2 : ℝ) • innerSL ℝ x := by
      rw [← Nat.cast_smul_eq_nsmul ℝ]; norm_num
    rwa [e2] at this
  have hφt := hφ.comp_hasFDerivAt x ht
  have hre := Complex.ofRealCLM.hasFDerivAt.comp x hφt
  have hz : HasFDerivAt (fun y : E 2 => zcL y) zcL x := zcL.hasFDerivAt
  have hzp := hz.pow m
  have hm := hre.mul hzp
  refine ⟨_, hm, ?_, ?_⟩
  · simp [zcL_apply, e, innerSL_apply_apply, EuclideanSpace.inner_single_right]
    linear_combination (-((φ (‖x‖ ^ 2) : ℂ) * m * ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ^ (m - 1))) * Complex.I_sq
  · simp [zcL_apply, e, innerSL_apply_apply, EuclideanSpace.inner_single_right]
    linear_combination (((φ (‖x‖ ^ 2) : ℂ) * m * ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) ^ (m - 1))) * Complex.I_sq

open Polynomial in
/-- The profile `t ↦ (1+t)^{-s} P(t)` and its derivative. -/
lemma hasDerivAt_prof (s : ℕ) (P : ℝ[X]) {t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (fun u : ℝ => ((1 + u) ^ s)⁻¹ * P.eval u)
      (((1 + t) ^ s)⁻¹ * P.derivative.eval t - (s : ℝ) * ((1 + t) ^ (s + 1))⁻¹ * P.eval t) t := by
  have h1 : HasDerivAt (fun u : ℝ => (1 + u) ^ s) ((s : ℝ) * (1 + t) ^ (s - 1)) t := by
    have := (hasDerivAt_pow s (1 + t)).comp t ((hasDerivAt_id t).const_add 1)
    simp only [mul_one] at this
    exact this
  have hne : (1 + t) ^ s ≠ 0 := pow_ne_zero _ ht
  have h2 := (h1.inv hne).mul (P.hasDerivAt t)
  convert h2 using 1
  rcases s with _ | s
  · simp
  · simp only [Nat.add_sub_cancel]
    have ha : (1 + t) ^ s ≠ 0 := pow_ne_zero _ ht
    push_cast
    rw [pow_succ]
    simp only [Pi.inv_apply]
    field_simp
    ring

open Polynomial in
/-- The angular spinor `g_{n}` built from radial polynomials `G` (for `c₁ = (1+t)^{-s} z^{n+1} G`)
and `F` (for `c₂ = (1+t)^{-s} z^n F`), `t = ‖y‖²`. -/
noncomputable def angG (ρ : CliffordRep 2 V) (v : V) (n s : ℕ) (G F : ℝ[X]) : E 2 → V :=
  angSpinor ρ v (angProfile (fun u => ((1 + u) ^ s)⁻¹ * G.eval u) (n + 1))
    (angProfile (fun u => ((1 + u) ^ s)⁻¹ * F.eval u) n)

lemma zbar_mul_z (x : E 2) : starRingEnd ℂ (zcL x) * zcL x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [zcL_apply, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, Complex.ext_iff, pow_two]
  ring

open Polynomial in
/-- **Flat equation of the angular spinor.** If `G, F` satisfy
`(1+X)((n+1) G + X G') − s X G = λ F` and `−((1+X) F' − s F) = λ G`, then `h D₀ g = λ g`. -/
theorem angG_flat_eigen (ρ : CliffordRep 2 V) (v : V) (n s : ℕ) (G F : ℝ[X]) (lam : ℝ)
    (ha : (1 + X) * (C ((n : ℝ) + 1) * G + X * G.derivative) - C (s : ℝ) * X * G = C lam * F)
    (hb : -((1 + X) * F.derivative - C (s : ℝ) * F) = C lam * G) (x : E 2) :
    stereoH x • dirac ρ (angG ρ v n s G F) x = lam • angG ρ v n s G F x := by
  have hne : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  obtain ⟨Ψ1, h1, d1m, d1p⟩ := angProfile_deriv (fun u => ((1 + u) ^ s)⁻¹ * G.eval u) (n + 1) x
    (hasDerivAt_prof s G hne)
  obtain ⟨Ψ2, h2, d2m, d2p⟩ := angProfile_deriv (fun u => ((1 + u) ^ s)⁻¹ * F.eval u) n x
    (hasDerivAt_prof s F hne)
  have hD := dirac_angular ρ v h1 h2
  have hae := congrArg (Polynomial.eval (‖x‖ ^ 2)) ha
  have hbe := congrArg (Polynomial.eval (‖x‖ ^ 2)) hb
  simp only [eval_mul, eval_add, eval_sub, eval_neg, eval_C, eval_X, eval_one] at hae hbe
  have hzz := zbar_mul_z x
  have hh : stereoH x = (1 + ‖x‖ ^ 2) / 2 := rfl
  generalize hT : ‖x‖ ^ 2 = T at *
  have hpow : starRingEnd ℂ (zcL x) * zcL x ^ (n + 1) = (T : ℂ) * zcL x ^ n := by
    rw [pow_succ, ← mul_assoc, mul_comm _ (zcL x ^ n), mul_assoc, hzz, mul_comm]
  have hcne : (1 + (T : ℂ)) ≠ 0 := by exact_mod_cast hne
  have hpne : ((1 + (T : ℂ)) ^ s) ≠ 0 := pow_ne_zero _ hcne
  have hac : (1 + (T : ℂ)) * (((n : ℂ) + 1) * ((G.eval T : ℝ) : ℂ) + T * ((G.derivative.eval T : ℝ) : ℂ)) -
      s * T * ((G.eval T : ℝ) : ℂ) = lam * ((F.eval T : ℝ) : ℂ) := by exact_mod_cast hae
  have hbc : -((1 + (T : ℂ)) * ((F.derivative.eval T : ℝ) : ℂ) - s * ((F.eval T : ℝ) : ℂ)) = lam * ((G.eval T : ℝ) : ℂ) := by
    exact_mod_cast hbe
  have eA : stereoH x • (Ψ1 (e 0) - Complex.I * Ψ1 (e 1)) =
      lam • (((((1 + T) ^ s)⁻¹ * F.eval T : ℝ) : ℂ) * zcL x ^ n) := by
    rw [d1m, Complex.real_smul, Complex.real_smul, hh, Nat.add_sub_cancel]
    push_cast
    rw [mul_assoc (2 * _) _ (zcL x ^ (n + 1)), hpow]
    field_simp
    linear_combination ((1 + (T : ℂ)) ^ (s + 1) * zcL x ^ n) * hac
  have eB : stereoH x • (Ψ2 (e 0) + Complex.I * Ψ2 (e 1)) =
      -lam • (((((1 + T) ^ s)⁻¹ * G.eval T : ℝ) : ℂ) * zcL x ^ (n + 1)) := by
    rw [d2p, Complex.real_smul, Complex.real_smul, hh]
    push_cast
    field_simp
    linear_combination (-((1 + (T : ℂ)) ^ (s + 1) * zcL x ^ (n + 1))) * hbc
  unfold angG
  rw [hD]
  have e3 : stereoH x • ((gam ρ 0) ((Lv ρ v) (Ψ1 (e 0) - Complex.I * Ψ1 (e 1))) -
      (Lv ρ v) (Ψ2 (e 0) + Complex.I * Ψ2 (e 1))) =
      (gam ρ 0) ((Lv ρ v) (stereoH x • (Ψ1 (e 0) - Complex.I * Ψ1 (e 1)))) -
      (Lv ρ v) (stereoH x • (Ψ2 (e 0) + Complex.I * Ψ2 (e 1))) := by
    rw [smul_sub, ← map_smul (gam ρ 0), ← map_smul (Lv ρ v), ← map_smul (Lv ρ v)]
  rw [e3, eA, eB]
  simp only [angSpinor, angProfile, map_smul, map_neg, neg_smul, sub_neg_eq_add, smul_add, hT]
  abel

open Polynomial in
/-- **Eigenspinor of the sphere from radial polynomials.** For `G, F` as in `angG_flat_eigen`,
`h^{1/2} g` is an eigenspinor of the Dirac operator of the unit 2-sphere with eigenvalue `λ`. -/
theorem angG_sphere_eigen (ρ : CliffordRep 2 V) (v : V) (n s : ℕ) (G F : ℝ[X]) (lam : ℝ)
    (ha : (1 + X) * (C ((n : ℝ) + 1) * G + X * G.derivative) - C (s : ℝ) * X * G = C lam * F)
    (hb : -((1 + X) * F.derivative - C (s : ℝ) * F) = C lam * G) (x : E 2) :
    diracF ρ stereoF stereoOmega
        (fun y => stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) • angG ρ v n s G F y) x =
      lam • (stereoH x ^ ((((2 : ℕ) : ℝ) - 1) / 2) • angG ρ v n s G F x) := by
  have hne : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  obtain ⟨Ψ1, h1, -, -⟩ := angProfile_deriv (fun u => ((1 + u) ^ s)⁻¹ * G.eval u) (n + 1) x
    (hasDerivAt_prof s G hne)
  obtain ⟨Ψ2, h2, -, -⟩ := angProfile_deriv (fun u => ((1 + u) ^ s)⁻¹ * F.eval u) n x
    (hasDerivAt_prof s F hne)
  have hd : DifferentiableAt ℝ (angG ρ v n s G F) x := (hasFDerivAt_angSpinor ρ v h1 h2).differentiableAt
  exact (diracF_stereo_conformal_eigen_iff ρ x hd lam).2 (angG_flat_eigen ρ v n s G F lam ha hb x)

open Polynomial

/-- The numerator polynomial `Ψ = (1+X)(m P + X P') − s X P`. -/
noncomputable def psiPoly (m s : ℝ) (P : ℝ[X]) : ℝ[X] :=
  (1 + X) * (C m * P + X * P.derivative) - C s * X * P

lemma coeff_psiPoly_zero (m s : ℝ) (P : ℝ[X]) : (psiPoly m s P).coeff 0 = m * P.coeff 0 := by
  simp [psiPoly, add_mul, coeff_derivative, mul_add]

lemma coeff_psiPoly_succ (m s : ℝ) (P : ℝ[X]) (j : ℕ) :
    (psiPoly m s P).coeff (j + 1) =
      (m + j + 1) * P.coeff (j + 1) + (m + j - s) * P.coeff j := by
  simp only [psiPoly, add_mul, one_mul, sub_mul, mul_add, coeff_add, coeff_sub, coeff_C_mul,
    coeff_X_mul, coeff_derivative, mul_assoc]
  have h3 : (X * P.derivative).coeff j = j * P.coeff j := by
    rcases j with _ | j
    · simp
    · rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  rw [h3]; ring

/-- **The radial ODE.** If the coefficients of `P` satisfy the two-term recurrence
`(i+1)(m+1+i) c_{i+1} + (s−m−i)(s−1−i) c_i = 0`, then `(1+X) Ψ' − s Ψ + s² P = 0`
for `Ψ = psiPoly m s P`. -/
lemma psiPoly_ode (m s : ℝ) (P : ℝ[X])
    (hrec : ∀ i : ℕ, ((i : ℝ) + 1) * (m + 1 + i) * P.coeff (i + 1) +
      (s - m - i) * (s - 1 - i) * P.coeff i = 0) :
    (1 + X) * (psiPoly m s P).derivative - C s * psiPoly m s P + C (s ^ 2) * P = 0 := by
  ext i
  have hd : ∀ j : ℕ, (psiPoly m s P).derivative.coeff j = (psiPoly m s P).coeff (j + 1) * ((j : ℝ) + 1) := by
    intro j; rw [coeff_derivative]
  rcases i with _ | j
  · simp only [add_mul, one_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_zero, coeff_X_mul_zero, hd]
    rw [coeff_psiPoly_succ, coeff_psiPoly_zero]
    push_cast
    linear_combination hrec 0
  · simp only [add_mul, one_mul, coeff_add, coeff_sub, coeff_C_mul, coeff_zero, coeff_X_mul, hd]
    simp only [coeff_psiPoly_succ]
    push_cast
    have h1 := hrec (j + 1)
    push_cast at h1
    linear_combination h1 + hrec j

/-- Coefficients of the radial polynomial of the mode `m` in the sphere of level `s = m + d`:
`c₀ = 1`, `c_{i+1} = −(d−i)(m+d−1−i) / ((i+1)(m+1+i)) · c_i`. -/
noncomputable def gcoef (m d : ℕ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => (-(((d : ℝ) - i) * ((m : ℝ) + d - 1 - i)) / (((i : ℝ) + 1) * ((m : ℝ) + 1 + i))) * gcoef m d i

lemma gcoef_rec (m d i : ℕ) :
    ((i : ℝ) + 1) * ((m : ℝ) + 1 + i) * gcoef m d (i + 1) +
      (((m + d : ℕ) : ℝ) - m - i) * (((m + d : ℕ) : ℝ) - 1 - i) * gcoef m d i = 0 := by
  have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((m : ℝ) + 1 + i) ≠ 0 := by positivity
  simp only [gcoef]
  push_cast
  field_simp
  ring

lemma gcoef_eq_zero (m d j : ℕ) : gcoef m d (d + 1 + j) = 0 := by
  induction j with
  | zero =>
    show gcoef m d (d + 1) = 0
    simp only [gcoef]
    push_cast
    ring_nf
  | succ j ih =>
    rw [← add_assoc]
    simp only [gcoef]
    rw [ih]
    ring

lemma gcoef_eq_zero_of_lt {m d j : ℕ} (h : d + 1 ≤ j) : gcoef m d j = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  exact gcoef_eq_zero m d i

/-- The radial polynomial `G_{m,d} = Σ_{i ≤ d} c_i X^i` (degree `d`). -/
noncomputable def gPoly (m d : ℕ) : ℝ[X] := ∑ j ∈ Finset.range (d + 1), C (gcoef m d j) * X ^ j

lemma coeff_gPoly (m d i : ℕ) : (gPoly m d).coeff i = gcoef m d i := by
  unfold gPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases h : i < d + 1
  · simp [h]
  · rw [Finset.sum_eq_zero]
    · exact (gcoef_eq_zero_of_lt (not_lt.mp h)).symm
    · intro j hj
      have : i ≠ j := by
        have := Finset.mem_range.mp hj
        omega
      simp [this]

lemma coeff_gPoly_zero (m d : ℕ) : (gPoly m d).coeff 0 = 1 := by
  rw [coeff_gPoly]; rfl

/-- The companion polynomial `F = Ψ/λ`. -/
noncomputable def fPoly (m d : ℕ) (lam : ℝ) : ℝ[X] :=
  C lam⁻¹ * psiPoly (m : ℝ) ((m + d : ℕ) : ℝ) (gPoly m d)

/-- **The `2(k+1)` eigenspinors of `S²`** (one family `n = 0..k`, `d = k−n`, level `s = k+1`):
for every `ε = ±1`, every constant spinor `v` and every `n, d`, the spinor `h^{1/2} g_{n}` with
`c₁ = (1+t)^{-s} z^{n+1} G`, `c₂ = (1+t)^{-s} z^n F` is an eigenspinor of the Dirac operator of the
unit 2-sphere in the stereographic chart with eigenvalue `ε (n+d+1)`. -/
theorem sphere_eigen_mode (ρ : CliffordRep 2 V) (v : V) (n d : ℕ) {ε : ℝ} (hε : ε * ε = 1) (x : E 2) :
    diracF ρ stereoF stereoOmega
        (fun y => stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) •
          angG ρ v n (n + 1 + d) (gPoly (n + 1) d) (fPoly (n + 1) d (ε * ((n + 1 + d : ℕ) : ℝ))) y) x =
      (ε * ((n + 1 + d : ℕ) : ℝ)) • (stereoH x ^ ((((2 : ℕ) : ℝ) - 1) / 2) •
        angG ρ v n (n + 1 + d) (gPoly (n + 1) d) (fPoly (n + 1) d (ε * ((n + 1 + d : ℕ) : ℝ))) x) := by
  set s : ℕ := n + 1 + d with hs
  set lam : ℝ := ε * (s : ℝ) with hlam
  have hsne : (s : ℝ) ≠ 0 := by rw [hs]; positivity
  have hlne : lam ≠ 0 := by
    rw [hlam]; intro h
    rcases mul_eq_zero.mp h with h | h
    · rw [h] at hε; simp at hε
    · exact hsne h
  have hl2 : lam ^ 2 = (s : ℝ) ^ 2 := by rw [hlam]; linear_combination (s : ℝ) ^ 2 * hε
  have hrec : ∀ i : ℕ, ((i : ℝ) + 1) * (((n + 1 : ℕ) : ℝ) + 1 + i) * (gPoly (n + 1) d).coeff (i + 1) +
      ((s : ℝ) - ((n + 1 : ℕ) : ℝ) - i) * ((s : ℝ) - 1 - i) * (gPoly (n + 1) d).coeff i = 0 := by
    intro i
    simp only [coeff_gPoly]
    exact gcoef_rec (n + 1) d i
  have hode := psiPoly_ode ((n + 1 : ℕ) : ℝ) (s : ℝ) (gPoly (n + 1) d) hrec
  refine angG_sphere_eigen ρ v n s _ _ lam ?_ ?_ x
  · rw [fPoly, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlne, C_1, one_mul]
    simp only [psiPoly]
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
  · have h1 : (1 + X) * (psiPoly ((n + 1 : ℕ) : ℝ) (s : ℝ) (gPoly (n + 1) d)).derivative -
        C (s : ℝ) * psiPoly ((n + 1 : ℕ) : ℝ) (s : ℝ) (gPoly (n + 1) d) =
        -(C ((s : ℝ) ^ 2) * gPoly (n + 1) d) := by linear_combination hode
    have hC : (C lam⁻¹ * C ((s : ℝ) ^ 2) : ℝ[X]) = C lam := by
      rw [← C_mul]; congr 1; rw [← hl2]; field_simp
    rw [fPoly, derivative_C_mul]
    linear_combination (-(C lam⁻¹ : ℝ[X])) * h1 + (gPoly (n + 1) d) * hC

/-- `angSpinor` is additive in the constant spinor. -/
lemma angSpinor_add (ρ : CliffordRep 2 V) (v w : V) (c₁ c₂ : E 2 → ℂ) :
    angSpinor ρ (v + w) c₁ c₂ = angSpinor ρ v c₁ c₂ + angSpinor ρ w c₁ c₂ := by
  funext y
  simp only [angSpinor, Lv_apply, map_add, map_smul, Pi.add_apply, smul_add]
  abel

/-- `angSpinor` is homogeneous in the constant spinor. -/
lemma angSpinor_smul (ρ : CliffordRep 2 V) (a : ℝ) (v : V) (c₁ c₂ : E 2 → ℂ) :
    angSpinor ρ (a • v) c₁ c₂ = a • angSpinor ρ v c₁ c₂ := by
  funext y
  simp only [angSpinor, Lv_apply, map_add, map_smul, Pi.smul_apply, smul_add, smul_comm a]

/-- The Dirac operator of the sphere is additive on differentiable spinors (finite sums). -/
lemma diracF_stereo_sum (ρ : CliffordRep 2 V) {ι : Type*} (t : Finset ι) (f : ι → E 2 → V) (x : E 2)
    (hf : ∀ i ∈ t, DifferentiableAt ℝ (f i) x) :
    diracF ρ stereoF stereoOmega (fun y => ∑ i ∈ t, f i y) x =
      ∑ i ∈ t, diracF ρ stereoF stereoOmega (f i) x := by
  have hs : HasFDerivAt (fun y => ∑ i ∈ t, f i y) (∑ i ∈ t, fderiv ℝ (f i) x) x :=
    HasFDerivAt.fun_sum (fun i hi => (hf i hi).hasFDerivAt)
  simp only [diracF_stereo, dirac, hs.fderiv, sum_apply, map_sum,
    Finset.smul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

/-- The `n`-th mode of level `k+1` (`0 ≤ n ≤ k`), sign `ε`, constant spinor `v`:
`h^{1/2} g_n` with `g_n = angG ρ v n (k+1) G F`, `G = gPoly (n+1) (k−n)`, `F = Ψ/λ`, `λ = ε(k+1)`. -/
noncomputable def modeFn (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) (n : ℕ) (v : V) : E 2 → V :=
  fun y => stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) •
    angG ρ v n (k + 1) (gPoly (n + 1) (k - n)) (fPoly (n + 1) (k - n) (ε * ((k + 1 : ℕ) : ℝ))) y

/-- Each mode is an eigenspinor with eigenvalue `ε (k+1)`. -/
theorem modeFn_eigen (ρ : CliffordRep 2 V) (k : ℕ) {ε : ℝ} (hε : ε * ε = 1) {n : ℕ} (hn : n ≤ k)
    (v : V) (x : E 2) :
    diracF ρ stereoF stereoOmega (modeFn ρ k ε n v) x = (ε * ((k + 1 : ℕ) : ℝ)) • modeFn ρ k ε n v x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e : n + d + 1 = n + 1 + d := by omega
  have h := sphere_eigen_mode ρ v n d hε x
  have hm : modeFn ρ (n + d) ε n v = fun y => stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) •
      angG ρ v n (n + 1 + d) (gPoly (n + 1) d) (fPoly (n + 1) d (ε * ((n + 1 + d : ℕ) : ℝ))) y := by
    funext y
    simp only [modeFn, e, Nat.add_sub_cancel_left]
  rw [hm]
  simp only [e]
  exact h

/-- Each mode is differentiable. -/
theorem modeFn_differentiable (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) (n : ℕ) (v : V) (x : E 2) :
    DifferentiableAt ℝ (modeFn ρ k ε n v) x := by
  have hne : 1 + ‖x‖ ^ 2 ≠ 0 := by positivity
  set G := gPoly (n + 1) (k - n)
  set F := fPoly (n + 1) (k - n) (ε * ((k + 1 : ℕ) : ℝ))
  obtain ⟨Ψ1, h1, -, -⟩ := angProfile_deriv (fun u => ((1 + u) ^ (k + 1))⁻¹ * G.eval u) (n + 1) x
    (hasDerivAt_prof (k + 1) G hne)
  obtain ⟨Ψ2, h2, -, -⟩ := angProfile_deriv (fun u => ((1 + u) ^ (k + 1))⁻¹ * F.eval u) n x
    (hasDerivAt_prof (k + 1) F hne)
  have hd : DifferentiableAt ℝ (angG ρ v n (k + 1) G F) x :=
    (hasFDerivAt_angSpinor ρ v h1 h2).differentiableAt
  have hH : DifferentiableAt ℝ (fun y : E 2 => stereoH y) x := by
    unfold stereoH
    have : DifferentiableAt ℝ (fun y : E 2 => ‖y‖ ^ 2) x := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.differentiableAt
    fun_prop
  have hP : DifferentiableAt ℝ (fun y : E 2 => stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2)) x :=
    hH.rpow_const (Or.inl (stereoH_pos x).ne')
  exact hP.smul hd

lemma modeFn_add (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) (n : ℕ) (v w : V) :
    modeFn ρ k ε n (v + w) = modeFn ρ k ε n v + modeFn ρ k ε n w := by
  funext y
  simp only [modeFn, angG, angSpinor_add, Pi.add_apply, smul_add]

lemma modeFn_smul (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) (n : ℕ) (a : ℝ) (v : V) :
    modeFn ρ k ε n (a • v) = a • modeFn ρ k ε n v := by
  funext y
  simp only [modeFn, angG, angSpinor_smul, Pi.smul_apply, smul_comm a]

/-- The linear map sending `(v_0, …, v_k)` to `∑ₙ h^{1/2} g_n(v_n)`. -/
noncomputable def modeMap (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) : (Fin (k + 1) → V) →ₗ[ℝ] (E 2 → V) where
  toFun w := fun y => ∑ n : Fin (k + 1), modeFn ρ k ε n (w n) y
  map_add' w w' := by
    funext y
    simp [modeFn_add, Finset.sum_add_distrib]
  map_smul' a w := by
    funext y
    simp [modeFn_smul, Finset.smul_sum]

/-- **Every image of `modeMap` is an eigenspinor** of the Dirac operator of `S²` (in the chart)
with eigenvalue `ε (k+1)`. -/
theorem modeMap_eigen (ρ : CliffordRep 2 V) (k : ℕ) {ε : ℝ} (hε : ε * ε = 1) (w : Fin (k + 1) → V)
    (x : E 2) :
    diracF ρ stereoF stereoOmega (modeMap ρ k ε w) x =
      (ε * ((k + 1 : ℕ) : ℝ)) • modeMap ρ k ε w x := by
  have h := diracF_stereo_sum ρ Finset.univ (fun n : Fin (k + 1) => modeFn ρ k ε n (w n)) x
    (fun n _ => modeFn_differentiable ρ k ε n (w n) x)
  have e : modeMap ρ k ε w = fun y => ∑ n : Fin (k + 1), modeFn ρ k ε n (w n) y := rfl
  rw [e, h]
  simp only [modeFn_eigen ρ k hε (Nat.lt_succ_iff.mp (Fin.is_lt _)), Finset.smul_sum]

end Lightlike.Dirac
