import Mathlib
import Lightlike.Dirac.EigenAngular

/-!
# The transition between the two stereographic charts of the unit 2-sphere

The unit 2-sphere is covered by the stereographic chart `y ∈ ℝ²` from the north pole and the chart
`w ∈ ℝ²` from the south pole; the transition is the inversion `w = ι y = y / ‖y‖²`, an
orientation-reversing isometry of the round metric `4 ‖dy‖² / (1 + ‖y‖²)²`.  Both charts carry the
same orthonormal frame `h ∂ₐ` (`h = (1 + ‖y‖²)/2`, `stereoF`), so the Dirac operator is
`diracF ρ stereoF stereoOmega` in both.  The frame change is the reflection
`R(y) = 1 - 2 n nᵀ`, `n = y/‖y‖`, and its Pin lift is `T(y) = ρ(n) J`, `J = γ₀γ₁`: it satisfies
`T(y) ρ(v) T(y)⁻¹ = ρ(R v)` (`sphereT_conj`).  A spinor of the first chart is transferred to the second by
`f_S(ι y) = T(y) f(y)` (`sphereT`).

The Clifford element `ρ(n)` alone would satisfy `ρ(n) ρ(v) ρ(n)⁻¹ = -ρ(R v)`: it is the lift of the
reflection in the other Pin convention and flips the sign of the Dirac eigenvalue
(`Lightlike/Dirac/Kelvin.lean`).

For the explicit eigenspinors `modeFn` of `sphere_dirac_lower_bound` the transfer is again an angular
polynomial spinor, with the polynomials reflected and exchanged (`modeFnS_inv2`): it is smooth at the
south pole.
-/

namespace Lightlike.Dirac

open CliffordAlgebra Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `‖w‖² = w₀² + w₁²` on the plane. -/
lemma norm_sq_E2 (w : E 2) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- The inversion `w ↦ w / ‖w‖²` of the plane. -/
noncomputable def inv2 (w : E 2) : E 2 := (‖w‖ ^ 2)⁻¹ • w

/-- Clifford multiplication by the vector `w = w₀e₀ + w₁e₁`. -/
noncomputable def cliffV (ρ : CliffordRep 2 V) (w : E 2) (v : V) : V :=
  w 0 • gam ρ 0 v + w 1 • gam ρ 1 v

/-- A vector of the plane in the standard basis. -/
lemma eq_smul_e_add (w : E 2) : w = w 0 • e 0 + w 1 • e 1 := by
  ext i; fin_cases i <;> simp [e]

lemma e00 : (e (0 : Fin 2) : E 2) 0 = 1 := by simp [e]
lemma e01 : (e (0 : Fin 2) : E 2) 1 = 0 := by simp [e]
lemma e10 : (e (1 : Fin 2) : E 2) 0 = 0 := by simp [e]
lemma e11 : (e (1 : Fin 2) : E 2) 1 = 1 := by simp [e]

/-- `γ₁γ₀ = -γ₀γ₁`. -/
lemma gam10 (ρ : CliffordRep 2 V) (v : V) : gam ρ 1 (gam ρ 0 v) = -gam ρ 0 (gam ρ 1 v) := by
  have := gam_anticomm ρ (i := 0) (j := 1) (by decide) v
  rw [eq_neg_iff_add_eq_zero]; rw [add_comm]; exact this

lemma Jop_apply (ρ : CliffordRep 2 V) (v : V) : Jop ρ v = gam ρ 0 (gam ρ 1 v) := rfl

/-- `J γ₀ = -γ₀ J`. -/
lemma Jop_gam0 (ρ : CliffordRep 2 V) (x : V) : Jop ρ (gam ρ 0 x) = -gam ρ 0 (Jop ρ x) := by
  have := gam0_Jop_comm ρ x
  rw [this]; simp

/-- `Lv v (ζ c)` for a complex `ζ`. -/
lemma Lv_mul (ρ : CliffordRep 2 V) (v : V) (ζ c : ℂ) :
    Lv ρ v (ζ * c) = ζ.re • Lv ρ v c + ζ.im • Jop ρ (Lv ρ v c) := by
  have h : ζ * c = (ζ.re : ℝ) • c + (ζ.im : ℝ) • (Complex.I * c) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [h, map_add, map_smul, map_smul, Lv_I_mul]

/-- `Lv (J v) c = Lv v (i c)`: the constant spinor `J v` is `i v`. -/
lemma Lv_Jop (ρ : CliffordRep 2 V) (v : V) (c : ℂ) :
    Lv ρ (Jop ρ v) c = Lv ρ v (Complex.I * c) := by
  rw [Lv_apply, Lv_apply, Jop_sq]
  simp [Complex.mul_re, Complex.mul_im]
  module

/-- `ρ(y) x = γ₀ (y₀ x - y₁ J x)`. -/
lemma cliffV_eq (ρ : CliffordRep 2 V) (y : E 2) (x : V) :
    cliffV ρ y x = gam ρ 0 (y 0 • x - y 1 • Jop ρ x) := by
  simp only [cliffV, map_sub, map_smul]
  rw [gam1_eq ρ x]
  simp only [map_neg, smul_neg]
  module

/-- `ρ(y)` on `Lv c`: `γ₀ Lv (ζ̄ c)`. -/
lemma cliffV_Lv (ρ : CliffordRep 2 V) (y : E 2) (v : V) (c : ℂ) :
    cliffV ρ y (Lv ρ v c) = gam ρ 0 (Lv ρ v (starRingEnd ℂ (zcL y) * c)) := by
  rw [cliffV_eq, Lv_mul]
  simp [zcL_apply, sub_eq_add_neg]

/-- `ρ(y)` on `γ₀ Lv c`: `-Lv (ζ c)`. -/
lemma cliffV_gam_Lv (ρ : CliffordRep 2 V) (y : E 2) (v : V) (c : ℂ) :
    cliffV ρ y (gam ρ 0 (Lv ρ v c)) = -Lv ρ v (zcL y * c) := by
  rw [cliffV_eq, Lv_mul, Jop_gam0]
  simp only [zcL_apply, map_sub, map_smul, map_neg, gam_sq]
  simp
  module

/-- The transition function `T(y) = ‖y‖⁻¹ ρ(y) J` of the spinor bundle of the unit 2-sphere. -/
noncomputable def sphereT (ρ : CliffordRep 2 V) (y : E 2) (x : V) : V :=
  ‖y‖⁻¹ • cliffV ρ y (Jop ρ x)

lemma sphereT_smul (ρ : CliffordRep 2 V) (y : E 2) (a : ℝ) (x : V) :
    sphereT ρ y (a • x) = a • sphereT ρ y x := by
  simp only [sphereT, cliffV, map_smul, smul_add, smul_comm a]

lemma cliffV_add (ρ : CliffordRep 2 V) (y : E 2) (a b : V) :
    cliffV ρ y (a + b) = cliffV ρ y a + cliffV ρ y b := by
  simp only [cliffV, map_add, smul_add]; abel

lemma cliffV_neg (ρ : CliffordRep 2 V) (y : E 2) (a : V) : cliffV ρ y (-a) = -cliffV ρ y a := by
  simp only [cliffV, map_neg, smul_neg]; abel

/-- The transfer of an angular spinor value:
`T(y)(Lv c₁ + γ₀ Lv c₂) = ‖y‖⁻¹ (Lv (i ζ c₂) + γ₀ Lv (i ζ̄ c₁))`. -/
lemma sphereT_angSpinor (ρ : CliffordRep 2 V) (y : E 2) (v : V) (c₁ c₂ : ℂ) :
    sphereT ρ y (Lv ρ v c₁ + gam ρ 0 (Lv ρ v c₂)) =
      ‖y‖⁻¹ • (Lv ρ v (Complex.I * zcL y * c₂) +
        gam ρ 0 (Lv ρ v (Complex.I * starRingEnd ℂ (zcL y) * c₁))) := by
  have hJ : Jop ρ (Lv ρ v c₁ + gam ρ 0 (Lv ρ v c₂)) =
      Lv ρ v (Complex.I * c₁) + -gam ρ 0 (Lv ρ v (Complex.I * c₂)) := by
    rw [map_add, Jop_gam0, ← Lv_I_mul, ← Lv_I_mul]
  unfold sphereT
  rw [hJ, cliffV_add, cliffV_neg, cliffV_Lv, cliffV_gam_Lv]
  have h1 : zcL y * (Complex.I * c₂) = Complex.I * zcL y * c₂ := by ring
  have h2 : starRingEnd ℂ (zcL y) * (Complex.I * c₁) = Complex.I * starRingEnd ℂ (zcL y) * c₁ := by ring
  rw [h1, h2, neg_neg, add_comm]

/-! ### Degrees of the mode polynomials -/

lemma natDegree_gPoly_le (m d : ℕ) : (gPoly m d).natDegree ≤ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_gPoly]
  exact gcoef_eq_zero_of_lt hj

/-- The companion polynomial has degree at most `d`: the top coefficient of `Ψ` cancels. -/
lemma natDegree_fPoly_le (m d : ℕ) (lam : ℝ) : (fPoly m d lam).natDegree ≤ d := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [fPoly, coeff_C_mul, coeff_psiPoly_succ, coeff_gPoly, coeff_gPoly]
  rcases Nat.lt_or_ge d j' with h | h
  · rw [gcoef_eq_zero_of_lt (by omega : d + 1 ≤ j' + 1), gcoef_eq_zero_of_lt (by omega : d + 1 ≤ j')]
    simp
  · have hj' : j' = d := by omega
    subst hj'
    rw [gcoef_eq_zero_of_lt (by omega : j' + 1 ≤ j' + 1)]
    push_cast
    simp

/-- Evaluation of the reflected polynomial: `f^r(1/t) t^N = f(t)`. -/
lemma eval_reflect_inv {f : ℝ[X]} {N : ℕ} (hf : f.natDegree ≤ N) {t : ℝ} (ht : t ≠ 0) :
    (f.reflect N).eval t⁻¹ * t ^ N = f.eval t := by
  haveI : Invertible t := invertibleOfNonzero ht
  have := eval₂_reflect_mul_pow (RingHom.id ℝ) t N f hf
  rw [Polynomial.eval₂_id, Polynomial.eval₂_id, invOf_eq_inv] at this
  exact this

/-- The profile of the reflected polynomial at `1/t`. -/
lemma reflect_profile {f : ℝ[X]} {n d : ℕ} (hf : f.natDegree ≤ d) {t : ℝ} (ht : 0 < t) :
    ((1 + t⁻¹) ^ (n + 1 + d))⁻¹ * (f.reflect d).eval t⁻¹ =
      t ^ (n + 1) * (((1 + t) ^ (n + 1 + d))⁻¹ * f.eval t) := by
  have h := eval_reflect_inv hf ht.ne'
  have hr : (f.reflect d).eval t⁻¹ = f.eval t / t ^ d := by
    rw [eq_div_iff (pow_pos ht d).ne']; exact h
  rw [hr]
  have h1 : (1 : ℝ) + t⁻¹ = (1 + t) / t := by field_simp <;> ring
  have h2 : (0 : ℝ) < 1 + t := by linarith
  rw [h1, div_pow, inv_div]
  field_simp
  ring

/-! ### Facts about the inversion -/

lemma norm_inv2 {y : E 2} (hy : y ≠ 0) : ‖inv2 y‖ = ‖y‖⁻¹ := by
  have : 0 < ‖y‖ := norm_pos_iff.mpr hy
  simp only [inv2, norm_smul, norm_inv, norm_pow, norm_norm]
  field_simp

lemma norm_sq_inv2 {y : E 2} (hy : y ≠ 0) : ‖inv2 y‖ ^ 2 = (‖y‖ ^ 2)⁻¹ := by
  rw [norm_inv2 hy, inv_pow]

lemma zcL_inv2 (y : E 2) : zcL (inv2 y) = (((‖y‖ ^ 2)⁻¹ : ℝ) : ℂ) * zcL y := by
  simp [inv2, map_smul, Complex.real_smul]

lemma stereoH_inv2 {y : E 2} (hy : y ≠ 0) : stereoH (inv2 y) = stereoH y / ‖y‖ ^ 2 := by
  have : 0 < ‖y‖ := norm_pos_iff.mpr hy
  simp only [stereoH, norm_sq_inv2 hy]
  field_simp
  ring

lemma rpow_exp_sq (r : ℝ) (hr : 0 ≤ r) : (r ^ 2) ^ ((((2 : ℕ) : ℝ) - 1) / 2) = r := by
  have : (((2 : ℕ) : ℝ) - 1) / 2 = 1 / 2 := by norm_num
  rw [this, ← Real.sqrt_eq_rpow, Real.sqrt_sq hr]

/-- The scalar factor: `h(ι y)^{1/2} = h(y)^{1/2} / ‖y‖`. -/
lemma stereoH_rpow_inv2 {y : E 2} (hy : y ≠ 0) :
    stereoH (inv2 y) ^ ((((2 : ℕ) : ℝ) - 1) / 2) = stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) * ‖y‖⁻¹ := by
  rw [stereoH_inv2 hy, Real.div_rpow (stereoH_pos y).le (by positivity), rpow_exp_sq _ (norm_nonneg y),
    div_eq_mul_inv]

/-- The first coordinate identity of the gluing: `t^{n+1} B (ζ/t)^{n+1} = ζ B ζ^n`. -/
lemma chart_cplx_one (t : ℝ) (ht : t ≠ 0) (ζ : ℂ) (B : ℝ) (n : ℕ) :
    Complex.I * (((t ^ (n + 1) * B : ℝ) : ℂ) * (((t⁻¹ : ℝ) : ℂ) * ζ) ^ (n + 1)) =
      Complex.I * ζ * ((B : ℂ) * ζ ^ n) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have key : (t : ℂ) ^ (n + 1) * ((t : ℂ)⁻¹) ^ (n + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ htC, one_pow]
  push_cast
  linear_combination (Complex.I * B * ζ ^ (n + 1)) * key

/-- The second coordinate identity of the gluing: `t^{n+1} B (ζ/t)^n = ζ̄ B ζ^{n+1}` for `ζ̄ ζ = t`. -/
lemma chart_cplx_two (t : ℝ) (ht : t ≠ 0) (ζ ζ' : ℂ) (hζ : ζ' * ζ = (t : ℂ)) (B : ℝ) (n : ℕ) :
    Complex.I * (((t ^ (n + 1) * B : ℝ) : ℂ) * (((t⁻¹ : ℝ) : ℂ) * ζ) ^ n) =
      Complex.I * ζ' * ((B : ℂ) * ζ ^ (n + 1)) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have key : (t : ℂ) ^ (n + 1) * ((t : ℂ)⁻¹) ^ n = t := by
    rw [pow_succ, mul_comm ((t : ℂ) ^ n) (t : ℂ), mul_assoc, ← mul_pow, mul_inv_cancel₀ htC, one_pow, mul_one]
  push_cast
  linear_combination (Complex.I * B * ζ ^ n) * key + (-(Complex.I * B * ζ ^ n)) * hζ

/-! ### The explicit eigenspinors in the chart of the south pole -/

/-- The transfer of `modeFn` to the chart of the south pole: the same family with the constant spinor
`J v` and the two polynomials reflected and exchanged. -/
noncomputable def modeFnS (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) (n : ℕ) (v : V) : E 2 → V :=
  fun y => stereoH y ^ ((((2 : ℕ) : ℝ) - 1) / 2) •
    angG ρ (Jop ρ v) n (k + 1) ((fPoly (n + 1) (k - n) (ε * ((k + 1 : ℕ) : ℝ))).reflect (k - n))
      ((gPoly (n + 1) (k - n)).reflect (k - n)) y

/-- **The gluing of the explicit modes.** `f_S (ι y) = T(y) f(y)` for `y ≠ 0`, where `f = modeFn` is the
eigenspinor of the chart of the north pole and `f_S = modeFnS`. -/
theorem modeFnS_inv2 (ρ : CliffordRep 2 V) (k : ℕ) (ε : ℝ) {n : ℕ} (hn : n ≤ k) (v : V) {y : E 2}
    (hy : y ≠ 0) :
    modeFnS ρ k ε n v (inv2 y) = sphereT ρ y (modeFn ρ k ε n v y) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hd : n + d - n = d := by omega
  have hs : n + d + 1 = n + 1 + d := by omega
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have htpos : 0 < ‖y‖ ^ 2 := by positivity
  have hG := natDegree_gPoly_le (n + 1) d
  have hF := natDegree_fPoly_le (n + 1) d (ε * ((n + d + 1 : ℕ) : ℝ))
  have hconj := zbar_mul_z y
  have e1 := reflect_profile (n := n) hF htpos
  have e2 := reflect_profile (n := n) hG htpos
  simp only [modeFnS, modeFn, hd, hs, angG, angSpinor, angProfile, norm_sq_inv2 hy, zcL_inv2,
    Lv_Jop, stereoH_rpow_inv2 hy] at *
  rw [sphereT_smul, sphereT_angSpinor, smul_smul]
  rw [e1, e2, chart_cplx_one _ htpos.ne', chart_cplx_two _ htpos.ne' _ _ hconj]

end Lightlike.Dirac
