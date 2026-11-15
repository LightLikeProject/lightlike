import Lightlike.Asymptotics.EPRL.GluingSolutions
import Lightlike.Asymptotics.EPRL.Normals
import Lightlike.Asymptotics.EPRL.Formula
import Lightlike.Regge.D4.Embedded

/-!
# The critical points of the Regge state

For the Regge state `reggeState σ` of a 4-simplex `σ` and spins proportional to the triangle
areas, the critical points of the coherent amplitude (the group elements where `|F_n| = 1` and
the integrand is stationary) are exactly the two gauge classes `±X₄ U⁻` and `±X₄ U⁺` of
`critMinus` and `critPlus σ` (Barrett, Dowdall, Fairbairn, Gomes, Hellmann, arXiv:0902.1170,
section 4).

* The quaternion lifts `reggeLift σ e i` of the Regge state, built from the normals
  `normalQuat σ a`, the lift `liftQuat` of the unit bivector and the phase `phaseQuat`, have
  matrices `reggeState σ e i` (`toMat_reggeLift`), so the Regge state is SU(2) data
  (`isSU2Data_reggeState`).
* Each lift rotates `i` to `±V_e` with `V_e = s_e⁻¹ Im(N̄_b N_a)` and `s_e = √(1 - ⟨N_a, N_b⟩²)`
  for `e = ab` (`rotI_reggeLift_zero`, `rotI_reggeLift_one`). Hence the data are glued at
  `X = 1` and at `X_a = N_a` (`glued_one`, `glued_normal`), and any three normal matrices
  `Q₄, Q_a, Q_b` are real independent (`linearIndependent_normalSU2`), from the
  nondegeneracy of `σ`.
* With spins `n_e = c A_e`, the normals of the data close at every node
  (`closure_reggeState`): `A_e / s_e = V_x / (2 h_y)` at the node `x` of the edge `e = xy`
  (`Normals.lean`), and the closure becomes `Σ_y h_y⁻¹ N_y = 0`
  (`sum_outNormal_div_height`).
* `reggeState_critical_iff` combines the gluing solutions (`glued_iff_two_classes`) with the
  stationarity criterion (`stationary_iff_closure`), and `critical_classes_disjoint` shows that
  the two classes do not meet.

The trust checks use the regular simplex: `X = 1` and `X = U⁺` are critical, a mixed choice is
not, and with a single nonzero spin `X = 1` has `|F_n| = 1` but is not stationary.
-/

open Quaternion Finset
open scoped Matrix RealInnerProductSpace

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 (bloch)

/-! ## Vectors of `ℝ⁴` as quaternions -/

/-- The quaternion `v₀ + v₁ i + v₂ j + v₃ k` of a vector `v ∈ ℝ⁴`, as a real linear map. -/
noncomputable def vecQuat : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] ℍ where
  toFun v := ⟨v 0, v 1, v 2, v 3⟩
  map_add' v w := by ext <;> simp
  map_smul' c v := by ext <;> simp

/-- The matrix of `vecQuat v` is `quatMat v`. -/
lemma toMat_vecQuat (v : EuclideanSpace ℝ (Fin 4)) : Lightlike.Spin4.toMat (vecQuat v) = quatMat v := by
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Lightlike.Spin4.toMat_apply, Lightlike.Spin4.quatMat, quatMat, vecQuat]

/-- `vecQuat` is injective. -/
lemma vecQuat_injective : Function.Injective vecQuat := by
  intro v w h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  ext i; fin_cases i
  exacts [h0, h1, h2, h3]

/-- The real part of `x̄ y` is the inner product `⟨x, y⟩`. -/
lemma re_star_vecQuat_mul (x y : EuclideanSpace ℝ (Fin 4)) :
    (star (vecQuat x) * vecQuat y).re = ⟪x, y⟫ := by
  rw [inner_eq_coords]; simp [vecQuat]

/-- The real part of `x ȳ` is the inner product `⟨x, y⟩`. -/
lemma re_vecQuat_mul_star (x y : EuclideanSpace ℝ (Fin 4)) :
    (vecQuat x * star (vecQuat y)).re = ⟪x, y⟫ := by
  rw [inner_eq_coords]; simp [vecQuat]

/-- The outward normal `N_a` of `σ` as a quaternion. -/
noncomputable def normalQuat (σ : Simplex4) (a : Fin 5) : ℍ := vecQuat (outNormal σ a)

/-- The matrix of the normal quaternion is `quatMat N_a`. -/
lemma toMat_normalQuat (σ : Simplex4) (a : Fin 5) :
    Lightlike.Spin4.toMat (normalQuat σ a) = quatMat (outNormal σ a) := toMat_vecQuat _

/-- The normal quaternions are unit quaternions. -/
lemma normSq_normalQuat (σ : Simplex4) (a : Fin 5) : normSq (normalQuat σ a) = 1 := by
  have h := inner_outNormal_self σ a
  rw [inner_eq_coords] at h
  rw [normSq_def']; simp only [normalQuat, vecQuat, LinearMap.coe_mk, AddHom.coe_mk]
  linear_combination h

/-- The normal `N_a` as an element of SU(2): the matrix `quatMat N_a`. -/
noncomputable def normalSU2 (σ : Simplex4) (a : Fin 5) : SU2 :=
  ⟨quatMat (outNormal σ a), by
    rw [← toMat_normalQuat]
    exact Lightlike.Spin4.toMat_mem_SU2 ⟨_, Lightlike.Spin4.mem_unitary_of_normSq (normSq_normalQuat σ a)⟩⟩

/-- The matrix of `normalSU2 σ a` is `quatMat N_a`. -/
@[simp] lemma coe_normalSU2 (σ : Simplex4) (a : Fin 5) :
    (normalSU2 σ a : Matrix (Fin 2) (Fin 2) ℂ) = quatMat (outNormal σ a) := rfl

/-! ## Quaternions and Bloch vectors -/

/-- The imaginary coordinates `(q_k, q_j, q_i)` of a quaternion, in the order of the Bloch vector:
`ν(toMat f) = vec3 (f i f̄)` (`bloch_toMat`). -/
def vec3 : ℍ →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun q := ![q.imK, q.imJ, q.imI]
  map_add' p q := by ext k; fin_cases k <;> simp
  map_smul' c q := by ext k; fin_cases k <;> simp

/-- The first coordinate of `vec3 q` is `q_k`. -/
@[simp] lemma vec3_zero (q : ℍ) : vec3 q 0 = q.imK := rfl

/-- The second coordinate of `vec3 q` is `q_j`. -/
@[simp] lemma vec3_one (q : ℍ) : vec3 q 1 = q.imJ := rfl

/-- The third coordinate of `vec3 q` is `q_i`. -/
@[simp] lemma vec3_two (q : ℍ) : vec3 q 2 = q.imI := rfl

/-- The Bloch vector of the matrix of `f` is `vec3` of the rotated `i`. -/
lemma bloch_toMat (f : ℍ) : bloch (Lightlike.Spin4.toMat f) = vec3 (rotI f) := by
  rw [rotI, mul_quatI_mul_star]; ext k; fin_cases k <;> rfl

/-- `vec3` vanishes on real quaternions. -/
lemma vec3_coe (r : ℝ) : vec3 (r : ℍ) = 0 := by ext k; fin_cases k <;> simp

/-- `vec3` only sees the imaginary part. -/
lemma vec3_im (q : ℍ) : vec3 q.im = vec3 q := by ext k; fin_cases k <;> simp

/-- `vec3` changes sign under conjugation. -/
lemma vec3_star (q : ℍ) : vec3 (star q) = -vec3 q := by ext k; fin_cases k <;> simp

/-- The squares of `vec3 q` sum to `|q|² - (Re q)²`. -/
lemma sum_vec3_sq (q : ℍ) : ∑ k, vec3 q k ^ 2 = normSq q - q.re ^ 2 := by
  rw [Fin.sum_univ_three, normSq_def']; simp; ring

/-- A pure quaternion with `vec3 q = 0` is zero. -/
lemma eq_zero_of_vec3 {q : ℍ} (hre : q.re = 0) (h : vec3 q = 0) : q = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [vec3_zero, vec3_one, vec3_two, Pi.zero_apply] at h0 h1 h2
  ext <;> simp [hre, h0, h1, h2]

/-- The Bloch vector of the matrix of a unit quaternion is nonzero. -/
lemma bloch_toMat_ne_zero {f : ℍ} (hf : normSq f = 1) : bloch (Lightlike.Spin4.toMat f) ≠ 0 := by
  rw [bloch_toMat]
  exact fun h => mul_quatI_mul_star_ne_zero hf (eq_zero_of_vec3 (re_mul_quatI_mul_star f) h)

/-! ## Conjugation by unit quaternions -/

/-- Conjugation by a unit quaternion keeps the real part. -/
lemma re_star_mul_mul {p : ℍ} (hp : normSq p = 1) (w : ℍ) : (star p * w * p).re = w.re := by
  rw [normSq_def'] at hp
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  linear_combination w.re * hp

/-- `Im q = q - Re q`. -/
lemma im_eq_sub (q : ℍ) : q.im = q - (q.re : ℍ) := eq_sub_of_add_eq' (Quaternion.re_add_im q)

/-- Conjugation by a unit quaternion commutes with taking the imaginary part. -/
lemma star_mul_im_mul {p : ℍ} (hp : normSq p = 1) (w : ℍ) :
    star p * w.im * p = (star p * w * p).im := by
  rw [im_eq_sub, im_eq_sub, re_star_mul_mul hp, mul_sub, sub_mul,
    ← Quaternion.coe_commutes, mul_assoc (w.re : ℍ), star_mul_of_normSq hp, mul_one]

/-- Conjugation by a unit quaternion commutes with taking the imaginary part. -/
lemma mul_im_mul_star {p : ℍ} (hp : normSq p = 1) (w : ℍ) :
    p * w.im * star p = (p * w * star p).im := by
  have hp' : normSq (star p) = 1 := by rw [Quaternion.normSq_star, hp]
  simpa only [star_star] using star_mul_im_mul hp' w

/-! ## Lifts of unit vectors and phases -/

/-- A unit quaternion that rotates `i` to the pure quaternion with `vec3 = v`: with
`α = √((1 + v₂)/2)`, the quaternion `α - (v₀/(2α)) j + (v₁/(2α)) k`, and `ε` for `v₂ = -1`.
Its matrix is `liftSU2 v` (`toMat_liftQuat`). -/
noncomputable def liftQuat (v : Fin 3 → ℝ) : ℍ :=
  if v 2 = -1 then quatEps else
    ⟨√((1 + v 2) / 2), 0, -(v 0 / (2 * √((1 + v 2) / 2))), v 1 / (2 * √((1 + v 2) / 2))⟩

/-- The matrix of `liftQuat v` is `liftSU2 v`. -/
lemma toMat_liftQuat (v : Fin 3 → ℝ) : Lightlike.Spin4.toMat (liftQuat v) = liftSU2 v := by
  unfold liftQuat liftSU2
  split_ifs with h
  · exact toMat_quatEps
  · set α := √((1 + v 2) / 2)
    have h2 : (2 : ℂ) * (α : ℂ) = ((2 * α : ℝ) : ℂ) := by push_cast; ring
    have e1 : ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / (2 * (α : ℂ)) =
        ⟨v 0 / (2 * α), v 1 / (2 * α)⟩ := by
      rw [h2]; apply Complex.ext
      · rw [Complex.div_ofReal_re]; simp
      · rw [Complex.div_ofReal_im]; simp
    have e2 : -(((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) / (2 * (α : ℂ))) =
        ⟨-(v 0 / (2 * α)), v 1 / (2 * α)⟩ := by
      rw [h2]; apply Complex.ext
      · rw [Complex.neg_re, Complex.div_ofReal_re]; simp
      · rw [Complex.neg_im, Complex.div_ofReal_im]; simp [neg_div]
    rw [e1, e2]
    ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [Lightlike.Spin4.toMat_apply, Lightlike.Spin4.quatMat]

/-- The quaternion `a + c j + d k` rotates `i` to `(a² - c² - d²) i + 2ad j - 2ac k`. -/
lemma rotI_mk (a c d : ℝ) :
    rotI ⟨a, 0, c, d⟩ = ⟨0, a ^ 2 - c ^ 2 - d ^ 2, 2 * a * d, -(2 * a * c)⟩ := by
  ext <;> simp [rotI, quatI] <;> ring

/-- The two pieces of `liftQuat (vec3 k)` for a pure unit quaternion `k` away from `-i`. -/
lemma liftQuat_aux {k : ℍ} (hk : k.re = 0) (hn : normSq k = 1) (h : k.imI ≠ -1) :
    0 < 1 + k.imI ∧ √((1 + k.imI) / 2) ^ 2 = (1 + k.imI) / 2 ∧
      (k.imK / (2 * √((1 + k.imI) / 2))) ^ 2 + (k.imJ / (2 * √((1 + k.imI) / 2))) ^ 2 =
        (1 - k.imI) / 2 := by
  rw [normSq_def', hk] at hn
  have hpos : 0 < 1 + k.imI := by
    have : -1 ≤ k.imI := by nlinarith [sq_nonneg k.imJ, sq_nonneg k.imK]
    exact lt_of_le_of_ne (by linarith) (fun h' => h (by linarith))
  have hα : √((1 + k.imI) / 2) ^ 2 = (1 + k.imI) / 2 := Real.sq_sqrt (by linarith)
  refine ⟨hpos, hα, ?_⟩
  rw [div_pow, div_pow, mul_pow, hα, ← add_div, div_eq_iff (by positivity)]
  linear_combination hn

/-- **The lift rotates `i` to `k`.** For a pure unit quaternion `k`, `liftQuat (vec3 k)` rotates
`i` to `k`. -/
lemma rotI_liftQuat {k : ℍ} (hk : k.re = 0) (hn : normSq k = 1) : rotI (liftQuat (vec3 k)) = k := by
  unfold liftQuat
  split_ifs with h
  · rw [vec3_two] at h
    have hn' := hn
    rw [normSq_def', hk, h] at hn'
    have hJ : k.imJ = 0 := by nlinarith [sq_nonneg k.imJ, sq_nonneg k.imK]
    have hK : k.imK = 0 := by nlinarith [sq_nonneg k.imJ, sq_nonneg k.imK]
    rw [rotI_quatEps]; ext <;> simp [quatI, hk, h, hJ, hK]
  · rw [vec3_two] at h
    obtain ⟨hpos, hα, hcd⟩ := liftQuat_aux hk hn h
    have hα0 : √((1 + k.imI) / 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    simp only [vec3_zero, vec3_one, vec3_two]
    rw [rotI_mk]
    ext
    · simp [hk]
    · simp only [neg_sq]; linear_combination hα - hcd
    · simp only; field_simp
    · simp only; field_simp

/-- For a pure unit quaternion `k`, `liftQuat (vec3 k)` is a unit quaternion. -/
lemma normSq_liftQuat {k : ℍ} (hk : k.re = 0) (hn : normSq k = 1) :
    normSq (liftQuat (vec3 k)) = 1 := by
  unfold liftQuat
  split_ifs with h
  · exact normSq_quatEps
  · rw [vec3_two] at h
    obtain ⟨-, hα, hcd⟩ := liftQuat_aux hk hn h
    simp only [vec3_zero, vec3_one, vec3_two]
    rw [normSq_def']
    simp only [neg_sq]
    linear_combination hα + hcd

/-- The phase `cos(β/2) + sin(β/2) i`, whose matrix is `phaseMat β` (`toMat_phaseQuat`). -/
noncomputable def phaseQuat (β : ℝ) : ℍ := ⟨Real.cos (β / 2), Real.sin (β / 2), 0, 0⟩

/-- The matrix of `phaseQuat β` is `phaseMat β`. -/
lemma toMat_phaseQuat (β : ℝ) : Lightlike.Spin4.toMat (phaseQuat β) = phaseMat β := by
  have h1 : Complex.I * (β : ℂ) / 2 = ((β / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have h2 : -(((β / 2 : ℝ) : ℂ) * Complex.I) = ((-(β / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have c1 : Complex.exp (((β / 2 : ℝ) : ℂ) * Complex.I) = ⟨Real.cos (β / 2), Real.sin (β / 2)⟩ :=
    Complex.ext (Complex.exp_ofReal_mul_I_re _) (Complex.exp_ofReal_mul_I_im _)
  have c2 : Complex.exp (((-(β / 2) : ℝ) : ℂ) * Complex.I) =
      ⟨Real.cos (β / 2), -Real.sin (β / 2)⟩ :=
    Complex.ext (by rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg])
      (by rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg])
  unfold phaseMat
  rw [h1, h2, c1, c2]
  ext i j; fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Lightlike.Spin4.toMat_apply, Lightlike.Spin4.quatMat, phaseQuat]

/-- The phase quaternion is a unit quaternion. -/
lemma normSq_phaseQuat (β : ℝ) : normSq (phaseQuat β) = 1 := by
  rw [normSq_def']; simp only [phaseQuat]
  linear_combination Real.cos_sq_add_sin_sq (β / 2)

/-- The phase fixes `i`. -/
lemma rotI_phaseQuat (β : ℝ) : rotI (phaseQuat β) = quatI := by
  ext <;> simp [rotI, quatI, phaseQuat]
  · ring
  · linear_combination Real.cos_sq_add_sin_sq (β / 2)

/-! ## The quaternion lifts of the Regge state -/

variable (σ : Simplex4)

/-- `s_e = √(1 - ⟨N_a, N_b⟩²)` for the edge `e = ab`: the sine of the angle between the normals,
and the length of the bivector of `e`. -/
noncomputable def edgeSin (e : Fin 10) : ℝ :=
  √(1 - ⟪outNormal σ (edgeSrc e), outNormal σ (edgeTgt e)⟫ ^ 2)

/-- `s_e > 0`. -/
lemma edgeSin_pos (e : Fin 10) : 0 < edgeSin σ e :=
  Real.sqrt_pos.mpr (one_sub_inner_outNormal_sq_pos σ (edgeSrc_ne_edgeTgt e))

/-- The unit bivector of the edge `e = ab` as a pure quaternion: `s_e⁻¹ Im(N_a N̄_b)`. -/
noncomputable def bivQuat (e : Fin 10) : ℍ :=
  (edgeSin σ e)⁻¹ • (normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e))).im

/-- The bivector is `vec3 (N_a N̄_b)`. -/
lemma bivector_eq_vec3 (e : Fin 10) :
    bivector σ e = vec3 (normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e))) := by
  have hM : quatMat (outNormal σ (edgeSrc e)) * (quatMat (outNormal σ (edgeTgt e)))ᴴ =
      Lightlike.Spin4.toMat (normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e))) := by
    rw [map_mul, Lightlike.Spin4.toMat_star, toMat_normalQuat, toMat_normalQuat]
  simp only [bivector, hM]
  ext k; fin_cases k <;> simp [Lightlike.Spin4.toMat_apply, Lightlike.Spin4.quatMat]

/-- The squared length of `N_a N̄_b` minus its real part is `s_e²`. -/
lemma normSq_sub_re_sq (e : Fin 10) :
    normSq (normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e))) -
        (normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e))).re ^ 2 = edgeSin σ e ^ 2 := by
  rw [edgeSin, Real.sq_sqrt (one_sub_inner_outNormal_sq_pos σ (edgeSrc_ne_edgeTgt e)).le,
    map_mul, Quaternion.normSq_star, normSq_normalQuat, normSq_normalQuat, one_mul, normalQuat,
    normalQuat, re_vecQuat_mul_star]

/-- `bivQuat` is pure. -/
lemma re_bivQuat (e : Fin 10) : (bivQuat σ e).re = 0 := by simp [bivQuat]

/-- `bivQuat` is a unit quaternion. -/
lemma normSq_bivQuat (e : Fin 10) : normSq (bivQuat σ e) = 1 := by
  have h := normSq_sub_re_sq σ e
  have hs := (edgeSin_pos σ e).ne'
  set w := normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e))
  rw [normSq_def'] at h
  rw [bivQuat, normSq_def']
  simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
    Quaternion.re_im, Quaternion.imI_im, Quaternion.imJ_im, Quaternion.imK_im, smul_eq_mul]
  field_simp
  linear_combination h

/-- `vec3 (bivQuat σ e)` is the unit bivector of `e`. -/
lemma vec3_bivQuat (e : Fin 10) : vec3 (bivQuat σ e) = unitBivector σ e := by
  rw [unitBivector, bivector_eq_vec3, sum_vec3_sq, normSq_sub_re_sq,
    Real.sqrt_sq (edgeSin_pos σ e).le, bivQuat, map_smul, vec3_im]

/-- The lift `m_e` of the unit bivector rotates `i` to `bivQuat σ e`. -/
lemma rotI_liftQuat_bivector (e : Fin 10) :
    rotI (liftQuat (unitBivector σ e)) = bivQuat σ e := by
  rw [← vec3_bivQuat]; exact rotI_liftQuat (re_bivQuat σ e) (normSq_bivQuat σ e)

/-- The lift `m_e` is a unit quaternion. -/
lemma normSq_liftQuat_bivector (e : Fin 10) : normSq (liftQuat (unitBivector σ e)) = 1 := by
  rw [← vec3_bivQuat]; exact normSq_liftQuat (re_bivQuat σ e) (normSq_bivQuat σ e)

/-- **The quaternion lifts of the Regge state**: `N̄_a m_e δ(Θ_e)` at the source and `N̄_b m_e ε`
at the target of the edge `e = ab`. -/
noncomputable def reggeLift (e : Fin 10) : Fin 2 → ℍ :=
  ![star (normalQuat σ (edgeSrc e)) * liftQuat (unitBivector σ e) * phaseQuat (reggeAngle σ e),
    star (normalQuat σ (edgeTgt e)) * liftQuat (unitBivector σ e) * quatEps]

/-- The matrices of the lifts are the Regge state. -/
lemma toMat_reggeLift (e : Fin 10) (i : Fin 2) :
    Lightlike.Spin4.toMat (reggeLift σ e i) = reggeState σ e i := by
  fin_cases i <;>
    simp [reggeLift, reggeState, map_mul, Lightlike.Spin4.toMat_star, toMat_normalQuat, toMat_liftQuat,
      toMat_phaseQuat, toMat_quatEps]

/-- The lifts are unit quaternions. -/
lemma normSq_reggeLift (e : Fin 10) (i : Fin 2) : normSq (reggeLift σ e i) = 1 := by
  fin_cases i <;>
    simp [reggeLift, map_mul, Quaternion.normSq_star, normSq_normalQuat,
      normSq_liftQuat_bivector, normSq_phaseQuat, normSq_quatEps]

/-- **The Regge state is SU(2) boundary data.** -/
theorem isSU2Data_reggeState : IsSU2Data (reggeState σ) := by
  intro e i
  rw [← toMat_reggeLift]
  exact Lightlike.Spin4.toMat_mem_SU2 ⟨_, Lightlike.Spin4.mem_unitary_of_normSq (normSq_reggeLift σ e i)⟩

/-! ## Gluing of the Regge state -/

/-- The rotated `i` of the source lift of the edge `e = ab`: `V_e = s_e⁻¹ Im(N̄_b N_a)`. -/
noncomputable def edgeVec (e : Fin 10) : ℍ :=
  (edgeSin σ e)⁻¹ • (star (normalQuat σ (edgeTgt e)) * normalQuat σ (edgeSrc e)).im

/-- The source lift rotates `i` to `V_e`. -/
lemma rotI_reggeLift_zero (e : Fin 10) : rotI (reggeLift σ e 0) = edgeVec σ e := by
  have hs := normSq_normalQuat σ (edgeSrc e)
  simp only [reggeLift, Matrix.cons_val_zero]
  rw [mul_assoc, rotI_mul, rotI_mul, rotI_phaseQuat, ← rotI, rotI_liftQuat_bivector, bivQuat,
    star_star, mul_smul_comm, smul_mul_assoc, star_mul_im_mul hs, star_mul_cancel hs, edgeVec]

/-- The target lift rotates `i` to `-V_e`. -/
lemma rotI_reggeLift_one (e : Fin 10) : rotI (reggeLift σ e 1) = -edgeVec σ e := by
  have ht := normSq_normalQuat σ (edgeTgt e)
  simp only [reggeLift, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [rotI_mul_quatEps, rotI_mul, rotI_liftQuat_bivector, bivQuat, star_star, mul_smul_comm,
    smul_mul_assoc, star_mul_im_mul ht, mul_assoc, mul_assoc, star_mul_of_normSq ht, mul_one,
    edgeVec]

/-! ## Gluing -/

/-- `X = 1` glues every edge of the Regge state. -/
theorem glued_one (e : Fin 10) :
    bloch (frameSrc (isSU2Data_reggeState σ) 1 e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt (isSU2Data_reggeState σ) 1 e : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [glued_iff_rotI _ 1 (fun _ => 1) (fun a => by simp) (reggeLift σ) (toMat_reggeLift σ) e,
    rotI_mul_quatEps, rotI_reggeLift_zero, rotI_reggeLift_one]

/-- `X_a = Q_a`, the normals as SU(2) elements, glues every edge of the Regge state. -/
theorem glued_normal (e : Fin 10) :
    bloch (frameSrc (isSU2Data_reggeState σ) (normalSU2 σ) e : Matrix (Fin 2) (Fin 2) ℂ) =
      bloch (frameTgt (isSU2Data_reggeState σ) (normalSU2 σ) e : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs := normSq_normalQuat σ (edgeSrc e)
  have ht := normSq_normalQuat σ (edgeTgt e)
  rw [glued_iff_rotI _ (normalSU2 σ) (normalQuat σ) (toMat_normalQuat σ) (reggeLift σ)
    (toMat_reggeLift σ) e, rotI_mul_quatEps, rotI_reggeLift_zero, rotI_reggeLift_one, edgeVec]
  have e1 : normalQuat σ (edgeSrc e) *
      (star (normalQuat σ (edgeTgt e)) * normalQuat σ (edgeSrc e)) *
        star (normalQuat σ (edgeSrc e)) =
        normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e)) := by
    rw [mul_assoc, mul_assoc, mul_star_of_normSq hs, mul_one]
  have e2 : normalQuat σ (edgeTgt e) *
      (star (normalQuat σ (edgeTgt e)) * normalQuat σ (edgeSrc e)) *
        star (normalQuat σ (edgeTgt e)) =
        normalQuat σ (edgeSrc e) * star (normalQuat σ (edgeTgt e)) := by
    rw [mul_star_cancel ht]
  simp only [mul_neg, neg_mul, neg_inj, mul_smul_comm, smul_mul_assoc]
  rw [mul_im_mul_star hs, mul_im_mul_star ht, e1, e2]

/-- For distinct nodes `a, b ≠ 4`, the normals `Q₄, Q_a, Q_b` are real independent matrices. -/
theorem linearIndependent_normalSU2 (a b : Fin 5) (hab : a ≠ b) (ha : a ≠ 4) (hb : b ≠ 4) :
    LinearIndependent ℝ
      ![(normalSU2 σ 4 : Matrix (Fin 2) (Fin 2) ℂ), normalSU2 σ a, normalSU2 σ b] := by
  have h := linearIndependent_outNormal_three σ (Ne.symm ha) (Ne.symm hb) hab
  have hL := h.map' (Lightlike.Spin4.toMat.toLinearMap ∘ₗ vecQuat)
    (LinearMap.ker_eq_bot.mpr (Lightlike.Spin4.toMat_injective.comp vecQuat_injective))
  convert hL using 1
  ext i : 1
  fin_cases i <;> simp [toMat_vecQuat]

/-! ## Closure -/

/-- Summing a function of the other end over the edges at `x` gives the total sum minus the value
at `x`. -/
lemma sum_edge_other {M : Type*} [AddCommGroup M] (φ : Fin 5 → M) (x : Fin 5) :
    ∑ e, (if edgeSrc e = x then φ (edgeTgt e) else if edgeTgt e = x then φ (edgeSrc e) else 0) =
      ∑ y, φ y - φ x := by
  rw [Fin.sum_univ_five]
  fin_cases x <;> simp [Fin.sum_univ_succ, edgeSrc, edgeTgt] <;> abel

/-- The term `h_y⁻¹ (Q̄_y Q_x)` of the closure at `x`, in Bloch coordinates. -/
noncomputable def closureTerm (x y : Fin 5) : Fin 3 → ℝ :=
  (σ.height y)⁻¹ • vec3 (star (normalQuat σ y) * normalQuat σ x)

/-- The closure terms add up to zero, by `Σ_y N_y / h_y = 0`. -/
lemma sum_closureTerm (x : Fin 5) : ∑ y, closureTerm σ x y = 0 := by
  have h := congrArg (fun v => vec3 (star (vecQuat v) * normalQuat σ x))
    (sum_outNormal_div_height σ)
  simp only [map_sum, map_smul, star_sum, Quaternion.star_smul, sum_mul, smul_mul_assoc, map_zero,
    star_zero, zero_mul] at h
  simpa [closureTerm, normalQuat] using h

/-- The closure term at `y = x` vanishes. -/
lemma closureTerm_self (x : Fin 5) : closureTerm σ x x = 0 := by
  rw [closureTerm, star_mul_of_normSq (normSq_normalQuat σ x), ← Quaternion.coe_one, vec3_coe,
    smul_zero]

/-- **Area times normal.** At a node `x` of the edge `e`, `A_e ν_e = (V_x / 2) h_y⁻¹ (Q̄_y Q_x)`
with `y` the other end of `e`. -/
lemma triArea_smul_nodeNormal (x : Fin 5) (e : Fin 10) :
    triArea σ e • nodeNormal (reggeState σ) x e =
      (nodeVol σ x / 2) • (if edgeSrc e = x then closureTerm σ x (edgeTgt e)
        else if edgeTgt e = x then closureTerm σ x (edgeSrc e) else 0) := by
  have hsin := (edgeSin_pos σ e).ne'
  unfold nodeNormal
  split_ifs with h1 h2
  · subst h1
    have hA : 2 * triArea σ e * σ.height (edgeTgt e) = edgeSin σ e * nodeVol σ (edgeSrc e) :=
      triArea_mul_height_tgt σ e
    have hh := (σ.height_pos (edgeTgt e)).ne'
    rw [← toMat_reggeLift, bloch_toMat, rotI_reggeLift_zero, edgeVec, map_smul, vec3_im,
      closureTerm, smul_smul, smul_smul]
    congr 1
    field_simp
    linear_combination hA
  · subst h2
    have hA : 2 * triArea σ e * σ.height (edgeSrc e) = edgeSin σ e * nodeVol σ (edgeTgt e) :=
      triArea_mul_height_src σ e
    have hh := (σ.height_pos (edgeSrc e)).ne'
    have hv : vec3 (star (normalQuat σ (edgeSrc e)) * normalQuat σ (edgeTgt e)) =
        -vec3 (star (normalQuat σ (edgeTgt e)) * normalQuat σ (edgeSrc e)) := by
      rw [← vec3_star, star_mul, star_star]
    rw [← toMat_reggeLift, bloch_toMat, rotI_reggeLift_one, edgeVec, map_neg, map_smul, vec3_im,
      closureTerm, hv]
    simp only [smul_neg, smul_smul, neg_inj]
    congr 1
    field_simp
    linear_combination hA
  · simp

/-- **Closure of the Regge state.** For spins proportional to the areas, the normals of the Regge
state close at every node. -/
theorem closure_reggeState (n : Fin 10 → ℕ)
    (hn : ∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e) (x : Fin 5) :
    ∑ e, (n e : ℝ) • nodeNormal (reggeState σ) x e = 0 := by
  obtain ⟨c, -, hc⟩ := hn
  simp_rw [hc, mul_smul, triArea_smul_nodeNormal]
  rw [← smul_sum, ← smul_sum, sum_edge_other (closureTerm σ x) x, sum_closureTerm,
    closureTerm_self, sub_zero, smul_zero, smul_zero]

/-- The triangle areas of a 4-simplex are positive. -/
lemma triArea_pos (e : Fin 10) : 0 < triArea σ e := by
  obtain ⟨h01, h02, h12, h0s, h1s, h2s, -, -, -, -⟩ := edge_distinct e
  have h2 := two_triArea σ e (Or.inl rfl)
  rw [inner_cross3_outNormal σ h0s h1s h2s] at h2
  have hind := (affineIndependent_iff_linearIndependent_vsub ℝ σ.points (edgeTri e 0)).mp
    σ.independent
  have hpair : LinearIndependent ℝ ![σ.points (edgeTri e 1) - σ.points (edgeTri e 0),
      σ.points (edgeTri e 2) - σ.points (edgeTri e 0)] := by
    have := hind.comp (![⟨edgeTri e 1, h01.symm⟩, ⟨edgeTri e 2, h02.symm⟩] :
      Fin 2 → {x // x ≠ edgeTri e 0}) (by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff])
    convert this using 1
    ext i : 1; fin_cases i <;> simp [vsub_eq_sub]
  have hg := Lightlike.Regge4.gram_two_pos hpair
  have : 0 < 2 * triArea σ e := by rw [h2]; exact Real.sqrt_pos.mpr hg
  linarith


/-! ## The critical points -/

/-- **The critical points of the Regge state.** For spins proportional to the triangle areas,
`X` is a critical point of the coherent amplitude (`|F_n(X)| = 1` and `F_n` stationary in all
twelve directions) exactly when `X_a = ±X₄ U⁻_a` for every `a` or `X_a = ±X₄ U⁺_a` for every `a`:
up to the gauge `X ↦ X₄ X` and the signs, the two points `critMinus` and `critPlus σ`. -/
theorem reggeState_critical_iff (n : Fin 10 → ℕ)
    (hn : ∃ c : ℝ, 0 < c ∧ ∀ e, (n e : ℝ) = c * triArea σ e) (X : Fin 5 → SU2) :
    (‖cohAmp n (reggeState σ) (fun a => (X a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ∧
      ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp n (reggeState σ) (chart (fun b => (X b : Matrix (Fin 2) (Fin 2) ℂ)) θ))
        l 0 = 0) ↔
      (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 * critMinus a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) = -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * critMinus a)) ∨
        (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 * critPlus σ a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * critPlus σ a)) := by
  have hg := isSU2Data_reggeState σ
  obtain ⟨c, hc, hce⟩ := hn
  have hne : ∀ e, n e ≠ 0 := fun e h0 => by
    have h := hce e
    rw [h0, Nat.cast_zero] at h
    exact (mul_pos hc (triArea_pos σ e)).ne h
  have key := glued_iff_two_classes hg (normalSU2 σ) (glued_one σ) (glued_normal σ)
    (linearIndependent_normalSU2 σ) X
  have hcls :
      ((∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 * critMinus a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) = -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * critMinus a)) ∨
        (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 * critPlus σ a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) = -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * critPlus σ a))) ↔
      ((∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) = -(X 4 : Matrix (Fin 2) (Fin 2) ℂ)) ∨
        (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            (X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (normalSU2 σ 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
              normalSU2 σ a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * (normalSU2 σ 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
              normalSU2 σ a))) := by
    simp only [critMinus, critPlus, mul_one, Matrix.mul_assoc, coe_normalSU2]
  rw [norm_cohAmp_eq_one_iff n hg X, hcls]
  constructor
  · rintro ⟨hglue, -⟩
    exact key.mp fun e => hglue e (hne e)
  · intro h
    have hglue := key.mpr h
    refine ⟨fun e _ => hglue e, ?_⟩
    rw [stationary_iff_closure n hg X fun e _ => hglue e]
    exact closure_reggeState σ n ⟨c, hc, hce⟩

/-- `U⁺_a = toMat (Q̄₄ Q_a)`. -/
lemma critPlus_eq_toMat (a : Fin 5) :
    critPlus σ a = Lightlike.Spin4.toMat (star (normalQuat σ 4) * normalQuat σ a) := by
  simp only [critPlus, map_mul, Lightlike.Spin4.toMat_star, toMat_normalQuat]

/-- `U⁺₄ = 1`. -/
lemma critPlus_four : critPlus σ 4 = 1 := by
  rw [critPlus_eq_toMat, star_mul_of_normSq (normSq_normalQuat σ 4), map_one]

/-- For `a ≠ 4`, `U⁺_a ≠ ±1`: two distinct normals are not parallel. -/
lemma critPlus_ne (a : Fin 5) (ha : a ≠ 4) : critPlus σ a ≠ 1 ∧ critPlus σ a ≠ -1 := by
  have hlt := abs_inner_outNormal_lt_one σ (Ne.symm ha)
  have hre : (star (normalQuat σ 4) * normalQuat σ a).re = ⟪outNormal σ 4, outNormal σ a⟫ :=
    re_star_vecQuat_mul (outNormal σ 4) (outNormal σ a)
  rw [critPlus_eq_toMat]
  constructor
  · intro h
    rw [← map_one Lightlike.Spin4.toMat] at h
    have h' := congrArg QuaternionAlgebra.re (Lightlike.Spin4.toMat_injective h)
    rw [hre] at h'
    rw [h'] at hlt
    norm_num at hlt
  · intro h
    rw [← map_one Lightlike.Spin4.toMat, ← map_neg] at h
    have h' := congrArg QuaternionAlgebra.re (Lightlike.Spin4.toMat_injective h)
    rw [hre] at h'
    rw [h'] at hlt
    norm_num at hlt

/-- **The two critical classes are disjoint**: no `X` lies in both. -/
theorem critical_classes_disjoint (X : Fin 5 → SU2) :
    ¬ ((∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 * critMinus a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) = -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * critMinus a)) ∧
        (∀ a, (X a : Matrix (Fin 2) (Fin 2) ℂ) = X 4 * critPlus σ a ∨
          (X a : Matrix (Fin 2) (Fin 2) ℂ) =
            -((X 4 : Matrix (Fin 2) (Fin 2) ℂ) * critPlus σ a))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨hne1, hne2⟩ := critPlus_ne σ 0 (by decide)
  have hX : (X 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X 4 = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup (X 4).2)
  have k1 : (X 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X 0 = 1 ∨
      (X 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X 0 = -1 := by
    rcases h1 0 with h | h
    · left; rw [h]; simp [critMinus, hX]
    · right; rw [h]; simp [critMinus, hX]
  have k2 : (X 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X 0 = critPlus σ 0 ∨
      (X 4 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * X 0 = -critPlus σ 0 := by
    rcases h2 0 with h | h
    · left; rw [h, ← Matrix.mul_assoc, hX, Matrix.one_mul]
    · right; rw [h, Matrix.mul_neg, ← Matrix.mul_assoc, hX, Matrix.one_mul]
  rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2 <;> rw [k1] at k2
  · exact hne1 k2.symm
  · exact hne2 (by rw [← neg_neg (critPlus σ 0), ← k2])
  · exact hne2 k2.symm
  · exact hne1 (by rw [← neg_neg (critPlus σ 0), ← k2, neg_neg])

/-- `U⁺` as a tuple of SU(2) elements. -/
noncomputable def critPlusSU2 (a : Fin 5) : SU2 :=
  ⟨critPlus σ a, by
    rw [critPlus_eq_toMat]
    exact Lightlike.Spin4.toMat_mem_SU2 ⟨_, Lightlike.Spin4.mem_unitary_of_normSq (by
      rw [map_mul, Quaternion.normSq_star, normSq_normalQuat, normSq_normalQuat, one_mul])⟩⟩

/-- The coercion of `critPlusSU2 σ` is `critPlus σ`. -/
@[simp] lemma coe_critPlusSU2 (a : Fin 5) :
    (critPlusSU2 σ a : Matrix (Fin 2) (Fin 2) ℂ) = critPlus σ a := rfl

/-! ## Trust checks -/

/-- **Non-vacuity of the area hypothesis**: at the regular simplex, unit spins on every edge are
proportional to the areas. -/
theorem regular_unit_spins_area :
    ∃ c : ℝ, 0 < c ∧ ∀ e, ((fun _ => 1 : Fin 10 → ℕ) e : ℝ) = c * triArea regSimplex e := by
  refine ⟨2 / √3, by positivity, fun e => ?_⟩
  rw [triArea_regular]
  have h3 : √3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp
  norm_num

/-- **Trust check: `X = 1` is a critical point** of the regular simplex with unit spins. -/
theorem regular_one_critical :
    ‖cohAmp (fun _ => 1) (reggeState regSimplex)
        (fun a => ((1 : Fin 5 → SU2) a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ∧
      ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp (fun _ => 1) (reggeState regSimplex)
          (chart (fun b => ((1 : Fin 5 → SU2) b : Matrix (Fin 2) (Fin 2) ℂ)) θ)) l 0 = 0 :=
  (reggeState_critical_iff regSimplex _ regular_unit_spins_area 1).mpr
    (Or.inl fun a => Or.inl (by simp [critMinus]))

/-- **Trust check: `X = U⁺` is a critical point** of the regular simplex with unit spins. -/
theorem regular_critPlus_critical :
    ‖cohAmp (fun _ => 1) (reggeState regSimplex)
        (fun a => (critPlusSU2 regSimplex a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ∧
      ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp (fun _ => 1) (reggeState regSimplex)
          (chart (fun b => (critPlusSU2 regSimplex b : Matrix (Fin 2) (Fin 2) ℂ)) θ)) l 0 = 0 :=
  (reggeState_critical_iff regSimplex _ regular_unit_spins_area _).mpr
    (Or.inr fun a => Or.inl (by rw [coe_critPlusSU2, coe_critPlusSU2, critPlus_four, one_mul]))

/-- The mixed tuple `X₀ = U⁺₀`, `X_a = 1` otherwise. -/
noncomputable def mixedX : Fin 5 → SU2 := fun a => if a = 0 then critPlusSU2 regSimplex 0 else 1

/-- **Wrong-input check: a mixed tuple is not critical.** Taking `U⁺` at one node and `1` at the
others gives a point that is not critical for the regular simplex with unit spins. -/
theorem regular_mixed_not_critical :
    ¬ (‖cohAmp (fun _ => 1) (reggeState regSimplex)
        (fun a => (mixedX a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ∧
      ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp (fun _ => 1) (reggeState regSimplex)
          (chart (fun b => (mixedX b : Matrix (Fin 2) (Fin 2) ℂ)) θ)) l 0 = 0) := by
  rw [reggeState_critical_iff regSimplex _ regular_unit_spins_area]
  have h4 : (mixedX 4 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp [mixedX]
  have h0 : (mixedX 0 : Matrix (Fin 2) (Fin 2) ℂ) = critPlus regSimplex 0 := by simp [mixedX]
  have h1 : (mixedX 1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp [mixedX]
  obtain ⟨n0, n0'⟩ := critPlus_ne regSimplex 0 (by decide)
  obtain ⟨n1, n1'⟩ := critPlus_ne regSimplex 1 (by decide)
  rintro (h | h)
  · rcases h 0 with h | h <;> simp only [h0, h4, critMinus, mul_one] at h
    · exact n0 h
    · exact n0' h
  · rcases h 1 with h | h <;> simp only [h1, h4, Matrix.one_mul] at h
    · exact n1 h.symm
    · exact n1' (by rw [h, neg_neg])

/-- **Wrong-input check: spins not proportional to the areas.** With a single nonzero spin, `X = 1`
still glues every edge, so `|F_n(1)| = 1`, but the closure fails at the node `0` and `X = 1` is not
stationary. -/
theorem single_spin_one_not_stationary :
    ‖cohAmp (fun e => if e = 0 then 1 else 0) (reggeState σ)
        (fun a => ((1 : Fin 5 → SU2) a : Matrix (Fin 2) (Fin 2) ℂ))‖ = 1 ∧
      ¬ ∀ l : Fin 12, Lightlike.Oscillatory.coordDeriv
        (fun θ => cohAmp (fun e => if e = 0 then 1 else 0) (reggeState σ)
          (chart (fun b => ((1 : Fin 5 → SU2) b : Matrix (Fin 2) (Fin 2) ℂ)) θ)) l 0 = 0 := by
  have hg := isSU2Data_reggeState σ
  refine ⟨(norm_cohAmp_eq_one_iff _ hg 1).mpr fun e _ => glued_one σ e, ?_⟩
  rw [stationary_iff_closure _ hg 1 fun e _ => glued_one σ e]
  intro hcl
  have h0 := hcl 0
  rw [Finset.sum_eq_single (0 : Fin 10)] at h0
  · simp [nodeNormal, edgeSrc] at h0
    rw [← toMat_reggeLift] at h0
    exact bloch_toMat_ne_zero (normSq_reggeLift σ 0 0) h0
  · intro e _ he
    simp [he]
  · simp

end Lightlike.Asymptotics.EPRL
