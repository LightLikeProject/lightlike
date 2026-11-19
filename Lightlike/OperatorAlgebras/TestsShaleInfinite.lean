import Lightlike.OperatorAlgebras.ShaleSufficiency
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Trust check: a squeezing of infinitely many modes is not implemented

For a conjugation `C` of a complex Hilbert space (antilinear, involutive, `⟪C f, C g⟫ = conj ⟪f, g⟫`) and real
`a`, `b` with `a² - b² = 1`, the map `f ↦ a f + b C f` is a Bogoliubov transformation
(`Bogoliubov.squeezeConj`), and `‖β e‖² = b²` for every unit vector `e` fixed by `C`
(`Bogoliubov.squeezeConj_norm_betaPart_sq`).

On `ℓ²(ℕ)` with the componentwise complex conjugation every vector of the standard basis is fixed, so
`∑ₙ ‖β eₙ‖² = ∑ₙ b²` diverges for `b ≠ 0`: the antilinear part is not Hilbert-Schmidt
(`not_isHilbertSchmidt_squeezeEllTwo`), and by the necessity part of Shale's criterion the squeezing is not
implemented in any Fock representation of `ℓ²(ℕ)` (`not_implements_squeezeEllTwo`). This is the wrong-input
control of the criterion: the same squeezing of one mode is implemented (`implements_squeeze`).
-/

open scoped InnerProductSpace
open Complex

universe u

namespace Lightlike.OperatorAlgebras

section Conjugation

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
  (C : h → h) (hadd : ∀ f g, C (f + g) = C f + C g)
  (hsmul : ∀ (c : ℂ) (f : h), C (c • f) = (starRingEnd ℂ) c • C f)
  (hinv : ∀ f, C (C f) = f) (hinner : ∀ f g, ⟪C f, C g⟫_ℂ = (starRingEnd ℂ) ⟪f, g⟫_ℂ)

include hinner in
lemma norm_conjugation (f : h) : ‖C f‖ = ‖f‖ := by
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (C f)
  rw [hinner] at h1
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) f
  have h3 : RCLike.re ((starRingEnd ℂ) ⟪f, f⟫_ℂ) = RCLike.re ⟪f, f⟫_ℂ := RCLike.conj_re _
  rw [h3, h2] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1.symm

/-- A conjugation as a continuous real-linear map. -/
noncomputable def conjugationCLM : h →L[ℝ] h :=
  LinearMap.mkContinuous
    { toFun := C
      map_add' := hadd
      map_smul' := fun r f => by
        show C (r • f) = r • C f
        rw [← Complex.coe_smul, hsmul, conj_ofReal, Complex.coe_smul] }
    1 (fun f => by rw [one_mul]; exact (norm_conjugation C hinner f).le)

/-- The real-linear map `f ↦ a f + b C f`. -/
noncomputable def squeezeConjMap (a b : ℝ) : h →L[ℝ] h :=
  a • ContinuousLinearMap.id ℝ h + b • conjugationCLM C hadd hsmul hinner

lemma squeezeConjMap_apply (a b : ℝ) (f : h) :
    squeezeConjMap C hadd hsmul hinner a b f = (a : ℂ) • f + (b : ℂ) • C f := by
  show a • f + b • C f = (a : ℂ) • f + (b : ℂ) • C f
  rw [Complex.coe_smul, Complex.coe_smul]

include hinv in
lemma squeezeConjMap_comp (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (f : h) :
    squeezeConjMap C hadd hsmul hinner a (-b) (squeezeConjMap C hadd hsmul hinner a b f) = f := by
  have h1 : ((a : ℂ)) ^ 2 - (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  rw [squeezeConjMap_apply, squeezeConjMap_apply, hadd, hsmul, hsmul, hinv, conj_ofReal, conj_ofReal]
  have h2 : (a : ℂ) • ((a : ℂ) • f + (b : ℂ) • C f) + ((-b : ℝ) : ℂ) • ((a : ℂ) • C f + (b : ℂ) • f) =
      ((a : ℂ) ^ 2 - (b : ℂ) ^ 2) • f := by
    push_cast
    module
  rw [h2, h1, one_smul]

/-- **The squeezing `f ↦ a f + b C f`** of a conjugation `C`, `a² - b² = 1`, as a Bogoliubov transformation. -/
noncomputable def Bogoliubov.squeezeConj (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) : Bogoliubov h where
  toEquiv := ContinuousLinearEquiv.equivOfInverse (squeezeConjMap C hadd hsmul hinner a b)
    (squeezeConjMap C hadd hsmul hinner a (-b)) (squeezeConjMap_comp C hadd hsmul hinv hinner a b hab)
    (fun f => by
      have := squeezeConjMap_comp C hadd hsmul hinv hinner a (-b) (by rw [neg_sq]; exact hab) f
      rwa [neg_neg] at this)
  symp_map f g := by
    show (⟪squeezeConjMap C hadd hsmul hinner a b f, squeezeConjMap C hadd hsmul hinner a b g⟫_ℂ).im =
      (⟪f, g⟫_ℂ).im
    have hx : ⟪f, C g⟫_ℂ = (starRingEnd ℂ) ⟪C f, g⟫_ℂ := by
      have := hinner (C f) g
      rwa [hinv] at this
    have key : ⟪squeezeConjMap C hadd hsmul hinner a b f, squeezeConjMap C hadd hsmul hinner a b g⟫_ℂ =
        ((a ^ 2 : ℝ) : ℂ) * ⟪f, g⟫_ℂ + ((b ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) ⟪f, g⟫_ℂ +
          ((a * b : ℝ) : ℂ) * (⟪C f, g⟫_ℂ + (starRingEnd ℂ) ⟪C f, g⟫_ℂ) := by
      rw [squeezeConjMap_apply, squeezeConjMap_apply]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_ofReal, hinner,
        hx]
      push_cast
      ring
    rw [key]
    simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.conj_im]
    linear_combination (⟪f, g⟫_ℂ).im * hab

lemma Bogoliubov.squeezeConj_apply (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (f : h) :
    (Bogoliubov.squeezeConj C hadd hsmul hinv hinner a b hab).toEquiv f = (a : ℂ) • f + (b : ℂ) • C f :=
  squeezeConjMap_apply C hadd hsmul hinner a b f

/-- **`‖β e‖² = b²`** for a unit vector `e` fixed by the conjugation. -/
theorem Bogoliubov.squeezeConj_norm_betaPart_sq (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) {e : h}
    (hCe : C e = e) (he : ‖e‖ = 1) :
    ‖(Bogoliubov.squeezeConj C hadd hsmul hinv hinner a b hab).betaPart e‖ ^ 2 = b ^ 2 := by
  have h1 : (Bogoliubov.squeezeConj C hadd hsmul hinv hinner a b hab).toEquiv e = ((a + b : ℝ) : ℂ) • e := by
    rw [Bogoliubov.squeezeConj_apply, hCe]
    push_cast
    rw [add_smul]
  have h2 : (Bogoliubov.squeezeConj C hadd hsmul hinv hinner a b hab).toEquiv (I • e) =
      ((a - b : ℝ) : ℂ) • (I • e) := by
    rw [Bogoliubov.squeezeConj_apply, hsmul, hCe, conj_I]
    push_cast
    module
  rw [Bogoliubov.norm_beta_sq_eq, h1, h2, norm_smul, norm_smul, norm_smul, Complex.norm_real,
    Complex.norm_real, Complex.norm_I, he]
  simp only [mul_one, Real.norm_eq_abs, sq_abs]
  linear_combination (1 / 2 : ℝ) * hab

end Conjugation

/-! ### The squeezing of `ℓ²(ℕ)` -/

/-- The Hilbert space `ℓ²(ℕ)`. -/
abbrev EllTwo : Type := lp (fun _ : ℕ => ℂ) 2

lemma EllTwo.inner_star_star (f g : EllTwo) : ⟪star f, star g⟫_ℂ = (starRingEnd ℂ) ⟪f, g⟫_ℂ := by
  have h1 := (lp.hasSum_inner (𝕜 := ℂ) f g).star
  have h2 := lp.hasSum_inner (𝕜 := ℂ) (star f) (star g)
  have h3 : (fun i => ⟪(star f) i, (star g) i⟫_ℂ) = fun i => star ⟪f i, g i⟫_ℂ := by
    funext i
    rw [lp.star_apply, lp.star_apply, RCLike.inner_apply, RCLike.inner_apply]
    simp [star_mul']
  rw [h3] at h2
  exact h2.unique h1

/-- **The squeezing of `ℓ²(ℕ)`**, `f ↦ a f + b f̄` with the componentwise conjugation. -/
noncomputable def squeezeEllTwo (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) : Bogoliubov EllTwo :=
  Bogoliubov.squeezeConj (star : EllTwo → EllTwo) star_add (fun c f => star_smul c f) star_star
    EllTwo.inner_star_star a b hab

/-- The standard Hilbert basis of `ℓ²(ℕ)`. -/
noncomputable def ellTwoBasis : HilbertBasis ℕ ℂ EllTwo :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ EllTwo)

lemma ellTwoBasis_apply (n : ℕ) : ellTwoBasis n = lp.single 2 n (1 : ℂ) :=
  (ellTwoBasis.repr_symm_single n).symm

lemma star_ellTwoBasis (n : ℕ) : star (ellTwoBasis n) = ellTwoBasis n := by
  rw [ellTwoBasis_apply]
  ext i
  rw [lp.star_apply]
  by_cases hi : i = n
  · subst hi
    rw [lp.single_apply_self]
    simp
  · rw [lp.single_apply_ne 2 n _ hi]
    simp

/-- **The antilinear part of the squeezing of `ℓ²(ℕ)` is not Hilbert-Schmidt** for `b ≠ 0`. -/
theorem not_isHilbertSchmidt_squeezeEllTwo (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (hb : b ≠ 0) :
    ¬ IsHilbertSchmidt (squeezeEllTwo a b hab).betaPart := by
  intro hHS
  have h1 := hHS ℕ ellTwoBasis
  have h2 : ∀ n, ‖(squeezeEllTwo a b hab).betaPart (ellTwoBasis n)‖ ^ 2 = b ^ 2 := fun n =>
    Bogoliubov.squeezeConj_norm_betaPart_sq _ _ _ _ _ a b hab (star_ellTwoBasis n)
      (ellTwoBasis.orthonormal.1 n)
  simp only [h2] at h1
  rw [summable_const_iff] at h1
  exact hb ((pow_eq_zero_iff two_ne_zero).1 h1)

/-- **Wrong-input control of Shale's criterion**: the squeezing of infinitely many modes is not implemented in
any Fock representation of `ℓ²(ℕ)`. -/
theorem not_implements_squeezeEllTwo {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (R : FockRep EllTwo K) (a b : ℝ) (hab : a ^ 2 - b ^ 2 = 1) (hb : b ≠ 0) :
    ¬ Implements R.toCCRRep (squeezeEllTwo a b hab) := fun hT =>
  not_isHilbertSchmidt_squeezeEllTwo a b hab hb (shale_necessity_of_implements R _ hT)

end Lightlike.OperatorAlgebras
