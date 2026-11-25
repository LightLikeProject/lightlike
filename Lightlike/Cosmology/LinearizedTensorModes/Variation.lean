import Lightlike.Cosmology.LinearizedTensorModes.Background

/-!
# The first variation of the Christoffel symbols of the conformal FLRW metric (row G1-031)

The tensor perturbation (plus polarisation) of `confMetric a` is `h = a² diag(0, f, -f, 0)`, i.e.
`tPert a f`; the perturbed metric `confMetric a + ε h` is `a² diag(-1, 1 + εf, 1 - εf, 1)`.
`dG a f i j k` is the closed form of `dChristoffel (confMetric a) (tPert a f) i j k`, written in the atoms
`𝓗 f` and the partial derivatives of `f` with index-dependent integer coefficients only, so that its partial
derivatives are obtained without a case split (`hasPd_dG`).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Cosmology.LinearizedTensorModes

open Lightlike Lightlike.Cosmology

/-- The polarisation tensor `diag(0, 1, -1, 0)` of the plus mode. -/
def cp (μ : Fin 4) : ℝ := if μ = 1 then 1 else if μ = 2 then -1 else 0

/-- The tensor perturbation `h = a² diag(0, f, -f, 0)` of `confMetric a`. -/
def tPert (a : ℝ → ℝ) (f : (Fin 4 → ℝ) → ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal fun μ => a (y 0) ^ 2 * (cp μ * f y)

/-- The Kronecker delta as a real number. -/
def dl (i j : Fin 4) : ℝ := if i = j then 1 else 0

/-- The coefficient of `𝓗 f` in `δΓ^i_{jk}`. -/
def K1 (i j k : Fin 4) : ℝ :=
  -cp i * (sgn i * dl i k * dl j 0 + sgn i * dl i j * dl k 0 - sgn j * dl j k * dl i 0) +
    sgn i * (dl i k * dl j 0 * cp i + dl i j * dl k 0 * cp i - dl j k * dl i 0 * cp j)

/-- The closed form of `δΓ^i_{jk}` for the tensor perturbation. -/
def dG (a : ℝ → ℝ) (f : (Fin 4 → ℝ) → ℝ) (i j k : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  K1 i j k * (Hf a y * f y) +
    (1 / 2) * sgn i * cp i * (dl i k * pd j f y + dl i j * pd k f y) -
      (1 / 2) * sgn i * cp j * dl j k * pd i f y

variable {a : ℝ → ℝ} {f : (Fin 4 → ℝ) → ℝ} {y x : Fin 4 → ℝ}

theorem tPert_apply (z : Fin 4 → ℝ) (l k : Fin 4) :
    tPert a f z l k = if l = k then a (z 0) ^ 2 * (cp l * f z) else 0 := by
  simp [tPert, Matrix.diagonal_apply]

/-- The partial derivatives of the entries of `tPert a f`. -/
theorem pd_tPert (ha : DifferentiableAt ℝ a (y 0)) (hf : DifferentiableAt ℝ f y) (j l k : Fin 4) :
    pd j (fun z => tPert a f z l k) y =
      if l = k then cp l * ((if j = 0 then 2 * a (y 0) * deriv a (y 0) else 0) * f y +
        a (y 0) ^ 2 * pd j f y) else 0 := by
  by_cases hlk : l = k
  · subst hlk
    have hd : HasDerivAt (fun t => a t ^ 2) (2 * a (y 0) * deriv a (y 0)) (y 0) := by
      have := ha.hasDerivAt.pow 2
      convert this using 1
      simp
    have h1 := hasPd_comp0 (j := j) (x := y) (φ := fun t => a t ^ 2) hd.differentiableAt
    rw [hd.deriv] at h1
    have h2 := h1.mul ((HasPd.const (j := j) (x := y) (cp l)).mul (⟨hf, rfl⟩ : HasPd j f y (pd j f y)))
    have h3 := h2.2
    simp only [tPert_apply, ite_true]
    rw [h3]
    split_ifs <;> simp <;> ring
  · simp only [tPert_apply, hlk, ite_false]
    exact pd_const _ _ _

/-- `δΓ` of the tensor perturbation of the conformal FLRW metric is `dG`. -/
theorem dChristoffel_tPert (ha : DifferentiableAt ℝ a (y 0)) (hpos : a (y 0) ≠ 0)
    (hf : DifferentiableAt ℝ f y) (i j k : Fin 4) :
    dChristoffel (confMetric a) (tPert a f) i j k y = dG a f i j k y := by
  have hd : ∀ μ, sgn μ * a (y 0) ^ 2 ≠ 0 := by
    intro μ; unfold sgn; split_ifs <;> simp [hpos]
  have hinv : (confMetric a y)⁻¹ = Matrix.diagonal (fun μ => (sgn μ * a (y 0) ^ 2)⁻¹) :=
    inv_diag' _ hd
  have hh : tPert a f y = Matrix.diagonal fun μ => a (y 0) ^ 2 * (cp μ * f y) := rfl
  unfold dChristoffel
  rw [hinv, hh]
  simp only [pd_confMetric ha, pd_tPert ha hf, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Fin.sum_univ_four]
  unfold dG K1 dl Hf
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [cp, sgn] <;> field_simp <;> ring

/-- The partial derivative `∂_μ δΓ^i_{jk}` of the tensor perturbation, in the atoms `f`, `∂f`, `∂∂f`,
`𝓗` and `∂𝓗`. -/
def dGd (a : ℝ → ℝ) (f : (Fin 4 → ℝ) → ℝ) (μ i j k : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  K1 i j k * (dH a μ x * f x + Hf a x * pd μ f x) +
    (1 / 2) * sgn i * cp i * (dl i k * pd μ (pd j f) x + dl i j * pd μ (pd k f) x) -
      (1 / 2) * sgn i * cp j * dl j k * pd μ (pd i f) x

/-- `δΓ^i_{jk}` of the tensor perturbation is differentiable, with partial derivative `dGd`. -/
theorem hasPd_dG (hf : ContDiff ℝ ∞ f) (ha : DifferentiableAt ℝ a (x 0))
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (hpos : a (x 0) ≠ 0) (μ i j k : Fin 4) :
    HasPd μ (dG a f i j k) x (dGd a f μ i j k x) := by
  have hH := hasPd_Hf (j := μ) ha ha' hpos
  have hF : HasPd μ f x (pd μ f x) := ⟨hf.differentiable (by simp) x, rfl⟩
  have hFj : ∀ j, HasPd μ (fun y => pd j f y) x (pd μ (fun y => pd j f y) x) :=
    fun j => ⟨((contDiff_pd hf j).differentiable (by simp)) x, rfl⟩
  have := ((HasPd.const (j := μ) (x := x) (K1 i j k)).mul (hH.mul hF)).add
    ((((HasPd.const (j := μ) (x := x) ((1 / 2) * sgn i * cp i)).mul
      (((HasPd.const (j := μ) (x := x) (dl i k)).mul (hFj j)).add
        ((HasPd.const (j := μ) (x := x) (dl i j)).mul (hFj k)))).add
      ((HasPd.const (j := μ) (x := x) (-((1 / 2) * sgn i * cp j * dl j k))).mul (hFj i))))
  unfold dG dGd
  convert this using 1
  · funext y; ring
  · ring

/-- `∂_μ` of the function `y ↦ δΓ^i_{jk}(y)` for the tensor perturbation of a global smooth `a ≠ 0`. -/
theorem pd_dChristoffel_tPert (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0) (hf : ContDiff ℝ ∞ f)
    (μ i j k : Fin 4) (x : Fin 4 → ℝ) :
    pd μ (dChristoffel (confMetric a) (tPert a f) i j k) x = dGd a f μ i j k x := by
  have hdiff : ∀ t, DifferentiableAt ℝ a t := fun t => (hfa.differentiable (by simp)) t
  have hdiff' : ∀ t, DifferentiableAt ℝ (deriv a) t :=
    fun t => (((contDiff_infty_iff_deriv.mp hfa).2).differentiable (by simp)) t
  have : dChristoffel (confMetric a) (tPert a f) i j k = dG a f i j k :=
    funext fun y => dChristoffel_tPert (hdiff _) (hne _) (hf.differentiable (by simp) y) i j k
  rw [this]
  exact (hasPd_dG hf (hdiff _) (hdiff' _) (hne _) μ i j k).2

end Lightlike.Cosmology.LinearizedTensorModes

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.K1 := _root_.Lightlike.Cosmology.LinearizedTensorModes.K1
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.cp := _root_.Lightlike.Cosmology.LinearizedTensorModes.cp
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.dChristoffel_tPert := _root_.Lightlike.Cosmology.LinearizedTensorModes.dChristoffel_tPert
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.dG := _root_.Lightlike.Cosmology.LinearizedTensorModes.dG
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.dGd := _root_.Lightlike.Cosmology.LinearizedTensorModes.dGd
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.dl := _root_.Lightlike.Cosmology.LinearizedTensorModes.dl
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.hasPd_dG := _root_.Lightlike.Cosmology.LinearizedTensorModes.hasPd_dG
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.pd_dChristoffel_tPert := _root_.Lightlike.Cosmology.LinearizedTensorModes.pd_dChristoffel_tPert
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.pd_tPert := _root_.Lightlike.Cosmology.LinearizedTensorModes.pd_tPert
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.tPert := _root_.Lightlike.Cosmology.LinearizedTensorModes.tPert
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_031.tPert_apply := _root_.Lightlike.Cosmology.LinearizedTensorModes.tPert_apply
