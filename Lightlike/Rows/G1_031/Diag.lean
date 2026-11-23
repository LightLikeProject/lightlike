import Lightlike.Rows.G1_031.Variation

/-!
# Diagonal perturbations of the conformal FLRW metric (row G1-031)

The diagonal perturbation `h = a² diag(u₀, u₁, u₂, u₃)` (`dPert a u`) of `confMetric a`, with arbitrary smooth
functions `u μ`, is the common frame of the scalar sector in the Newtonian gauge
(`u = (-2Φ, -2Ψ, -2Ψ, -2Ψ)`).  `dGD a u i j k` is the closed form of the first variation of the Christoffel
symbols `dChristoffel (confMetric a) (dPert a u) i j k` (`dChristoffel_dPert`); it is written in the atoms
`u_l`, `∂_j u_l` and `𝓗` with index-dependent constants only, so that its partial derivatives
are obtained without a case split (`hasPd_dGD`, `pd_dChristoffel_dPert`).
-/

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.Rows.G1_031

open Lightlike Lightlike.Cosmology

/-- The diagonal perturbation `h = a² diag(u₀, u₁, u₂, u₃)` of `confMetric a`. -/
def dPert (a : ℝ → ℝ) (u : Fin 4 → (Fin 4 → ℝ) → ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal fun μ => a (y 0) ^ 2 * u μ y

/-- The coefficient of `u_i 𝓗` in `δΓ^i_{jk}`. -/
def K2 (i j k : Fin 4) : ℝ := sgn i * (-cc i j k + dl i k * dl j 0 + dl i j * dl k 0)

/-- The coefficient of `u_j 𝓗` in `δΓ^i_{jk}`. -/
def K3 (i j k : Fin 4) : ℝ := -sgn i * dl j k * dl i 0

/-- The closed form of `δΓ^i_{jk}` for the diagonal perturbation `dPert a u`. -/
def dGD (a : ℝ → ℝ) (u : Fin 4 → (Fin 4 → ℝ) → ℝ) (i j k : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  K2 i j k * (u i y * Hf a y) + K3 i j k * (u j y * Hf a y) +
    (1 / 2) * sgn i * (dl i k * pd j (u i) y + dl i j * pd k (u i) y - dl j k * pd i (u j) y)

variable {a : ℝ → ℝ} {u : Fin 4 → (Fin 4 → ℝ) → ℝ} {y x : Fin 4 → ℝ}

theorem dPert_apply (z : Fin 4 → ℝ) (l k : Fin 4) :
    dPert a u z l k = if l = k then a (z 0) ^ 2 * u l z else 0 := by
  simp [dPert, Matrix.diagonal_apply]

/-- The partial derivatives of the entries of `dPert a u`. -/
theorem pd_dPert (ha : DifferentiableAt ℝ a (y 0)) (hu : ∀ i, DifferentiableAt ℝ (u i) y)
    (j l k : Fin 4) :
    pd j (fun z => dPert a u z l k) y =
      if l = k then (if j = 0 then 2 * a (y 0) * deriv a (y 0) else 0) * u l y +
        a (y 0) ^ 2 * pd j (u l) y else 0 := by
  by_cases hlk : l = k
  · subst hlk
    have hd : HasDerivAt (fun t => a t ^ 2) (2 * a (y 0) * deriv a (y 0)) (y 0) := by
      have := ha.hasDerivAt.pow 2
      convert this using 1
      simp
    have h1 := hasPd_comp0 (j := j) (x := y) (φ := fun t => a t ^ 2) hd.differentiableAt
    rw [hd.deriv] at h1
    have h2 := h1.mul (⟨hu l, rfl⟩ : HasPd j (u l) y (pd j (u l) y))
    have h3 := h2.2
    simp only [dPert_apply, ite_true]
    rw [h3]
    split_ifs <;> ring
  · simp only [dPert_apply, hlk, ite_false]
    exact pd_const _ _ _

/-- `δΓ` of the diagonal perturbation of the conformal FLRW metric is `dGD`. -/
theorem dChristoffel_dPert (ha : DifferentiableAt ℝ a (y 0)) (hpos : a (y 0) ≠ 0)
    (hu : ∀ i, DifferentiableAt ℝ (u i) y) (i j k : Fin 4) :
    dChristoffel (confMetric a) (dPert a u) i j k y = dGD a u i j k y := by
  have hd : ∀ μ, sgn μ * a (y 0) ^ 2 ≠ 0 := by
    intro μ; unfold sgn; split_ifs <;> simp [hpos]
  have hinv : (confMetric a y)⁻¹ = Matrix.diagonal (fun μ => (sgn μ * a (y 0) ^ 2)⁻¹) :=
    inv_diag' _ hd
  have hh : dPert a u y = Matrix.diagonal fun μ => a (y 0) ^ 2 * u μ y := rfl
  unfold dChristoffel
  rw [hinv, hh]
  simp only [pd_confMetric ha, pd_dPert ha hu, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Fin.sum_univ_four]
  unfold dGD K2 K3 dl Hf
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [cc, sgn] <;> field_simp <;> ring

/-- The partial derivative `∂_μ δΓ^i_{jk}` of the diagonal perturbation, in the atoms `u`, `∂u`, `∂∂u`,
`𝓗` and `∂𝓗`. -/
def dGDd (a : ℝ → ℝ) (u : Fin 4 → (Fin 4 → ℝ) → ℝ) (μ i j k : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  K2 i j k * (u i x * dH a μ x + Hf a x * pd μ (u i) x) +
    K3 i j k * (u j x * dH a μ x + Hf a x * pd μ (u j) x) +
    (1 / 2) * sgn i * (dl i k * pd μ (pd j (u i)) x + dl i j * pd μ (pd k (u i)) x -
      dl j k * pd μ (pd i (u j)) x)

/-- `δΓ^i_{jk}` of the diagonal perturbation is differentiable, with partial derivative `dGDd`. -/
theorem hasPd_dGD (hu : ∀ i, ContDiff ℝ ∞ (u i)) (ha : DifferentiableAt ℝ a (x 0))
    (ha' : DifferentiableAt ℝ (deriv a) (x 0)) (hpos : a (x 0) ≠ 0) (μ i j k : Fin 4) :
    HasPd μ (dGD a u i j k) x (dGDd a u μ i j k x) := by
  have hH := hasPd_Hf (j := μ) ha ha' hpos
  have hU : ∀ l, HasPd μ (u l) x (pd μ (u l) x) :=
    fun l => ⟨(hu l).differentiable (by simp) x, rfl⟩
  have hUj : ∀ l j, HasPd μ (fun y => pd j (u l) y) x (pd μ (fun y => pd j (u l) y) x) :=
    fun l j => ⟨((contDiff_pd (hu l) j).differentiable (by simp)) x, rfl⟩
  have := ((((HasPd.const (j := μ) (x := x) (K2 i j k)).mul ((hU i).mul hH)).add
      ((HasPd.const (j := μ) (x := x) (K3 i j k)).mul ((hU j).mul hH))).add
    ((((HasPd.const (j := μ) (x := x) ((1 / 2) * sgn i * dl i k)).mul (hUj i j)).add
      ((HasPd.const (j := μ) (x := x) ((1 / 2) * sgn i * dl i j)).mul (hUj i k))).add
      ((HasPd.const (j := μ) (x := x) (-((1 / 2) * sgn i * dl j k))).mul (hUj j i))))
  unfold dGD dGDd
  convert this using 1
  · funext y; ring
  · ring

/-- `∂_μ` of the function `y ↦ δΓ^i_{jk}(y)` for the diagonal perturbation of a global smooth `a ≠ 0`. -/
theorem pd_dChristoffel_dPert (hfa : ContDiff ℝ ∞ a) (hne : ∀ t, a t ≠ 0)
    (hu : ∀ i, ContDiff ℝ ∞ (u i)) (μ i j k : Fin 4) (x : Fin 4 → ℝ) :
    pd μ (dChristoffel (confMetric a) (dPert a u) i j k) x = dGDd a u μ i j k x := by
  have hdiff : ∀ t, DifferentiableAt ℝ a t := fun t => (hfa.differentiable (by simp)) t
  have hdiff' : ∀ t, DifferentiableAt ℝ (deriv a) t :=
    fun t => (((contDiff_infty_iff_deriv.mp hfa).2).differentiable (by simp)) t
  have : dChristoffel (confMetric a) (dPert a u) i j k = dGD a u i j k :=
    funext fun y => dChristoffel_dPert (hdiff _) (hne _)
      (fun l => (hu l).differentiable (by simp) y) i j k
  rw [this]
  exact (hasPd_dGD hu (hdiff _) (hdiff' _) (hne _) μ i j k).2

end Lightlike.Rows.G1_031
