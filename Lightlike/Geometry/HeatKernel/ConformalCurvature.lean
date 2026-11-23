import Mathlib
import Lightlike.Spacetime.Curvature

/-!
# Curvature of a conformally flat coordinate metric `f · δ`

Ties the scalar-curvature input `R` of the heat-kernel coefficients to Lightlike's coordinate
curvature `Lightlike.scalarCurvature`: for the coordinate metric `g = f · 1` we compute the Christoffel
symbols in closed form (`christoffel_conf`) and their derivative at a critical point of `f`
(`pd_christoffel_conf`).
-/

open Lightlike Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike.HeatKernel

variable {n : ℕ}

/-- The conformally flat coordinate metric `g y = f y • 1`. -/
def confMetric (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
  fun y => f y • (1 : Matrix (Fin n) (Fin n) ℝ)

lemma confMetric_apply (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) (l k : Fin n) :
    confMetric f y l k = if l = k then f y else 0 := by
  simp [confMetric, Matrix.one_apply]

lemma pd_confMetric (f : (Fin n → ℝ) → ℝ) (j l k : Fin n) (x : Fin n → ℝ) :
    pd j (fun y => confMetric f y l k) x = if l = k then pd j f x else 0 := by
  by_cases h : l = k
  · simp [confMetric_apply, h, pd]
  · simp [confMetric_apply, h, pd_const]

lemma confMetric_inv (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hx : f x ≠ 0) :
    (confMetric f x)⁻¹ = (f x)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  apply Matrix.inv_eq_right_inv
  simp [confMetric, smul_smul, hx]

/-- Closed form of the Christoffel symbols of `f · δ`. -/
lemma christoffel_conf (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hx : f x ≠ 0) (i j k : Fin n) :
    christoffel (confMetric f) i j k x = (1 / (2 * f x)) *
      ((if i = k then pd j f x else 0) + (if i = j then pd k f x else 0) -
        (if j = k then pd i f x else 0)) := by
  unfold christoffel
  rw [confMetric_inv f x hx]
  simp only [pd_confMetric, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp [mul_ite, Finset.sum_ite_eq]
  by_cases h1 : i = k <;> by_cases h2 : i = j <;> by_cases h3 : j = k <;> simp [h1, h2, h3] <;>
    field_simp

lemma pd_ite (c : Prop) [Decidable c] (F : (Fin n → ℝ) → ℝ) (μ : Fin n) (x : Fin n → ℝ) :
    pd μ (fun y => if c then F y else 0) x = if c then pd μ F x else 0 := by
  by_cases h : c
  · simp [h, pd]
  · simp [h, pd_const]

lemma diff_ite (c : Prop) [Decidable c] (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (fun y => if c then F y else 0) x := by
  by_cases h : c <;> simp [h, hF]

lemma pd_add {A B : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    pd μ (fun y => A y + B y) x = pd μ A x + pd μ B x := by
  unfold pd
  rw [fderiv_fun_add hA hB]
  rfl

lemma pd_sub {A B : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    pd μ (fun y => A y - B y) x = pd μ A x - pd μ B x := by
  unfold pd
  rw [fderiv_fun_sub hA hB]
  rfl

lemma pd_mul {A B : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (μ : Fin n)
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x) :
    pd μ (fun y => A y * B y) x = A x * pd μ B x + B x * pd μ A x := by
  unfold pd
  rw [fderiv_fun_mul hA hB]
  simp

lemma contDiff_pd {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (a : Fin n) :
    ContDiff ℝ ∞ (pd a f) := by
  unfold pd
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- Derivative of the Christoffel symbols of `f · δ` at a critical point of `f`. -/
lemma pd_christoffel_conf {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hpos : ∀ y, f y ≠ 0)
    (x : Fin n → ℝ) (hgrad : ∀ a, pd a f x = 0) (μ ρ ν σ : Fin n) :
    pd μ (christoffel (confMetric f) ρ ν σ) x = (1 / (2 * f x)) *
      ((if ρ = σ then pd μ (pd ν f) x else 0) + (if ρ = ν then pd μ (pd σ f) x else 0) -
        (if ν = σ then pd μ (pd ρ f) x else 0)) := by
  have hfun : christoffel (confMetric f) ρ ν σ = fun y => (1 / (2 * f y)) *
      ((if ρ = σ then pd ν f y else 0) + (if ρ = ν then pd σ f y else 0) -
        (if ν = σ then pd ρ f y else 0)) :=
    funext fun y => christoffel_conf f y (hpos y) ρ ν σ
  have hd : ∀ a, DifferentiableAt ℝ (pd a f) x := fun a =>
    ((contDiff_pd hf a).differentiable (by simp)).differentiableAt
  have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)).differentiableAt
  have hu : DifferentiableAt ℝ (fun y => 1 / (2 * f y)) x :=
    by
    have : (fun y => 1 / (2 * f y)) = Inv.inv ∘ (fun y => 2 * f y) := by
      funext y; simp
    rw [this]
    exact (differentiableAt_inv (mul_ne_zero two_ne_zero (hpos x))).comp x (hfd.const_mul 2)
  have h1 := diff_ite (ρ = σ) _ x (hd ν)
  have h2 := diff_ite (ρ = ν) _ x (hd σ)
  have h3 := diff_ite (ν = σ) _ x (hd ρ)
  have hh0 : ((if ρ = σ then pd ν f x else 0) + (if ρ = ν then pd σ f x else 0) -
      (if ν = σ then pd ρ f x else 0)) = 0 := by
    simp [hgrad]
  have h12 : DifferentiableAt ℝ (fun y => (if ρ = σ then pd ν f y else 0) +
      (if ρ = ν then pd σ f y else 0)) x := h1.add h2
  have h123 : DifferentiableAt ℝ (fun y => (if ρ = σ then pd ν f y else 0) +
      (if ρ = ν then pd σ f y else 0) - (if ν = σ then pd ρ f y else 0)) x := h12.sub h3
  rw [hfun, pd_mul μ hu h123, pd_sub μ h12 h3, pd_add μ h1 h2,
    pd_ite, pd_ite, pd_ite, hh0]
  ring

/-- Riemann tensor of `f · δ` at a critical point of `f` with Hessian `c · δ`. -/
lemma riemann_conf {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hpos : ∀ y, f y ≠ 0)
    (x : Fin n → ℝ) (hgrad : ∀ a, pd a f x = 0) (c : ℝ)
    (hess : ∀ a b, pd a (pd b f) x = if a = b then c else 0) (ρ σ μ ν : Fin n) :
    riemann (confMetric f) ρ σ μ ν x = (1 / (2 * f x)) *
      (((if ρ = σ then (if μ = ν then c else 0) else 0) +
        (if ρ = ν then (if μ = σ then c else 0) else 0) -
        (if ν = σ then (if μ = ρ then c else 0) else 0)) -
       ((if ρ = σ then (if ν = μ then c else 0) else 0) +
        (if ρ = μ then (if ν = σ then c else 0) else 0) -
        (if μ = σ then (if ν = ρ then c else 0) else 0))) := by
  unfold riemann
  rw [pd_christoffel_conf hf hpos x hgrad, pd_christoffel_conf hf hpos x hgrad]
  have hΓ : ∀ i j k, christoffel (confMetric f) i j k x = 0 := by
    intro i j k
    rw [christoffel_conf f x (hpos x)]
    simp [hgrad]
  simp only [hΓ, hess, mul_zero, sub_self, Finset.sum_const_zero, add_zero]
  ring

lemma ite_aux (c : ℝ) (ρ σ ν : Fin n) :
    (((if ρ = σ then (if ρ = ν then c else 0) else 0) +
        (if ρ = ν then (if ρ = σ then c else 0) else 0) -
        (if ν = σ then (if ρ = ρ then c else 0) else 0)) -
       ((if ρ = σ then (if ν = ρ then c else 0) else 0) +
        (if ρ = ρ then (if ν = σ then c else 0) else 0) -
        (if ρ = σ then (if ν = ρ then c else 0) else 0))) =
      2 * (if ρ = σ then (if σ = ν then c else 0) else 0) - 2 * (if ν = σ then c else 0) := by
  by_cases h1 : ρ = σ
  · subst h1
    by_cases h2 : ρ = ν
    · subst h2; simp
    · have h3 : ν ≠ ρ := fun h => h2 h.symm
      simp [h2, h3]
  · by_cases h2 : ρ = ν
    · subst h2
      simp [h1]
    · by_cases h3 : ν = σ
      · simp [h1, h2, h3]; ring
      · simp [h1, h2, h3]

/-- Ricci tensor of `f · δ` at a critical point of `f` with Hessian `c · δ`. -/
lemma ricci_conf {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hpos : ∀ y, f y ≠ 0)
    (x : Fin n → ℝ) (hgrad : ∀ a, pd a f x = 0) (c : ℝ)
    (hess : ∀ a b, pd a (pd b f) x = if a = b then c else 0) (σ ν : Fin n) :
    ricci (confMetric f) σ ν x = (c / f x) * (1 - n) * (if σ = ν then 1 else 0) := by
  unfold ricci
  have key : ∀ ρ, riemann (confMetric f) ρ σ ρ ν x = (1 / (2 * f x)) *
      (2 * (if ρ = σ then (if σ = ν then c else 0) else 0) - 2 * (if ν = σ then c else 0)) :=
    fun ρ => by rw [riemann_conf hf hpos x hgrad c hess, ite_aux]
  simp only [key]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hx := hpos x
  by_cases h : σ = ν
  · subst h; simp; field_simp
  · have h' : ν ≠ σ := fun h2 => h h2.symm
    simp [h, h']

/-- **Scalar curvature of `f · δ`** at a critical point `x` of `f` with Hessian `c · δ`:
`R(x) = c · n (1 − n) / f(x)²`. -/
theorem scalarCurvature_conf {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hpos : ∀ y, f y ≠ 0)
    (x : Fin n → ℝ) (hgrad : ∀ a, pd a f x = 0) (c : ℝ)
    (hess : ∀ a b, pd a (pd b f) x = if a = b then c else 0) :
    scalarCurvature (confMetric f) x = c * n * (1 - n) / f x ^ 2 := by
  unfold scalarCurvature
  rw [confMetric_inv f x (hpos x)]
  have hx := hpos x
  simp only [ricci_conf hf hpos x hgrad c hess, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp [Finset.sum_ite_eq]
  field_simp

end Lightlike.HeatKernel
