import Mathlib
import Lightlike.Canonical.HamiltonianHH
import Lightlike.Canonical.DensityDeriv

/-!
# The derivative of the unit `π`-gradient of the Hamiltonian constraint

`P = (2 hπh − (2/(d−1)) tr(hπ) h)/√det h` is a smooth function of `(h, π)`. Its partial derivative is the
product rule applied to the three factors; the derivative of `√det h` is `pd_sqrt_det`.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The matrix of partial derivatives `∂_a F_ij` of a matrix field at a point. -/
def dM (a : Fin d) (F : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => Lightlike.pd a (fun y => F y i j) x

/-- Product rule for matrix fields, entrywise. -/
lemma pd_matmul {F G : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {x : Fin d → ℝ}
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x) (hG : ∀ i j, DifferentiableAt ℝ (fun y => G y i j) x)
    (a i j : Fin d) :
    Lightlike.pd a (fun y => (F y * G y) i j) x = (dM a F x * G x + F x * dM a G x) i j := by
  simp only [Matrix.mul_apply]
  rw [Lightlike.pd_sum Finset.univ (f := fun k y => F y i k * G y k j) (fun k _ => (hF i k).mul (hG k j)) a]
  simp only [Matrix.add_apply, Matrix.mul_apply, dM, Matrix.of_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => Lightlike.pd_mul (hF i k) (hG k j) a

/-- The partial derivative of the trace of a matrix field. -/
lemma pd_trace {F : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} {x : Fin d → ℝ}
    (hF : ∀ i j, DifferentiableAt ℝ (fun y => F y i j) x) (a : Fin d) :
    Lightlike.pd a (fun y => (F y).trace) x = (dM a F x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Lightlike.pd_sum Finset.univ (f := fun k y => F y k k) (fun k _ => hF k k) a]
  rfl

/-- The derivative of the inverse of a scalar field. -/
lemma pd_inv_scalar {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hf : DifferentiableAt ℝ f x) (h0 : f x ≠ 0)
    (a : Fin d) : Lightlike.pd a (fun y => (f y)⁻¹) x = -(Lightlike.pd a f x) / (f x) ^ 2 := by
  have hi : DifferentiableAt ℝ (fun y => (f y)⁻¹) x := hf.inv h0
  have h1 := Lightlike.pd_mul hf hi a
  have e : (fun y => f y * (f y)⁻¹) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    have : ∀ᶠ y in nhds x, f y ≠ 0 := hf.continuousAt.eventually_ne h0
    filter_upwards [this] with y hy using mul_inv_cancel₀ hy
  rw [Lightlike.pd_congr e, Lightlike.pd_const] at h1
  field_simp
  field_simp at h1
  linarith

/-- The matrix field `X = 2 hπh − c tr(hπ) h`. -/
def Xfield (c : ℝ) (h π : TensorField d) (y : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (2 : ℝ) • (h y * π y * h y) - (c * (h y * π y).trace) • h y

/-- **The derivative of the unit `π`-gradient**, entrywise, before the identification of the matrix
products: `∂_a (X_ij/√det h) = −(∂_a √det h) X_ij/det h + ∂_a X_ij/√det h`. -/
lemma pd_Pf {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π) (c : ℝ) {x : Fin d → ℝ}
    (hpos : 0 < (h x).det) (a i j : Fin d) :
    Lightlike.pd a (fun y => (Real.sqrt (h y).det)⁻¹ * Xfield c h π y i j) x =
      (-(Lightlike.pd a (fun y => Real.sqrt (h y).det) x) / (Real.sqrt (h x).det) ^ 2) * Xfield c h π x i j +
        (Real.sqrt (h x).det)⁻¹ * (2 * (dM a h x * π x * h x + h x * dM a π x * h x + h x * π x * dM a h x) i j -
          c * ((dM a h x * π x + h x * dM a π x).trace * h x i j + (h x * π x).trace * dM a h x i j)) := by
  have dH : ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x := fun i j => diff_of_smooth (hh i j) x
  have dP : ∀ i j, DifferentiableAt ℝ (fun y => π y i j) x := fun i j => diff_of_smooth (hπ i j) x
  have dHP : ∀ i j, DifferentiableAt ℝ (fun y => (h y * π y) i j) x := dm_mul dH dP
  have dHPH : ∀ i j, DifferentiableAt ℝ (fun y => (h y * π y * h y) i j) x := dm_mul dHP dH
  have dtr : DifferentiableAt ℝ (fun y => (h y * π y).trace) x := dm_trace dHP
  have dsd : DifferentiableAt ℝ (fun y => Real.sqrt (h y).det) x := differentiableAt_sqrt_det_comp hh hpos
  have hne : Real.sqrt (h x).det ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have e : (fun y => Xfield c h π y i j) = fun y => 2 * (h y * π y * h y) i j -
      (c * (h y * π y).trace) * h y i j := by
    funext y; simp [Xfield, Matrix.sub_apply]
  have dX : DifferentiableAt ℝ (fun y => Xfield c h π y i j) x := by
    rw [e]; exact ((dHPH i j).const_mul 2).sub ((dtr.const_mul c).mul (dH i j))
  have e1 : dM a (fun y => h y * π y) x = dM a h x * π x + h x * dM a π x := by
    ext k l; exact pd_matmul dH dP a k l
  have hX : Lightlike.pd a (fun y => Xfield c h π y i j) x =
      2 * (dM a h x * π x * h x + h x * dM a π x * h x + h x * π x * dM a h x) i j -
        c * ((dM a h x * π x + h x * dM a π x).trace * h x i j + (h x * π x).trace * dM a h x i j) := by
    have s1 := Lightlike.pd_sub (f₁ := fun y => 2 * (h y * π y * h y) i j)
      (f₂ := fun y => c * (h y * π y).trace * h y i j) ((dHPH i j).const_mul 2)
      ((dtr.const_mul c).mul (dH i j)) a
    have s2 := Lightlike.pd_mul (f₁ := fun y => c * (h y * π y).trace) (f₂ := fun y => h y i j)
      (dtr.const_mul c) (dH i j) a
    have s3 := Lightlike.pd_const_mul 2 (dHPH i j) a
    have s4 := Lightlike.pd_const_mul c dtr a
    rw [e, s1, s2, s3, s4, pd_trace dHP a, e1]
    have e2 : Lightlike.pd a (fun y => (h y * π y * h y) i j) x =
        ((dM a h x * π x + h x * dM a π x) * h x + h x * π x * dM a h x) i j := by
      have := pd_matmul dHP dH a i j
      rw [this, e1]
    rw [e2]
    simp only [Matrix.add_mul, Matrix.add_apply, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc]
    have e3 : Lightlike.pd a (fun y => h y i j) x = dM a h x i j := rfl
    rw [e3]
    ring
  have s5 := Lightlike.pd_mul (f₁ := fun y => (Real.sqrt (h y).det)⁻¹) (f₂ := fun y => Xfield c h π y i j)
    (dsd.inv hne) dX a
  rw [s5, pd_inv_scalar dsd hne a, hX]

end Lightlike.Canonical

end
