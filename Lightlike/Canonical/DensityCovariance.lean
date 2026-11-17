import Mathlib
import Lightlike.Canonical.KineticCovariance
import Lightlike.Canonical.CurvatureCovariance

/-!
# The Hamiltonian density is a scalar density: the pointwise identity

For smooth `h`, `π` and a smooth vector field `ξ`, with `h` positive definite, the derivative of the Hamiltonian density
along `h + t ℒ_ξ h` at `t = 0`, plus its derivative along `π + t ℒ_ξ π` (the Lie derivative of a tensor density of
weight one, `lieDens`), is `Σ_k ∂_k (ξ^k ℋ)` (`hamiltonianDensity_covariance`).
-/

open Matrix Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The Lie derivative of a tensor density of weight one with upper indices,
`(ℒ_ξ π)^{ij} = ξ^k ∂_k π^{ij} − π^{kj} ∂_k ξ^i − π^{ik} ∂_k ξ^j + (∂_k ξ^k) π^{ij}`. -/
def lieDens (ξ : VectorField d) (π : TensorField d) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ k, ξ x k * Lightlike.pd k (fun y => π y i j) x -
    ∑ k, π x k j * Lightlike.pd k (fun y => ξ y i) x - ∑ k, π x i k * Lightlike.pd k (fun y => ξ y j) x +
    (∑ k, Lightlike.pd k (fun y => ξ y k) x) * π x i j

/-- The matrix of first derivatives `(∂_k h)_{ab}` of a tensor field at a point. -/
def dMat (h : TensorField d) (x : Fin d → ℝ) (k : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => Lightlike.pd k (fun y => h y a b) x

/-- The matrix `X i k = ∂_i ξ^k` of a vector field at a point. -/
def dVec (ξ : VectorField d) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i k => Lightlike.pd i (fun y => ξ y k) x

lemma lieTensor_matrix (ξ : VectorField d) (h : TensorField d) (x : Fin d → ℝ) :
    lieTensor ξ h x = (∑ k, ξ x k • dMat h x k) + dVec ξ x * h x + h x * (dVec ξ x)ᵀ := by
  ext i j
  simp only [lieTensor, lieDeriv, dMat, dVec, Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
  have e : ∑ k, h x k j * Lightlike.pd i (fun y => ξ y k) x =
      ∑ k, Lightlike.pd i (fun y => ξ y k) x * h x k j := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e]

lemma lieDens_matrix (ξ : VectorField d) (π : TensorField d) (x : Fin d → ℝ) :
    lieDens ξ π x = (∑ k, ξ x k • dMat π x k) +
      (-((dVec ξ x)ᵀ * π x) - π x * dVec ξ x + (dVec ξ x).trace • π x) := by
  ext i j
  simp only [lieDens, dMat, dVec, Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.sub_apply, Matrix.trace, Matrix.diag_apply,
    smul_eq_mul]
  have e : ∑ k, π x k j * Lightlike.pd k (fun y => ξ y i) x =
      ∑ k, Lightlike.pd k (fun y => ξ y i) x * π x k j := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [e]
  ring

lemma kineticDensity_eq_kinJ (h π : TensorField d) (x : Fin d → ℝ) :
    kineticDensity h π x = kinJ (1 / ((d : ℝ) - 1)) (h x) (π x) := rfl

/-- The `t`-derivative of the Hamiltonian density along `h + t ℒ_ξ h`, at `t = 0` and a point `x`. -/
def hamDerivH (ξ : VectorField d) (h π : TensorField d) (x : Fin d → ℝ) : ℝ :=
  dkinJ (1 / ((d : ℝ) - 1)) (h x) (π x) (lieTensor ξ h x) 0 -
    ((h x).det * ((h x)⁻¹ * lieTensor ξ h x).trace / (2 * Real.sqrt (h x).det) *
        Lightlike.scalarCurvature h x +
      Real.sqrt (h x).det * ∑ k, ξ x k * Lightlike.pd k (Lightlike.scalarCurvature h) x)

/-- The Hamiltonian density is differentiable along `h + t ℒ_ξ h`, with derivative `hamDerivH`. -/
theorem hasDerivAt_hamiltonianDensity_lie {h π : TensorField d} {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hh : SmoothTensor h) (hpos : ∀ y, (h y).PosDef) (x : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => hamiltonianDensity (fun y => h y + t • lieTensor ξ h y) π x)
      (hamDerivH ξ h π x) 0 := by
  have hH : 0 < (h x).det := (hpos x).det_pos
  have hkin : HasDerivAt (fun t : ℝ => kineticDensity (fun y => h y + t • lieTensor ξ h y) π x)
      (dkinJ (1 / ((d : ℝ) - 1)) (h x) (π x) (lieTensor ξ h x) 0) 0 := by
    have := hasDerivAt_kinJ (1 / ((d : ℝ) - 1)) (h x) (π x) (lieTensor ξ h x) 0 hH
    simpa [kineticDensity_eq_kinJ] using this
  have hs := hasDerivAt_sqrt_det (h x) (lieTensor ξ h x) hH
  have hR := hasDerivAt_scalar_lie hξ hh hpos x
  have hprod := hs.mul hR
  have := hkin.sub hprod
  unfold hamDerivH hamiltonianDensity
  refine HasDerivAt.congr_deriv this ?_
  simp only [add_zero, zero_smul]

/-- **The Hamiltonian density is a scalar density**, pointwise:
`hamDerivH + dkinJ(0, ℒ_ξ π) = Σ_k ∂_k (ξ^k ℋ)`. -/
theorem hamDerivH_add_pi {h π : TensorField d} {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hh : SmoothTensor h) (hπ : SmoothTensor π) (hpos : ∀ y, (h y).PosDef) (x : Fin d → ℝ) :
    hamDerivH ξ h π x + dkinJ (1 / ((d : ℝ) - 1)) (h x) (π x) 0 (lieDens ξ π x) =
      ∑ k, Lightlike.pd k (fun y => ξ y k * hamiltonianDensity h π y) x := by
  have hH : 0 < (h x).det := (hpos x).det_pos
  set c := 1 / ((d : ℝ) - 1) with hc
  have dK := differentiableAt_kinJ_comp hh hπ c hH
  have dS := differentiableAt_sqrt_det_comp hh hH
  have dR := differentiableAt_scalarCurvature hh hpos x
  have hu : ∀ y, hamiltonianDensity h π y = kinJ c (h y) (π y) - Real.sqrt (h y).det *
      Lightlike.scalarCurvature h y := fun y => rfl
  have hpd : ∀ k, Lightlike.pd k (fun y => ξ y k * hamiltonianDensity h π y) x =
      Lightlike.pd k (fun y => ξ y k) x * hamiltonianDensity h π x +
        ξ x k * (Lightlike.pd k (fun y => kinJ c (h y) (π y)) x -
          (Lightlike.pd k (fun y => Real.sqrt (h y).det) x * Lightlike.scalarCurvature h x +
            Real.sqrt (h x).det * Lightlike.pd k (Lightlike.scalarCurvature h) x)) := by
    intro k
    have dsR : DifferentiableAt ℝ (fun y => Real.sqrt (h y).det * Lightlike.scalarCurvature h y) x := dS.mul dR
    have hdu : DifferentiableAt ℝ (fun y => hamiltonianDensity h π y) x := by
      simp only [hu]
      exact dK.sub dsR
    rw [Lightlike.pd_mul (diff_of_smooth (hξ k) x) hdu]
    congr 1
    congr 1
    simp only [hu]
    rw [Lightlike.pd_sub (f₁ := fun y => kinJ c (h y) (π y))
        (f₂ := fun y => Real.sqrt (h y).det * Lightlike.scalarCurvature h y) dK dsR,
      Lightlike.pd_mul (f₁ := fun y => Real.sqrt (h y).det) (f₂ := fun y => Lightlike.scalarCurvature h y) dS dR]
  have hK : ∀ k, Lightlike.pd k (fun y => kinJ c (h y) (π y)) x = dkinJ c (h x) (π x) (dMat h x k) (dMat π x k) :=
    fun k => pd_kinJ hh hπ c hH k
  have hS : ∀ k, Lightlike.pd k (fun y => Real.sqrt (h y).det) x =
      (h x).det * ((h x)⁻¹ * dMat h x k).trace / (2 * Real.sqrt (h x).det) := fun k => pd_sqrt_det hh hH k
  have hτ : (dVec ξ x).trace = ∑ k, Lightlike.pd k (fun y => ξ y k) x := by simp [Matrix.trace, dVec]
  have hlie := dkinJ_lie c (h x) (π x) (dVec ξ x) (dMat h x) (dMat π x) (ξ x) hH
  have hsq := sqrt_det_lie (h x) (dVec ξ x) (dMat h x) (ξ x) hH
  unfold hamDerivH
  rw [← hc]
  rw [lieTensor_matrix, lieDens_matrix]
  simp only [hpd, hK, hS, Finset.sum_add_distrib]
  rw [hsq]
  have hu0 : hamiltonianDensity h π x = kinJ c (h x) (π x) - Real.sqrt (h x).det * Lightlike.scalarCurvature h x := rfl
  rw [hu0]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_add, ← Finset.sum_mul, ← Finset.mul_sum, ← hτ]
  have h1 : ∑ k, ξ x k * ((h x).det * ((h x)⁻¹ * dMat h x k).trace / (2 * Real.sqrt (h x).det)) *
      Lightlike.scalarCurvature h x = (∑ k, ξ x k * ((h x).det * ((h x)⁻¹ * dMat h x k).trace /
      (2 * Real.sqrt (h x).det))) * Lightlike.scalarCurvature h x := by rw [Finset.sum_mul]
  have h2 : ∑ k, ξ x k * Real.sqrt (h x).det * Lightlike.pd k (Lightlike.scalarCurvature h) x =
      Real.sqrt (h x).det * ∑ k, ξ x k * Lightlike.pd k (Lightlike.scalarCurvature h) x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  simp only [mul_assoc] at h1 h2 ⊢
  linear_combination hlie + h1 + h2

end Lightlike.Canonical

end
