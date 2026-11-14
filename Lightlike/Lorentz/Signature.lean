module

public import Lightlike.Lorentz.KernelBound
public import Lightlike.Spacetime.Minkowski
public import Physlib.Relativity.SL2C.Basic

/-!
# The signature bridge: Physlib's Lorentz matrices in the project's convention

Physlib's double cover `Lorentz.SL2C.toLorentzGroup : SL(2,ℂ) →* LorentzGroup 3` produces
matrices indexed by `Fin 1 ⊕ Fin 3` that preserve Physlib's Minkowski matrix `diag(+1,-1,-1,-1)`.
The project's spacetime convention is coordinates `Fin 4 → ℝ`, index `0` = time, signature
`(−,+,+,+)` (`Lightlike.eta`, `Lightlike.minkowskiForm`). This file transports Physlib's matrices to that
convention and connects them with the kernel of the EPRL vertex amplitude.

Main results
* `lorentzMat g` : the vector-representation matrix of `g ∈ SL(2,ℂ)` on `Fin 4 → ℝ`, obtained by
  reindexing Physlib's `toLorentzGroup g` along `Fin 1 ⊕ Fin 3 ≃ Fin 4`; it is multiplicative
  (`lorentzMat_mul`, `lorentzMat_one`).
* `reindex_minkowskiMatrix` : the reindexed Physlib Minkowski matrix is `-η` (the signature flip).
* `lorentzMat_transpose_mul_eta_mul_self` : `Λᵀ η Λ = η` for the project's `η`, i.e. `lorentzMat g`
  is a Lorentz transformation in the project's convention.
* `coshDist_eq_lorentzMat` : the quantity `coshDist g = ½ Σ |g_ij|²` used throughout the
  Plancherel and EPRL files is the time-time entry `Λ(g)₀₀`.
* `normal_minkowskiForm_self`, `one_le_normal_zero` : the normal `N = Λ(g) e₀` is a future unit
  timelike vector, `η(N,N) = -1` and `N⁰ ≥ 1`, i.e. a point of hyperbolic 3-space.
* `coshDist_inv_mul` : `coshDist (A⁻¹ B) = -η(Λ(A) e₀, Λ(B) e₀)`. In the EPRL vertex amplitude the
  link coefficient for `(a,b)` depends on the gauge variables through `(g_a)⁻¹ g_b`; this theorem
  says it depends only on the hyperbolic distance between the normals `N_a = Λ(g_a) e₀` and
  `N_b`, which is the form of the integrand in Engle–Pereira (2009), Sec. 4, and in Barrett–Crane
  (2000), where `cosh r_ab = −η(N_a, N_b)` in the mostly-plus signature.

**References.** J. Engle, R. Pereira, *Regularization and finiteness of the Lorentzian loop
quantum gravity vertices*, Phys. Rev. D **79** (2009) 084034, arXiv:0805.4696, Sec. 4;
J. W. Barrett, L. Crane, *A Lorentzian signature model for quantum general relativity*,
Class. Quantum Grav. **17** (2000) 3101, arXiv:gr-qc/9904025; Physlib,
`Physlib/Relativity/SL2C/Basic.lean`.
-/

@[expose] public section

open Matrix

noncomputable section

namespace Lightlike.Lorentz

/-- The vector-representation matrix of `g ∈ SL(2,ℂ)` in the project's coordinates `Fin 4 → ℝ`
(index `0` = time): Physlib's `toLorentzGroup g`, reindexed along `Fin 1 ⊕ Fin 3 ≃ Fin 4`. -/
def lorentzMat (g : SL2C) : Matrix (Fin 4) (Fin 4) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv (Lorentz.SL2C.toLorentzGroup g).1

/-- Reindexing commutes with matrix multiplication. -/
lemma reindex_fin_mul (M N : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :
    (reindex finSumFinEquiv finSumFinEquiv (M * N) : Matrix (Fin 4) (Fin 4) ℝ) =
      reindex finSumFinEquiv finSumFinEquiv M * reindex finSumFinEquiv finSumFinEquiv N := by
  simp only [reindex_apply, submatrix_mul_equiv]

/-- `lorentzMat` is multiplicative. -/
lemma lorentzMat_mul (g h : SL2C) : lorentzMat (g * h) = lorentzMat g * lorentzMat h := by
  simp only [lorentzMat, map_mul, lorentzGroupIsGroup_mul_coe, reindex_fin_mul]

/-- `lorentzMat 1 = 1`. -/
lemma lorentzMat_one : lorentzMat 1 = 1 := by
  simp only [lorentzMat, map_one, lorentzGroupIsGroup_one_coe, reindex_apply,
    submatrix_one_equiv]

/-- **The signature flip.** Physlib's Minkowski matrix `diag(+1,-1,-1,-1)` on `Fin 1 ⊕ Fin 3`,
reindexed to `Fin 4`, is minus the project's `η = diag(-1,+1,+1,+1)`. -/
theorem reindex_minkowskiMatrix :
    (reindex finSumFinEquiv finSumFinEquiv (minkowskiMatrix : Matrix (Fin 1 ⊕ Fin 3) _ ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) = -eta 4 := by
  rw [minkowskiMatrix.as_diagonal, reindex_apply, submatrix_diagonal_equiv, eta,
    diagonal_neg]
  congr 1
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have h := finSumFinEquiv_symm_apply_castAdd (m := 1) (n := 3) i
    rw [Function.comp_apply]
    erw [h]
    simp [etaDiag]
  · have h := finSumFinEquiv_symm_apply_natAdd (m := 1) (n := 3) i
    rw [Function.comp_apply]
    erw [h]
    simp [etaDiag]

/-- **`lorentzMat g` is a Lorentz transformation in the project's signature:** `Λᵀ η Λ = η`. -/
theorem lorentzMat_transpose_mul_eta_mul_self (g : SL2C) :
    (lorentzMat g)ᵀ * eta 4 * lorentzMat g = eta 4 := by
  have h := congrArg (fun M : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ =>
      (reindex finSumFinEquiv finSumFinEquiv M : Matrix (Fin 4) (Fin 4) ℝ))
    (LorentzGroup.transpose_mul_minkowskiMatrix_mul_self (Λ := Lorentz.SL2C.toLorentzGroup g))
  simp only [reindex_fin_mul, reindex_minkowskiMatrix] at h
  simpa [lorentzMat, Matrix.mul_neg, Matrix.neg_mul] using h

/-- **The radial variable is the time-time entry.** `coshDist g = ½ Σ |g_ij|²`, the argument of
every kernel and spherical function in the Plancherel and EPRL files, equals `Λ(g)₀₀`. -/
theorem coshDist_eq_lorentzMat (g : SL2C) : coshDist g = lorentzMat g 0 0 := by
  have h0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 1 ⊕ Fin 3) = Sum.inl 0 :=
    finSumFinEquiv_symm_apply_castAdd 0
  rw [lorentzMat, reindex_apply, submatrix_apply, h0, Lorentz.SL2C.toLorentzGroup_inl_inl]
  rfl

/-- The time unit vector `e₀` of `Fin 4 → ℝ`. -/
def timeVec : Fin 4 → ℝ := Pi.single 0 1

/-- The unit normal `Λ(g) e₀` attached to `g`: the image of the origin of hyperbolic 3-space. -/
def normal (g : SL2C) : Fin 4 → ℝ := lorentzMat g *ᵥ timeVec

/-- The Minkowski form as `v ⬝ (η w)`. -/
lemma minkowskiForm_eq_dotProduct {n : ℕ} (v w : Fin n → ℝ) :
    minkowskiForm n v w = v ⬝ᵥ (eta n *ᵥ w) := by
  simp only [minkowskiForm_apply, dotProduct, eta, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `η(Λ e₀, Λ' e₀) = (Λᵀ η Λ')₀₀`. -/
lemma minkowskiForm_mulVec_timeVec (M N : Matrix (Fin 4) (Fin 4) ℝ) :
    minkowskiForm 4 (M *ᵥ timeVec) (N *ᵥ timeVec) = (Mᵀ * eta 4 * N) 0 0 := by
  rw [minkowskiForm_eq_dotProduct, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, timeVec, single_dotProduct, mulVec_single_one, one_mul]
  rfl

/-- `η(e₀, e₀) = -1` read off the matrix: `η₀₀ = -1`. -/
lemma eta_zero_zero : eta 4 0 0 = -1 := by simp [eta, etaDiag]

/-- **The normal is a unit timelike vector:** `η(N, N) = -1`. -/
theorem normal_minkowskiForm_self (g : SL2C) : minkowskiForm 4 (normal g) (normal g) = -1 := by
  rw [normal, minkowskiForm_mulVec_timeVec, lorentzMat_transpose_mul_eta_mul_self, eta_zero_zero]

/-- **The normal is future-directed:** `N⁰ = coshDist g ≥ 1`. -/
theorem one_le_normal_zero (g : SL2C) : 1 ≤ normal g 0 := by
  have h : normal g 0 = lorentzMat g 0 0 := by
    simp [normal, timeVec]
  rw [h, ← coshDist_eq_lorentzMat]
  exact one_le_coshDist g

/-- `Λ(A)ᵀ η = η Λ(A⁻¹)`. -/
lemma transpose_mul_eta_eq (A : SL2C) :
    (lorentzMat A)ᵀ * eta 4 = eta 4 * lorentzMat A⁻¹ := by
  calc (lorentzMat A)ᵀ * eta 4
      = (lorentzMat A)ᵀ * eta 4 * (lorentzMat A * lorentzMat A⁻¹) := by
        rw [← lorentzMat_mul, mul_inv_cancel, lorentzMat_one, Matrix.mul_one]
    _ = eta 4 * lorentzMat A⁻¹ := by
        rw [← Matrix.mul_assoc, lorentzMat_transpose_mul_eta_mul_self]

/-- **The link variable is the hyperbolic distance between normals:**
`coshDist (A⁻¹ B) = -η(N_A, N_B)` with `N = Λ(·) e₀`, in the project's signature `(−,+,+,+)`. -/
theorem coshDist_inv_mul (A B : SL2C) :
    coshDist (A⁻¹ * B) = -minkowskiForm 4 (normal A) (normal B) := by
  rw [normal, normal, minkowskiForm_mulVec_timeVec, transpose_mul_eta_eq, Matrix.mul_assoc,
    ← lorentzMat_mul, coshDist_eq_lorentzMat]
  simp [eta, Matrix.diagonal_mul, etaDiag]

end Lightlike.Lorentz
