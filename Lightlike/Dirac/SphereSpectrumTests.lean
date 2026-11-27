import Lightlike.Dirac.SphereSpectrum

/-!
# Non-vacuity of the Dirac spectrum of the unit 2-sphere

`sphere_spectrum` assumes a Clifford module `ρ : CliffordRep 2 V` with `dim_ℝ V = 4`.  The
quaternions are one: `e₀ ↦ i·`, `e₁ ↦ j·` (left multiplication), since `(a i + b j)² = -(a² + b²)`.
-/

namespace Lightlike.Dirac

open Quaternion

/-- The pure quaternion `v₀ i + v₁ j` of a vector of the plane. -/
noncomputable def quatOfE2 : E 2 →ₗ[ℝ] ℍ[ℝ] where
  toFun v := ⟨0, v 0, v 1, 0⟩
  map_add' v w := by ext <;> simp
  map_smul' c v := by ext <;> simp

lemma quatOfE2_mul_self (v : E 2) :
    quatOfE2 v * quatOfE2 v = ((-(v 0 ^ 2 + v 1 ^ 2) : ℝ) : ℍ[ℝ]) := by
  ext <;> simp only [quatOfE2, LinearMap.coe_mk, AddHom.coe_mk, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_coe,
    Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe] <;> ring

lemma Qneg_two_apply (v : E 2) : Qneg 2 v = -(v 0 ^ 2 + v 1 ^ 2) := by
  rw [Qneg_apply, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp

/-- The quaternions as a `Cl₂`-module: `e₀ ↦ i·`, `e₁ ↦ j·`. -/
noncomputable def quatRep : CliffordRep 2 ℍ[ℝ] :=
  CliffordAlgebra.lift (Qneg 2)
    ⟨(ContinuousLinearMap.mul ℝ ℍ[ℝ]).toLinearMap ∘ₗ quatOfE2, fun v => by
      refine ContinuousLinearMap.ext fun x => ?_
      change quatOfE2 v * (quatOfE2 v * x) = algebraMap ℝ (ℍ[ℝ] →L[ℝ] ℍ[ℝ]) (Qneg 2 v) x
      rw [← mul_assoc, quatOfE2_mul_self, Qneg_two_apply, Quaternion.coe_mul_eq_smul,
        Algebra.algebraMap_eq_smul_one]
      rfl⟩

/-- **Non-vacuity of `sphere_spectrum`**: its hypotheses hold for the quaternions. -/
example : Module.finrank ℝ ℍ[ℝ] = 4 := Quaternion.finrank_eq_four

example (lam : ℝ) :
    (SphereEigenspace quatRep lam ≠ ⊥ ↔ ∃ k : ℕ, lam = ((k + 1 : ℕ) : ℝ) ∨ lam = -((k + 1 : ℕ) : ℝ)) ∧
    ∀ (k : ℕ) {ε : ℝ}, ε * ε = 1 →
      Module.finrank ℝ (SphereEigenspace quatRep (ε * ((k + 1 : ℕ) : ℝ))) = 4 * (k + 1) :=
  sphere_spectrum quatRep Quaternion.finrank_eq_four lam

end Lightlike.Dirac
