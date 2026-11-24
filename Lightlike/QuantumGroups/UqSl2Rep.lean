import Lightlike.QuantumGroups.UqSl2

/-!
# The two-dimensional representation of `U_q(sl₂)`

On `k²` with basis `v₀, v₁` (`K v₀ = q v₀`, `K v₁ = q⁻¹ v₁`): `E v₁ = v₀`, `F v₀ = v₁`, `E v₀ = F v₁ = 0`. It is a
representation of `UqSl2 k q` for every unit `q` (`fundRep`).
-/

namespace Lightlike.QuantumGroups

variable {k : Type*} [Field k] (q : kˣ)

namespace UqSl2

/-- The matrix of `E` in the two-dimensional representation. -/
def fundE : Matrix (Fin 2) (Fin 2) k := !![0, 1; 0, 0]

/-- The matrix of `F` in the two-dimensional representation. -/
def fundF : Matrix (Fin 2) (Fin 2) k := !![0, 0; 1, 0]

/-- The matrix of `K` in the two-dimensional representation. -/
def fundK : Matrix (Fin 2) (Fin 2) k := !![(q : k), 0; 0, ((q⁻¹ : kˣ) : k)]

/-- The matrix of `K⁻¹` in the two-dimensional representation. -/
def fundKi : Matrix (Fin 2) (Fin 2) k := !![((q⁻¹ : kˣ) : k), 0; 0, (q : k)]

/-- The images of the generators in the two-dimensional representation. -/
def fundGen : Gen → Matrix (Fin 2) (Fin 2) k
  | Gen.E => fundE
  | Gen.F => fundF
  | Gen.K => fundK q
  | Gen.Ki => fundKi q

/-- The generators' matrices satisfy the defining relations of `U_q(sl₂)`. -/
theorem fundGen_rel ⦃x y : FreeAlgebra k Gen⦄ (h : Rel k q x y) :
    FreeAlgebra.lift k (fundGen q) x = FreeAlgebra.lift k (fundGen q) y := by
  have hq : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp
  have hq' : ((q⁻¹ : kˣ) : k) * (q : k) = 1 := by simp
  cases h <;>
  · simp only [map_mul, map_sub, map_one, FreeAlgebra.lift_ι_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fundGen, fundE, fundF, fundK, fundKi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hq, hq'] <;>
      field_simp <;> ring_nf <;> simp [hq, hq']

/-- **The two-dimensional representation** of `U_q(sl₂)` for every unit `q` of a field `k`. -/
noncomputable def fundRep : UqSl2 k q →ₐ[k] Matrix (Fin 2) (Fin 2) k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (fundGen q), fundGen_rel q⟩

/-- `fundRep` sends `E` to `fundE`. -/
theorem fundRep_E : fundRep q (E : UqSl2 k q) = fundE := by
  simp [fundRep, E, fundGen]

/-- `fundRep` sends `F` to `fundF`. -/
theorem fundRep_F : fundRep q (F : UqSl2 k q) = fundF := by
  simp [fundRep, F, fundGen]

/-- `fundRep` sends `K` to `fundK`. -/
theorem fundRep_K : fundRep q (K : UqSl2 k q) = fundK q := by
  simp [fundRep, K, fundGen]

/-- `fundRep` sends `K⁻¹` to `fundKi`. -/
theorem fundRep_Ki : fundRep q (Ki : UqSl2 k q) = fundKi q := by
  simp [fundRep, Ki, fundGen]

end UqSl2

end Lightlike.QuantumGroups
