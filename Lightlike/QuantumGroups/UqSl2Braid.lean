import Lightlike.QuantumGroups.UqSl2Rep

/-!
# The braiding of the two-dimensional representation of `U_q(sl₂)`

On `k² ⊗ k²` (basis `v_{ab}`, `a, b ∈ {0, 1}`) the matrices of `ΔE = E ⊗ K + 1 ⊗ E`, `ΔF = F ⊗ 1 + K⁻¹ ⊗ F` and
`ΔK = K ⊗ K` (the coproduct of `UqSl2`) are `fundCoE`, `fundCoF`, `fundCoK`, `fundCoKi`. The braiding
`Ř = P R` is `fundBraid`: `Ř v₀₀ = q v₀₀`, `Ř v₁₁ = q v₁₁`, `Ř v₀₁ = v₁₀`, `Ř v₁₀ = v₀₁ + (q - q⁻¹) v₁₀`.
It commutes with the coproduct of every generator (`fundBraid_comm_*`), satisfies the Hecke relation
`(Ř - q)(Ř + q⁻¹) = 0` and the braid relation on `k² ⊗ k² ⊗ k²`.
-/

open Matrix

namespace Lightlike.QuantumGroups

variable {k : Type*} [Field k] (q : kˣ)

namespace UqSl2

/-- The matrix of `ΔE = E ⊗ K + 1 ⊗ E` on `k² ⊗ k²`. -/
def fundCoE : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  kroneckerMap (· * ·) fundE (fundK q) + kroneckerMap (· * ·) 1 fundE

/-- The matrix of `ΔF = F ⊗ 1 + K⁻¹ ⊗ F` on `k² ⊗ k²`. -/
def fundCoF : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  kroneckerMap (· * ·) fundF 1 + kroneckerMap (· * ·) (fundKi q) fundF

/-- The matrix of `ΔK = K ⊗ K` on `k² ⊗ k²`. -/
def fundCoK : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  kroneckerMap (· * ·) (fundK q) (fundK q)

/-- The matrix of `ΔK⁻¹ = K⁻¹ ⊗ K⁻¹` on `k² ⊗ k²`. -/
def fundCoKi : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  kroneckerMap (· * ·) (fundKi q) (fundKi q)

/-- **The braiding `Ř`** of the two-dimensional representation: `Ř v₀₀ = q v₀₀`, `Ř v₁₁ = q v₁₁`, `Ř v₀₁ = v₁₀`,
`Ř v₁₀ = v₀₁ + (q - q⁻¹) v₁₀`; the entry `(i, j)` is the coefficient of `v_i` in `Ř v_j`. -/
def fundBraid : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  Matrix.of fun i j =>
    if i = (0, 0) ∧ j = (0, 0) then (q : k)
    else if i = (1, 1) ∧ j = (1, 1) then (q : k)
    else if i = (1, 0) ∧ j = (0, 1) then 1
    else if i = (0, 1) ∧ j = (1, 0) then 1
    else if i = (1, 0) ∧ j = (1, 0) then (q : k) - ((q⁻¹ : kˣ) : k)
    else 0


section Relations

variable {q}

/-- `q q⁻¹ = 1` in the field. -/
private lemma q_mul_inv (q : kˣ) : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp

/-- `q⁻¹ q = 1` in the field. -/
private lemma inv_mul_q (q : kˣ) : ((q⁻¹ : kˣ) : k) * (q : k) = 1 := by simp

/-- **The braiding commutes with `ΔE`.** -/
theorem fundBraid_comm_E : fundBraid q * fundCoE q = fundCoE q * (fundBraid q : Matrix _ _ k) := by
  have h1 := q_mul_inv q
  have h2 := inv_mul_q q
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [fundBraid, fundCoE, fundE, fundK, kroneckerMap_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, h1, h2] <;> ring_nf <;> simp [h1, h2]

/-- **The braiding commutes with `ΔF`.** -/
theorem fundBraid_comm_F : fundBraid q * fundCoF q = fundCoF q * (fundBraid q : Matrix _ _ k) := by
  have h1 := q_mul_inv q
  have h2 := inv_mul_q q
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [fundBraid, fundCoF, fundF, fundKi, kroneckerMap_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, h1, h2] <;> ring_nf <;> simp [h1, h2]

/-- **The braiding commutes with `ΔK`.** -/
theorem fundBraid_comm_K : fundBraid q * fundCoK q = fundCoK q * (fundBraid q : Matrix _ _ k) := by
  have h1 := q_mul_inv q
  have h2 := inv_mul_q q
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [fundBraid, fundCoK, fundK, kroneckerMap_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, h1, h2] <;> ring_nf <;> simp [h1, h2]

/-- **The braiding commutes with `ΔK⁻¹`.** -/
theorem fundBraid_comm_Ki : fundBraid q * fundCoKi q = fundCoKi q * (fundBraid q : Matrix _ _ k) := by
  have h1 := q_mul_inv q
  have h2 := inv_mul_q q
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [fundBraid, fundCoKi, fundKi, kroneckerMap_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Matrix.one_apply, h1, h2] <;> ring_nf <;> simp [h1, h2]

/-- **The Hecke relation** `(Ř - q)(Ř + q⁻¹) = 0`. -/
theorem fundBraid_hecke :
    (fundBraid q - (q : k) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k)) *
      (fundBraid q + ((q⁻¹ : kˣ) : k) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k)) = 0 := by
  have h1 := q_mul_inv q
  have h2 := inv_mul_q q
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [fundBraid, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      Matrix.sub_apply, Matrix.add_apply, h1, h2] <;> ring_nf <;> simp [h1, h2]

/-- `Ř` acting on the first two factors of `k² ⊗ k² ⊗ k²`. -/
def braid12 (q : kˣ) : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) k :=
  Matrix.of fun i j => fundBraid q (i.1, i.2.1) (j.1, j.2.1) * (if i.2.2 = j.2.2 then 1 else 0)

/-- `Ř` acting on the last two factors of `k² ⊗ k² ⊗ k²`. -/
def braid23 (q : kˣ) : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) k :=
  Matrix.of fun i j => (if i.1 = j.1 then 1 else 0) * fundBraid q i.2 j.2

set_option maxHeartbeats 1600000 in
/-- **The braid relation** `Ř₁₂ Ř₂₃ Ř₁₂ = Ř₂₃ Ř₁₂ Ř₂₃` on `k² ⊗ k² ⊗ k²` (Yang–Baxter). -/
theorem fundBraid_braid : braid12 q * braid23 q * braid12 q = braid23 q * braid12 q * (braid23 q : Matrix _ _ k) := by
  have hq0 : (q : k) ≠ 0 := q.ne_zero
  ext ⟨a, b, c⟩ ⟨d, e, f⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> fin_cases f <;>
    simp [braid12, braid23, fundBraid, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Units.val_inv_eq_inv_val] <;>
    (try field_simp) <;> (try ring_nf)

/-- The images of the generators in the tensor square `k² ⊗ k²` (the matrices of the coproducts). -/
def tensorGen (q : kˣ) : Gen → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k
  | Gen.E => fundCoE q
  | Gen.F => fundCoF q
  | Gen.K => fundCoK q
  | Gen.Ki => fundCoKi q

/-- The matrices of the coproducts satisfy the defining relations of `U_q(sl₂)`. -/
theorem tensorGen_rel (q : kˣ) ⦃x y : FreeAlgebra k Gen⦄ (h : Rel k q x y) :
    FreeAlgebra.lift k (tensorGen q) x = FreeAlgebra.lift k (tensorGen q) y := by
  have hq0 : (q : k) ≠ 0 := q.ne_zero
  cases h <;>
  · simp only [map_mul, map_sub, map_one, FreeAlgebra.lift_ι_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    ext ⟨a, b⟩ ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [tensorGen, fundCoE, fundCoF, fundCoK, fundCoKi, fundE, fundF, fundK, fundKi, kroneckerMap_apply,
        Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
        Units.val_inv_eq_inv_val] <;> (try field_simp) <;> (try ring_nf)

/-- **The tensor square of the two-dimensional representation**: the representation of `U_q(sl₂)` on `k² ⊗ k²` with
`E, F, K, K⁻¹` acting by the matrices of `ΔE, ΔF, ΔK, ΔK⁻¹`. -/
noncomputable def fundTensorRep (q : kˣ) : UqSl2 k q →ₐ[k] Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (tensorGen q), tensorGen_rel q⟩

/-- **`Ř` is an intertwiner of the tensor square**: it commutes with the action of every element of `U_q(sl₂)` on
`k² ⊗ k²`. -/
theorem fundBraid_comm_all (x : UqSl2 k q) :
    fundBraid q * fundTensorRep q x = fundTensorRep q x * fundBraid q := by
  obtain ⟨y, rfl⟩ := RingQuot.mkAlgHom_surjective k (Rel k q) x
  induction y using FreeAlgebra.induction with
  | grade0 r =>
    simp only [AlgHom.commutes]
    exact (Algebra.commutes r (fundBraid q)).symm
  | grade1 g =>
    cases g <;> simp [fundTensorRep, tensorGen, fundBraid_comm_E, fundBraid_comm_F, fundBraid_comm_K,
      fundBraid_comm_Ki]
  | mul a b ha hb =>
    simp only [map_mul, ← Matrix.mul_assoc, ha]
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc]
  | add a b ha hb =>
    simp only [map_add, Matrix.mul_add, Matrix.add_mul, ha, hb]

end Relations

end UqSl2

end Lightlike.QuantumGroups
