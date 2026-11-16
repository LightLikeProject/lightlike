import Lightlike.Asymptotics.EPRL.HaarNode
import Lightlike.SpinFoam.TetrahedronSixJ

/-!
# The Hom form of an invariant four-leg tensor

An `SU(2)`-invariant tensor `v` on four legs `⊗_a V_{J_a/2}` (`IsInvariantN J v`) is turned into a
linear map `homForm J v` from the last two legs to the first two by contracting the last two with the
singlet form `Wᴴ ⊗ Wᴴ` (`Wm`, the matrix of `w = [[0, 1], [-1, 0]]`). The result commutes with the
diagonal action (`homForm_isIntertwiner`), so it is an `SU(2)` intertwiner in the sense of
`Lightlike.Spin4.IsIntertwiner`, where the library has an orthonormal basis `ivec` and a completeness
theorem.

## Main results

* `asMat_rhoN`: the group action on four-leg tensors in matrix form,
  `asMat (ρ(g) v) = D₀₁(g) (asMat v) D₂₃(g)ᵀ`.
* `homForm_rhoN`: `homForm (ρ(g) v) = D₀₁(g) (homForm v) D₂₃(g)ᴴ`.
* `hsInner_conj_of_isIntertwiner`: the Hilbert–Schmidt pairing with an intertwiner is invariant under
  that conjugation action.
* `homForm_isIntertwiner`: **a four-leg invariant tensor, in Hom form, is an intertwiner**.

## References

* Lightlike/Spin4/Intertwiner4.lean (`IsIntertwiner`, `ivec`, `eq_sum_ivec`) and
  Lightlike/SpinFoam/Tetrahedron.lean (`Wm`).
-/

open Matrix
open scoped Matrix
open scoped Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling PhyslibAlpha.Sl2 Finset

variable (J : Fin 4 → ℕ)

/-- The four legs of a tensor as the pair of the first two and the last two. -/
def legEquiv : LIdx J ≃ Idx (J 0) (J 1) × Idx (J 2) (J 3) where
  toFun k := ((k 0, k 1), (k 2, k 3))
  invFun x := Fin.cons (α := fun l => Fin (J l + 1)) x.1.1
    (Fin.cons (α := fun l => Fin (J l.succ + 1)) x.1.2
      (Fin.cons (α := fun l => Fin (J l.succ.succ + 1)) x.2.1
        (Fin.cons (α := fun l => Fin (J l.succ.succ.succ + 1)) x.2.2 finZeroElim)))
  left_inv k := by
    funext l
    fin_cases l <;> rfl
  right_inv x := rfl

@[simp] lemma legEquiv_symm_zero (x : Idx (J 0) (J 1) × Idx (J 2) (J 3)) :
    (legEquiv J).symm x 0 = x.1.1 := rfl
@[simp] lemma legEquiv_symm_one (x : Idx (J 0) (J 1) × Idx (J 2) (J 3)) :
    (legEquiv J).symm x 1 = x.1.2 := rfl
@[simp] lemma legEquiv_symm_two (x : Idx (J 0) (J 1) × Idx (J 2) (J 3)) :
    (legEquiv J).symm x 2 = x.2.1 := rfl
@[simp] lemma legEquiv_symm_three (x : Idx (J 0) (J 1) × Idx (J 2) (J 3)) :
    (legEquiv J).symm x 3 = x.2.2 := rfl

/-- A four-leg tensor as a matrix from the last two legs to the first two. -/
def asMat (v : LIdx J → ℂ) : Matrix (Idx (J 0) (J 1)) (Idx (J 2) (J 3)) ℂ :=
  fun p q => v ((legEquiv J).symm (p, q))

/-- **Invariance in matrix form**: an invariant four-leg tensor `v` satisfies
`D_{01}(g) M D_{23}(g)ᵀ = M` for `M = asMat v`. -/
theorem asMat_invariant {v : LIdx J → ℂ} (hv : IsInvariantN J v) (g : SU2) :
    pairMat (J 0) (J 1) g * asMat J v * (pairMat (J 2) (J 3) g)ᵀ = asMat J v := by
  ext p q
  have h := congrFun (hv g) ((legEquiv J).symm (p, q))
  rw [mulVec, dotProduct] at h
  rw [← (legEquiv J).symm.sum_comp, Fintype.sum_prod_type] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ => ?_) h
  simp only [pairMat, kroneckerMap_apply, Matrix.transpose_apply, asMat, rhoN, Matrix.of_apply,
    Fin.prod_univ_four, legEquiv_symm_zero, legEquiv_symm_one, legEquiv_symm_two,
    legEquiv_symm_three]
  ring

/-- `D(g)` is unitary. -/
lemma spinMat_conjTranspose_mul_self (n : ℕ) (g : SU2) :
    (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [spinMat_conjTranspose, ← spinMat_mul]
  have hu : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  rw [hu, spinMat_one]

/-- **The action on four-leg tensors in matrix form**: `asMat (ρ(g) v) = D₀₁(g) (asMat v) D₂₃(g)ᵀ`. -/
theorem asMat_rhoN (v : LIdx J → ℂ) (g : SU2) :
    asMat J (rhoN J g *ᵥ v) =
      pairMat (J 0) (J 1) g * asMat J v * (pairMat (J 2) (J 3) g)ᵀ := by
  ext p q
  have h : (rhoN J g *ᵥ v) ((legEquiv J).symm (p, q)) =
      ∑ x : Idx (J 0) (J 1) × Idx (J 2) (J 3),
        rhoN J g ((legEquiv J).symm (p, q)) ((legEquiv J).symm x) * v ((legEquiv J).symm x) := by
    rw [mulVec, dotProduct]
    exact ((legEquiv J).symm.sum_comp fun i => rhoN J g ((legEquiv J).symm (p, q)) i * v i).symm
  rw [Fintype.sum_prod_type] at h
  show (rhoN J g *ᵥ v) ((legEquiv J).symm (p, q)) = _
  rw [h, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ => ?_
  simp only [pairMat, kroneckerMap_apply, Matrix.transpose_apply, asMat, rhoN, Matrix.of_apply,
    Fin.prod_univ_four, legEquiv_symm_zero, legEquiv_symm_one, legEquiv_symm_two,
    legEquiv_symm_three]
  ring

/-- `D(g)ᵀ Wᴴ D(g) = Wᴴ`: the singlet form, read on the left. -/
lemma spinMat_transpose_mul_Wm_conjTranspose_mul (n : ℕ) (g : SU2) :
    (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ))ᵀ * (Wm n)ᴴ * spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (Wm n)ᴴ := by
  set D := spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) with hD
  have hDD : Dᴴ * D = 1 := spinMat_conjTranspose_mul_self n g
  have hWW : (Wm n)ᴴ * Wm n = 1 := Wm_conjTranspose_mul
  have hWW' : Wm n * (Wm n)ᴴ = 1 := mul_eq_one_comm.mp hWW
  have hW : D * Wm n * Dᵀ = Wm n := spinMat_mul_Wm_mul_transpose g
  have c1 : ∀ X, Dᴴ * (D * X) = X := fun X => by rw [← Matrix.mul_assoc, hDD, Matrix.one_mul]
  have c2 : ∀ X, (Wm n)ᴴ * (Wm n * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hWW, Matrix.one_mul]
  have hT : Dᵀ = (Wm n)ᴴ * Dᴴ * Wm n := by
    have e : (Wm n)ᴴ * Dᴴ * (D * Wm n * Dᵀ) = (Wm n)ᴴ * Dᴴ * Wm n := by rw [hW]
    rw [← e]
    simp only [Matrix.mul_assoc]
    rw [c1, c2]
  have c3 : ∀ X, Wm n * ((Wm n)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hWW', Matrix.one_mul]
  rw [hT]
  simp only [Matrix.mul_assoc]
  rw [c3, hDD, Matrix.mul_one]

/-- The singlet form `Wᴴ ⊗ Wᴴ` on the two incoming legs, which turns them into outgoing ones. -/
noncomputable def singlet2 : Matrix (Idx (J 2) (J 3)) (Idx (J 2) (J 3)) ℂ :=
  (Wm (J 2))ᴴ ⊗ₖ (Wm (J 3))ᴴ

/-- The Hom form of a four-leg tensor: `asMat v` followed by the singlet form on the last two legs. -/
noncomputable def homForm (v : LIdx J → ℂ) : Matrix (Idx (J 0) (J 1)) (Idx (J 2) (J 3)) ℂ :=
  asMat J v * singlet2 J

/-- `D(g)ᵀ E D(g) = E` for the pair of the last two legs. -/
lemma pair_transpose_mul_singlet2_mul (g : SU2) :
    (pairMat (J 2) (J 3) g)ᵀ * singlet2 J * pairMat (J 2) (J 3) g = singlet2 J := by
  unfold singlet2 pairMat
  rw [← kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    spinMat_transpose_mul_Wm_conjTranspose_mul, spinMat_transpose_mul_Wm_conjTranspose_mul]

/-- The pair action is unitary. -/
lemma pair_conjTranspose_mul_self (n m : ℕ) (g : SU2) :
    (pairMat n m g)ᴴ * pairMat n m g = 1 := by
  unfold pairMat
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, spinMat_conjTranspose_mul_self,
    spinMat_conjTranspose_mul_self, Matrix.one_kronecker_one]

/-- `E P† = Pᵀ E` for the pair action of the last two legs. -/
lemma singlet2_mul_conjTranspose (g : SU2) :
    singlet2 J * (pairMat (J 2) (J 3) g)ᴴ = (pairMat (J 2) (J 3) g)ᵀ * singlet2 J := by
  have hPP : (pairMat (J 2) (J 3) g)ᴴ * pairMat (J 2) (J 3) g = 1 :=
    pair_conjTranspose_mul_self _ _ g
  have hPP' : pairMat (J 2) (J 3) g * (pairMat (J 2) (J 3) g)ᴴ = 1 := mul_eq_one_comm.mp hPP
  calc singlet2 J * (pairMat (J 2) (J 3) g)ᴴ
      = ((pairMat (J 2) (J 3) g)ᵀ * singlet2 J * pairMat (J 2) (J 3) g) *
          (pairMat (J 2) (J 3) g)ᴴ := by rw [pair_transpose_mul_singlet2_mul]
    _ = (pairMat (J 2) (J 3) g)ᵀ * singlet2 J := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hPP', Matrix.mul_one]

/-- **`homForm` is equivariant**: `homForm (ρ(g) v) = D₀₁(g) (homForm v) D₂₃(g)ᴴ`. -/
theorem homForm_rhoN (v : LIdx J → ℂ) (g : SU2) :
    homForm J (rhoN J g *ᵥ v) =
      pairMat (J 0) (J 1) g * homForm J v * (pairMat (J 2) (J 3) g)ᴴ := by
  unfold homForm
  rw [asMat_rhoN, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, ← singlet2_mul_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- **The Hilbert–Schmidt pairing with an intertwiner is invariant under the conjugation action**:
`⟨R, D₀₁(g) T D₂₃(g)ᴴ⟩ = ⟨R, T⟩` for `R` an `SU(2)` intertwiner. -/
theorem hsInner_conj_of_isIntertwiner {R : Matrix (Idx (J 0) (J 1)) (Idx (J 2) (J 3)) ℂ}
    (hR : IsIntertwiner (J 0) (J 1) (J 2) (J 3) R)
    (T : Matrix (Idx (J 0) (J 1)) (Idx (J 2) (J 3)) ℂ) (g : SU2) :
    hsInner R (pairMat (J 0) (J 1) g * T * (pairMat (J 2) (J 3) g)ᴴ) = hsInner R T := by
  set A := pairMat (J 0) (J 1) g with hA
  set B := pairMat (J 2) (J 3) g with hB
  have hAA : Aᴴ * A = 1 := pair_conjTranspose_mul_self _ _ g
  have hRg : A * R = R * B := hR g
  have key : Aᴴ * R * B = R := by
    calc Aᴴ * R * B = Aᴴ * (R * B) := by rw [Matrix.mul_assoc]
      _ = Aᴴ * (A * R) := by rw [hRg]
      _ = R := by rw [← Matrix.mul_assoc, hAA, Matrix.one_mul]
  rw [hsInner_eq_trace, hsInner_eq_trace]
  calc trace (Rᴴ * (A * T * Bᴴ)) = trace (Bᴴ * (Rᴴ * (A * T))) := by
        rw [show Rᴴ * (A * T * Bᴴ) = (Rᴴ * (A * T)) * Bᴴ by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
    _ = trace ((Aᴴ * R * B)ᴴ * T) := by
        have : Bᴴ * (Rᴴ * (A * T)) = (Aᴴ * R * B)ᴴ * T := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
        rw [this]
    _ = trace (Rᴴ * T) := by rw [key]

/-- **A four-leg invariant tensor, in Hom form, is an `SU(2)` intertwiner** (general, not specific to
coherent intertwiners): the Hom form `asMat v · (Wᴴ ⊗ Wᴴ)` commutes with the diagonal action. -/
theorem homForm_isIntertwiner {v : LIdx J → ℂ} (hv : IsInvariantN J v) :
    IsIntertwiner (J 0) (J 1) (J 2) (J 3) (homForm J v) := by
  intro g
  set P := pairMat (J 2) (J 3) g with hP
  set M := asMat J v with hM
  set E := singlet2 J with hE
  have hPP : Pᴴ * P = 1 := pair_conjTranspose_mul_self _ _ g
  have hPP' : P * Pᴴ = 1 := mul_eq_one_comm.mp hPP
  have hR : Pᵀ * E * P = E := pair_transpose_mul_singlet2_mul J g
  have hE' : E * Pᴴ = Pᵀ * E := by
    calc E * Pᴴ = (Pᵀ * E * P) * Pᴴ := by rw [hR]
      _ = Pᵀ * E := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hPP', Matrix.mul_one]
  have hA : pairMat (J 0) (J 1) g * M * Pᵀ = M := asMat_invariant J hv g
  have key : pairMat (J 0) (J 1) g * (M * E) * Pᴴ = M * E := by
    calc pairMat (J 0) (J 1) g * (M * E) * Pᴴ
        = pairMat (J 0) (J 1) g * M * (E * Pᴴ) := by simp only [Matrix.mul_assoc]
      _ = pairMat (J 0) (J 1) g * M * (Pᵀ * E) := by rw [hE']
      _ = (pairMat (J 0) (J 1) g * M * Pᵀ) * E := by simp only [Matrix.mul_assoc]
      _ = M * E := by rw [hA]
  unfold homForm
  calc pairMat (J 0) (J 1) g * (M * E)
      = pairMat (J 0) (J 1) g * (M * E) * (Pᴴ * P) := by rw [hPP, Matrix.mul_one]
    _ = (pairMat (J 0) (J 1) g * (M * E) * Pᴴ) * P := by simp only [Matrix.mul_assoc]
    _ = (M * E) * P := by rw [key]

end Lightlike.Asymptotics.EPRL
