import Lightlike.Asymptotics.EPRL.EprlHighMap
import Lightlike.Asymptotics.EPRL.EprlCoherentNode

/-!
# The `γ > 1` lift of a product tensor is rank one

For the lowest Clebsch–Gordan component the lift `Φ̃(T) = (Y₀ ⊗ Y₁) T (Y₂ ⊗ Y₃)ᴴ` of the Hom form of a
product tensor `⊗_l s_l` is a rank-one matrix whose two vectors are the pair maps applied to the products
of the leg vectors (`eprlLiftLow_homForm_prod`). Each leg contributes the vector `Y s_l` on
`V_{n_l} ⊗ V_{m_l}` (`eprlPairLow_mulVec_prod`). Unlike `γ < 1` the image of a coherent state is a
superposition and not a product of a self-dual and an anti-self-dual coherent state, so the leg vectors
stay as they are.

The proof uses that `Y_low` has real entries and intertwines the singlet forms
(`eprlMapLow_Wm_conjTranspose`), as `Y_high` does for `γ < 1`.

## Main results

* `star_eprlMapLow`, `eprlPairLow_conjTranspose_eq_transpose`: reality.
* `eprlMapLow_Wm`, `eprlMapLow_Wm_conjTranspose`, `singlet2_mul_eprlPairLow_conjTranspose`: intertwining
  of the singlet forms.
* `eprlPairLow_mulVec_prod`, `eprlLiftLow_homForm_prod`.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4, Figure 4 and the paragraph before eq. (17); EPRL,
  arXiv:0711.0146, Section III, eq. (27).
-/

open Matrix Finset
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

/-- The lowest Clebsch–Gordan component has real entries. -/
lemma star_eprlMapLow (n m : ℕ) (p : Idx n m) (c : Fin (n - m + 1)) :
    star (eprlMapLow n m p c) = eprlMapLow n m p c := by
  simp [eprlMapLow, cgz]

/-- **`Y_low` intertwines the singlet forms**: `(W_n ⊗ W_m) Y = Y W_{n-m}`. -/
theorem eprlMapLow_Wm {n m : ℕ} (h : m ≤ n) :
    (Wm n ⊗ₖ Wm m) * eprlMapLow n m = eprlMapLow n m * Wm (n - m) :=
  eprlMapLow_equivariant h wSU2

/-- `(W_nᴴ ⊗ W_mᴴ) Y = Y W_{n-m}ᴴ`. -/
theorem eprlMapLow_Wm_conjTranspose {n m : ℕ} (h : m ≤ n) :
    ((Wm n)ᴴ ⊗ₖ (Wm m)ᴴ) * eprlMapLow n m = eprlMapLow n m * (Wm (n - m))ᴴ := by
  have h' := eprlMapLow_equivariant h (star wSU2)
  simpa [Wm, wSU2, spinMat_conjTranspose, Matrix.star_eq_conjTranspose] using h'

/-- `(Y₁ ⊗ Y₂)ᴴ = (Y₁ ⊗ Y₂)ᵀ`: the pair map for `γ > 1` has real entries. -/
lemma eprlPairLow_conjTranspose_eq_transpose (n₁ m₁ n₂ m₂ : ℕ) :
    (eprlPairLow n₁ m₁ n₂ m₂)ᴴ = (eprlPairLow n₁ m₁ n₂ m₂)ᵀ := by
  ext c P
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, eprlPairLow, submatrix_apply,
    kroneckerMap_apply, star_mul', star_eprlMapLow]

/-- **`E_{n-m} Yᴴ = Yᴴ (E_n ⊗ E_m)` on the legs `2, 3`** for `γ > 1`. -/
theorem singlet2_mul_eprlPairLow_conjTranspose (n m : Fin 4 → ℕ) (h₂ : m 2 ≤ n 2) (h₃ : m 3 ≤ n 3) :
    singlet2 (n - m) * (eprlPairLow (n 2) (m 2) (n 3) (m 3))ᴴ =
      (eprlPairLow (n 2) (m 2) (n 3) (m 3))ᴴ * (singlet2 n ⊗ₖ singlet2 m) := by
  have hW : ((Wm (n 2) ⊗ₖ Wm (n 3)) ⊗ₖ (Wm (m 2) ⊗ₖ Wm (m 3))) * eprlPairLow (n 2) (m 2) (n 3) (m 3) =
      eprlPairLow (n 2) (m 2) (n 3) (m 3) * (Wm (n 2 - m 2) ⊗ₖ Wm (n 3 - m 3)) := by
    rw [kronecker_shuffle, eprlPairLow, submatrix_mul_equiv, ← mul_kronecker_mul,
      eprlMapLow_Wm h₂, eprlMapLow_Wm h₃, mul_kronecker_mul]
    ext P c
    simp [mul_apply, submatrix_apply]
  have h' := congrArg Matrix.conjTranspose hW
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose] at h'
  unfold singlet2
  simpa [Matrix.conjTranspose_kronecker] using h'.symm


/-- **The pair map for `γ > 1` sends a product to the product of the images**: the leg vector
`Y s_l` on `V_{n_l} ⊗ V_{m_l}`. -/
theorem eprlPairLow_mulVec_prod (n₁ m₁ n₂ m₂ : ℕ) (s₁ : Fin (n₁ - m₁ + 1) → ℂ)
    (s₂ : Fin (n₂ - m₂ + 1) → ℂ) :
    eprlPairLow n₁ m₁ n₂ m₂ *ᵥ (fun c : Idx (n₁ - m₁) (n₂ - m₂) => s₁ c.1 * s₂ c.2) =
      fun P : Idx n₁ n₂ × Idx m₁ m₂ =>
        (eprlMapLow n₁ m₁ *ᵥ s₁) (P.1.1, P.2.1) * (eprlMapLow n₂ m₂ *ᵥ s₂) (P.1.2, P.2.2) := by
  funext P
  simp only [Matrix.mulVec, dotProduct, eprlPairLow, submatrix_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, id]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [shuffle, Equiv.coe_fn_symm_mk]
  ring

/-- **The `γ > 1` lift of the Hom form of a product tensor is rank one**:
`Φ̃(homForm ⊗_l s_l) = |(Y₀ s₀) ⊗ (Y₁ s₁)⟩ ⟨ (E_n ⊗ E_m) (Y₂ s₂) ⊗ (Y₃ s₃) |`, in terms of the pair maps.
Unlike `γ < 1` the image of a coherent state is not a coherent state, so the leg vectors `Y s_l` stay
as they are. -/
theorem eprlLiftLow_homForm_prod (n m : Fin 4 → ℕ) (h₂ : m 2 ≤ n 2) (h₃ : m 3 ≤ n 3)
    (s : (l : Fin 4) → Fin ((n - m) l + 1) → ℂ) :
    eprlLiftLow (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
        (homForm (n - m) (prodVec (n - m) s)) =
      Matrix.vecMulVec
        (eprlPairLow (n 0) (m 0) (n 1) (m 1) *ᵥ (fun p : Idx (n 0 - m 0) (n 1 - m 1) => s 0 p.1 * s 1 p.2))
        ((eprlPairLow (n 2) (m 2) (n 3) (m 3) *ᵥ (fun q : Idx (n 2 - m 2) (n 3 - m 3) => s 2 q.1 * s 3 q.2)) ᵥ*
          (singlet2 n ⊗ₖ singlet2 m)) := by
  have hY34 := eprlPairLow_conjTranspose_eq_transpose (n 2) (m 2) (n 3) (m 3)
  unfold homForm eprlLiftLow
  rw [asMat_prodVec, Matrix.vecMulVec_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  rw [Matrix.vecMul_vecMul, singlet2_mul_eprlPairLow_conjTranspose n m h₂ h₃, ← Matrix.vecMul_vecMul,
    hY34, Matrix.vecMul_transpose]
  rfl

end Lightlike.Asymptotics.EPRL
