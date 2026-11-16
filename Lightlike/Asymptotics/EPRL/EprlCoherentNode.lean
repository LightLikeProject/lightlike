import Lightlike.Asymptotics.EPRL.HomFormExpansion

/-!
# The EPRL lift of a coherent intertwiner

For `γ < 1` the coherent Spin(4) boundary state is the product of the self-dual and anti-self-dual
coherent states. This file shows, at the level of Hom forms, that the Hilbert–Schmidt pairing of
a Spin(4) basis intertwiner `ι⁺_x ⊗ ι⁻_y` with the EPRL lift of the `SU(2)` coherent intertwiner of
spins `n + m` is the product of the two `SU(2)` pairings (`hsInner_ivec4_eprlLift_cohInt` in `EprlCoherentPullback.lean`).

## Main results

* `eprlMap_Wm`, `eprlPair_Wm`, `singlet2_mul_eprlPair_conjTranspose`: the EPRL map intertwines the
  singlet forms.
* `eprlPair_mulVec_coh`: the pair map sends a product of coherent states to the product of the
  self-dual and anti-self-dual ones.
* `eprlLift_homForm_prod`: the EPRL lift of the Hom form of a product of coherent states is the
  Kronecker product of the two Hom forms.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, §3.
-/

open Matrix
open scoped Matrix
open scoped Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling PhyslibAlpha.Sl2 Finset

variable (J : Fin 4 → ℕ)

/-- The matrix `w = [[0, 1], [-1, 0]]` as an element of `SU(2)`. -/
def wSU2 : SU2 :=
  ⟨wM, by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [wM, Matrix.det_fin_two]⟩

/-- **The EPRL map intertwines the singlet forms**: `(W_n ⊗ W_m) Y = Y W_{n+m}`. -/
theorem eprlMap_Wm (n m : ℕ) : (Wm n ⊗ₖ Wm m) * eprlMap n m = eprlMap n m * Wm (n + m) :=
  eprlMap_equivariant wSU2

/-- `(W_nᴴ ⊗ W_mᴴ) Y = Y W_{n+m}ᴴ`. -/
theorem eprlMap_Wm_conjTranspose (n m : ℕ) :
    ((Wm n)ᴴ ⊗ₖ (Wm m)ᴴ) * eprlMap n m = eprlMap n m * (Wm (n + m))ᴴ := by
  have h := eprlMap_equivariant (n := n) (m := m) (star wSU2)
  simpa [Wm, wSU2, spinMat_conjTranspose, Matrix.star_eq_conjTranspose] using h

/-- Regrouping a Kronecker product of two Kronecker products (the `shuffle` of the Spin(4) links). -/
lemma kronecker_shuffle {n₁ n₂ m₁ m₂ : ℕ} (A₁ : Matrix (Fin (n₁ + 1)) (Fin (n₁ + 1)) ℂ)
    (A₂ : Matrix (Fin (n₂ + 1)) (Fin (n₂ + 1)) ℂ) (B₁ : Matrix (Fin (m₁ + 1)) (Fin (m₁ + 1)) ℂ)
    (B₂ : Matrix (Fin (m₂ + 1)) (Fin (m₂ + 1)) ℂ) :
    (A₁ ⊗ₖ A₂) ⊗ₖ (B₁ ⊗ₖ B₂) =
      ((A₁ ⊗ₖ B₁) ⊗ₖ (A₂ ⊗ₖ B₂)).submatrix (shuffle n₁ m₁ n₂ m₂).symm
        (shuffle n₁ m₁ n₂ m₂).symm := by
  ext P Q
  simp only [kroneckerMap_apply, submatrix_apply, shuffle, Equiv.coe_fn_symm_mk]
  ring

/-- **The EPRL pair map intertwines the singlet forms on two legs**:
`(E_n ⊗ E_m) (Y₂ ⊗ Y₃) = (Y₂ ⊗ Y₃) E_{n+m}`, for the legs `2, 3`. -/
theorem eprlPair_singlet2 (n m : Fin 4 → ℕ) :
    (singlet2 n ⊗ₖ singlet2 m) * eprlPair (n 2) (m 2) (n 3) (m 3) =
      eprlPair (n 2) (m 2) (n 3) (m 3) * singlet2 (n + m) := by
  unfold singlet2
  rw [kronecker_shuffle, eprlPair, submatrix_mul_equiv, ← mul_kronecker_mul,
    eprlMap_Wm_conjTranspose, eprlMap_Wm_conjTranspose, mul_kronecker_mul]
  ext P c
  simp [mul_apply, submatrix_apply]

/-- `(W_{n₂} ⊗ W_{n₃}) ⊗ (W_{m₂} ⊗ W_{m₃})` intertwines the pair map. -/
theorem eprlPair_Wm (n m : Fin 4 → ℕ) :
    ((Wm (n 2) ⊗ₖ Wm (n 3)) ⊗ₖ (Wm (m 2) ⊗ₖ Wm (m 3))) * eprlPair (n 2) (m 2) (n 3) (m 3) =
      eprlPair (n 2) (m 2) (n 3) (m 3) * (Wm (n 2 + m 2) ⊗ₖ Wm (n 3 + m 3)) := by
  rw [kronecker_shuffle, eprlPair, submatrix_mul_equiv, ← mul_kronecker_mul,
    eprlMap_Wm, eprlMap_Wm, mul_kronecker_mul]
  ext P c
  simp [mul_apply, submatrix_apply]

/-- **`E_{n+m} Yᴴ = Yᴴ (E_n ⊗ E_m)` on the legs `2, 3`**. -/
theorem singlet2_mul_eprlPair_conjTranspose (n m : Fin 4 → ℕ) :
    singlet2 (n + m) * (eprlPair (n 2) (m 2) (n 3) (m 3))ᴴ =
      (eprlPair (n 2) (m 2) (n 3) (m 3))ᴴ * (singlet2 n ⊗ₖ singlet2 m) := by
  have h := congrArg Matrix.conjTranspose (eprlPair_Wm n m)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_conjTranspose] at h
  unfold singlet2
  simpa [Matrix.conjTranspose_kronecker] using h.symm

/-- The EPRL map has real entries. -/
lemma star_eprlMap (n m : ℕ) (p : Idx n m) (c : Fin (n + m + 1)) :
    star (eprlMap n m p c) = eprlMap n m p c := by
  rw [eprlMap_apply]
  split_ifs <;> simp

/-- `(Y₁ ⊗ Y₂)ᴴ = (Y₁ ⊗ Y₂)ᵀ`: the pair map has real entries. -/
lemma eprlPair_conjTranspose_eq_transpose (n₁ m₁ n₂ m₂ : ℕ) :
    (eprlPair n₁ m₁ n₂ m₂)ᴴ = (eprlPair n₁ m₁ n₂ m₂)ᵀ := by
  ext c P
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, eprlPair_apply, star_mul',
    star_eprlMap]

/-- **The EPRL pair map sends a product of coherent states to the product of the self-dual and
anti-self-dual coherent states.** -/
theorem eprlPair_mulVec_coh (n₁ m₁ n₂ m₂ : ℕ) (g₁ g₂ : SU2) :
    eprlPair n₁ m₁ n₂ m₂ *ᵥ (fun c : Idx (n₁ + m₁) (n₂ + m₂) =>
        cohState (n₁ + m₁) g₁ c.1 * cohState (n₂ + m₂) g₂ c.2) =
      fun P : Idx n₁ n₂ × Idx m₁ m₂ =>
        (cohState n₁ g₁ P.1.1 * cohState n₂ g₂ P.1.2) *
          (cohState m₁ g₁ P.2.1 * cohState m₂ g₂ P.2.2) := by
  funext P
  have h1 := congrFun (eprlMap_cohState (n := n₁) (m := m₁) g₁) (P.1.1, P.2.1)
  have h2 := congrFun (eprlMap_cohState (n := n₂) (m := m₂) g₂) (P.1.2, P.2.2)
  simp only [cohState4] at h1 h2
  simp only [Matrix.mulVec, dotProduct, eprlPair_apply, Fintype.sum_prod_type] at h1 h2 ⊢
  calc ∑ a, ∑ b, eprlMap n₁ m₁ (P.1.1, P.2.1) a * eprlMap n₂ m₂ (P.1.2, P.2.2) b *
        (cohState (n₁ + m₁) g₁ a * cohState (n₂ + m₂) g₂ b)
      = (∑ a, eprlMap n₁ m₁ (P.1.1, P.2.1) a * cohState (n₁ + m₁) g₁ a) *
        (∑ b, eprlMap n₂ m₂ (P.1.2, P.2.2) b * cohState (n₂ + m₂) g₂ b) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by rw [h1, h2]; ring

/-- The Kronecker product of two rank-one matrices. -/
lemma vecMulVec_kronecker {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁] [Fintype κ₂]
    (x : ι₁ → ℂ) (y : κ₁ → ℂ) (x' : ι₂ → ℂ) (y' : κ₂ → ℂ) :
    Matrix.vecMulVec x y ⊗ₖ Matrix.vecMulVec x' y' =
      Matrix.vecMulVec (fun P : ι₁ × ι₂ => x P.1 * x' P.2) (fun Q : κ₁ × κ₂ => y Q.1 * y' Q.2) := by
  ext P Q
  simp only [kroneckerMap_apply, Matrix.vecMulVec_apply]
  ring

/-- A product vector times a Kronecker product. -/
lemma vecMul_kronecker_prod {ι₁ ι₂ κ₁ κ₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype κ₁]
    [Fintype κ₂] (u : ι₁ → ℂ) (u' : ι₂ → ℂ) (A : Matrix ι₁ κ₁ ℂ) (B : Matrix ι₂ κ₂ ℂ) :
    (fun Q : ι₁ × ι₂ => u Q.1 * u' Q.2) ᵥ* (A ⊗ₖ B) =
      fun R : κ₁ × κ₂ => (u ᵥ* A) R.1 * (u' ᵥ* B) R.2 := by
  funext R
  simp only [Matrix.vecMul, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The matrix of a product tensor is rank one. -/
lemma asMat_prodVec (K : Fin 4 → ℕ) (s : (l : Fin 4) → Fin (K l + 1) → ℂ) :
    asMat K (prodVec K s) = Matrix.vecMulVec (fun p : Idx (K 0) (K 1) => s 0 p.1 * s 1 p.2)
      (fun q : Idx (K 2) (K 3) => s 2 q.1 * s 3 q.2) := by
  ext p q
  simp only [asMat, prodVec, Matrix.vecMulVec_apply, Fin.prod_univ_four, legEquiv_symm_zero,
    legEquiv_symm_one, legEquiv_symm_two, legEquiv_symm_three]
  ring

section Spin4Side

variable (n m : Fin 4 → ℕ)

/-- The pullback of a Spin(4) basis intertwiner `ι⁺_x ⊗ ι⁻_y` along the EPRL map,
`R = (Y₁ ⊗ Y₂)ᴴ (ι⁺_x ⊗ ι⁻_y) (Y₃ ⊗ Y₄)`. -/
noncomputable def pullback (x y : ℕ) :
    Matrix (Idx (n 0 + m 0) (n 1 + m 1)) (Idx (n 2 + m 2) (n 3 + m 3)) ℂ :=
  (eprlPair (n 0) (m 0) (n 1) (m 1))ᴴ *
      ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y *
    eprlPair (n 2) (m 2) (n 3) (m 3)

/-- **`⟨ι⁺_x ⊗ ι⁻_y, Φ̃(T)⟩ = ⟨R, T⟩`**: the EPRL lift before projection is adjoint to the pullback. -/
theorem hsInner_ivec4_eprlLift (x y : ℕ)
    (T : Matrix (Idx (n 0 + m 0) (n 1 + m 1)) (Idx (n 2 + m 2) (n 3 + m 3)) ℂ) :
    hsInner (ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y)
        (eprlLift (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) T) =
      hsInner (pullback n m x y) T := by
  unfold eprlLift pullback
  rw [hsInner_eq_trace, hsInner_eq_trace]
  rw [show (ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y)ᴴ *
        (eprlPair (n 0) (m 0) (n 1) (m 1) * T * (eprlPair (n 2) (m 2) (n 3) (m 3))ᴴ) =
      ((ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) x y)ᴴ *
        (eprlPair (n 0) (m 0) (n 1) (m 1) * T)) * (eprlPair (n 2) (m 2) (n 3) (m 3))ᴴ by
      simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- **The EPRL lift of a product of coherent states is the product of the self-dual and
anti-self-dual Hom forms**: `Φ̃(S_{n+m}) = S_n ⊗ S_m`, with `S_K = homForm K (⊗_l |K_l/2, g_l⟩)`. -/
theorem eprlLift_homForm_prod (g : Fin 4 → SU2) :
    eprlLift (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
        (homForm (n + m) (prodVec (n + m) fun l => cohState ((n + m) l) (g l))) =
      homForm n (prodVec n fun l => cohState (n l) (g l)) ⊗ₖ
        homForm m (prodVec m fun l => cohState (m l) (g l)) := by
  set bJ : Idx (n 2 + m 2) (n 3 + m 3) → ℂ := fun q =>
    cohState ((n + m) 2) (g 2) q.1 * cohState ((n + m) 3) (g 3) q.2 with hbJ
  set bn : Idx (n 2) (n 3) → ℂ := fun q => cohState (n 2) (g 2) q.1 * cohState (n 3) (g 3) q.2
    with hbn
  set bm : Idx (m 2) (m 3) → ℂ := fun q => cohState (m 2) (g 2) q.1 * cohState (m 3) (g 3) q.2
    with hbm
  have hY34 : (eprlPair (n 2) (m 2) (n 3) (m 3))ᴴ = (eprlPair (n 2) (m 2) (n 3) (m 3))ᵀ :=
    eprlPair_conjTranspose_eq_transpose _ _ _ _
  have hR : (fun R : Idx (n 2) (n 3) × Idx (m 2) (m 3) => bn R.1 * bm R.2) =
      eprlPair (n 2) (m 2) (n 3) (m 3) *ᵥ bJ := (eprlPair_mulVec_coh (n 2) (m 2) (n 3) (m 3)
        (g 2) (g 3)).symm
  unfold homForm eprlLift
  rw [asMat_prodVec, asMat_prodVec, asMat_prodVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mul, vecMulVec_kronecker]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have e1 : (fun P : Idx (n 0) (n 1) × Idx (m 0) (m 1) =>
      (cohState (n 0) (g 0) P.1.1 * cohState (n 1) (g 1) P.1.2) *
        (cohState (m 0) (g 0) P.2.1 * cohState (m 1) (g 1) P.2.2)) =
      eprlPair (n 0) (m 0) (n 1) (m 1) *ᵥ (fun p : Idx (n 0 + m 0) (n 1 + m 1) =>
        cohState ((n + m) 0) (g 0) p.1 * cohState ((n + m) 1) (g 1) p.2) :=
    (eprlPair_mulVec_coh (n 0) (m 0) (n 1) (m 1) (g 0) (g 1)).symm
  have e2 : ((bJ ᵥ* singlet2 (n + m)) ᵥ* (eprlPair (n 2) (m 2) (n 3) (m 3))ᴴ) =
      fun R : Idx (n 2) (n 3) × Idx (m 2) (m 3) => (bn ᵥ* singlet2 n) R.1 * (bm ᵥ* singlet2 m) R.2 := by
    rw [Matrix.vecMul_vecMul, singlet2_mul_eprlPair_conjTranspose, ← Matrix.vecMul_vecMul, hY34,
      Matrix.vecMul_transpose, ← hR]
    exact vecMul_kronecker_prod bn bm (singlet2 n) (singlet2 m)
  rw [e1]
  congr 1

end Spin4Side

end Lightlike.Asymptotics.EPRL
