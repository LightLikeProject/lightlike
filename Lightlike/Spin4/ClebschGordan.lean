import Lightlike.Spin4.Rep
import Lightlike.SU2.Completeness
import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorDecomposition

/-!
# Clebsch–Gordan: `(j₊, j₋)` restricted to the diagonal SU(2)

Restricted to the diagonal subgroup `{(g, g)}` of `Spin4 = SU(2) × SU(2)`, the representation
`(j₊, j₋) = (n/2, m/2)` splits into the spins `j₊ + j₋, j₊ + j₋ - 1, …, |j₊ - j₋|`, each once
(`spin4_diag_clebschGordan`):

  `D^{n/2}(g) ⊗ D^{m/2}(g) ≅ ⊕_{k=0}^{min(n,m)} D^{(n+m)/2 - k}(g)`.

The right side is `cgMat n m g`, the block-diagonal matrix with blocks `spinMat (n + m - 2k) g`,
on `ℂ^{(n+1)(m+1)}` indexed by `CGIdx n m` (pairs `(k, l)` with `k ≤ min(n,m)`,
`l ≤ n + m - 2k`).

## Proof

Physlib proves the decomposition for the Lie algebra `sl₂`: `cgEquiv` is an explicit linear
equivalence `V(n) ⊗ V(m) ≃ ⊕_k V(n + m - 2k)` (from the lowering strings of the highest-weight
vectors) that intertwines the raising, lowering and weight operators. Through `SU2.Ψ`, which
identifies Physlib's `V(n)` with `ℂ^{n+1}` and the operators with the differentials `dSpin n`
(`Lightlike/SU2/LieBridge.lean`), this gives a linear equivalence `cgT n m` that intertwines the
differentials `dSpin n X ⊗ 1 + 1 ⊗ dSpin m X` and `⊕_k dSpin (n+m-2k) X` for every traceless `X`.
Every `g ∈ SU(2)` is `exp X` with `X ∈ su(2)`, `spinMat n (exp X) = exp (dSpin n X)`
(`SU2.dσ_eq`), and an intertwiner of generators intertwines their exponentials.

## References

* D. A. Varshalovich, A. N. Moskalev, V. K. Khersonskii, *Quantum Theory of Angular Momentum*,
  World Scientific (1988), Ch. 8 (Clebsch–Gordan coefficients).
* A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press (1957),
  Ch. 3 (coupling of two angular momenta).
-/

open Matrix TensorProduct PhyslibAlpha.Sl2
open scoped Kronecker

namespace Lightlike.Spin4

open SU2

/-! ## A. The block-diagonal side -/

/-- Labels of the Clebsch–Gordan side: `(k, l)` with `k ≤ min(n, m)` (the summand of spin
`(n+m)/2 - k`) and `l ≤ n + m - 2k`. This is Physlib's `StringIndex n m`. -/
abbrev CGIdx (n m : ℕ) := Σ k : Fin (min n m + 1), Fin (n + m - 2 * (k : ℕ) + 1)

/-- The block-diagonal action of SU(2) on `⊕_k ℂ^{n+m-2k+1}`: spin `(n+m)/2 - k` on the
`k`-th block. -/
noncomputable def cgMat (n m : ℕ) (g : SU2) : Matrix (CGIdx n m) (CGIdx n m) ℂ :=
  blockDiagonal' fun k => spinMat (n + m - 2 * (k : ℕ)) g

/-! ## B. Exponentials -/

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Intertwining passes to exponentials (any finite index types). -/
lemma intertwine_exp' {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hT : ∀ v, T (A *ᵥ v) = B *ᵥ T v) (v : ι → ℂ) :
    T (NormedSpace.exp A *ᵥ v) = NormedSpace.exp B *ᵥ T v := by
  have hpow : ∀ k : ℕ, T (A ^ k *ᵥ v) = B ^ k *ᵥ T v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, hT, ih, pow_succ', ← mulVec_mulVec]
  let gA : Matrix ι ι ℂ →ₗ[ℝ] (κ → ℂ) :=
    { toFun := fun M => T (M *ᵥ v)
      map_add' := fun M N => by rw [add_mulVec, map_add]
      map_smul' := fun r M => by rw [smul_mulVec, T.map_smul_of_tower]; rfl }
  let gB : Matrix κ κ ℂ →ₗ[ℝ] (κ → ℂ) :=
    { toFun := fun M => M *ᵥ T v
      map_add' := fun M N => add_mulVec M N _
      map_smul' := fun r M => by rw [smul_mulVec]; rfl }
  have hA := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map gA
    (LinearMap.continuous_of_finiteDimensional gA)
  have hB := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) B).map gB
    (LinearMap.continuous_of_finiteDimensional gB)
  refine hA.unique ?_
  convert hB using 1
  funext k
  show T ((((k.factorial : ℝ)⁻¹) • A ^ k) *ᵥ v) = (((k.factorial : ℝ)⁻¹) • B ^ k) *ᵥ T v
  rw [smul_mulVec, T.map_smul_of_tower, hpow, smul_mulVec]
  rfl

/-- `X ↦ X ⊗ₖ 1` as a ring homomorphism. -/
noncomputable def kronOneHom (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] : Matrix ι ι ℂ →+* Matrix (ι × κ) (ι × κ) ℂ where
  toFun X := X ⊗ₖ (1 : Matrix κ κ ℂ)
  map_one' := one_kronecker_one
  map_mul' X Y := by rw [← mul_kronecker_mul, one_mul]
  map_zero' := zero_kronecker _
  map_add' X Y := add_kronecker _ _ _

/-- `X ↦ 1 ⊗ₖ X` as a ring homomorphism. -/
noncomputable def oneKronHom (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] : Matrix κ κ ℂ →+* Matrix (ι × κ) (ι × κ) ℂ where
  toFun X := (1 : Matrix ι ι ℂ) ⊗ₖ X
  map_one' := one_kronecker_one
  map_mul' X Y := by rw [← mul_kronecker_mul, one_mul]
  map_zero' := kronecker_zero _
  map_add' X Y := kronecker_add _ _ _

/-- `exp A ⊗ₖ exp B = exp (A ⊗ₖ 1 + 1 ⊗ₖ B)`. -/
lemma exp_kronecker {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    NormedSpace.exp A ⊗ₖ NormedSpace.exp B =
      NormedSpace.exp (A ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ B) := by
  have hL : Continuous (kronOneHom ι κ) := continuous_matrix fun p q =>
    (continuous_id.matrix_elem p.1 q.1).mul continuous_const
  have hR : Continuous (oneKronHom ι κ) := continuous_matrix fun p q =>
    continuous_const.mul (continuous_id.matrix_elem p.2 q.2)
  have hcomm : Commute (A ⊗ₖ (1 : Matrix κ κ ℂ)) ((1 : Matrix ι ι ℂ) ⊗ₖ B) := by
    rw [Commute, SemiconjBy, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
      one_mul, mul_one]
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  have h1 : NormedSpace.exp (A ⊗ₖ (1 : Matrix κ κ ℂ)) = NormedSpace.exp A ⊗ₖ 1 :=
    (NormedSpace.map_exp (kronOneHom ι κ) hL A).symm
  have h2 : NormedSpace.exp ((1 : Matrix ι ι ℂ) ⊗ₖ B) = 1 ⊗ₖ NormedSpace.exp B :=
    (NormedSpace.map_exp (oneKronHom ι κ) hR B).symm
  rw [h1, h2, ← mul_kronecker_mul, mul_one, one_mul]

/-- The exponential of a block-diagonal matrix is block-diagonal. -/
lemma exp_blockDiagonal'_fun {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (C : ∀ i, Matrix (κ i) (κ i) ℂ) :
    NormedSpace.exp (blockDiagonal' C) = blockDiagonal' fun i => NormedSpace.exp (C i) := by
  rw [Matrix.exp_blockDiagonal']
  congr 1
  funext i
  exact Pi.coe_exp C i

/-- `spinMat n (exp X) = exp (dSpin n X)` for `X ∈ su(2)`. -/
lemma spinMat_Γ (n : ℕ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) :
    spinMat n (Γ X hX 1 : Matrix (Fin 2) (Fin 2) ℂ) = NormedSpace.exp (dSpin n X) := by
  rw [← σ_apply, rho_Γ (continuous_σ n) hX, dσ_eq n hX, one_smul]

end Exp

/-! ## C. The Clebsch–Gordan equivalence and the Lie algebra -/

/-- A block-diagonal matrix acts blockwise. -/
lemma blockDiagonal'_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (C : ∀ i, Matrix (κ i) (κ i) ℂ)
    (v : (Σ i, κ i) → ℂ) (k : ι) (l : κ k) :
    (blockDiagonal' C *ᵥ v) ⟨k, l⟩ = (C k *ᵥ fun l' => v ⟨k, l'⟩) l := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single k (fun k' _ hk' => Finset.sum_eq_zero fun l' _ => by
    rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hk'), zero_mul]) (by simp)]
  simp [blockDiagonal'_apply_eq]

variable {n m : ℕ}

/-- On the coordinates `ℂ^{(n+1)(m+1)}`, `diagEnd A B = A ⊗ 1 + 1 ⊗ B` is `A ⊗ₖ 1 + 1 ⊗ₖ B`. -/
lemma tensorEquiv_diagEnd (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (t : TensorSpace n m) :
    tensorEquiv n m (diagEnd (Matrix.toLin' A) (Matrix.toLin' B) t) =
      (A ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) +
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ B) *ᵥ tensorEquiv n m t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [diagEnd_tmul, map_add, tensorEquiv_tmul, tensorEquiv_tmul, tensorEquiv_tmul, add_mulVec,
      kronecker_mulVec_prod, kronecker_mulVec_prod, one_mulVec, one_mulVec]
    rfl
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, mulVec_add]

/-- `Ψ⁻¹ ⊗ Ψ⁻¹`: the coordinates of `ℂ^{n+1} ⊗ ℂ^{m+1}` in Physlib's `V(n) ⊗ V(m)`. -/
noncomputable def psiTensor (n m : ℕ) :
    TensorSpace n m ≃ₗ[ℂ] (StandardSl2Module ℂ n ⊗[ℂ] StandardSl2Module ℂ m) :=
  TensorProduct.congr (Ψ n).symm (Ψ m).symm

/-- `Ψ⁻¹ ⊗ Ψ⁻¹` carries `dSpin ⊗ 1 + 1 ⊗ dSpin` of an `sl₂` generator to Physlib's diagonal
operator, given the single-factor relation `dSpin k Y Ψ = Ψ ρ`. -/
lemma psiTensor_diagEnd (Y : Matrix (Fin 2) (Fin 2) ℂ)
    (ρY : ∀ k, Module.End ℂ (StandardSl2Module ℂ k))
    (hY : ∀ k (w : StandardSl2Module ℂ k), dSpin k Y *ᵥ Ψ k w = Ψ k (ρY k w))
    (t : TensorSpace n m) :
    psiTensor n m (diagEnd (Matrix.toLin' (dSpin n Y)) (Matrix.toLin' (dSpin m Y)) t) =
      diagEnd (ρY n) (ρY m) (psiTensor n m t) := by
  have hΨ : ∀ k (x : Fin (k + 1) → ℂ), (Ψ k).symm (dSpin k Y *ᵥ x) = ρY k ((Ψ k).symm x) :=
    fun k x => by
      apply (Ψ k).injective
      rw [LinearEquiv.apply_symm_apply, ← hY, LinearEquiv.apply_symm_apply]
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [psiTensor, diagEnd_tmul, map_add, TensorProduct.congr_tmul, Matrix.toLin'_apply, hΨ]
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]

/-- The coordinates of `⊕_k V(n+m-2k)` in `ℂ^{(n+1)(m+1)}`, indexed by `CGIdx n m`. -/
noncomputable def sumCoord (n m : ℕ) : CGSum ℂ n m ≃ₗ[ℂ] (CGIdx n m → ℂ) :=
  (DirectSum.linearEquivFunOnFintype ℂ (Fin (min n m + 1)) (CGSummand ℂ n m)).trans
    ((LinearEquiv.piCongrRight fun k : Fin (min n m + 1) => Ψ (n + m - 2 * (k : ℕ))).trans
      (LinearEquiv.piCurry ℂ
        (fun (k : Fin (min n m + 1)) (_ : Fin (n + m - 2 * (k : ℕ) + 1)) => ℂ)).symm)

lemma sumCoord_apply (s : CGSum ℂ n m) (k : Fin (min n m + 1)) (l) :
    sumCoord n m s ⟨k, l⟩ = Ψ (n + m - 2 * (k : ℕ)) (s k) l := rfl

/-- `sumCoord` carries `sumEnd ρY` to the block-diagonal `⊕_k dSpin (n+m-2k) Y`. -/
lemma sumCoord_sumEnd (Y : Matrix (Fin 2) (Fin 2) ℂ)
    (ρY : ∀ k, Module.End ℂ (StandardSl2Module ℂ k))
    (hY : ∀ k (w : StandardSl2Module ℂ k), dSpin k Y *ᵥ Ψ k w = Ψ k (ρY k w))
    (s : CGSum ℂ n m) :
    sumCoord n m (sumEnd (fun k => ρY (n + m - 2 * (k : ℕ))) s) =
      blockDiagonal' (fun k : Fin (min n m + 1) => dSpin (n + m - 2 * (k : ℕ)) Y) *ᵥ
        sumCoord n m s := by
  funext ⟨k, l⟩
  rw [blockDiagonal'_mulVec_apply, sumCoord_apply]
  have : (fun l' => sumCoord n m s ⟨k, l'⟩) = Ψ (n + m - 2 * (k : ℕ)) (s k) := rfl
  rw [this, hY]
  rfl

/-- **The Clebsch–Gordan equivalence** `ℂ^{(n+1)(m+1)} ≃ ⊕_k ℂ^{n+m-2k+1}` (for `n + m > 0`):
Physlib's `cgEquiv`, in coordinates. -/
noncomputable def cgT (hnm : 0 < n + m) : (Idx n m → ℂ) ≃ₗ[ℂ] (CGIdx n m → ℂ) :=
  (tensorEquiv n m).symm.trans ((psiTensor n m).trans ((cgEquiv (K := ℂ) hnm).trans (sumCoord n m)))

/-- `cgT` intertwines an `sl₂` generator `Y` of the diagonal action with the block-diagonal
action. -/
lemma cgT_generator (hnm : 0 < n + m) (Y : Matrix (Fin 2) (Fin 2) ℂ)
    (ρY : ∀ k, Module.End ℂ (StandardSl2Module ℂ k))
    (hY : ∀ k (w : StandardSl2Module ℂ k), dSpin k Y *ᵥ Ψ k w = Ψ k (ρY k w))
    (hcg : ∀ x, cgEquiv (K := ℂ) hnm (diagEnd (ρY n) (ρY m) x) =
      sumEnd (fun k => ρY (n + m - 2 * (k : ℕ))) (cgEquiv hnm x))
    (v : Idx n m → ℂ) :
    cgT hnm ((dSpin n Y ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) +
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ dSpin m Y) *ᵥ v) =
      blockDiagonal' (fun k : Fin (min n m + 1) => dSpin (n + m - 2 * (k : ℕ)) Y) *ᵥ
        cgT hnm v := by
  obtain ⟨t, rfl⟩ := (tensorEquiv n m).surjective v
  rw [← tensorEquiv_diagEnd]
  simp only [cgT, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [psiTensor_diagEnd Y ρY hY, hcg, sumCoord_sumEnd Y ρY hY]

/-- A traceless `2 × 2` matrix in the basis `H, E, F` of `sl₂(ℂ)`. -/
lemma traceless_eq {X : Matrix (Fin 2) (Fin 2) ℂ} (h : X 1 1 = -X 0 0) :
    X = X 0 0 • matH + X 0 1 • matE + X 1 0 • matF := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [matH, matE, matF, h]

/-- **Lie-algebra Clebsch–Gordan.** For traceless `X`, `cgT` intertwines the differential
`dSpin n X ⊗ 1 + 1 ⊗ dSpin m X` of the diagonal action with `⊕_k dSpin (n+m-2k) X`. -/
lemma cgT_lie (hnm : 0 < n + m) {X : Matrix (Fin 2) (Fin 2) ℂ} (h : X 1 1 = -X 0 0)
    (v : Idx n m → ℂ) :
    cgT hnm ((dSpin n X ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) +
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ dSpin m X) *ᵥ v) =
      blockDiagonal' (fun k : Fin (min n m + 1) => dSpin (n + m - 2 * (k : ℕ)) X) *ᵥ
        cgT hnm v := by
  have hE := cgT_generator hnm matE (fun k => (ρE : Module.End ℂ (StandardSl2Module ℂ k)))
    (fun k w => dSpin_E w) (fun x => cgEquiv_tensorE hnm x)
  have hF := cgT_generator hnm matF (fun k => (ρF : Module.End ℂ (StandardSl2Module ℂ k)))
    (fun k w => dSpin_F w) (fun x => cgEquiv_tensorF hnm x)
  have hH := cgT_generator hnm matH (fun k => (ρH : Module.End ℂ (StandardSl2Module ℂ k)))
    (fun k w => dSpin_H w) (fun x => cgEquiv_tensorH hnm x)
  have hd : ∀ k, dSpin k X = X 0 0 • dSpin k matH + X 0 1 • dSpin k matE + X 1 0 • dSpin k matF :=
    fun k => by
      conv_lhs => rw [traceless_eq h]
      rw [dSpin_add, dSpin_add, dSpin_smul, dSpin_smul, dSpin_smul]
  set D : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Idx n m) (Idx n m) ℂ := fun Y =>
    dSpin n Y ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) +
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ dSpin m Y with hDdef
  set C : Matrix (Fin 2) (Fin 2) ℂ → Matrix (CGIdx n m) (CGIdx n m) ℂ := fun Y =>
    blockDiagonal' (fun k : Fin (min n m + 1) => dSpin (n + m - 2 * (k : ℕ)) Y) with hCdef
  have hD : D X = X 0 0 • D matH + X 0 1 • D matE + X 1 0 • D matF := by
    simp only [hDdef, hd, add_kronecker, kronecker_add, smul_kronecker, kronecker_smul, smul_add]
    abel
  have hC : C X = X 0 0 • C matH + X 0 1 • C matE + X 1 0 • C matF := by
    simp only [hCdef, hd]
    rw [show (fun k : Fin (min n m + 1) => X 0 0 • dSpin (n + m - 2 * (k : ℕ)) matH +
        X 0 1 • dSpin (n + m - 2 * (k : ℕ)) matE + X 1 0 • dSpin (n + m - 2 * (k : ℕ)) matF) =
        X 0 0 • (fun k : Fin (min n m + 1) => dSpin (n + m - 2 * (k : ℕ)) matH) +
        X 0 1 • (fun k : Fin (min n m + 1) => dSpin (n + m - 2 * (k : ℕ)) matE) +
        X 1 0 • (fun k : Fin (min n m + 1) => dSpin (n + m - 2 * (k : ℕ)) matF) from rfl,
      blockDiagonal'_add, blockDiagonal'_add, blockDiagonal'_smul, blockDiagonal'_smul,
      blockDiagonal'_smul]
  change cgT hnm (D X *ᵥ v) = C X *ᵥ cgT hnm v
  rw [hD, hC, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, smul_mulVec, map_add, map_add,
    map_smul, map_smul, map_smul, hH, hE, hF, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec,
    smul_mulVec]

/-- **Clebsch–Gordan for Spin(4) on the diagonal SU(2).** Restricted to the pairs `(g, g)`, the
spin-`(n/2, m/2)` representation is equivalent to `⊕_{k=0}^{min(n,m)}` spin `(n+m)/2 - k`:
`D^{n/2}(g) ⊗ D^{m/2}(g) ≅ ⊕_k D^{(n+m)/2-k}(g)`. -/
theorem spin4_diag_clebschGordan (n m : ℕ) :
    ∃ T : (Idx n m → ℂ) ≃ₗ[ℂ] (CGIdx n m → ℂ), ∀ (g : SU2) (v : Idx n m → ℂ),
      T (spin4Mat n m (g, g) *ᵥ v) = cgMat n m g *ᵥ T v := by
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hnm
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
    have hcard : Fintype.card (CGIdx 0 0) = Fintype.card (Idx 0 0) := by decide
    refine ⟨LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivOfCardEq hcard), fun g v => ?_⟩
    have h1 : spin4Mat 0 0 (g, g) = 1 := by
      rw [spin4Mat, spinMat_zero', one_kronecker_one]
    have h2 : cgMat 0 0 g = 1 := by
      rw [cgMat, ← blockDiagonal'_one]
      congr 1
      funext k
      have hk : (0 : ℕ) + 0 - 2 * (k : ℕ) = 0 := by omega
      rw [Pi.one_apply, hk, spinMat_zero']
    rw [h1, h2, one_mulVec, one_mulVec]
  · refine ⟨cgT hnm, fun g v => ?_⟩
    obtain ⟨X, hX, rfl⟩ := exists_Γ_one g
    have h1 : spin4Mat n m (Γ X hX 1, Γ X hX 1) =
        NormedSpace.exp (dSpin n X ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) +
          (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ dSpin m X) := by
      rw [spin4Mat, spinMat_Γ, spinMat_Γ, exp_kronecker]
    have h2 : cgMat n m (Γ X hX 1) =
        NormedSpace.exp (blockDiagonal' fun k : Fin (min n m + 1) =>
          dSpin (n + m - 2 * (k : ℕ)) X) := by
      rw [cgMat, exp_blockDiagonal'_fun]
      congr 1
      funext k
      rw [spinMat_Γ]
    rw [h1, h2]
    exact intertwine_exp' (cgT hnm).toLinearMap (cgT_lie hnm hX.trace_eq) v

end Lightlike.Spin4
