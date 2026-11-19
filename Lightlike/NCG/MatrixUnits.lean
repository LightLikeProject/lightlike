import Lightlike.NCG.Complexification

/-!
# Matrix units on a Hilbert space

A **system of matrix units** of `⊕ₖ M_dₖ(ℂ)` on `H` is a family of operators `U k x y` with
`U k x y U k z w = δ_yz U k x w`, `U k x y U l z w = 0` for `k ≠ l`, `U k x y* = U k y x` and `∑ₖ ∑ₓ U k x x = 1`. Then
`σ(Y) = ∑ₖ ∑ₓ ∑_y Y k x y U k x y` is a complex `*`-homomorphism `⊕ₖ M_dₖ(ℂ) → B(H)`, faithful when every `U k x x ≠ 0`
(`U k x x' σ(Y) U k y x = Y k x' y U k x x`, here with `x = x'`). This is how the irreducible representations of a real
summand (T. Krajewski, arXiv:hep-th/9701081, Section 3.1, p. 10) are realized on `H`.

* `MatrixUnits`, `MatrixUnits.toFun`, `MatrixUnits.U_mul_toFun`, `MatrixUnits.toFun_mul_U`;
* `MatrixUnits.hom`: the `*`-homomorphism; `MatrixUnits.hom_injective`, `MatrixUnits.U_diag_eq`, `MatrixUnits.U_ne_zero`,
  `MatrixUnits.hom_injective_of_block`: faithful when every block unit `∑ₓ U k x x` is nonzero;
* `MatrixUnits.hom_mem_span`: `σ(Y)` lies in every submodule containing the units.
-/

namespace Lightlike.NCG

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]

variable (d H) in
/-- **A system of matrix units** of `⊕ₖ M_dₖ(ℂ)` on `H`. -/
structure MatrixUnits where
  /-- The units. -/
  U : ∀ k, Fin (d k) → Fin (d k) → (H →L[ℂ] H)
  /-- `U k x y U k z w = δ_yz U k x w`. -/
  mul_same : ∀ k x y z w, U k x y * U k z w = if y = z then U k x w else 0
  /-- Units of different blocks multiply to `0`. -/
  mul_ne : ∀ k l, k ≠ l → ∀ x y z w, U k x y * U l z w = 0
  /-- `U k x y* = U k y x`. -/
  star_U : ∀ k x y, star (U k x y) = U k y x
  /-- `∑ₖ ∑ₓ U k x x = 1`. -/
  sum_U : ∑ k, ∑ x, U k x x = 1

namespace MatrixUnits

variable (M : MatrixUnits d H)

/-- `σ(Y) = ∑ₖ ∑ₓ ∑_y Y k x y U k x y`. -/
def toFun (Y : MatSum d) : H →L[ℂ] H := ∑ k, ∑ x, ∑ y, Y k x y • M.U k x y

/-- `U k x y σ(Z) = ∑_w Z k y w U k x w`. -/
lemma U_mul_toFun (k : ι) (x y : Fin (d k)) (Z : MatSum d) :
    M.U k x y * M.toFun Z = ∑ w, Z k y w • M.U k x w := by
  simp only [toFun, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_eq_single k]
  · simp only [M.mul_same, smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  · intro l _ hl
    simp only [M.mul_ne k l (Ne.symm hl), smul_zero, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- `σ(Z) U k x y = ∑_v Z k v x U k v y`. -/
lemma toFun_mul_U (k : ι) (x y : Fin (d k)) (Z : MatSum d) :
    M.toFun Z * M.U k x y = ∑ v, Z k v x • M.U k v y := by
  simp only [toFun, Finset.sum_mul, smul_mul_assoc]
  rw [Finset.sum_eq_single k]
  · simp only [M.mul_same, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro l _ hl
    simp only [M.mul_ne l k hl, smul_zero, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- `σ` is additive. -/
lemma toFun_add (Y Z : MatSum d) : M.toFun (Y + Z) = M.toFun Y + M.toFun Z := by
  simp only [toFun, Pi.add_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/-- `σ` is complex-linear. -/
lemma toFun_smul (c : ℂ) (Y : MatSum d) : M.toFun (c • Y) = c • M.toFun Y := by
  simp only [toFun, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- `σ(1) = 1`. -/
lemma toFun_one : M.toFun 1 = 1 := by
  simp only [toFun, Pi.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, M.sum_U]

/-- `σ` is multiplicative. -/
lemma toFun_mul (Y Z : MatSum d) : M.toFun (Y * Z) = M.toFun Y * M.toFun Z := by
  conv_rhs => rw [toFun]
  simp only [Finset.sum_mul, smul_mul_assoc, U_mul_toFun, Finset.smul_sum, smul_smul]
  simp only [toFun, Pi.mul_apply, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm

/-- `σ(Y*) = σ(Y)*`. -/
lemma toFun_star (Y : MatSum d) : M.toFun (star Y) = star (M.toFun Y) := by
  simp only [toFun, star_sum, star_smul, M.star_U, Pi.star_apply, Matrix.star_apply]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- **The `*`-homomorphism of a system of matrix units.** -/
def hom : MatSum d →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := M.toFun
  map_one' := M.toFun_one
  map_mul' := M.toFun_mul
  map_zero' := by simp only [toFun, Pi.zero_apply, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]
  map_add' := M.toFun_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (M.toFun_smul c 1).trans (by rw [M.toFun_one])
  map_star' := M.toFun_star

/-- `σ(Y) = ∑ₖ ∑ₓ ∑_y Y k x y U k x y`. -/
lemma hom_apply (Y : MatSum d) : M.hom Y = ∑ k, ∑ x, ∑ y, Y k x y • M.U k x y := rfl

/-- `U k x x σ(Y) U k y x = Y k x y U k x x`. -/
lemma U_mul_hom_mul_U (Y : MatSum d) (k : ι) (x y : Fin (d k)) :
    M.U k x x * M.hom Y * M.U k y x = Y k x y • M.U k x x := by
  rw [show M.hom Y = M.toFun Y from rfl, U_mul_toFun, Finset.sum_mul]
  simp only [smul_mul_assoc, M.mul_same, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Faithfulness**: if every `U k x x ≠ 0`, then `σ` is injective. -/
theorem hom_injective (hne : ∀ k x, M.U k x x ≠ 0) : Function.Injective M.hom := by
  rw [injective_iff_map_eq_zero]
  intro Y hY
  funext k; ext x y
  have h := M.U_mul_hom_mul_U Y k x y
  rw [hY, mul_zero, zero_mul] at h
  rw [Pi.zero_apply, Matrix.zero_apply]
  exact (smul_eq_zero.mp h.symm).resolve_right (hne k x)

/-- `U k y y = U k y x U k x x U k x y`. -/
lemma U_diag_eq (k : ι) (x y : Fin (d k)) : M.U k y y = M.U k y x * M.U k x x * M.U k x y := by
  rw [M.mul_same, if_pos rfl, M.mul_same, if_pos rfl]

/-- **A nonzero block has nonzero diagonal units**: if one `U k x x = 0`, all `U k y y = 0` and the block unit
`∑_y U k y y` vanishes. -/
lemma U_ne_zero (k : ι) (hk : ∑ y, M.U k y y ≠ 0) (x : Fin (d k)) : M.U k x x ≠ 0 := by
  intro hx
  apply hk
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [M.U_diag_eq k x y, hx, mul_zero, zero_mul]

/-- **Faithfulness from the block units**: if every block unit `∑ₓ U k x x` is nonzero, `σ` is injective. -/
theorem hom_injective_of_block (hk : ∀ k, ∑ x, M.U k x x ≠ 0) : Function.Injective M.hom :=
  M.hom_injective fun k x => M.U_ne_zero k (hk k) x

/-- **`σ(Y)` lies in every submodule containing the units.** -/
lemma hom_mem (p : Submodule ℂ (H →L[ℂ] H)) (hp : ∀ k x y, M.U k x y ∈ p) (Y : MatSum d) : M.hom Y ∈ p :=
  Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun y _ =>
    Submodule.smul_mem _ _ (hp k x y)

end MatrixUnits

end

end Lightlike.NCG
