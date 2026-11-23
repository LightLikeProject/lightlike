import Mathlib
import Lightlike.Upstream.Spin4.Spin4Cover

/-!
# The Clifford-algebra spin group of `ℝ⁴ = ℍ` is `Spin(4)`

Mathlib defines `spinGroup Q` inside the Clifford algebra `CliffordAlgebra Q`. Take `ℝ⁴ = ℍ[ℝ]`
with the negative definite form `Q v = -|v|²` (`Quaternion.negNormSq`), so `v * v = -|v|²` in
`CliffordAlgebra Q` as for imaginary quaternions. We prove
`spinGroup negNormSq ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ]` (`Quaternion.spinGroupEquiv`), and with
`Quaternion.unitaryEquivSU2` that it is `SU(2) × SU(2)` (`Quaternion.spinGroupEquivSU2`).
The isomorphism carries `v ↦ x v x⁻¹` on vectors to the double cover `Quaternion.rotHom`
(`Quaternion.spinGroup_conj_ι`).

## Implementation notes

* `cliffordToMat : CliffordAlgebra negNormSq →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ]` sends `v` to
  `[[0, v], [-v̄, 0]]`. It sends Clifford conjugation to the quaternionic conjugate transpose, is
  surjective and, both sides having dimension 16, bijective.
* Even elements go to diagonal matrices `diag(a, b)`, elements of the spin group to pairs of unit
  quaternions. Surjectivity: every unit quaternion is a commutator, and products `v w` of unit
  vectors give the pairs `(-v w̄, -v̄ w)`.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989), Ch. I.
-/

open Module Submodule CliffordAlgebra Matrix
open scoped Quaternion

namespace Quaternion

/-! ## The quadratic form and the matrix representation -/

/-- The negative definite form `Q v = -|v|²` on `ℝ⁴ = ℍ[ℝ]`. -/
noncomputable def negNormSq : QuadraticForm ℝ ℍ[ℝ] :=
  -(LinearMap.BilinMap.toQuadraticMap (innerₗ ℍ[ℝ]))

lemma negNormSq_apply (v : ℍ[ℝ]) : negNormSq v = -normSq v := by
  simp [negNormSq, LinearMap.BilinMap.toQuadraticMap_apply, normSq_eq_norm_mul_self, sq]

/-- The vector `v` as the matrix `[[0, v], [-v̄, 0]]`. -/
def vecMat : ℍ[ℝ] →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] where
  toFun v := !![0, v; -star v, 0]
  map_add' u v := Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' r v := Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> simp

lemma vecMat_apply (v : ℍ[ℝ]) : vecMat v = !![0, v; -star v, 0] := rfl

lemma vecMat_mul_self (v : ℍ[ℝ]) : vecMat v * vecMat v = algebraMap ℝ _ (negNormSq v) := by
  rw [negNormSq_apply, vecMat_apply, Algebra.algebraMap_eq_smul_one]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Quaternion.self_mul_star, Quaternion.star_mul_self,
      Algebra.smul_def]

/-- `Cl(ℍ[ℝ], -|·|²)` as `2 × 2` quaternionic matrices: the algebra homomorphism with
`ι v ↦ [[0, v], [-v̄, 0]]`. -/
noncomputable def cliffordToMat :
    CliffordAlgebra negNormSq →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  CliffordAlgebra.lift negNormSq ⟨vecMat, vecMat_mul_self⟩

lemma cliffordToMat_ι (v : ℍ[ℝ]) : cliffordToMat (ι negNormSq v) = vecMat v :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- Clifford conjugation becomes the quaternionic conjugate transpose. -/
lemma cliffordToMat_star (x : CliffordAlgebra negNormSq) :
    cliffordToMat (star x) = (cliffordToMat x)ᴴ := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [star_algebraMap, AlgHom.commutes, Matrix.algebraMap_eq_diagonal, diagonal_conjTranspose]
    congr 1
    funext i
    simp
  | ι v =>
    rw [star_ι, map_neg, cliffordToMat_ι, vecMat_apply]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
  | mul a b ha hb => rw [star_mul, map_mul, map_mul, ha, hb, conjTranspose_mul]
  | add a b ha hb => rw [star_add, map_add, map_add, ha, hb, conjTranspose_add]

/-! ## `cliffordToMat` is an isomorphism -/

/-- `dim Cl(ℝ⁴) = 2⁴ = 16`. -/
lemma finrank_cliffordAlgebra_negNormSq :
    Module.finrank ℝ (CliffordAlgebra negNormSq) = 16 := by
  rw [(CliffordAlgebra.equivExterior negNormSq).finrank_eq,
    Module.finrank_eq_card_basis (basisH.ExteriorAlgebra), Fintype.card_finset, Fintype.card_fin]
  norm_num

/-- `dim M₂(ℍ) = 16`. -/
lemma finrank_matrix_quaternion : Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) = 16 := by
  rw [Module.finrank_matrix, Quaternion.finrank_eq_four]
  simp

private def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
private def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
private def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

lemma cliffordToMat_ι_mul_ι (u w : ℍ[ℝ]) :
    cliffordToMat (ι negNormSq u * ι negNormSq w) =
      !![-(u * star w), 0; 0, -(star u * w)] := by
  rw [map_mul, cliffordToMat_ι, cliffordToMat_ι, vecMat_apply, vecMat_apply]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `cliffordToMat` is surjective. -/
lemma cliffordToMat_surjective : Function.Surjective cliffordToMat := by
  have hR : ∀ M, M ∈ cliffordToMat.range → ∀ N, N ∈ cliffordToMat.range →
      M * N ∈ cliffordToMat.range := fun M hM N hN => Subalgebra.mul_mem _ hM hN
  have hvec : ∀ v, vecMat v ∈ cliffordToMat.range := fun v => ⟨ι negNormSq v, cliffordToMat_ι v⟩
  have hpair : ∀ u w, (!![-(u * star w), 0; 0, -(star u * w)] : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) ∈
      cliffordToMat.range := fun u w => ⟨ι negNormSq u * ι negNormSq w, cliffordToMat_ι_mul_ι u w⟩
  have hD : ∀ w : ℍ[ℝ], (!![w, 0; 0, star w] : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) ∈
      cliffordToMat.range := by
    intro w
    have := hpair 1 (-star w)
    simpa using this
  have hP0 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) ∈ cliffordToMat.range := by
    have h1 := hR _ (hD qi) _ (hpair qj qk)
    have h2 : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) =
        (1 / 2 : ℝ) • (1 - !![qi, 0; 0, star qi] * !![-(qj * star qk), 0; 0, -(star qj * qk)]) := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> ext <;> norm_num [qi, qj, qk]
    rw [h2]
    exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) h1) _
  have hP1 : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) ∈ cliffordToMat.range := by
    have : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) = 1 - !![1, 0; 0, 0] := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp
    rw [this]
    exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) hP0
  have hsingle : ∀ (a b : Fin 2) (w : ℍ[ℝ]), Matrix.single a b w ∈ cliffordToMat.range := by
    intro a b w
    fin_cases a <;> fin_cases b
    · convert hR _ hP0 _ (hD w) using 1
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
    · convert hR _ hP0 _ (hvec w) using 1
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, vecMat_apply]
    · convert hR _ hP1 _ (hvec (-star w)) using 1
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, vecMat_apply]
    · convert hR _ hP1 _ (hD (star w)) using 1
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  intro M
  have hM : M ∈ cliffordToMat.range := by
    rw [Matrix.matrix_eq_sum_single M]
    exact Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ => hsingle a b (M a b)
  obtain ⟨x, hx⟩ := hM
  exact ⟨x, hx⟩

/-- `cliffordToMat` is injective (a surjection between spaces of equal dimension 16). -/
lemma cliffordToMat_injective : Function.Injective cliffordToMat := by
  have : FiniteDimensional ℝ (CliffordAlgebra negNormSq) :=
    Module.finite_of_finrank_pos (by rw [finrank_cliffordAlgebra_negNormSq]; norm_num)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := cliffordToMat.toLinearMap)
    (finrank_cliffordAlgebra_negNormSq.trans finrank_matrix_quaternion.symm)).mpr
    cliffordToMat_surjective

/-! ## Every unit quaternion is a commutator -/

/-- `c₀ = |p|² - q p` (`p`, `q` the pure parts of `x`, `y`) satisfies `c₀ x = y c₀` when `x` and
`y` have the same real part and pure parts of the same length. -/
lemma conj_witness (x y : ℍ[ℝ]) (hre : x.re = y.re)
    (hs : x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 = y.imI ^ 2 + y.imJ ^ 2 + y.imK ^ 2) :
    ((x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2) • (1 : ℍ[ℝ]) - (y - (y.re : ℍ[ℝ])) * (x - (x.re : ℍ[ℝ]))) * x =
      y * ((x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2) • (1 : ℍ[ℝ]) -
        (y - (y.re : ℍ[ℝ])) * (x - (x.re : ℍ[ℝ]))) := by
  ext <;> simp <;> rw [hre] <;>
    first
    | ring1
    | linear_combination x.imI * hs | linear_combination (-x.imI) * hs
    | linear_combination x.imJ * hs | linear_combination (-x.imJ) * hs
    | linear_combination x.imK * hs

/-- A nonzero intertwiner `c x = y c` can be normalised to a unit quaternion `u` with
`u x ū = y`. -/
lemma exists_unit_conj_of_mul_eq {c x y : ℍ[ℝ]} (hc : c ≠ 0) (h : c * x = y * c) :
    ∃ u : ℍ[ℝ], normSq u = 1 ∧ u * x * star u = y := by
  have hN : normSq c ≠ 0 := normSq_ne_zero.mpr hc
  set t : ℝ := (Real.sqrt (normSq c))⁻¹
  have ht : t * t * normSq c = 1 := by
    have h0 : 0 ≤ normSq c := normSq_nonneg
    simp only [t]
    rw [← mul_inv, Real.mul_self_sqrt h0, inv_mul_cancel₀ hN]
  refine ⟨(t : ℍ[ℝ]) * c, ?_, ?_⟩
  · rw [map_mul, normSq_coe, sq]; exact ht
  · calc (t : ℍ[ℝ]) * c * x * star ((t : ℍ[ℝ]) * c)
        = (t : ℍ[ℝ]) * ((c * x) * star c) * t := by rw [star_mul, star_coe]; simp only [mul_assoc]
      _ = (t : ℍ[ℝ]) * (y * (c * star c)) * t := by rw [h]; simp only [mul_assoc]
      _ = y * ((t * t * normSq c : ℝ) : ℍ[ℝ]) := by
          rw [self_mul_star]
          ext <;> simp <;> ring
      _ = y := by rw [ht, coe_one, mul_one]

/-- Unit quaternions with the same real part are conjugate by a unit quaternion. -/
lemma exists_unit_conj {x y : ℍ[ℝ]} (hx : normSq x = 1) (hy : normSq y = 1) (hre : x.re = y.re) :
    ∃ u : ℍ[ℝ], normSq u = 1 ∧ u * x * star u = y := by
  have hs : x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 = y.imI ^ 2 + y.imJ ^ 2 + y.imK ^ 2 := by
    rw [normSq_def'] at hx hy; rw [hre] at hx; linarith
  set c := (x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2) • (1 : ℍ[ℝ]) -
    (y - (y.re : ℍ[ℝ])) * (x - (x.re : ℍ[ℝ]))
  by_cases hc : c ≠ 0
  · exact exists_unit_conj_of_mul_eq hc (conj_witness x y hre hs)
  push Not at hc
  have hre0 := congrArg (fun z : ℍ[ℝ] => z.re) hc
  simp only [c] at hre0
  simp at hre0
  have hpq : y.imI = -x.imI ∧ y.imJ = -x.imJ ∧ y.imK = -x.imK := by
    have : (y.imI + x.imI) ^ 2 + (y.imJ + x.imJ) ^ 2 + (y.imK + x.imK) ^ 2 = 0 := by
      nlinarith [hre0, hs]
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (y.imI + x.imI), sq_nonneg (y.imJ + x.imJ),
      sq_nonneg (y.imK + x.imK)]
  obtain ⟨h1, h2, h3⟩ := hpq
  have hy' : y = ⟨x.re, -x.imI, -x.imJ, -x.imK⟩ := by ext <;> simp [h1, h2, h3, hre]
  rw [hy']
  by_cases hp : x.imJ = 0 ∧ x.imK = 0
  · by_cases hp1 : x.imI = 0
    · refine ⟨1, by simp, ?_⟩
      ext <;> simp [hp1, hp.1, hp.2]
    · refine exists_unit_conj_of_mul_eq (c := ⟨0, 0, 1, 0⟩) (by simp [Quaternion.ext_iff]) ?_
      ext <;> simp [hp.1, hp.2]
  · refine exists_unit_conj_of_mul_eq (c := ⟨0, 0, x.imK, -x.imJ⟩) ?_ ?_
    · intro h0
      apply hp
      have := congrArg (fun z : ℍ[ℝ] => (z.imJ, z.imK)) h0
      simp at this
      exact ⟨by linarith [this.2], this.1⟩
    · ext <;> simp <;> ring

/-- Every unit quaternion is a commutator `c d c̄ d̄` of unit quaternions. -/
lemma exists_commutator {a : ℍ[ℝ]} (ha : normSq a = 1) :
    ∃ c d : ℍ[ℝ], normSq c = 1 ∧ normSq d = 1 ∧ c * d * star c * star d = a := by
  obtain ⟨e, he, he0⟩ : ∃ e : ℍ[ℝ], e ∈ (ℝ ∙ (a - 1))ᗮ ∧ e ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro hbot
    have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ (a - 1))
    rw [hbot, finrank_bot, add_zero, Quaternion.finrank_eq_four] at h1
    have h2 := finrank_span_le_card (R := ℝ) ({a - 1} : Set ℍ[ℝ])
    simp at h2
    omega
  have he0' : 0 < normSq e := lt_of_le_of_ne normSq_nonneg (Ne.symm (normSq_ne_zero.mpr he0))
  set t : ℝ := (Real.sqrt (normSq e))⁻¹
  set d : ℍ[ℝ] := (t : ℍ[ℝ]) * star e
  have hd : normSq d = 1 := by
    simp only [d, map_mul, normSq_coe, normSq_star, t, inv_pow, Real.sq_sqrt he0'.le]
    exact inv_mul_cancel₀ he0'.ne'
  have hred : (a * d).re = d.re := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_def] at he
    have h1 : (a * star e).re = (star e).re := by
      rw [sub_mul, one_mul, re_sub] at he; linarith
    have e1 : a * d = (t : ℍ[ℝ]) * (a * star e) := by
      simp only [d]; rw [← mul_assoc, ← coe_commutes, mul_assoc]
    rw [e1]
    simp only [d, coe_mul_eq_smul, re_smul, smul_eq_mul, h1]
  have had : normSq (a * d) = 1 := by rw [map_mul, ha, hd, one_mul]
  obtain ⟨c, hc, hcd⟩ := exists_unit_conj hd had hred.symm
  refine ⟨c, d, hc, hd, ?_⟩
  rw [hcd, mul_assoc, self_mul_star, hd, coe_one, mul_one]

/-! ## The spin group -/

/-- Even elements of `Cl(Q)` are diagonal matrices. -/
lemma cliffordToMat_offDiag {x : CliffordAlgebra negNormSq} (hx : x ∈ evenOdd negNormSq 0) :
    cliffordToMat x 0 1 = 0 ∧ cliffordToMat x 1 0 = 0 := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r => simp [Matrix.algebraMap_eq_diagonal]
  | add x y hx hy ihx ihy => simp [ihx.1, ihy.1, ihx.2, ihy.2]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, cliffordToMat_ι_mul_ι]
    simp [Matrix.mul_apply, Fin.sum_univ_two, ih.1, ih.2]

lemma cliffordToMat_offDiag_spinGroup (x : spinGroup negNormSq) :
    cliffordToMat (x : CliffordAlgebra negNormSq) 0 1 = 0 ∧
      cliffordToMat (x : CliffordAlgebra negNormSq) 1 0 = 0 :=
  cliffordToMat_offDiag (spinGroup.mem_even x.2)

/-- The `(k, k)` entry of a product of two elements of the spin group. -/
lemma cliffordToMat_mul_diag (x y : spinGroup negNormSq) (k : Fin 2) :
    cliffordToMat ((x : CliffordAlgebra negNormSq) * y) k k =
      cliffordToMat (x : CliffordAlgebra negNormSq) k k *
        cliffordToMat (y : CliffordAlgebra negNormSq) k k := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨hx1, hx2⟩ := cliffordToMat_offDiag_spinGroup x
  fin_cases k <;> simp [hx1, hx2]

/-- The diagonal entries of an element of the spin group are unit quaternions. -/
lemma cliffordToMat_diag_mem_unitary (x : spinGroup negNormSq) (k : Fin 2) :
    cliffordToMat (x : CliffordAlgebra negNormSq) k k ∈ unitary ℍ[ℝ] := by
  obtain ⟨hx1, hx2⟩ := cliffordToMat_offDiag_spinGroup x
  have h1 := congrArg (fun M => M k k)
    (congrArg cliffordToMat (spinGroup.star_mul_self_of_mem x.2))
  have h2 := congrArg (fun M => M k k)
    (congrArg cliffordToMat (spinGroup.mul_star_self_of_mem x.2))
  simp only [map_mul, cliffordToMat_star, map_one, Matrix.mul_apply, Fin.sum_univ_two,
    conjTranspose_apply] at h1 h2
  rw [Unitary.mem_iff]
  fin_cases k <;> simp_all

/-- The spin group as pairs of unit quaternions: `x ↦ (a, b)` where `x ↦ diag(a, b)`. -/
noncomputable def spinGroupToUnitary :
    spinGroup negNormSq →* unitary ℍ[ℝ] × unitary ℍ[ℝ] where
  toFun x := (⟨_, cliffordToMat_diag_mem_unitary x 0⟩, ⟨_, cliffordToMat_diag_mem_unitary x 1⟩)
  map_one' := Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp))
  map_mul' x y := Prod.ext (Subtype.ext (cliffordToMat_mul_diag x y 0))
    (Subtype.ext (cliffordToMat_mul_diag x y 1))

/-- `spinGroupToUnitary` is injective. -/
lemma spinGroupToUnitary_injective : Function.Injective spinGroupToUnitary := by
  intro x y h
  have h0 := congrArg (fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] => (p.1 : ℍ[ℝ])) h
  have h1 := congrArg (fun p : unitary ℍ[ℝ] × unitary ℍ[ℝ] => (p.2 : ℍ[ℝ])) h
  simp only [spinGroupToUnitary, MonoidHom.coe_mk, OneHom.coe_mk] at h0 h1
  obtain ⟨hx1, hx2⟩ := cliffordToMat_offDiag_spinGroup x
  obtain ⟨hy1, hy2⟩ := cliffordToMat_offDiag_spinGroup y
  apply Subtype.ext
  apply cliffordToMat_injective
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp_all

/-- A unit vector is in the pin group. -/
lemma ι_mem_pinGroup {u : ℍ[ℝ]} (hu : normSq u = 1) : ι negNormSq u ∈ pinGroup negNormSq := by
  have hsq : ι negNormSq u * ι negNormSq u = -1 := by
    rw [ι_sq_scalar, negNormSq_apply, hu, map_neg, map_one]
  refine ⟨⟨⟨ι negNormSq u, -ι negNormSq u, by rw [mul_neg, hsq, neg_neg],
    by rw [neg_mul, hsq, neg_neg]⟩, Subgroup.subset_closure ⟨u, rfl⟩, rfl⟩, ?_⟩
  change ι negNormSq u ∈ unitary (CliffordAlgebra negNormSq)
  rw [Unitary.mem_iff, star_ι]
  exact ⟨by rw [neg_mul, hsq, neg_neg], by rw [mul_neg, hsq, neg_neg]⟩

/-- The product of two unit vectors is in the spin group. -/
lemma ι_mul_ι_mem_spinGroup {u w : ℍ[ℝ]} (hu : normSq u = 1) (hw : normSq w = 1) :
    ι negNormSq u * ι negNormSq w ∈ spinGroup negNormSq :=
  ⟨Submonoid.mul_mem _ (ι_mem_pinGroup hu) (ι_mem_pinGroup hw),
    ι_mul_ι_mem_evenOdd_zero negNormSq u w⟩

/-- The pairs `(-u w̄, -ū w)`, for unit `u`, `w`, are in the image. -/
lemma pair_mem_range_spinGroupToUnitary {u w : ℍ[ℝ]} (hu : normSq u = 1) (hw : normSq w = 1)
    (h1 : -(u * star w) ∈ unitary ℍ[ℝ]) (h2 : -(star u * w) ∈ unitary ℍ[ℝ]) :
    (⟨_, h1⟩, ⟨_, h2⟩) ∈ spinGroupToUnitary.range :=
  ⟨⟨_, ι_mul_ι_mem_spinGroup hu hw⟩, by
    ext <;> simp [spinGroupToUnitary, cliffordToMat_ι_mul_ι]⟩

/-- `(c, c̄)` is in the image. -/
lemma conj_pair_mem_range (c : unitary ℍ[ℝ]) : (c, star c) ∈ spinGroupToUnitary.range := by
  have hc := normSq_eq_one_of_mem_unitary c
  have hw : normSq (-star (c : ℍ[ℝ])) = 1 := by rw [normSq_neg, normSq_star, hc]
  obtain ⟨x, hx⟩ := pair_mem_range_spinGroupToUnitary (u := 1) (w := -star (c : ℍ[ℝ]))
    (by simp) hw (by simp) (by simp)
  refine ⟨x, ?_⟩
  rw [hx]
  ext <;> simp

/-- A subgroup of `Sp(1) × Sp(1)` containing every pair `(c, c̄)` is everything (every unit
quaternion is a commutator, and `(c, c̄)(d, d̄)(c̄ d̄, d c) = (c d c̄ d̄, 1)`). -/
lemma eq_top_of_conj_pairs (H : Subgroup (unitary ℍ[ℝ] × unitary ℍ[ℝ]))
    (hH : ∀ c : unitary ℍ[ℝ], (c, star c) ∈ H) : H = ⊤ := by
  have hleft : ∀ a : unitary ℍ[ℝ], (a, 1) ∈ H := by
    intro a
    obtain ⟨c, d, hc, hd, hcd⟩ := exists_commutator (normSq_eq_one_of_mem_unitary a)
    let c' : unitary ℍ[ℝ] := ⟨c, mem_unitary_of_normSq_eq_one hc⟩
    let d' : unitary ℍ[ℝ] := ⟨d, mem_unitary_of_normSq_eq_one hd⟩
    have := H.mul_mem (H.mul_mem (hH c') (hH d')) (hH (star c' * star d'))
    convert this using 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp only [Prod.fst_mul, Submonoid.coe_mul, Unitary.coe_star, c', d']
      rw [← hcd]; simp only [mul_assoc]
    · simp only [Prod.snd_mul, Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, c', d',
        OneMemClass.coe_one]
      rw [show star c * star d * (d * c) = star c * (star d * d) * c by simp only [mul_assoc],
        Unitary.star_mul_self_of_mem d'.2, mul_one, Unitary.star_mul_self_of_mem c'.2]
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have hb : ((1 : unitary ℍ[ℝ]), b) ∈ H := by
    have := H.mul_mem (hH (star b)) (hleft b)
    convert this using 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp
    · simp
  have := H.mul_mem (hleft a) hb
  convert this using 1
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp

/-- The spin group maps onto all pairs of unit quaternions. -/
lemma spinGroupToUnitary_surjective : Function.Surjective spinGroupToUnitary := by
  rw [← MonoidHom.range_eq_top]
  exact eq_top_of_conj_pairs _ conj_pair_mem_range

/-- **Mathlib's Clifford-algebra spin group of `(ℝ⁴, -|·|²)` is the group of pairs of unit
quaternions.** -/
noncomputable def spinGroupEquiv : spinGroup negNormSq ≃* unitary ℍ[ℝ] × unitary ℍ[ℝ] :=
  MulEquiv.ofBijective spinGroupToUnitary
    ⟨spinGroupToUnitary_injective, spinGroupToUnitary_surjective⟩

/-- **The spin group of `(ℝ⁴, -|·|²)` is `Spin(4) = SU(2) × SU(2)`.** -/
noncomputable def spinGroupEquivSU2 :
    spinGroup negNormSq ≃*
      Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  spinGroupEquiv.trans (MulEquiv.prodCongr unitaryEquivSU2 unitaryEquivSU2)

/-- **The isomorphism is the double cover.** Conjugating a vector by `x` in the Clifford algebra
is the rotation `rotHom (spinGroupEquiv x)` of `ℝ⁴ = ℍ[ℝ]`: `x v x̄ = p v q̄`. -/
theorem spinGroup_conj_ι (x : spinGroup negNormSq) (v : ℍ[ℝ]) :
    (x : CliffordAlgebra negNormSq) * ι negNormSq v * star (x : CliffordAlgebra negNormSq) =
      ι negNormSq ((rotHom (spinGroupEquiv x) : ℍ[ℝ] ≃ₗᵢ[ℝ] ℍ[ℝ]) v) := by
  apply cliffordToMat_injective
  obtain ⟨h01, h10⟩ := cliffordToMat_offDiag_spinGroup x
  rw [rotHom_apply, map_mul, map_mul, cliffordToMat_star, cliffordToMat_ι, cliffordToMat_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, vecMat_apply, h01, h10, spinGroupEquiv,
      spinGroupToUnitary, mul_assoc]

/-- Trust check: the spin element `u w` (unit vectors) maps to the pair `(-u w̄, -ū w)`. -/
example {u w : ℍ[ℝ]} (hu : normSq u = 1) (hw : normSq w = 1) :
    ((spinGroupEquiv ⟨_, ι_mul_ι_mem_spinGroup hu hw⟩).1 : ℍ[ℝ]) = -(u * star w) ∧
      ((spinGroupEquiv ⟨_, ι_mul_ι_mem_spinGroup hu hw⟩).2 : ℍ[ℝ]) = -(star u * w) := by
  constructor <;> simp [spinGroupEquiv, spinGroupToUnitary, cliffordToMat_ι_mul_ι]

/-- Trust check: the spin element `1 * 1` (unit vector `1` twice) maps to `-1 ≠ 1`, the
nontrivial element of the kernel of the double cover. -/
example : ((spinGroupEquiv ⟨_, ι_mul_ι_mem_spinGroup (u := 1) (w := 1) (by simp) (by simp)⟩).1 :
    ℍ[ℝ]) ≠ 1 := by
  simp only [spinGroupEquiv, spinGroupToUnitary]
  simp
  intro h
  have h2 := congrArg (fun q : ℍ[ℝ] => q.re) h
  simp [negNormSq_apply, Matrix.algebraMap_eq_diagonal] at h2
  norm_num at h2

end Quaternion
