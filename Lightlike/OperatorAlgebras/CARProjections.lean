import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Finset.NoncommProd

/-!
# Products of commuting projections and the Bonferroni inequality

For a family `n k` of commuting symmetric idempotent operators on a Hilbert space (the number operators `c_k a_k`
of CAR modes), the projections `Q k = 1 - n k` commute, and for a finite set `F` the product
`PF F = ∏_{k ∈ F} Q k` is a symmetric idempotent with `‖PF F v‖² ≥ ‖v‖² - ∑_{k ∈ F} ‖n k v‖²`
(`norm_sq_prod_ge`). This is the lower bound used to show that a Bogoliubov vacuum exists when the antilinear
part is small in the Hilbert-Schmidt norm.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CARProjections

variable {ι : Type*} {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  (n : ι → (Γ →L[ℂ] Γ))

/-- The hypotheses: commuting, symmetric idempotents. -/
structure IsProjFamily : Prop where
  /-- Each `n k` is symmetric. -/
  symm : ∀ k x y, ⟪n k x, y⟫_ℂ = ⟪x, n k y⟫_ℂ
  /-- Each `n k` is idempotent. -/
  idem : ∀ k, n k * n k = n k
  /-- The `n k` commute. -/
  comm : ∀ k l, n k * n l = n l * n k

variable {n}

/-- The complementary projection `1 - n k`. -/
def Q (n : ι → (Γ →L[ℂ] Γ)) (k : ι) : Γ →L[ℂ] Γ := 1 - n k

lemma commute_Q (h : IsProjFamily n) (k l : ι) : Commute (Q n k) (Q n l) := by
  show Q n k * Q n l = Q n l * Q n k
  simp only [Q, sub_mul, mul_sub, one_mul, mul_one, h.comm k l]
  abel

/-- The product `∏_{k ∈ F} (1 - n k)`. -/
noncomputable def PF (h : IsProjFamily n) (F : Finset ι) : Γ →L[ℂ] Γ :=
  F.noncommProd (Q n) (fun k _ l _ _ => commute_Q h k l)

lemma PF_empty (h : IsProjFamily n) : PF h ∅ = 1 := rfl

lemma PF_insert [DecidableEq ι] (h : IsProjFamily n) {F : Finset ι} {k : ι} (hk : k ∉ F) :
    PF h (insert k F) = Q n k * PF h F := by
  unfold PF
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ hk

section

variable [DecidableEq ι] (h : IsProjFamily n)
include h

lemma Q_symm (k : ι) (x y : Γ) : ⟪Q n k x, y⟫_ℂ = ⟪x, Q n k y⟫_ℂ := by
  simp only [Q, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_left, inner_sub_right,
    h.symm k x y]

lemma Q_idem (k : ι) : Q n k * Q n k = Q n k := by
  simp only [Q, sub_mul, mul_sub, one_mul, mul_one, h.idem k]; abel

lemma Q_mul_n (k : ι) : Q n k * n k = 0 := by
  simp only [Q, sub_mul, one_mul, h.idem k, sub_self]

lemma PF_comm_Q (F : Finset ι) (l : ι) : Q n l * PF h F = PF h F * Q n l := by
  induction F using Finset.induction_on with
  | empty => rw [PF_empty, mul_one, one_mul]
  | insert k F hk ih =>
    rw [PF_insert h hk, ← mul_assoc, (commute_Q h l k).eq, mul_assoc, ih, mul_assoc]

lemma PF_comm_n (F : Finset ι) (l : ι) : n l * PF h F = PF h F * n l := by
  have := PF_comm_Q h F l
  simp only [Q, sub_mul, mul_sub, one_mul, mul_one] at this
  have h2 : PF h F - n l * PF h F = PF h F - PF h F * n l := by simpa using this
  exact sub_right_injective h2

lemma PF_symm (F : Finset ι) (x y : Γ) : ⟪PF h F x, y⟫_ℂ = ⟪x, PF h F y⟫_ℂ := by
  induction F using Finset.induction_on generalizing x y with
  | empty => simp [PF_empty]
  | insert k F hk ih =>
    rw [PF_insert h hk, ContinuousLinearMap.mul_apply, Q_symm h, ih, ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← PF_comm_Q h F k]

lemma PF_idem (F : Finset ι) : PF h F * PF h F = PF h F := by
  induction F using Finset.induction_on with
  | empty => rw [PF_empty, mul_one]
  | insert k F hk ih =>
    rw [PF_insert h hk]
    calc Q n k * PF h F * (Q n k * PF h F) = Q n k * (PF h F * Q n k) * PF h F := by simp only [mul_assoc]
      _ = Q n k * (Q n k * PF h F) * PF h F := by rw [← PF_comm_Q h F k]
      _ = (Q n k * Q n k) * (PF h F * PF h F) := by simp only [mul_assoc]
      _ = Q n k * PF h F := by rw [Q_idem h, ih]

lemma norm_PF_le (F : Finset ι) (x : Γ) : ‖PF h F x‖ ≤ ‖x‖ := by
  have h1 : ⟪PF h F x, PF h F x⟫_ℂ = ⟪x, PF h F x⟫_ℂ := by
    rw [PF_symm h, ← ContinuousLinearMap.mul_apply, PF_idem h]
  have h2 : ‖PF h F x‖ ^ 2 ≤ ‖x‖ * ‖PF h F x‖ := by
    have := congrArg RCLike.re h1
    rw [inner_self_eq_norm_sq] at this
    calc ‖PF h F x‖ ^ 2 = RCLike.re ⟪x, PF h F x⟫_ℂ := by simpa using this
      _ ≤ ‖⟪x, PF h F x⟫_ℂ‖ := RCLike.re_le_norm _
      _ ≤ ‖x‖ * ‖PF h F x‖ := norm_inner_le_norm _ _
  by_cases h0 : ‖PF h F x‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖PF h F x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma norm_sq_Q (k : ι) (x : Γ) : ‖Q n k x‖ ^ 2 = ‖x‖ ^ 2 - ‖n k x‖ ^ 2 := by
  have hx : x = Q n k x + n k x := by simp [Q]
  have horth : ⟪Q n k x, n k x⟫_ℂ = 0 := by
    rw [Q_symm h, ← ContinuousLinearMap.mul_apply, Q_mul_n h]; simp
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ horth
  rw [← hx] at this
  linarith

/-- **Bonferroni**: `‖PF F v‖² ≥ ‖v‖² - ∑_{k∈F} ‖n k v‖²`. -/
theorem norm_sq_PF_ge (F : Finset ι) (v : Γ) : ‖v‖ ^ 2 - ∑ k ∈ F, ‖n k v‖ ^ 2 ≤ ‖PF h F v‖ ^ 2 := by
  induction F using Finset.induction_on with
  | empty => simp [PF_empty]
  | insert k F hk ih =>
    rw [Finset.sum_insert hk, PF_insert h hk, ContinuousLinearMap.mul_apply, norm_sq_Q h]
    have h1 : ‖n k (PF h F v)‖ ≤ ‖n k v‖ := by
      have : n k (PF h F v) = PF h F (n k v) := by
        rw [← ContinuousLinearMap.mul_apply, PF_comm_n h, ContinuousLinearMap.mul_apply]
      rw [this]; exact norm_PF_le h F _
    nlinarith [norm_nonneg (n k (PF h F v)), norm_nonneg (n k v)]

/-- If `PF t ψ = ψ` then every `Q k ψ = ψ` for `k ∈ t`. -/
lemma Q_fix {t : Finset ι} {ψ : Γ} (hψ : PF h t ψ = ψ) {k : ι} (hk : k ∈ t) : Q n k ψ = ψ := by
  have heq : PF h t = Q n k * PF h (t.erase k) := by
    rw [← PF_insert h (Finset.notMem_erase k t), Finset.insert_erase hk]
  have e : Q n k * PF h t = PF h t := by
    rw [heq, ← mul_assoc, Q_idem h]
  calc Q n k ψ = Q n k (PF h t ψ) := by rw [hψ]
    _ = (Q n k * PF h t) ψ := rfl
    _ = ψ := by rw [e]; exact hψ

/-- **The ranges of `PF` decrease**: if `s ⊆ t` and `PF t ψ = ψ` then `PF s ψ = ψ`. -/
lemma PF_fix_of_subset {s t : Finset ι} (hst : s ⊆ t) {ψ : Γ} (hψ : PF h t ψ = ψ) : PF h s ψ = ψ := by
  induction s using Finset.induction_on with
  | empty => simp [PF_empty]
  | insert k s hk ih =>
    rw [PF_insert h hk, ContinuousLinearMap.mul_apply,
      ih ((Finset.subset_insert _ _).trans hst), Q_fix h hψ (hst (Finset.mem_insert_self _ _))]

end

section Car

variable [DecidableEq ι] (a c : ι → (Γ →L[ℂ] Γ))

/-- The number operators `c k * a k` of CAR modes form a family of commuting symmetric idempotents. -/
theorem isProjFamily_of_car (hcc : ∀ i j, c i * c j + c j * c i = 0) (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (hadj : ∀ j x y, ⟪a j x, y⟫_ℂ = ⟪x, c j y⟫_ℂ) :
    IsProjFamily (fun k => c k * a k) where
  symm k x y := by
    have hadj' : ∀ j x y, ⟪c j x, y⟫_ℂ = ⟪x, a j y⟫_ℂ := fun j x y => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    simp only [ContinuousLinearMap.mul_apply, hadj', hadj]
  idem k := by
    have h1 := hca k k
    have h2 : c k * c k = 0 := by
      have := hcc k k
      have h3 : (2 : ℂ) • (c k * c k) = 0 := by rw [two_smul]; exact this
      exact (smul_eq_zero.1 h3).resolve_left two_ne_zero
    simp only [if_true] at h1
    calc c k * a k * (c k * a k) = c k * (a k * c k) * a k := by simp only [mul_assoc]
      _ = c k * (1 - c k * a k) * a k := by rw [eq_sub_of_add_eq h1]
      _ = c k * a k := by
        rw [mul_sub, mul_one, sub_mul, show c k * (c k * a k) * a k = (c k * c k) * a k * a k by simp only [mul_assoc], h2]
        simp
  comm k l := by
    by_cases hkl : k = l
    · rw [hkl]
    · have h1 : a k * c l = -(c l * a k) := by
        have := hca k l
        rw [if_neg hkl] at this; exact eq_neg_of_add_eq_zero_left this
      have h2 : a l * c k = -(c k * a l) := by
        have := hca l k
        rw [if_neg (Ne.symm hkl)] at this; exact eq_neg_of_add_eq_zero_left this
      have h3 : c l * c k = -(c k * c l) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hcc k l)
      have h4 : a l * a k = -(a k * a l) := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact haa k l)
      have eA : c k * a k * (c l * a l) = -(c k * c l * (a k * a l)) := by
        rw [show c k * a k * (c l * a l) = c k * (a k * c l) * a l by simp only [mul_assoc], h1]
        simp only [mul_neg, neg_mul, mul_assoc]
      have eB : c l * a l * (c k * a k) = -(c l * c k * (a l * a k)) := by
        rw [show c l * a l * (c k * a k) = c l * (a l * c k) * a k by simp only [mul_assoc], h2]
        simp only [mul_neg, neg_mul, mul_assoc]
      rw [eA, eB, h3, h4]
      simp

lemma norm_sq_cre_ann (hcc : ∀ i j, c i * c j + c j * c i = 0) (haa : ∀ i j, a i * a j + a j * a i = 0)
    (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (hadj : ∀ j x y, ⟪a j x, y⟫_ℂ = ⟪x, c j y⟫_ℂ)
    (k : ι) (x : Γ) : ‖c k (a k x)‖ ^ 2 = ‖a k x‖ ^ 2 := by
  have hP := isProjFamily_of_car a c hcc haa hca hadj
  have h1 : ⟪c k (a k x), c k (a k x)⟫_ℂ = ⟪a k x, a k x⟫_ℂ := by
    have e1 := hP.symm k (x) ((c k * a k) x)
    have e2 := hP.idem k
    have e3 : ⟪(c k * a k) x, (c k * a k) x⟫_ℂ = ⟪x, (c k * a k) x⟫_ℂ := by
      rw [hP.symm k, ← ContinuousLinearMap.mul_apply, e2]
    have e4 : ⟪x, (c k * a k) x⟫_ℂ = ⟪a k x, a k x⟫_ℂ := by
      simp only [ContinuousLinearMap.mul_apply]
      rw [← hadj]
    exact e3.trans e4
  have := congrArg RCLike.re h1
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at this
  exact_mod_cast this

end Car

end Lightlike.OperatorAlgebras.CARProjections
