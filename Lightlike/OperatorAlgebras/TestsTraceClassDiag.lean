import Lightlike.OperatorAlgebras.TestsTraceClass
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Trust check: the diagonal operator with eigenvalues `1 / (n + 1)` on `ℓ²(ℕ)`

The check of milestone OP6: `D = diag (1 / (n + 1))` on `ℓ²(ℕ)` is Hilbert-Schmidt and not trace class (`diag_isHilbertSchmidt`,
`diag_not_isTraceClass`). Mathlib has no multiplication operator on `lp`, so the diagonal operator of a sequence of norm at most one is
built here (`diagOp`), for this check only.
-/

open scoped InnerProductSpace ComplexOrder

namespace Lightlike.OperatorAlgebras.TraceClass

/-- `ℓ²(ℕ)` over `ℂ`. -/
abbrev L2N : Type := lp (fun _ : ℕ => ℂ) 2

lemma memℓp_mul {w : ℕ → ℂ} (hw : ∀ n, ‖w n‖ ≤ 1) (x : L2N) : Memℓp (fun n => w n * x n) 2 := by
  have hx := lp.memℓp x
  rw [memℓp_gen_iff (by norm_num)] at hx ⊢
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_of_le_one_left (by positivity) (Real.rpow_le_one (norm_nonneg _) (hw n) (by norm_num))

/-- **The diagonal operator** `x ↦ (wₙ xₙ)ₙ` on `ℓ²(ℕ)` for a sequence with `‖wₙ‖ ≤ 1`. -/
noncomputable def diagOp (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) : L2N →L[ℂ] L2N :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => w n * x n, memℓp_mul hw x⟩
      map_add' := fun x y => by ext n; simp [mul_add, Pi.add_apply]; rfl
      map_smul' := fun c x => by ext n; simp [mul_left_comm] } 1
    (fun x => by
      rw [one_mul]
      refine lp.norm_le_of_forall_sum_le (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (norm_nonneg x) fun s => ?_
      refine le_trans (Finset.sum_le_sum fun n _ => ?_) (lp.sum_rpow_le_norm_rpow (by norm_num) x s)
      show ‖w n * x n‖ ^ (2 : ENNReal).toReal ≤ ‖x n‖ ^ (2 : ENNReal).toReal
      rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      exact mul_le_of_le_one_left (by positivity) (Real.rpow_le_one (norm_nonneg _) (hw n) (by norm_num)))

lemma diagOp_apply (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (x : L2N) (n : ℕ) : diagOp w hw x n = w n * x n := rfl

/-- The standard vectors `eₙ` of `ℓ²(ℕ)`. -/
noncomputable def stdVec (n : ℕ) : L2N := lp.single 2 n (1 : ℂ)

lemma diagOp_stdVec (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (n : ℕ) : diagOp w hw (stdVec n) = w n • stdVec n := by
  classical
  ext k
  rw [diagOp_apply, stdVec, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : k = n
  · subst h; simp
  · simp [h, Pi.single_apply]

/-- The absolute value of a positive operator is itself. -/
lemma abs_eq_self_of_nonneg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : 0 ≤ T) : CFC.abs T = T := CFC.abs_of_nonneg T hT

/-- The standard Hilbert basis of `ℓ²(ℕ)`. -/
noncomputable def stdBasis : HilbertBasis ℕ ℂ L2N := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ L2N)

lemma stdBasis_apply (n : ℕ) : stdBasis n = stdVec n := by
  classical
  have h := stdBasis.repr_self n
  simpa [stdBasis, stdVec] using h

lemma stdVec_injective : Function.Injective stdVec := by
  have h : ⇑stdBasis = stdVec := funext stdBasis_apply
  rw [← h]; exact stdBasis.orthonormal.linearIndependent.injective

/-- The standard Hilbert basis indexed by its own range, the form the trace-class API (`IsTraceClass`, `IsHilbertSchmidt`) uses. -/
noncomputable def stdBasisW : HilbertBasis (Set.range stdVec) ℂ L2N :=
  HilbertBasis.mk (v := (Subtype.val : Set.range stdVec → L2N))
    (by
      have h : ⇑stdBasis = stdVec := funext stdBasis_apply
      rw [← h]; exact stdBasis.orthonormal.toSubtypeRange)
    (by
      have h : ⇑stdBasis = stdVec := funext stdBasis_apply
      rw [Subtype.range_coe, ← h, stdBasis.dense_span])

lemma stdBasisW_apply (i : Set.range stdVec) : stdBasisW i = i := by
  simp [stdBasisW]

/-- The weights `1 / (n + 1)` as complex numbers. -/
noncomputable def invWeight (n : ℕ) : ℂ := (((n : ℝ) + 1)⁻¹ : ℝ)

lemma norm_invWeight_le (n : ℕ) : ‖invWeight n‖ ≤ 1 := by
  rw [invWeight, Complex.norm_real, Real.norm_eq_abs, abs_inv]
  exact inv_le_one_of_one_le₀ (by rw [abs_of_pos (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

/-- **The diagonal operator `D = diag (1 / (n + 1))`** on `ℓ²(ℕ)`. -/
noncomputable def invDiag : L2N →L[ℂ] L2N := diagOp invWeight norm_invWeight_le

/-- **`D` is Hilbert-Schmidt**: `∑ ‖D eₙ‖² = ∑ 1 / (n + 1)² < ∞`. -/
theorem invDiag_isHilbertSchmidt : HilbertSchmidt.IsHilbertSchmidt invDiag := by
  refine ⟨_, stdBasisW, ?_⟩
  let e : ℕ ≃ Set.range stdVec := Equiv.ofInjective stdVec stdVec_injective
  rw [← e.summable_iff]
  have hterm : ∀ n, ‖invDiag (stdBasisW (e n))‖ ^ 2 = (((n : ℝ) + 1)⁻¹) ^ 2 := by
    intro n
    rw [stdBasisW_apply]
    show ‖invDiag (stdVec n)‖ ^ 2 = _
    rw [invDiag, diagOp_stdVec, norm_smul, stdVec, lp.norm_single (by norm_num), norm_one, mul_one, invWeight,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp only [Function.comp_def, hterm]
  exact (diag_weights_square_summable_not_summable).1

/-- `⟪D x, x⟫ = ∑ wₙ ‖xₙ‖²` for real weights. -/
lemma inner_invDiag_self (x : L2N) :
    ⟪invDiag x, x⟫_ℂ = ((∑' n : ℕ, ((n : ℝ) + 1)⁻¹ * ‖x n‖ ^ 2 : ℝ) : ℂ) := by
  rw [lp.inner_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  show ⟪invWeight n * x n, x n⟫_ℂ = _
  rw [invWeight, RCLike.inner_apply, map_mul, Complex.conj_ofReal, mul_left_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast; ring

/-- **`D` is positive**. -/
lemma invDiag_nonneg : 0 ≤ invDiag := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  rw [inner_invDiag_self]
  refine ⟨by simp, ?_⟩
  simpa using tsum_nonneg fun n : ℕ => (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ * ‖x n‖ ^ 2)

/-- **`D` is not trace class**: in the standard basis the diagonal sums of `|D| = D` are `∑ 1 / (n + 1) = ∞`. -/
theorem invDiag_not_isTraceClass : ¬ IsTraceClass invDiag := by
  intro h
  have hs := (isTraceClass_iff.mp h) _ stdBasisW
  rw [abs_eq_self_of_nonneg invDiag_nonneg] at hs
  let e : ℕ ≃ Set.range stdVec := Equiv.ofInjective stdVec stdVec_injective
  rw [← e.summable_iff] at hs
  have hterm : ∀ n, (⟪stdBasisW (e n), invDiag (stdBasisW (e n))⟫_ℂ).re = ((n : ℝ) + 1)⁻¹ := by
    intro n
    rw [stdBasisW_apply]
    show (⟪stdVec n, invDiag (stdVec n)⟫_ℂ).re = _
    rw [invDiag, diagOp_stdVec, inner_smul_right, inner_self_eq_norm_sq_to_K, stdVec, lp.norm_single (by norm_num),
      norm_one]
    simp only [invWeight]
    rw [Complex.re_ofReal_mul]
    simp
  simp only [Function.comp_def, hterm] at hs
  exact (diag_weights_square_summable_not_summable).2 hs

end Lightlike.OperatorAlgebras.TraceClass
