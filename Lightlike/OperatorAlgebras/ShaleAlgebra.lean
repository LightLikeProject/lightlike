import Lightlike.OperatorAlgebras.Weyl
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# The algebra of a Bogoliubov transformation

Helper lemmas for the necessity part of Shale's criterion (`T-OP2-P6`). For a Bogoliubov transformation `T`
with parts `α, β` (`T f = α f + β f`), the symplectic condition gives `‖α e‖² - ‖β e‖² = ‖e‖²` and so
`4 ‖β e‖² = ‖T e‖² + ‖T (i e)‖² - 2 ‖e‖²`: the Hilbert-Schmidt condition on `β` is a condition on the quadratic form
`q f = ‖T f‖²` alone.
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

lemma Bogoliubov.map_eq (T : Bogoliubov h) (f : h) : T.toEquiv f = T.alphaPart f + T.betaPart f := by
  unfold Bogoliubov.alphaPart Bogoliubov.betaPart
  match_scalars <;> ring

lemma Bogoliubov.map_I_smul (T : Bogoliubov h) (f : h) :
    T.toEquiv (Complex.I • f) = Complex.I • (T.alphaPart f - T.betaPart f) := by
  unfold Bogoliubov.alphaPart Bogoliubov.betaPart
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

/-- **`‖α e‖² - ‖β e‖² = ‖e‖²`**, from the symplectic condition applied to `e` and `i e`. -/
lemma Bogoliubov.norm_alpha_sq_sub_norm_beta_sq (T : Bogoliubov h) (e : h) :
    ‖T.alphaPart e‖ ^ 2 - ‖T.betaPart e‖ ^ 2 = ‖e‖ ^ 2 := by
  set a := T.alphaPart e with ha
  set b := T.betaPart e with hb
  have h1 := T.symp_map e (Complex.I • e)
  rw [T.map_eq e, T.map_I_smul e, ← ha, ← hb] at h1
  have h2 : symp h e (Complex.I • e) = ‖e‖ ^ 2 := by
    unfold symp
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [h2] at h1
  unfold symp at h1
  simp only [inner_add_left, inner_smul_right, inner_sub_right, inner_self_eq_norm_sq_to_K] at h1
  have hconj : ⟪b, a⟫_ℂ = (starRingEnd ℂ) ⟪a, b⟫_ℂ := (inner_conj_symm b a).symm
  have hre : (⟪b, a⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
    have := congrArg Complex.re hconj
    rw [this]; exact Complex.conj_re _
  simp [← Complex.ofReal_pow] at h1
  linarith

/-- **The antilinear part through the quadratic form**: `4 ‖β e‖² = ‖T e‖² + ‖T (i e)‖² - 2 ‖e‖²`. -/
lemma Bogoliubov.four_norm_beta_sq (T : Bogoliubov h) (e : h) :
    4 * ‖T.betaPart e‖ ^ 2 = ‖T.toEquiv e‖ ^ 2 + ‖T.toEquiv (Complex.I • e)‖ ^ 2 - 2 * ‖e‖ ^ 2 := by
  have h1 := T.norm_alpha_sq_sub_norm_beta_sq e
  have h2 : ‖T.toEquiv e‖ ^ 2 + ‖T.toEquiv (Complex.I • e)‖ ^ 2 =
      2 * (‖T.alphaPart e‖ ^ 2 + ‖T.betaPart e‖ ^ 2) := by
    rw [T.map_eq e, T.map_I_smul e, norm_smul, Complex.norm_I, one_mul]
    have := parallelogram_law_with_norm ℂ (T.alphaPart e) (T.betaPart e)
    nlinarith [this]
  nlinarith [h1, h2]

/-- `IsHilbertSchmidt β` for the antilinear part is the summability of `q(e_i) + q(i e_i) - 2`. -/
lemma Bogoliubov.norm_beta_sq_eq (T : Bogoliubov h) (e : h) :
    ‖T.betaPart e‖ ^ 2 = (‖T.toEquiv e‖ ^ 2 + ‖T.toEquiv (Complex.I • e)‖ ^ 2 - 2 * ‖e‖ ^ 2) / 4 := by
  have := T.four_norm_beta_sq e
  linarith

lemma Bogoliubov.alphaPart_I_smul (T : Bogoliubov h) (f : h) :
    T.alphaPart (Complex.I • f) = Complex.I • T.alphaPart f := by
  unfold Bogoliubov.alphaPart
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [smul_sub, smul_smul, T.toEquiv.map_neg, smul_neg]
  match_scalars <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

lemma Bogoliubov.alphaPart_real_smul (T : Bogoliubov h) (r : ℝ) (f : h) :
    T.alphaPart ((r : ℂ) • f) = (r : ℂ) • T.alphaPart f := by
  unfold Bogoliubov.alphaPart
  have h2 : Complex.I • ((r : ℂ) • f) = r • (Complex.I • f) := by
    rw [smul_comm, Complex.coe_smul]
  rw [h2, Complex.coe_smul, T.toEquiv.map_smul, T.toEquiv.map_smul]
  simp only [Complex.coe_smul, smul_sub, smul_smul]
  match_scalars <;> simp [Algebra.algebraMap_eq_smul_one] <;> ring

lemma Bogoliubov.alphaPart_smul (T : Bogoliubov h) (c : ℂ) (f : h) :
    T.alphaPart (c • f) = c • T.alphaPart f := by
  have hc : c • f = (c.re : ℂ) • f + (c.im : ℂ) • (Complex.I • f) := by
    rw [smul_smul, ← add_smul]; congr 1; apply Complex.ext <;> simp
  have hadd : ∀ x y : h, T.alphaPart (x + y) = T.alphaPart x + T.alphaPart y := fun x y => by
    unfold Bogoliubov.alphaPart
    simp only [map_add, smul_add, smul_sub]
    match_scalars <;> ring
  rw [hc, hadd, T.alphaPart_real_smul, T.alphaPart_real_smul, T.alphaPart_I_smul,
    smul_smul, ← add_smul]
  congr 1; apply Complex.ext <;> simp

variable [CompleteSpace h]

/-- The complex-linear part `α` of a Bogoliubov transformation, as a bounded operator. -/
noncomputable def Bogoliubov.alphaCLM (T : Bogoliubov h) : h →L[ℂ] h :=
  LinearMap.mkContinuous
    { toFun := T.alphaPart
      map_add' := fun f g => by
        unfold Bogoliubov.alphaPart
        simp only [map_add, smul_add, smul_sub]
        match_scalars <;> ring
      map_smul' := fun c f => T.alphaPart_smul c f }
    (‖(T.toEquiv : h →L[ℝ] h)‖) (fun f => by
      show ‖T.alphaPart f‖ ≤ ‖(T.toEquiv : h →L[ℝ] h)‖ * ‖f‖
      unfold Bogoliubov.alphaPart
      have h1 : ‖T.toEquiv f‖ ≤ ‖(T.toEquiv : h →L[ℝ] h)‖ * ‖f‖ := (T.toEquiv : h →L[ℝ] h).le_opNorm f
      have h2 : ‖T.toEquiv (Complex.I • f)‖ ≤ ‖(T.toEquiv : h →L[ℝ] h)‖ * ‖f‖ := by
        have := (T.toEquiv : h →L[ℝ] h).le_opNorm (Complex.I • f)
        rwa [norm_smul, Complex.norm_I, one_mul] at this
      rw [norm_smul]
      calc ‖(1 / 2 : ℂ)‖ * ‖T.toEquiv f - Complex.I • T.toEquiv (Complex.I • f)‖
          ≤ ‖(1 / 2 : ℂ)‖ * (‖T.toEquiv f‖ + ‖T.toEquiv (Complex.I • f)‖) := by
            gcongr
            calc _ ≤ ‖T.toEquiv f‖ + ‖Complex.I • T.toEquiv (Complex.I • f)‖ := norm_sub_le _ _
              _ = _ := by rw [norm_smul, Complex.norm_I, one_mul]
        _ ≤ _ := by
            have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
            rw [this]; nlinarith)

lemma Bogoliubov.alphaCLM_apply (T : Bogoliubov h) (f : h) : T.alphaCLM f = T.alphaPart f := rfl

/-- `⟪e, (α†α - 1) e⟫ = ‖β e‖²`. -/
lemma Bogoliubov.inner_alpha_sub_one (T : Bogoliubov h) (e : h) :
    ⟪e, (ContinuousLinearMap.adjoint T.alphaCLM * T.alphaCLM - 1) e⟫_ℂ = ((‖T.betaPart e‖ ^ 2 : ℝ) : ℂ) := by
  have h1 := T.norm_alpha_sq_sub_norm_beta_sq e
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.one_apply,
    T.alphaCLM_apply, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  have h2 : ‖T.betaPart e‖ ^ 2 = ‖T.alphaPart e‖ ^ 2 - ‖e‖ ^ 2 := by linarith
  rw [h2]; push_cast; rfl

/-- `α†α - 1` is a positive operator. -/
lemma Bogoliubov.alpha_sub_one_nonneg (T : Bogoliubov h) :
    0 ≤ ContinuousLinearMap.adjoint T.alphaCLM * T.alphaCLM - 1 := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have h1 := T.inner_alpha_sub_one x
  have h2 : ⟪(ContinuousLinearMap.adjoint T.alphaCLM * T.alphaCLM - 1) x, x⟫_ℂ =
      ((‖T.betaPart x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm, h1]; simp
  rw [h2]
  refine ⟨?_, ?_⟩ <;> simp [← Complex.ofReal_pow, sq_nonneg]

end Lightlike.OperatorAlgebras
