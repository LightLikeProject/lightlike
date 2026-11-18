import Lightlike.OperatorAlgebras.Weyl

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

end Lightlike.OperatorAlgebras
