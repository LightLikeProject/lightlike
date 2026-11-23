import Mathlib

/-!
# A bounded sesquilinear form on a dense range is given by a bounded operator

Let `ι : X →ₗ[ℂ] K` be a linear map with dense range into a Hilbert space and `β : X → X → ℂ` linear in the
first and conjugate-linear in the second argument, with `‖β x y‖ ≤ C ‖ι x‖ ‖ι y‖`. Then there is a bounded operator
`T` on `K` with `⟪ι y, T (ι x)⟫ = β x y` (`exists_op_of_bdd_form`). This is the Radon–Nikodym step in the proof that
a vector state with a cyclic vector and trivial commutant is pure
(`Lightlike.OperatorAlgebras.QuasiFreeState.Pure`).
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.QuasiFreeState

variable {K X : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [AddCommGroup X] [Module ℂ X]

omit [CompleteSpace K] in
/-- A vector orthogonal to a dense range is zero. -/
lemma eq_zero_of_forall_inner_range {ι : X →ₗ[ℂ] K} (hd : DenseRange ι) {v : K}
    (h : ∀ y, ⟪v, ι y⟫_ℂ = 0) : v = 0 := by
  have key : ∀ u : K, ⟪v, u⟫_ℂ = 0 := fun u =>
    hd.induction_on u (isClosed_eq (by fun_prop) continuous_const) (fun y => h y)
  exact inner_self_eq_zero.1 (key v)

/-- **A bounded sesquilinear form on a dense range is an operator.** -/
theorem exists_op_of_bdd_form (ι : X →ₗ[ℂ] K) (hd : DenseRange ι) (β : X → X → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x y, ‖β x y‖ ≤ C * ‖ι x‖ * ‖ι y‖)
    (hadd₁ : ∀ x x' y, β (x + x') y = β x y + β x' y) (hsm₁ : ∀ (c : ℂ) x y, β (c • x) y = c * β x y)
    (hadd₂ : ∀ x y y', β x (y + y') = β x y + β x y')
    (hsm₂ : ∀ (c : ℂ) x y, β x (c • y) = conj c * β x y) :
    ∃ T : K →L[ℂ] K, ∀ x y, ⟪ι y, T (ι x)⟫_ℂ = β x y := by
  -- the functional `y ↦ conj β x y`, extended to `K`
  let f : X → X →ₗ[ℂ] ℂ := fun x =>
    { toFun := fun y => conj (β x y)
      map_add' := fun y y' => by simp [hadd₂]
      map_smul' := fun c y => by simp [hsm₂] }
  have hf : ∀ x y, ‖f x y‖ ≤ (C * ‖ι x‖) * ‖ι y‖ := fun x y => by
    show ‖conj (β x y)‖ ≤ _
    rw [Complex.norm_conj]; exact hb x y
  let g : X → (K →L[ℂ] ℂ) := fun x => (f x).extendOfNorm ι
  have hg : ∀ x y, g x (ι y) = conj (β x y) := fun x y =>
    LinearMap.extendOfNorm_eq hd ⟨C * ‖ι x‖, hf x⟩ y
  have hgn : ∀ x, ‖g x‖ ≤ C * ‖ι x‖ := fun x =>
    LinearMap.opNorm_extendOfNorm_le hd (mul_nonneg hC (norm_nonneg _)) (hf x)
  let w : X → K := fun x => (InnerProductSpace.toDual ℂ K).symm (g x)
  have hw : ∀ x y, ⟪w x, ι y⟫_ℂ = conj (β x y) := fun x y => by
    rw [InnerProductSpace.toDual_symm_apply, hg]
  have hwn : ∀ x, ‖w x‖ ≤ C * ‖ι x‖ := fun x => by
    show ‖(InnerProductSpace.toDual ℂ K).symm (g x)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]; exact hgn x
  let W : X →ₗ[ℂ] K :=
    { toFun := w
      map_add' := fun x x' => by
        refine sub_eq_zero.1 (eq_zero_of_forall_inner_range hd fun y => ?_)
        rw [inner_sub_left, inner_add_left, hw, hw, hw, hadd₁]
        simp
      map_smul' := fun c x => by
        refine sub_eq_zero.1 (eq_zero_of_forall_inner_range hd fun y => ?_)
        rw [inner_sub_left, inner_smul_left, hw, hw, hsm₁]
        simp }
  refine ⟨W.extendOfNorm ι, fun x y => ?_⟩
  rw [LinearMap.extendOfNorm_eq hd ⟨C, fun x => hwn x⟩ x]
  show ⟪ι y, w x⟫_ℂ = _
  rw [← inner_conj_symm, hw, Complex.conj_conj]

end Lightlike.OperatorAlgebras.QuasiFreeState
