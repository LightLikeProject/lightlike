import Lightlike.OperatorAlgebras.QuasiFreeState.State
import Lightlike.OperatorAlgebras.QuasiFreeState.PositiveFunctional
import Lightlike.OperatorAlgebras.QuasiFreeState.BoundedForm

/-!
# Purity of vector states with a cyclic vector and trivial commutant

A state `ρ` of a unital star algebra `A` is **pure** (`IsPureState`) if it is an extreme point of the convex set of
states.

**Theorem** (`isPureState_vecState`; the easy half of the GNS characterization of purity). Let `A` be a star subalgebra
of `B(K)` and `Ω` a unit vector that is cyclic for `A` (`AΩ` dense in `K`). If every bounded operator commuting with
`A` is a scalar, then the vector state `a ↦ ⟨Ω, a Ω⟩` is a pure state of `A`.

Proof. If `ρ = aρ₁ + bρ₂` with `a, b > 0`, then `a ρ₁(x* x) ≤ ‖xΩ‖²`, so by Cauchy–Schwarz for `ρ₁` the form
`(x, y) ↦ ρ₁(y* x)` is bounded by `a⁻¹ ‖xΩ‖ ‖yΩ‖` on the dense subspace `AΩ`. By `exists_op_of_bdd_form` it is given
by a bounded operator `T` on `K`, which commutes with `A`, hence `T = c`, and `ρ₁ = c ρ`, `c = 1`.

Reference: Bratteli–Robinson 1, Section 2.3 (`bratteli-robinson-1997`); no equation number is claimed.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Lightlike.OperatorAlgebras

/-- **A pure state**: an extreme point of the convex set of states. -/
def IsPureState {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] (ρ : A →ₗ[ℂ] ℂ) : Prop :=
  ρ ∈ Set.extremePoints ℝ {σ : A →ₗ[ℂ] ℂ | IsState σ}

section Vector

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (A : StarSubalgebra ℂ (K →L[ℂ] K)) (Ω : K)

/-- The map `a ↦ a Ω`. -/
def evalVec : A →ₗ[ℂ] K where
  toFun a := (a : K →L[ℂ] K) Ω
  map_add' a b := by simp
  map_smul' c a := by simp

/-- The vector state `a ↦ ⟨Ω, a Ω⟩` of a star subalgebra of `B(K)`. -/
noncomputable def vecState : A →ₗ[ℂ] ℂ where
  toFun a := ⟪Ω, (a : K →L[ℂ] K) Ω⟫_ℂ
  map_add' a b := by simp
  map_smul' c a := by simp

variable {A Ω}

lemma vecState_star_mul (y x : A) :
    vecState A Ω (star y * x) = ⟪evalVec A Ω y, evalVec A Ω x⟫_ℂ := by
  show ⟪Ω, (star (y : K →L[ℂ] K) * (x : K →L[ℂ] K)) Ω⟫_ℂ = _
  rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rfl

lemma vecState_re (x : A) : (vecState A Ω (star x * x)).re = ‖evalVec A Ω x‖ ^ 2 := by
  rw [vecState_star_mul]
  simpa using (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (evalVec A Ω x)).symm

/-- The vector state of a unit vector is a state. -/
theorem isState_vecState (hΩ : ‖Ω‖ = 1) : IsState (vecState A Ω) where
  map_one := by
    show ⟪Ω, ((1 : A) : K →L[ℂ] K) Ω⟫_ℂ = 1
    simp [inner_self_eq_norm_sq_to_K, hΩ]
  nonneg a := by
    rw [vecState_star_mul, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    exact Complex.zero_le_real.2 (sq_nonneg _)

/-- **Purity of a vector state** with cyclic vector and trivial commutant. -/
theorem isPureState_vecState (hΩ : ‖Ω‖ = 1) (hcyc : DenseRange (evalVec A Ω))
    (hirr : ∀ T : K →L[ℂ] K, (∀ z ∈ A, T * z = z * T) → ∃ c : ℂ, T = c • 1) :
    IsPureState (vecState A Ω) := by
  refine ⟨isState_vecState hΩ, ?_⟩
  have key : ∀ (ρ₁ ρ₂ : A →ₗ[ℂ] ℂ) (a b : ℝ), IsState ρ₁ → IsState ρ₂ → 0 < a → 0 < b → a + b = 1 →
      a • ρ₁ + b • ρ₂ = vecState A Ω → ρ₁ = vecState A Ω := by
    intro ρ₁ ρ₂ a b h₁ h₂ ha hb hab hseg
    have hle : ∀ x : A, a * (ρ₁ (star x * x)).re ≤ ‖evalVec A Ω x‖ ^ 2 := fun x => by
      have h := congrArg Complex.re (LinearMap.congr_fun hseg (star x * x))
      rw [vecState_re] at h
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Complex.add_re, Complex.smul_re,
        smul_eq_mul] at h
      have := (Complex.nonneg_iff.1 (h₂.nonneg x)).1
      nlinarith
    have hbd : ∀ x y : A, ‖ρ₁ (star y * x)‖ ≤ (1 / a) * ‖evalVec A Ω x‖ * ‖evalVec A Ω y‖ := by
      intro x y
      have hcs := posFun_norm_sq_le ρ₁ h₁.nonneg y x
      have hx : (ρ₁ (star x * x)).re ≤ ‖evalVec A Ω x‖ ^ 2 / a := (le_div_iff₀ ha).2 (by linarith [hle x])
      have hy : (ρ₁ (star y * y)).re ≤ ‖evalVec A Ω y‖ ^ 2 / a := (le_div_iff₀ ha).2 (by linarith [hle y])
      have hx0 := (Complex.nonneg_iff.1 (h₁.nonneg x)).1
      have hy0 := (Complex.nonneg_iff.1 (h₁.nonneg y)).1
      have hsq : ‖ρ₁ (star y * x)‖ ^ 2 ≤ ((1 / a) * ‖evalVec A Ω x‖ * ‖evalVec A Ω y‖) ^ 2 := by
        calc ‖ρ₁ (star y * x)‖ ^ 2 ≤ _ := hcs
          _ ≤ (‖evalVec A Ω y‖ ^ 2 / a) * (‖evalVec A Ω x‖ ^ 2 / a) :=
              mul_le_mul hy hx hx0 (by positivity)
          _ = _ := by field_simp
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq
    obtain ⟨T, hT⟩ := exists_op_of_bdd_form (evalVec A Ω) hcyc (fun x y => ρ₁ (star y * x)) (1 / a)
      (by positivity) hbd
      (fun x x' y => by simp [mul_add])
      (fun c x y => by simp)
      (fun x y y' => by simp [add_mul])
      (fun c x y => by simp)
    have hcomm : ∀ z ∈ A, T * z = z * T := by
      intro z hz
      let zA : A := ⟨z, hz⟩
      have hz1 : ∀ x : A, z (evalVec A Ω x) = evalVec A Ω (zA * x) := fun x => rfl
      have hz2 : ∀ y : A, (star z) (evalVec A Ω y) = evalVec A Ω (star zA * y) := fun y => rfl
      have hD : ∀ x : A, (T * z - z * T) (evalVec A Ω x) = 0 := by
        intro x
        refine eq_zero_of_forall_inner_range hcyc fun y => ?_
        have e1 : ⟪evalVec A Ω y, T (z (evalVec A Ω x))⟫_ℂ = ρ₁ (star y * (zA * x)) := by
          rw [hz1]; exact hT _ _
        have e2 : ⟪evalVec A Ω y, z (T (evalVec A Ω x))⟫_ℂ = ρ₁ (star y * (zA * x)) := by
          rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hz2, hT]
          simp [mul_assoc]
        rw [← inner_conj_symm]
        have : ⟪evalVec A Ω y, (T * z - z * T) (evalVec A Ω x)⟫_ℂ = 0 := by
          rw [sub_apply, inner_sub_right]
          show ⟪evalVec A Ω y, T (z (evalVec A Ω x))⟫_ℂ - ⟪evalVec A Ω y, z (T (evalVec A Ω x))⟫_ℂ = 0
          rw [e1, e2, sub_self]
        rw [this, map_zero]
      have hD0 : T * z - z * T = 0 :=
        ContinuousLinearMap.ext fun u =>
          hcyc.induction_on u (isClosed_eq (T * z - z * T).continuous continuous_const) hD
      exact sub_eq_zero.1 hD0
    obtain ⟨c, hc⟩ := hirr T hcomm
    have hρ : ∀ x : A, ρ₁ x = c * vecState A Ω x := fun x => by
      have h := hT x 1
      rw [hc] at h
      have h1 : evalVec A Ω 1 = Ω := by simp [evalVec]
      rw [h1, star_one, one_mul] at h
      rw [← h]
      show ⟪Ω, (c • (1 : K →L[ℂ] K)) (evalVec A Ω x)⟫_ℂ = c * ⟪Ω, (x : K →L[ℂ] K) Ω⟫_ℂ
      simp [evalVec]
    have hc1 : c = 1 := by
      have := hρ 1
      rw [h₁.map_one, (isState_vecState hΩ : IsState (vecState A Ω)).map_one, mul_one] at this
      exact this.symm
    refine LinearMap.ext fun x => ?_
    rw [hρ x, hc1, one_mul]
  intro ρ₁ h₁ ρ₂ h₂ hseg
  obtain ⟨a, b, ha, hb, hab, hseg⟩ := hseg
  exact key ρ₁ ρ₂ a b h₁ h₂ ha hb hab hseg

end Vector

end Lightlike.OperatorAlgebras.QuasiFreeState
