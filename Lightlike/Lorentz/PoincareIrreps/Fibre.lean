module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Wigner

/-!
# The states at a fixed momentum (HA6, fibre dimension)

For the induced representation `inducedRep hm n` of `SL(2,ℂ)` on functions on the mass shell with values
in `ℂ^{n+1}` (spin `n/2`) we prove:

* `atMomentum n P`: the space of (generalised) states supported at the single momentum `P`;
* `atMomentumEquiv`: it is linearly isomorphic to the little-group space `ℂ^{n+1}`;
* `finrank_atMomentum`: it has dimension `n + 1`, so a massive spin-`1/2` representation has **two
  states per momentum** (`finrank_atMomentum_spinHalf`);
* `inducedRep_atMomentum`: `U(A)` maps the states at `P` into the states at `A P`, acting there by
  the Wigner rotation: `(U(A) ψ)(A P) = D(W(A, P)) ψ(P)` (`inducedRep_apply_smul`).

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the statements
proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

variable {m : ℝ} (hm : 0 < m)

open Classical in
/-- The states of the pointwise induced space supported at the single momentum `P`. -/
def atMomentum (m : ℝ) (n : ℕ) (P : massShell m) :
    Submodule ℂ (massShell m → Fin (n + 1) → ℂ) where
  carrier := {ψ | ∀ Q, Q ≠ P → ψ Q = 0}
  add_mem' := by
    intro ψ φ hψ hφ Q hQ
    simp [hψ Q hQ, hφ Q hQ]
  zero_mem' := fun _ _ => rfl
  smul_mem' := by
    intro c ψ hψ Q hQ
    simp [hψ Q hQ]

open Classical in
/-- **The states at a momentum `P` are the little-group space `ℂ^{n+1}`**: evaluation at `P`. -/
noncomputable def atMomentumEquiv (m : ℝ) (n : ℕ) (P : massShell m) :
    atMomentum m n P ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun ψ := ψ.1 P
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Pi.single P v, fun Q hQ => by simp [Pi.single_eq_of_ne hQ]⟩
  left_inv ψ := by
    apply Subtype.ext
    funext Q
    by_cases hQ : Q = P
    · subst hQ; simp
    · simp [Pi.single_eq_of_ne hQ, ψ.2 Q hQ]
  right_inv v := by simp

/-- The space of states at one momentum has dimension `n + 1` (the dimension of the spin-`n/2`
representation of the little group `SU(2)`). -/
theorem finrank_atMomentum (m : ℝ) (n : ℕ) (P : massShell m) :
    Module.finrank ℂ (atMomentum m n P) = n + 1 := by
  rw [(atMomentumEquiv m n P).finrank_eq]
  simp

/-- **Massive spin `1/2` has two states per momentum.** -/
theorem finrank_atMomentum_spinHalf (m : ℝ) (P : massShell m) :
    Module.finrank ℂ (atMomentum m 1 P) = 2 :=
  finrank_atMomentum m 1 P

include hm in
/-- The value of `U(A) ψ` at `A P` is the Wigner rotation `D(W(A, P))` applied to `ψ(P)`. -/
theorem inducedRep_apply_smul (n : ℕ) (A : SL2C) (ψ : massShell m → Fin (n + 1) → ℂ)
    (P : massShell m) :
    inducedRep hm n A ψ (shellSMul hm A P) =
      (SU2Spin.spinRep n (wignerSU2 hm A P) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ ψ P := by
  have h : shellSMul hm A⁻¹ (shellSMul hm A P) = P := by
    simpa using shellSMul_inv_smul hm A⁻¹ P
  rw [inducedRep_apply, h]

include hm in
/-- `U(A)` maps the states at `P` into the states at `A P`. -/
theorem inducedRep_atMomentum (n : ℕ) (A : SL2C) (P : massShell m) :
    ∀ ψ ∈ atMomentum m n P, inducedRep hm n A ψ ∈ atMomentum m n (shellSMul hm A P) := by
  intro ψ hψ Q hQ
  have hne : shellSMul hm A⁻¹ Q ≠ P := by
    intro h
    apply hQ
    rw [← h, shellSMul_inv_smul hm]
  rw [inducedRep_apply, hψ _ hne, Matrix.mulVec_zero]

end Lightlike.Lorentz.Poincare
