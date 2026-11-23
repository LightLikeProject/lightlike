module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Boost
public import Lightlike.Upstream.SU2Spin.SpinRep

/-!
# The Wigner cocycle and the induced action on the massive mass shell

HA6 (Wigner's classification), third piece. Let `m > 0` and `W(A, P) = L(A P)⁻¹ A L(P)` be the
Wigner rotation of `Boost.lean`. We prove

* `shellSMul_mul`: the `SL(2,ℂ)`-action on the mass shell is an action;
* `wignerSL_mul`: the cocycle identity `W(A B, P) = W(A, B P) W(B, P)`;
* `wignerSU2`: the Wigner rotation as a genuine element of `SU(2)`, with the same cocycle identity
  (`wignerSU2_mul`), via injectivity of `SL2C.ofSU2`;
* `inducedRep`: the *pointwise* induced representation of `SL(2,ℂ)` on the space of functions on the
  mass shell with values in `ℂ^{n+1}` (spin `n/2`),
  `(U(A) ψ)(P) = D^{n/2}(W(A, A⁻¹ P)) ψ(A⁻¹ P)`, as a `Representation ℂ SL2C`
  (`inducedRep`, with `inducedRep_apply`). Unitarity needs the invariant measure on the orbit and
  is left for the next piece.

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the statements
proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

variable {m : ℝ} (hm : 0 < m)

include hm in
lemma shellSMul_one (P : massShell m) : shellSMul hm 1 P = P :=
  Subtype.ext (one_smul _ _)

include hm in
lemma shellSMul_mul (A B : SL2C) (P : massShell m) :
    shellSMul hm (A * B) P = shellSMul hm A (shellSMul hm B P) :=
  Subtype.ext (mul_smul _ _ _)

include hm in
lemma shellSMul_inv_smul (A : SL2C) (P : massShell m) :
    shellSMul hm A (shellSMul hm A⁻¹ P) = P := by
  rw [← shellSMul_mul hm, mul_inv_cancel, shellSMul_one hm]

/-- **The Wigner cocycle identity** `W(A B, P) = W(A, B P) W(B, P)` in `SL(2,ℂ)`. -/
theorem wignerSL_mul (A B : SL2C) (P : massShell m) :
    wignerSL hm (A * B) P = wignerSL hm A (shellSMul hm B P) * wignerSL hm B P := by
  simp only [wignerSL, shellSMul_mul hm]
  group

include hm in
lemma wignerSL_one (P : massShell m) : wignerSL hm 1 P = 1 := by
  simp [wignerSL, shellSMul_one hm]

/-- **The Wigner rotation as an element of `SU(2)`.** -/
noncomputable def wignerSU2 (A : SL2C) (P : massShell m) : Lightlike.SU2 :=
  Classical.choose (exists_wigner_su2 hm A P)

lemma ofSU2_wignerSU2 (A : SL2C) (P : massShell m) :
    SL2C.ofSU2 (wignerSU2 hm A P) = wignerSL hm A P :=
  Classical.choose_spec (exists_wigner_su2 hm A P)

/-- The Wigner cocycle identity in `SU(2)`. -/
theorem wignerSU2_mul (A B : SL2C) (P : massShell m) :
    wignerSU2 hm (A * B) P = wignerSU2 hm A (shellSMul hm B P) * wignerSU2 hm B P := by
  apply SL2C.ofSU2_injective
  rw [map_mul, ofSU2_wignerSU2, ofSU2_wignerSU2, ofSU2_wignerSU2]
  exact wignerSL_mul hm A B P

lemma wignerSU2_one (P : massShell m) : wignerSU2 hm 1 P = 1 := by
  apply SL2C.ofSU2_injective
  rw [ofSU2_wignerSU2, wignerSL_one hm, map_one]

/-! ## The induced action on functions on the mass shell -/

/-- The operator `ψ ↦ (P ↦ D^{n/2}(W(A, A⁻¹ P)) ψ(A⁻¹ P))`. -/
noncomputable def inducedOp (n : ℕ) (A : SL2C) :
    (massShell m → Fin (n + 1) → ℂ) →ₗ[ℂ] (massShell m → Fin (n + 1) → ℂ) where
  toFun ψ P :=
    (SU2Spin.spinRep n (wignerSU2 hm A (shellSMul hm A⁻¹ P)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ ψ (shellSMul hm A⁻¹ P)
  map_add' ψ φ := by
    funext P
    simp [Matrix.mulVec_add]
  map_smul' c ψ := by
    funext P
    simp [Matrix.mulVec_smul]

/-- **The pointwise induced representation** of `SL(2,ℂ)` on functions on the massive mass shell
with values in the spin-`n/2` space: `(U(A) ψ)(P) = D(W(A, A⁻¹ P)) ψ(A⁻¹ P)`. -/
noncomputable def inducedRep (n : ℕ) :
    Representation ℂ SL2C (massShell m → Fin (n + 1) → ℂ) where
  toFun A := inducedOp hm n A
  map_one' := by
    ext ψ P i
    simp [inducedOp, shellSMul_one hm, wignerSU2_one hm]
  map_mul' A B := by
    ext ψ P i
    have h1 : shellSMul hm (A * B)⁻¹ P = shellSMul hm B⁻¹ (shellSMul hm A⁻¹ P) := by
      rw [_root_.mul_inv_rev, shellSMul_mul hm]
    have h2 : wignerSU2 hm (A * B) (shellSMul hm B⁻¹ (shellSMul hm A⁻¹ P)) =
        wignerSU2 hm A (shellSMul hm A⁻¹ P) *
          wignerSU2 hm B (shellSMul hm B⁻¹ (shellSMul hm A⁻¹ P)) := by
      rw [wignerSU2_mul hm, shellSMul_inv_smul hm]
    simp only [Module.End.mul_apply, inducedOp, LinearMap.coe_mk, AddHom.coe_mk, h1, h2, map_mul,
      Submonoid.coe_mul, ← Matrix.mulVec_mulVec]

lemma inducedRep_apply (n : ℕ) (A : SL2C) (ψ : massShell m → Fin (n + 1) → ℂ) (P : massShell m) :
    inducedRep hm n A ψ P =
      (SU2Spin.spinRep n (wignerSU2 hm A (shellSMul hm A⁻¹ P)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ ψ (shellSMul hm A⁻¹ P) := rfl

end Lightlike.Lorentz.Poincare
