module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Massless
public import Lightlike.Lorentz.PoincareIrreps.Poincare

/-!
# The Poincaré group on the massless one-particle space

HA6 (Wigner's classification), sixth piece: the massless analogue of `Poincare.lean`.

* `lightTranslateOp a`: `(T(a) ψ)(P) = e^{i P·a} ψ(P)` on functions on the positive light cone;
* `lightTranslateRep`: the translation group acts by these operators;
* `lightInducedRep_translate`: covariance `U(A) T(a) = T(A a) U(A)`;
* `lightPoincareRep h : Representation ℂ ISL2C (lightCone → ℂ)`, `(a, A) ↦ T(a) U_h(A)`: the
  induced representation of `ISL(2,ℂ)` from the character `phase^h` of the little group (helicity
  `h/2`), with `P² = det P = 0` pointwise (`det_of_mem_lightCone`).

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the
statements proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

/-- The translation operator `(T(a) ψ)(P) = e^{i P·a} ψ(P)` on functions on the light cone. -/
noncomputable def lightTranslateOp (a : Herm2) : (lightCone → ℂ) →ₗ[ℂ] (lightCone → ℂ) where
  toFun ψ P := Complex.exp (Complex.I * (pairing P.1 a : ℂ)) * ψ P
  map_add' ψ φ := by
    funext P
    simp [mul_add]
  map_smul' c ψ := by
    funext P
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The translation group acts on functions on the light cone by `e^{i P·a}`. -/
noncomputable def lightTranslateRep : Representation ℂ (Multiplicative Herm2) (lightCone → ℂ) where
  toFun a := lightTranslateOp a.toAdd
  map_one' := by
    ext ψ P
    simp [lightTranslateOp, pairing_zero_right]
  map_mul' a b := by
    ext ψ P
    simp only [Module.End.mul_apply, lightTranslateOp, LinearMap.coe_mk, AddHom.coe_mk, toAdd_mul,
      pairing_add_right]
    push_cast
    rw [mul_add, Complex.exp_add]
    ring

/-- **Covariance**: `U(A) T(a) U(A)⁻¹ = T(A a)` on the light cone. -/
theorem lightInducedRep_translate (h : ℤ) (A : SL2C) (a : Herm2) :
    lightInducedRep h A ∘ₗ lightTranslateOp a = lightTranslateOp (A • a) ∘ₗ lightInducedRep h A := by
  ext ψ P
  have hp : pairing (lightSMul A⁻¹ P).1 a = pairing P.1 (A • a) := by
    have e : A • (lightSMul A⁻¹ P).1 = P.1 := congrArg Subtype.val (lightSMul_inv_smul A P)
    rw [← pairing_smul A, e]
  simp only [LinearMap.comp_apply, lightInducedRep_apply, lightTranslateOp, LinearMap.coe_mk,
    AddHom.coe_mk, hp]
  ring

/-- **The representation of the Poincaré group on the massless one-particle space of helicity
`h/2`**: `(a, A) ↦ T(a) U_h(A)`, i.e.
`(U(a,A) ψ)(P) = e^{i P·a} χ_h(W(A, A⁻¹P)) ψ(A⁻¹ P)`. -/
noncomputable def lightPoincareRep (h : ℤ) : Representation ℂ ISL2C (lightCone → ℂ) where
  toFun g := lightTranslateRep g.left * lightInducedRep h g.right
  map_one' := by
    simp
  map_mul' g g' := by
    have cov : lightTranslateRep (lorentzAut g.right g'.left) * lightInducedRep h g.right =
        lightInducedRep h g.right * lightTranslateRep g'.left :=
      (lightInducedRep_translate h g.right g'.left.toAdd).symm
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul]
    calc lightTranslateRep g.left * lightTranslateRep (lorentzAut g.right g'.left) *
          (lightInducedRep h g.right * lightInducedRep h g'.right)
        = lightTranslateRep g.left *
            (lightTranslateRep (lorentzAut g.right g'.left) * lightInducedRep h g.right) *
              lightInducedRep h g'.right := by simp only [mul_assoc]
      _ = lightTranslateRep g.left *
            (lightInducedRep h g.right * lightTranslateRep g'.left) *
              lightInducedRep h g'.right := by rw [cov]
      _ = _ := by simp only [mul_assoc]

/-- On the light cone the momentum square vanishes: `P² = det P = 0`. -/
theorem det_of_mem_lightCone (P : lightCone) : P.1.1.det = 0 := P.2.1

end Lightlike.Lorentz.Poincare
