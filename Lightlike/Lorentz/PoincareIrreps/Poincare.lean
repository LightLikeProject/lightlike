module

public import Mathlib
public import Lightlike.Lorentz.PoincareIrreps.Wigner

/-!
# The Poincaré group `Herm2 ⋊ SL(2,ℂ)` and its action on the massive one-particle space

HA6 (Wigner's classification), fifth piece. Translations are the additive group of Hermitian
matrices (spinor form of `ℝ^{1,3}`); the double cover of the Poincaré group is the semidirect product
`ISL(2,ℂ) = Multiplicative Herm2 ⋊[lorentzAut] SL(2,ℂ)`.

* `pairing P Q = ½ (tr P tr Q - tr (P Q))`, the Minkowski product `p·a = p₀a₀ - p⃗·a⃗` in signature
  `(+,−,−,−)` (`pairing_ofVec`), additive and `SL(2,ℂ)`-invariant (`pairing_smul`);
* `ISL2C`, the group `Multiplicative Herm2 ⋊[lorentzAut] SL2C`;
* `translateRep hm n`: translations `(T(a) ψ)(P) = e^{i P·a} ψ(P)` on functions on the mass shell, and
  the covariance relation `U(A) T(a) = T(A a) U(A)` (`inducedRep_translate`);
* `poincareRep hm n : ISL2C →* Module.End ℂ _`, `(a, A) ↦ T(a) U(A)`, the induced representation of
  the Poincaré group on the massive mass shell; on it `P² = m²` holds pointwise
  (`det_of_mem_massShell`).

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2; only the statements proved
here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

/-- The Hermitian matrices form an additive subgroup of all matrices. -/
def hermSubgroup : AddSubgroup (Matrix (Fin 2) (Fin 2) ℂ) where
  carrier := {M | M.IsHermitian}
  add_mem' := fun ha hb => Matrix.IsHermitian.add ha hb
  zero_mem' := Matrix.isHermitian_zero
  neg_mem' := fun ha => Matrix.IsHermitian.neg ha

/-- The additive group structure on spinor momenta. -/
instance : AddCommGroup Herm2 := inferInstanceAs (AddCommGroup hermSubgroup)

@[simp] lemma coe_add_herm (P Q : Herm2) :
    ((P + Q : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) = P.1 + Q.1 := rfl

@[simp] lemma coe_zero_herm : ((0 : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) = 0 := rfl

@[simp] lemma coe_neg_herm (P : Herm2) : ((-P : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) = -P.1 := rfl

/-- `SL(2,ℂ)` acts on spinor momenta by additive maps. -/
instance : DistribMulAction SL2C Herm2 where
  smul_zero A := Subtype.ext (by
    change (A : Matrix (Fin 2) (Fin 2) ℂ) * 0 * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = 0
    simp)
  smul_add A P Q := Subtype.ext (by
    change (A : Matrix (Fin 2) (Fin 2) ℂ) * (P.1 + Q.1) * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ =
      (A : Matrix (Fin 2) (Fin 2) ℂ) * P.1 * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ +
        (A : Matrix (Fin 2) (Fin 2) ℂ) * Q.1 * (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
    rw [Matrix.mul_add, Matrix.add_mul])

/-- The Minkowski product `p·a` of two spinor momenta, `½ (tr P tr Q - tr (P Q))`. -/
noncomputable def pairing (P Q : Herm2) : ℝ :=
  (P.1.trace * Q.1.trace - (P.1 * Q.1).trace).re / 2

lemma pairing_add_right (P Q R : Herm2) : pairing P (Q + R) = pairing P Q + pairing P R := by
  simp only [pairing, coe_add_herm, Matrix.trace_add, Complex.sub_re, Complex.add_re, mul_add]
  ring

lemma pairing_zero_right (P : Herm2) : pairing P 0 = 0 := by
  simp [pairing]

/-- The polarisation identity: `det (P + Q) = det P + det Q + (tr P tr Q - tr (P Q))`. -/
lemma det_add_herm (P Q : Herm2) :
    (P + Q).1.det = P.1.det + Q.1.det + (P.1.trace * Q.1.trace - (P.1 * Q.1).trace) := by
  simp only [coe_add_herm, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **The Minkowski product is Lorentz invariant.** -/
theorem pairing_smul (A : SL2C) (P Q : Herm2) : pairing (A • P) (A • Q) = pairing P Q := by
  have h1 := det_add_herm (A • P) (A • Q)
  have h2 := det_add_herm P Q
  rw [← smul_add, det_smul, det_smul, det_smul] at h1
  have h3 : ((A • P).1.trace * (A • Q).1.trace - ((A • P).1 * (A • Q).1).trace) =
      (P.1.trace * Q.1.trace - (P.1 * Q.1).trace) := by
    have := h1.symm.trans h2
    linear_combination this
  unfold pairing
  rw [h3]

/-- The pairing of the matrices of two four-vectors is `p₀a₀ - p₁a₁ - p₂a₂ - p₃a₃`. -/
theorem pairing_ofVec (p a : Fin 4 → ℝ) :
    pairing (ofVec p) (ofVec a) = p 0 * a 0 - p 1 * a 1 - p 2 * a 2 - p 3 * a 3 := by
  simp only [pairing, ofVec, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sub_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-! ## The group -/

/-- The action of `SL(2,ℂ)` on the translation group by Lorentz transformations. -/
def lorentzAut : SL2C →* MulAut (Multiplicative Herm2) where
  toFun A := (DistribMulAction.toAddAut SL2C Herm2 A).toMultiplicative
  map_one' := by
    refine MulEquiv.ext fun a => ?_
    exact congrArg Multiplicative.ofAdd (one_smul SL2C a.toAdd)
  map_mul' A B := by
    refine MulEquiv.ext fun a => ?_
    exact congrArg Multiplicative.ofAdd (mul_smul A B a.toAdd)

/-- **The (double cover of the) Poincaré group** `ISL(2,ℂ) = ℝ^{1,3} ⋊ SL(2,ℂ)`. -/
abbrev ISL2C : Type := Multiplicative Herm2 ⋊[lorentzAut] SL2C

/-! ## Translations on the mass shell -/

variable {m : ℝ} (hm : 0 < m)

/-- The translation operator `(T(a) ψ)(P) = e^{i P·a} ψ(P)` on functions on the mass shell. -/
noncomputable def translateOp (n : ℕ) (a : Herm2) :
    (massShell m → Fin (n + 1) → ℂ) →ₗ[ℂ] (massShell m → Fin (n + 1) → ℂ) where
  toFun ψ P := Complex.exp (Complex.I * (pairing P.1 a : ℂ)) • ψ P
  map_add' ψ φ := by
    funext P
    simp
  map_smul' c ψ := by
    funext P
    simp only [RingHom.id_apply, Pi.smul_apply]
    exact smul_comm _ _ _

/-- The translation group acts on functions on the mass shell by `e^{i P·a}`. -/
noncomputable def translateRep (n : ℕ) :
    Representation ℂ (Multiplicative Herm2) (massShell m → Fin (n + 1) → ℂ) where
  toFun a := translateOp (m := m) n a.toAdd
  map_one' := by
    ext ψ P i
    simp [translateOp, pairing_zero_right]
  map_mul' a b := by
    ext ψ P i
    simp only [Module.End.mul_apply, translateOp, LinearMap.coe_mk, AddHom.coe_mk, toAdd_mul,
      pairing_add_right, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [mul_add, Complex.exp_add]
    ring

/-- **Covariance**: `U(A) T(a) U(A)⁻¹ = T(A a)`, the defining relation of the semidirect product. -/
theorem inducedRep_translate (n : ℕ) (A : SL2C) (a : Herm2) :
    inducedRep hm n A ∘ₗ translateOp n a = translateOp n (A • a) ∘ₗ inducedRep hm n A := by
  ext ψ P i
  have h : pairing (shellSMul hm A⁻¹ P).1 a = pairing P.1 (A • a) := by
    have e : A • (shellSMul hm A⁻¹ P).1 = P.1 := congrArg Subtype.val (shellSMul_inv_smul hm A P)
    rw [← pairing_smul A, e]
  simp only [LinearMap.comp_apply, inducedRep_apply, translateOp, LinearMap.coe_mk, AddHom.coe_mk,
    h, Matrix.mulVec_smul]

/-- **The representation of the Poincaré group on the massive one-particle space**:
`(a, A) ↦ T(a) U(A)`, i.e. `(U(a,A) ψ)(P) = e^{i P·a} D(W(A, A⁻¹P)) ψ(A⁻¹ P)`. -/
noncomputable def poincareRep (n : ℕ) :
    Representation ℂ ISL2C (massShell m → Fin (n + 1) → ℂ) where
  toFun g := translateRep (m := m) n g.left * inducedRep hm n g.right
  map_one' := by
    simp
  map_mul' g h := by
    have cov : translateRep (m := m) n (lorentzAut g.right h.left) * inducedRep hm n g.right =
        inducedRep hm n g.right * translateRep (m := m) n h.left :=
      (inducedRep_translate hm n g.right h.left.toAdd).symm
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul]
    calc translateRep (m := m) n g.left * translateRep (m := m) n (lorentzAut g.right h.left) *
          (inducedRep hm n g.right * inducedRep hm n h.right)
        = translateRep (m := m) n g.left *
            (translateRep (m := m) n (lorentzAut g.right h.left) * inducedRep hm n g.right) *
              inducedRep hm n h.right := by simp only [mul_assoc]
      _ = translateRep (m := m) n g.left *
            (inducedRep hm n g.right * translateRep (m := m) n h.left) *
              inducedRep hm n h.right := by rw [cov]
      _ = _ := by simp only [mul_assoc]

/-- On the mass shell the momentum square is `m²`: `P² = det P = m²`. -/
theorem det_of_mem_massShell (P : massShell m) : P.1.1.det = ((m ^ 2 : ℝ) : ℂ) := P.2.1

end Lightlike.Lorentz.Poincare
