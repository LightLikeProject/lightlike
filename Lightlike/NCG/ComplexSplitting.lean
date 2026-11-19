import Lightlike.NCG.TensorForm

/-!
# The fundamental and the conjugate part of a real representation of a complex summand

T. Krajewski, arXiv:hep-th/9701081, Section 3.1, p. 10 (read): "`Mₙ(ℂ)` has two inequivalent irreducible
representations, the fundamental one and its complex conjugate". For a real-linear `*`-representation `π` of a real
`*`-algebra with a central element `u`, `u² = -1`, `u* = -u` (for a complex summand, `u = i · 1`), `π(u)` is a skew-adjoint
unitary, and `Q₊ = (1 - i π(u))/2`, `Q₋ = (1 + i π(u))/2` are complementary idempotents commuting with `π(A)`, with
`π(u) = i` on `Q₊ H` and `π(u) = -i` on `Q₋ H`. This is `Mₙ(ℂ) ⊗_ℝ ℂ ≅ Mₙ(ℂ) ⊕ Mₙ(ℂ)` in representation form.

* `Qp`, `Qm`, `Qp_add_Qm`, `pi_u_Qp`, `pi_u_Qm`, `pi_comm_Qp`, `pi_comm_Qm`;
* `Qp_mul_Qp`, `Qm_mul_Qm`, `Qp_mul_Qm`, `Qm_mul_Qp`, `star_Qp`, `star_Qm`: complementary orthogonal projections;
* `Qp_pi_smul`, `Qm_pi_smul`: `π` is complex-linear on the fundamental part and antilinear on the conjugate part;
* `QpR`, `QmR`, `J_Qp_J`, `J_Qm_J`, `QpR_add_QmR`, `pi_comm_QpR`, `pi_comm_QmR`, `Qp_comm_QpR`, `Qp_comm_QmR`: the parts
  for the right action, `J Q± J = (1 ± i J π(u) J)/2`, commuting with `π(A)` and with `Q₊`.
-/

namespace Lightlike.NCG

noncomputable section

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable (T : FiniteSpectralTriple A H) {u : A}

/-- `Q₊ = (1 - i π(u))/2`, the fundamental part. -/
def Qp (u : A) : H →L[ℂ] H := (1 / 2 : ℂ) • (1 - Complex.I • T.π u)

/-- `Q₋ = (1 + i π(u))/2`, the conjugate part. -/
def Qm (u : A) : H →L[ℂ] H := (1 / 2 : ℂ) • (1 + Complex.I • T.π u)

/-- `Q₊ + Q₋ = 1`. -/
lemma Qp_add_Qm (u : A) : Qp T u + Qm T u = 1 := by
  simp only [Qp, Qm, ← smul_add]
  rw [sub_add_add_cancel, ← two_smul ℂ (1 : H →L[ℂ] H), smul_smul]
  norm_num

/-- `π(u)² = -1` for `u² = -1`. -/
lemma pi_u_sq (hu : u * u = -1) : T.π u * T.π u = -1 := by
  rw [← map_mul, hu, map_neg, map_one]

/-- **`π(u) Q₊ = i Q₊`**: `π(u) = i` on the fundamental part. -/
lemma pi_u_Qp (hu : u * u = -1) : T.π u * Qp T u = Complex.I • Qp T u := by
  simp only [Qp, mul_smul_comm, mul_sub, mul_one, mul_smul_comm, pi_u_sq T hu, smul_sub, smul_neg, smul_smul]
  rw [show Complex.I * (1 / 2 * Complex.I) = -(1 / 2 : ℂ) by rw [mul_left_comm, Complex.I_mul_I]; ring]
  module

/-- **`π(u) Q₋ = -i Q₋`**: `π(u) = -i` on the conjugate part. -/
lemma pi_u_Qm (hu : u * u = -1) : T.π u * Qm T u = -Complex.I • Qm T u := by
  simp only [Qm, mul_smul_comm, mul_add, mul_one, pi_u_sq T hu, smul_add, smul_neg, smul_smul]
  rw [show -Complex.I * (1 / 2 * Complex.I) = (1 / 2 : ℂ) by rw [neg_mul, mul_left_comm, Complex.I_mul_I]; ring]
  module

/-- `π(a)` commutes with `Q₊` for central `u`. -/
lemma pi_comm_Qp (hc : ∀ a, u * a = a * u) (a : A) : T.π a * Qp T u = Qp T u * T.π a := by
  simp only [Qp, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, ← map_mul, hc a]

/-- `π(a)` commutes with `Q₋` for central `u`. -/
lemma pi_comm_Qm (hc : ∀ a, u * a = a * u) (a : A) : T.π a * Qm T u = Qm T u * T.π a := by
  simp only [Qm, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, ← map_mul, hc a]

/-- **`Q₊` is idempotent.** -/
lemma Qp_mul_Qp (hu : u * u = -1) : Qp T u * Qp T u = Qp T u := by
  simp only [Qp, smul_mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    pi_u_sq T hu, Complex.I_mul_I]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> norm_num

/-- **`Q₋` is idempotent.** -/
lemma Qm_mul_Qm (hu : u * u = -1) : Qm T u * Qm T u = Qm T u := by
  simp only [Qm, smul_mul_smul_comm, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    pi_u_sq T hu, Complex.I_mul_I]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> norm_num

/-- **`Q₊ Q₋ = 0`.** -/
lemma Qp_mul_Qm (hu : u * u = -1) : Qp T u * Qm T u = 0 := by
  simp only [Qp, Qm, smul_mul_smul_comm, sub_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    pi_u_sq T hu, Complex.I_mul_I]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> norm_num

/-- **`Q₋ Q₊ = 0`.** -/
lemma Qm_mul_Qp (hu : u * u = -1) : Qm T u * Qp T u = 0 := by
  simp only [Qp, Qm, smul_mul_smul_comm, add_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    pi_u_sq T hu, Complex.I_mul_I]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> norm_num

/-- **`Q₊` is self-adjoint** for `u* = -u`. -/
lemma star_Qp (hs : star u = -u) : star (Qp T u) = Qp T u := by
  simp only [Qp, star_smul, star_sub, star_one, ← map_star, hs, map_neg, Complex.star_def, Complex.conj_I,
    map_div₀, map_one, map_ofNat, smul_neg, neg_smul, sub_neg_eq_add]
  module

/-- **`Q₋` is self-adjoint** for `u* = -u`. -/
lemma star_Qm (hs : star u = -u) : star (Qm T u) = Qm T u := by
  simp only [Qm, star_smul, star_add, star_one, ← map_star, hs, map_neg, Complex.star_def, Complex.conj_I,
    map_div₀, map_one, map_ofNat, smul_neg, neg_smul, neg_neg]

section ComplexAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (T' : FiniteSpectralTriple (MatSum n) H)

/-- `c a = Re c · a + Im c · (i a)` in `⊕ Mₙᵢ(ℂ)`. -/
lemma smul_eq_re_add_im (c : ℂ) (a : MatSum n) :
    c • a = c.re • a + c.im • ((Complex.I • (1 : MatSum n)) * a) := by
  rw [smul_one_mul]
  ext i α β
  simp only [Pi.add_apply, Pi.smul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im c]
  ring

/-- **On the fundamental part `π` is complex-linear**: `Q₊ π(c a) = c Q₊ π(a)` (Krajewski, Section 3.1, p. 10: the
fundamental representation). -/
theorem Qp_pi_smul (c : ℂ) (a : MatSum n) :
    Qp T' (Complex.I • 1) * T'.π (c • a) = c • (Qp T' (Complex.I • 1) * T'.π a) := by
  have hu : (Complex.I • (1 : MatSum n)) * (Complex.I • 1) = -1 := by
    rw [smul_one_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hc : ∀ b : MatSum n, (Complex.I • (1 : MatSum n)) * b = b * (Complex.I • 1) := fun b => by
    rw [smul_one_mul, mul_smul_one]
  have hπ : T'.π (c • a) = (c.re : ℂ) • T'.π a + (c.im : ℂ) • (T'.π (Complex.I • 1) * T'.π a) := by
    rw [smul_eq_re_add_im, map_add, map_smul, map_smul, map_mul]
    rfl
  rw [hπ, mul_add, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← pi_comm_Qp T' hc (Complex.I • 1), pi_u_Qp T' hu, smul_mul_assoc,
    smul_smul, ← add_smul]
  congr 1
  exact Complex.re_add_im c

/-- **On the conjugate part `π` is antilinear**: `Q₋ π(c a) = c̄ Q₋ π(a)` (Krajewski, Section 3.1, p. 10: the complex
conjugate representation). -/
theorem Qm_pi_smul (c : ℂ) (a : MatSum n) :
    Qm T' (Complex.I • 1) * T'.π (c • a) = (starRingEnd ℂ c) • (Qm T' (Complex.I • 1) * T'.π a) := by
  have hu : (Complex.I • (1 : MatSum n)) * (Complex.I • 1) = -1 := by
    rw [smul_one_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
  have hc : ∀ b : MatSum n, (Complex.I • (1 : MatSum n)) * b = b * (Complex.I • 1) := fun b => by
    rw [smul_one_mul, mul_smul_one]
  have hπ : T'.π (c • a) = (c.re : ℂ) • T'.π a + (c.im : ℂ) • (T'.π (Complex.I • 1) * T'.π a) := by
    rw [smul_eq_re_add_im, map_add, map_smul, map_smul, map_mul]
    rfl
  rw [hπ, mul_add, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← pi_comm_Qm T' hc (Complex.I • 1), pi_u_Qm T' hu, smul_mul_assoc,
    smul_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

end ComplexAlgebra

section RightAction

variable (R : RealStructure T)

/-- `J Q₊ J`, the fundamental part for the right action. -/
def QpR (u : A) : H →ₗ[ℂ] H := (1 / 2 : ℂ) • (1 + Complex.I • rightOp R u)

/-- `J Q₋ J`, the conjugate part for the right action. -/
def QmR (u : A) : H →ₗ[ℂ] H := (1 / 2 : ℂ) • (1 - Complex.I • rightOp R u)

/-- **`J Q₊ J = (1 + i J π(u) J)/2`**: `J` is antilinear, so conjugating `Q₊` by `J` flips the sign of `i`. -/
lemma J_Qp_J (u : A) (x : H) : R.J (Qp T u (R.J x)) = QpR T R u x := by
  simp only [Qp, QpR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, LinearMap.map_smulₛₗ, map_sub, R.J_J,
    rightOp_apply, Complex.conj_I, map_div₀, map_one, map_ofNat]
  module

/-- **`J Q₋ J = (1 - i J π(u) J)/2`.** -/
lemma J_Qm_J (u : A) (x : H) : R.J (Qm T u (R.J x)) = QmR T R u x := by
  simp only [Qm, QmR, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.map_smulₛₗ, map_add, R.J_J,
    rightOp_apply, Complex.conj_I, map_div₀, map_one, map_ofNat]
  module

/-- `J Q₊ J + J Q₋ J = 1`. -/
lemma QpR_add_QmR (u : A) : QpR T R u + QmR T R u = 1 := by
  simp only [QpR, QmR, ← smul_add]
  rw [add_add_sub_cancel, ← two_smul ℂ (1 : H →ₗ[ℂ] H), smul_smul]
  norm_num

/-- **The right-action parts commute with `π(A)`** (the order-zero condition). -/
lemma pi_comm_QpR (u a : A) (x : H) : T.π a (QpR T R u x) = QpR T R u (T.π a x) := by
  simp only [QpR, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, map_smul, map_add,
    rightOp_apply, R.order_zero a u x]

/-- `J Q₋ J` commutes with `π(A)` (the order-zero condition). -/
lemma pi_comm_QmR (u a : A) (x : H) : T.π a (QmR T R u x) = QmR T R u (T.π a x) := by
  simp only [QmR, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_sub,
    rightOp_apply, R.order_zero a u x]

/-- **The left and the right parts commute**: `Q₊`, `Q₋` lie in the span of `1` and `π(u)`. -/
lemma Qp_comm_QpR (u v : A) (x : H) : Qp T u (QpR T R v x) = QpR T R v (Qp T u x) := by
  simp only [Qp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    map_smul, map_sub, pi_comm_QpR T R v u x]

/-- `Q₊` commutes with `J Q₋ J`. -/
lemma Qp_comm_QmR (u v : A) (x : H) : Qp T u (QmR T R v x) = QmR T R v (Qp T u x) := by
  simp only [Qp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    map_smul, map_sub, pi_comm_QmR T R v u x]

end RightAction

end

end Lightlike.NCG
