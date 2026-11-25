import Mathlib
import Lightlike.TemperleyLieb.GramVanish

/-!
# The expansion of a second-bracketing tree vector in the first-bracketing basis

`U_R(f,d') = Σ_{e,d} α(e,d) U_L(e,d)` with `α = (κ_e κ_d)⁻¹ g(e,d; f,d')` where `g` is the Gram scalar
(`g = 0` for different total channels).
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- The first-bracketing tree vector `V_e V_d`. -/
noncomputable def UL (q : kˣ) (a b c e d : ℕ) : Module.End k (ModelSpace k) :=
  Vop q a b e * Vop q (a + b - 2 * e) c d

/-- The dual first-bracketing tree vector `W_d W_e`. -/
noncomputable def ULd (q : kˣ) (a b c e d : ℕ) : Module.End k (ModelSpace k) :=
  Wop q (a + b - 2 * e) c d * Wop q a b e

/-- The second-bracketing tree vector `sh V_f · V_{d'}`. -/
noncomputable def UR (q : kˣ) (a b c f d' : ℕ) : Module.End k (ModelSpace k) :=
  sh a (Vop q b c f) * Vop q a (b + c - 2 * f) d'

/-- `treeL = (κ_e κ_d)⁻¹ · U_L U_L'`. -/
theorem treeL_eq_UU (q : kˣ) (a b c e d : ℕ)
    (hd : ∀ j, j ≤ a + b - 2 * e + c → chebD (loopVal q) j ≠ 0) :
    treeL q a b c e d = ((kapRec q a b e)⁻¹ * (kapRec q (a + b - 2 * e) c d)⁻¹) •
      (UL q a b c e d * ULd q a b c e d) := by
  rw [treeL_eq q a b c e d hd]
  unfold Eop UL ULd
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]

/-- The right projector of `U_L` is absorbed. -/
theorem UL_mul_proj (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b) (hdA : d ≤ a + b - 2 * e) (hdc : d ≤ c)
    (hd : ∀ j, j ≤ a + b - 2 * e + c → chebD (loopVal q) j ≠ 0) :
    UL q a b c e d * jwAt q 0 (a + b - 2 * e + c - 2 * d) = UL q a b c e d := by
  unfold UL
  rw [mul_assoc, Vop_mul_jwAt (k := k) q (a + b - 2 * e) c hd hdA hdc]

/-- `P₃ · U_R = U_R`. -/
theorem P3_mul_UR (q : kˣ) (a b c f d' : ℕ) (hfb : f ≤ b) (hfc : f ≤ c)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    P3 q a b c * UR q a b c f d' = UR q a b c f d' := by
  have hdc : ∀ j, j ≤ a + (b + c - 2 * f) → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hQs : sh a (Qab q b c : Module.End k (ModelSpace k)) = jwAt q a b * jwAt q (b + a) c := by
    unfold Qab; rw [sh_mul, sh_jwAt, sh_jwAt]; simp
  have hsh := congrArg (sh a) (Qab_idem (k := k) q b c (fun j hj => hd j (by omega)))
  rw [sh_mul, hQs] at hsh
  have hp : (jwAt q 0 a : Module.End k (ModelSpace k)) * (jwAt q a b * jwAt q (b + a) c) =
      (jwAt q a b * jwAt q (b + a) c) * jwAt q 0 a := by
    rw [← mul_assoc, jwAt_comm_jwAt q le_rfl b, mul_assoc, jwAt_comm_jwAt q (by omega) c, mul_assoc]
  have hP3 : P3 q a b c = jwAt q 0 a * (jwAt q a b * jwAt q (b + a) c) := by
    rw [← jwAt_mul_sh_Qab, hQs]
  have hQ := jwAt_mul_Qab' (k := k) q a (b + c - 2 * f) hdc
  have hpJ := jwAt_comm_jwAt (k := k) q (A := a) (s := a) le_rfl (b + c - 2 * f)
  have hpn := jwAt_mul_nestCup (k := k) q (a := a) (l := b - f + a) (by omega) f
  unfold UR
  rw [sh_Vop, hP3]
  set Qs : Module.End k (ModelSpace k) := jwAt q a b * jwAt q (b + a) c with hQsdef
  calc jwAt q 0 a * Qs * (Qs * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d')
      = jwAt q 0 a * (Qs * Qs) * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        simp only [mul_assoc]
    _ = (jwAt q 0 a * Qs) * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        rw [hsh]
    _ = Qs * jwAt q 0 a * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        rw [hp]
    _ = Qs * (nestCup q (b - f + a) f * jwAt q 0 a) * jwAt q a (b + c - 2 * f) * Vop q a (b + c - 2 * f) d' := by
        rw [← hpn]; simp only [mul_assoc]
    _ = Qs * nestCup q (b - f + a) f * (jwAt q 0 a * jwAt q a (b + c - 2 * f)) * Vop q a (b + c - 2 * f) d' := by
        simp only [mul_assoc]
    _ = Qs * nestCup q (b - f + a) f * (jwAt q a (b + c - 2 * f) * jwAt q 0 a) * Vop q a (b + c - 2 * f) d' := by
        rw [hpJ]
    _ = Qs * nestCup q (b - f + a) f * jwAt q a (b + c - 2 * f) * (jwAt q 0 a * Vop q a (b + c - 2 * f) d') := by
        simp only [mul_assoc]
    _ = _ := by
        have : jwAt q 0 a * Vop q a (b + c - 2 * f) d' = Vop q a (b + c - 2 * f) d' := by
          unfold Vop; rw [← mul_assoc, ← mul_assoc, hQ]
        rw [this]

end Lightlike.TemperleyLieb
