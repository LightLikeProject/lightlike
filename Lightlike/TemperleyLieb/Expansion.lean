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

end Lightlike.TemperleyLieb
