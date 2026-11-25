import Mathlib
import Lightlike.TemperleyLieb.Shift

/-!
# Recoupling: the two decompositions of the projector on three blocks

`P₃ = Q(a,b) p_c` is the sum of the first-bracketing tree idempotents `treeL e d` and also of the second-bracketing
ones `treeR f d'`.  Every `treeL e d` is one-dimensional inside `C (N-1)`, so the scalars `treeL · treeR · treeL`
are well defined: these are the recoupling coefficients, and their row sums are `1`.
-/

namespace Lightlike.TemperleyLieb

open scoped Classical

variable {k : Type*} [Field k]

/-- The projector on three blocks. -/
noncomputable def P3 (q : kˣ) (a b c : ℕ) : Module.End k (ModelSpace k) := Qab q a b * jwAt q (a + b) c

/-- `Q(a,b)` commutes with a projector on the strands beyond `a + b`. -/
theorem Qab_comm_jwAt (q : kˣ) (a b c : ℕ) :
    (Qab q a b : Module.End k (ModelSpace k)) * jwAt q (a + b) c = jwAt q (a + b) c * Qab q a b := by
  have h1 : (jwAt q 0 a : Module.End k (ModelSpace k)) * jwAt q (a + b) c = jwAt q (a + b) c * jwAt q 0 a :=
    jwAt_comm_jwAt q (by omega) c
  have h2 := congrArg (sh a) (jwAt_comm_jwAt (k := k) q (A := b) (s := b) le_rfl c)
  rw [sh_mul, sh_mul, sh_jwAt, sh_jwAt] at h2
  simp only [zero_add] at h2
  rw [add_comm b a] at h2
  unfold Qab
  rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]

/-- `treeL · P₃ = treeL`. -/
theorem treeL_mul_P3 (q : kˣ) (a b c e d : ℕ) (hea : e ≤ a) (heb : e ≤ b)
    (hd : ∀ j, j ≤ a + b + c → chebD (loopVal q) j ≠ 0) :
    treeL q a b c e d * P3 q a b c = treeL q a b c e d := by
  have hdAc : ∀ j, j ≤ a + b - 2 * e + c → chebD (loopVal q) j ≠ 0 := fun j hj => hd j (by omega)
  have hQ := Qab_idem (k := k) q a b (fun j hj => hd j (by omega))
  have hnc := nestCap_mul_jwAt (k := k) q (l := a - e) (s := a + b - 2 * e) (by omega) c e
  rw [show a + b - 2 * e + 2 * e = a + b by omega] at hnc
  have hEJ := Eop_mul_jwAt_shift (k := k) q (a + b - 2 * e) c d hdAc
  unfold treeL P3
  rw [smul_mul_assoc]
  congr 1
  calc Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e * Qab q a b *
        (Qab q a b * jwAt q (a + b) c)
      = Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e *
        ((Qab q a b * Qab q a b) * jwAt q (a + b) c) := by simp only [mul_assoc]
    _ = Qab q a b * nestCup q (a - e) e * Eop q (a + b - 2 * e) c d * nestCap q (a - e) e *
        (jwAt q (a + b) c * Qab q a b) := by rw [hQ, Qab_comm_jwAt]
    _ = Qab q a b * nestCup q (a - e) e * (Eop q (a + b - 2 * e) c d * jwAt q (a + b - 2 * e) c) *
        nestCap q (a - e) e * Qab q a b := by
          simp only [← mul_assoc]; rw [mul_assoc _ (nestCap q (a - e) e), hnc]; simp only [mul_assoc]
    _ = _ := by rw [hEJ]

end Lightlike.TemperleyLieb
