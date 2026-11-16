import Lightlike.TuraevViro.Reflect.RacahGTerm

/-!
# Polynomials without the variable `Z`

`noZ P` tests that no monomial of the reflected polynomial `P` contains `Z`, and `eval_noZ` shows
that the value of such a polynomial does not depend on `Z`. `RacahRec` uses this to evaluate the
recurrence coefficients independently of `Z`. Written by hand, not generated.

## Main results

* `eval_noZ`: if `noZ P = true`, the evaluation of `P` is the same for every value of `Z`.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

variable {K : Type*} [Field K]

section Pointwise

/-- A polynomial with no `Z` in any monomial. -/
def noZ (P : Poly) : Bool := P.all fun t => t.1.e7 == 0

theorem eval_noZ (P : Poly) (h : noZ P = true) (u p1 p2 p3 p4 q2 q3 Z Z' : K) :
    Poly.eval (env u p1 p2 p3 p4 q2 q3 Z) P = Poly.eval (env u p1 p2 p3 p4 q2 q3 Z') P := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    obtain ⟨m, a⟩ := t
    simp only [noZ, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ih' := ih (by simpa [noZ] using h.2)
    have hm : Mono.eval (env u p1 p2 p3 p4 q2 q3 Z) m = Mono.eval (env u p1 p2 p3 p4 q2 q3 Z') m := by
      simp only [Mono.eval, env, h.1, zpow_zero, mul_one]
    simp only [Poly.eval, hm, ih']

end Pointwise

end Lightlike.TV.Refl
