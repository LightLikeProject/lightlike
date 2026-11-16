import Lightlike.TuraevViro.Reflect.RacahGTerm

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
