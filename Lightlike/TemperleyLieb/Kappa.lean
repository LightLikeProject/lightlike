import Mathlib
import Lightlike.TemperleyLieb.Contraction

/-!
# Absorption of the sub-blocks of a projector

`jwAt q (s+1) n · jwAt q s (n+1) = jwAt q s (n+1)`: the projector on `n+1` strands absorbs the projector on its last
`n` strands (the first `n` strands are `JwProps.absL`); this is the mirror image.
-/

namespace Lightlike.TemperleyLieb

open Finsupp

variable {k : Type*} [Field k]

/-- The projector on `n + 1` strands absorbs, on the left, the projector on its last `n` strands. -/
theorem jwAt_absorb_suffix_left (q : kˣ) (s n : ℕ) (hd : ∀ j, j < n + 1 → chebD (loopVal q) j ≠ 0) :
    jwAt q (s + 1) n * jwAt q s (n + 1) = jwAt q s (n + 1) := by
  set N := s + n + 1 with hN
  have hρ := reflectOp_mul_self (k := k) N
  have m1 : jwAt q s (n + 1) = reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 s (n + 1) hd
    rwa [show 0 + s + (n + 1) = N by omega] at this
  have m2 : jwAt q (s + 1) n = reflectOp k N * jwAt q 0 n * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 (s + 1) n (fun j hj => hd j (by omega))
    rwa [show 0 + (s + 1) + n = N by omega] at this
  have hp := jwProps_of_le (isTL_shift q 0) (n + 1) hd (n + 1) le_rfl
  have h1 : jwAt q 0 n * jwAt q 0 (n + 1) = jwAt q 0 (n + 1) := hp.absL n (by omega)
  rw [m1, m2]
  calc reflectOp k N * jwAt q 0 n * reflectOp k N * (reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N)
      = reflectOp k N * (jwAt q 0 n * jwAt q 0 (n + 1)) * reflectOp k N := by
        simp only [mul_assoc, ← mul_assoc (reflectOp k N) (reflectOp k N), hρ, one_mul]
    _ = _ := by rw [h1]

/-- The projector on `n + 1` strands absorbs, on the right, the projector on its last `n` strands. -/
theorem jwAt_absorb_suffix_right (q : kˣ) (s n : ℕ) (hd : ∀ j, j < n + 1 → chebD (loopVal q) j ≠ 0) :
    jwAt q s (n + 1) * jwAt q (s + 1) n = jwAt q s (n + 1) := by
  set N := s + n + 1 with hN
  have hρ := reflectOp_mul_self (k := k) N
  have m1 : jwAt q s (n + 1) = reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 s (n + 1) hd
    rwa [show 0 + s + (n + 1) = N by omega] at this
  have m2 : jwAt q (s + 1) n = reflectOp k N * jwAt q 0 n * reflectOp k N := by
    have := jwAt_mirror (k := k) q 0 (s + 1) n (fun j hj => hd j (by omega))
    rwa [show 0 + (s + 1) + n = N by omega] at this
  have hp := jwProps_of_le (isTL_shift q 0) (n + 1) hd (n + 1) le_rfl
  have h1 : jwAt q 0 (n + 1) * jwAt q 0 n = jwAt q 0 (n + 1) := hp.absR n (by omega)
  rw [m1, m2]
  calc reflectOp k N * jwAt q 0 (n + 1) * reflectOp k N * (reflectOp k N * jwAt q 0 n * reflectOp k N)
      = reflectOp k N * (jwAt q 0 (n + 1) * jwAt q 0 n) * reflectOp k N := by
        simp only [mul_assoc, ← mul_assoc (reflectOp k N) (reflectOp k N), hρ, one_mul]
    _ = _ := by rw [h1]

end Lightlike.TemperleyLieb
