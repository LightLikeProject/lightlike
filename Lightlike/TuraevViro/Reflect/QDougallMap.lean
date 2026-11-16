import Lightlike.TuraevViro.Reflect.JacksonWZ
import Lightlike.TuraevViro.Reflect.RacahDc

/-!
# Steps toward the boundary evaluation `QDougall` from Jackson's sum

The boundary evaluation `QDougall` is the weighted norm of the column of the lowest sixth colour of
the q-6j matrix. At that colour the q-Racah sum has one term (`Sj_single`), so the weighted terms are
products of quantum factorials, and Jackson's terminating very-well-poised sum evaluates their sum
once the terms are matched with its summand `Tj` at `Q = uC r ^ 2`. This file holds the first two
ingredients of that matching.

## Main results

* `one_sub_Q_zpow`: `1 - Q^m = - u^m (u^m - u^{-m})`, so every factor `1 - Q^m` of the series is a
  bracket `bk (uC r ^ m)` times a power of `u`, and `bk (uC r ^ m) / (u - u⁻¹)` is the quantum
  integer `qZ r m` (`bk_uC_div`).
* `Tj_succ`: the ratio of consecutive Jackson summands, when the denominators do not vanish.

## Implementation notes

The matching itself (the terms of `QDougall` as a constant times `Tj`) is not in this file; it is
checked numerically by `scripts/qracah/qd_map_check.py`.
-/

namespace Lightlike.TV.Refl
open Finset

/-- `1 - Q^m = - u^m (u^m - u^{-m})` with `Q = u²`: the factors of Jackson's series are brackets. -/
lemma one_sub_Q_zpow (r : ℕ) (m : ℤ) :
    1 - (uC r ^ 2) ^ m = - uC r ^ m * bk (uC r ^ m) := by
  have hu : uC r ^ m ≠ 0 := zpow_ne_zero m (uC_ne_zero r)
  have h2 : (uC r ^ 2) ^ m = (uC r ^ m) ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [h2, bk]
  field_simp
  ring

set_option maxHeartbeats 800000 in
/-- One step of the Jackson summand, when the denominators involved do not vanish. -/
lemma Tj_succ {q a b c x : ℂ} (k : ℕ) (ha : 1 - a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h0 : 1 - a * q ^ (2 * k) ≠ 0)
    (hq : pk q q k ≠ 0) (hb' : pk (a * q / b) q k ≠ 0) (hc' : pk (a * q / c) q k ≠ 0)
    (hx : pk (a * q * x) q k ≠ 0)
    (e1 : 1 - q * q ^ k ≠ 0) (e2 : 1 - a * q / b * q ^ k ≠ 0) (e3 : 1 - a * q / c * q ^ k ≠ 0)
    (e4 : 1 - a * q * x * q ^ k ≠ 0) :
    Tj q a b c x (k + 1) = Tj q a b c x k *
      ((1 - a * q ^ (2 * (k + 1))) / (1 - a * q ^ (2 * k)) *
        ((1 - a * q ^ k) * (1 - b * q ^ k) * (1 - c * q ^ k) * (1 - x⁻¹ * q ^ k)) /
        ((1 - q * q ^ k) * (1 - a * q / b * q ^ k) * (1 - a * q / c * q ^ k) *
          (1 - a * q * x * q ^ k)) * (a * q * x / (b * c))) := by
  have hP : ∀ z : ℂ, pk z q (k + 1) = pk z q k * (1 - z * q ^ k) := fun z => rfl
  have h2k : q ^ (2 * (k + 1)) = (q ^ k) ^ 2 * q ^ 2 := by ring
  have h2k' : q ^ (2 * k) = (q ^ k) ^ 2 := by ring
  rw [h2k'] at h0
  simp only [Tj, hP, pow_succ (a * q * x / (b * c)) k, h2k, h2k']
  generalize pk a q k = A
  generalize pk b q k = B
  generalize pk c q k = C
  generalize pk x⁻¹ q k = X
  generalize pk q q k = P1 at hq ⊢
  generalize pk (a * q / b) q k = P2 at hb' ⊢
  generalize pk (a * q / c) q k = P3 at hc' ⊢
  generalize pk (a * q * x) q k = P4 at hx ⊢
  generalize (a * q * x / (b * c)) ^ k = W
  generalize a * q * x / (b * c) = Z
  generalize q ^ k = m at *
  generalize a * q / b = ab at *
  generalize a * q / c = ac at *
  generalize x⁻¹ = xi at *
  generalize hD1 : 1 - a * m ^ 2 = D0 at h0 ⊢
  generalize hD2 : 1 - q * m = D1 at e1 ⊢
  generalize hD3 : 1 - ab * m = D2 at e2 ⊢
  generalize hD4 : 1 - ac * m = D3 at e3 ⊢
  generalize hD5 : 1 - a * q * x * m = D4 at e4 ⊢
  field_simp

end Lightlike.TV.Refl
