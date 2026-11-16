import Lightlike.TuraevViro.Reflect.RacahRoot

/-!
# Telescoping the q-Racah recurrence at the root of unity `u = e^{iπ/r}`

Summing the pointwise recurrence over a range of `z` turns the right-hand side `G(z+1) - G(z)`
into `G(L+n) - G(L)`, which vanishes when `G` vanishes at both ends. The hypotheses are explicit:
the bounds `z - a_i ≤ r - 2`, `b_j - z ≤ r - 2` that keep the local step relations valid on the
range, and the nonvanishing of the four quantum integers that occur as denominators.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Real Finset

section General
variable {K : Type*} [Field K] {u : K} {N : ℤ} {Fi Pn : ℤ → K}

/-- The telescoped recurrence over `z = L, ..., L + n - 1`, in any field. -/
theorem telescope (hu : u ≠ 0) (hd : u - u⁻¹ ≠ 0) (h2 : (2 : K) ≠ 0)
    (hF : ∀ n : ℤ, n ≤ N → Fi n = bk (u ^ (n + 1)) / (u - u⁻¹) * Fi (n + 1))
    (a1 a2 a3 a4 b1 b2 b3 L : ℤ) (n : ℕ) (p1 p2 p3 p4 q2 q3 : K)
    (hP : ∀ z : ℤ, L ≤ z → z < L + n → Pn (z + 1 + 1) = bk (u ^ (z + 1 + 1)) / (u - u⁻¹) * Pn (z + 1))
    (hB1 : ∀ z, L ≤ z → z < L + n → z - a1 ≤ N) (hB2 : ∀ z, L ≤ z → z < L + n → z - a2 ≤ N)
    (hB3 : ∀ z, L ≤ z → z < L + n → z - a3 ≤ N) (hB4 : ∀ z, L ≤ z → z < L + n → z - a4 ≤ N)
    (hB5 : ∀ z, L ≤ z → z < L + n → b1 - z - 1 ≤ N) (hB6 : ∀ z, L ≤ z → z < L + n → b2 - z ≤ N)
    (hB7 : ∀ z, L ≤ z → z < L + n → b3 - z ≤ N)
    (hp1 : p1 = u ^ a1) (hp2 : p2 = u ^ a2) (hp3 : p3 = u ^ a3) (hp4 : p4 = u ^ a4)
    (hq2 : q2 = u ^ b2) (hq3 : q3 = u ^ b3) (hb : u ^ b1 = p1 * p2 * p3 * p4 * q2⁻¹ * q3⁻¹)
    (hQ0 : recCoef fQ0 u p1 p2 p3 p4 q2 q3 ≠ 0) (hQ1 : recCoef fQ1 u p1 p2 p3 p4 q2 q3 ≠ 0)
    (hQ2 : recCoef fQ2 u p1 p2 p3 p4 q2 q3 ≠ 0) (hDc : recCoef Dc u p1 p2 p3 p4 q2 q3 ≠ 0)
    (hG0 : Gq (Fi := Fi) (Pn := Pn) u (rhoC u p1 p2 p3 p4 q2 q3) a1 a2 a3 a4 b1 b2 b3 L = 0)
    (hG1 : Gq (Fi := Fi) (Pn := Pn) u (rhoC u p1 p2 p3 p4 q2 q3) a1 a2 a3 a4 b1 b2 b3 (L + n) = 0) :
    ∑ k ∈ range n,
      (2 * (recCoef fNa u p1 p2 p3 p4 q2 q3 / 2 /
          (recCoef fQ1 u p1 p2 p3 p4 q2 q3 * recCoef fQ2 u p1 p2 p3 p4 q2 q3))
        * tt Fi Pn (a1 + 1) a2 a3 (a4 + 1) b1 (b2 + 1) (b3 + 1) (L + k)
      + 2 * (recCoef fbn u p1 p2 p3 p4 q2 q3 /
          (2 * recCoef fQ0 u p1 p2 p3 p4 q2 q3 * recCoef fQ2 u p1 p2 p3 p4 q2 q3))
        * tt Fi Pn a1 a2 a3 a4 b1 b2 b3 (L + k)
      + 2 * (recCoef fNc u p1 p2 p3 p4 q2 q3 / 2 /
          (recCoef fQ0 u p1 p2 p3 p4 q2 q3 * recCoef fQ1 u p1 p2 p3 p4 q2 q3))
        * tt Fi Pn (a1 - 1) a2 a3 (a4 - 1) b1 (b2 - 1) (b3 - 1) (L + k)
      - recCoef fCq u p1 p2 p3 p4 q2 q3 * tt Fi Pn a1 a2 a3 a4 b1 b2 b3 (L + k)) = 0 := by
  have e := Finset.sum_range_sub (fun k : ℕ =>
    Gq (Fi := Fi) (Pn := Pn) u (rhoC u p1 p2 p3 p4 q2 q3) a1 a2 a3 a4 b1 b2 b3 (L + k)) n
  simp only [Nat.cast_succ, ← add_assoc, Nat.cast_zero, add_zero] at e
  rw [hG0, hG1, sub_zero] at e
  rw [← e]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hk0 : (0 : ℤ) ≤ k := by positivity
  have hkn : (k : ℤ) < n := by exact_mod_cast hk'
  have := pointwise (Fi := Fi) (Pn := Pn) hu hd h2 hF a1 a2 a3 a4 b1 b2 b3 (L + k) p1 p2 p3 p4 q2 q3
    (hP _ (by omega) (by omega))
    (hB1 _ (by omega) (by omega)) (hB2 _ (by omega) (by omega)) (hB3 _ (by omega) (by omega))
    (hB4 _ (by omega) (by omega)) (hB5 _ (by omega) (by omega)) (hB6 _ (by omega) (by omega))
    (hB7 _ (by omega) (by omega)) hp1 hp2 hp3 hp4 hq2 hq3 hb hQ0 hQ1 hQ2 hDc
  rw [this]

end General

end Lightlike.TV.Refl
