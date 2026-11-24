import Lightlike.TuraevViro.FusionRing

/-!
# The S matrix of SU(2) at level `r - 2` (QU3, first row)

`sMat r a b = √(2/r) sin(π (a+1)(b+1)/r)` for the colours `a, b ∈ {0, …, r - 2}` (doubled spins).

* `sMat_comm`: `S` is symmetric;
* `sMat_zero_left`: the row of the unit object, `S_{0 b} = S_{00} · [b + 1]_q`, so the quantum dimension is `S_{0b}/S_{00}`;
* `sMat_zero_zero_pos`: `S_{00} > 0` for `r ≥ 2`;
* `verlinde_zero`: the Verlinde formula for the row of the unit object, `S_{0a} S_{0b} / S_{00} = Σ_c N_{ab}^c S_{0c}`
  (the multiplicativity of the quantum dimension, `fusion_dim`).

NOT proved: the Verlinde formula for the other rows (`Σ_c N_{ab}^c S_{cx}/S_{0x} = S_{ax} S_{bx}/S_{0x}²`), the orthogonality
`S² = 1` (here the charge conjugation is trivial), unitarity, and the modular relation with the T matrix.
No comparison with a published statement of the S matrix is claimed.
-/

open Finset Real

namespace Lightlike.TV

/-- The S matrix of SU(2) at level `r - 2`: `√(2/r) sin(π (a+1)(b+1)/r)`. -/
noncomputable def sMat (r a b : ℕ) : ℝ :=
  Real.sqrt (2 / r) * Real.sin (((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) * π / r)

/-- The S matrix is symmetric. -/
lemma sMat_comm (r a b : ℕ) : sMat r a b = sMat r b a := by
  unfold sMat; rw [mul_comm ((a + 1 : ℕ) : ℝ)]

/-- `S_{0 b} = S_{00} [b+1]_q`. -/
lemma sMat_zero_left {r : ℕ} (hr : 2 ≤ r) (b : ℕ) : sMat r 0 b = sMat r 0 0 * qnum r (b + 1) := by
  have hs := (sin_pi_div_pos hr).ne'
  unfold sMat qnum
  simp only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul]
  field_simp

/-- `S_{00} > 0`. -/
lemma sMat_zero_zero_pos {r : ℕ} (hr : 2 ≤ r) : 0 < sMat r 0 0 := by
  unfold sMat
  have hr' : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  refine mul_pos (Real.sqrt_pos.mpr (by positivity)) ?_
  simpa [mul_comm, div_eq_mul_inv] using sin_pi_div_pos hr

/-- **The Verlinde formula for the unit-object row**: `S_{0a} S_{0b} = S_{00} Σ_c N_{ab}^c S_{0c}`. -/
theorem verlinde_zero {r a b : ℕ} (hr : 2 ≤ r) (ha : a ≤ r - 2) (hb : b ≤ r - 2) :
    sMat r 0 a * sMat r 0 b = sMat r 0 0 * ∑ c ∈ range (r - 1), (fusionN r a b c : ℝ) * sMat r 0 c := by
  have h := fusion_dim hr ha hb
  have hsum : ∑ c ∈ range (r - 1), (fusionN r a b c : ℝ) * sMat r 0 c =
      sMat r 0 0 * ∑ c ∈ range (r - 1), (fusionN r a b c : ℝ) * qnum r (c + 1) := by
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [sMat_zero_left hr c]; ring
  rw [hsum, h, sMat_zero_left hr a, sMat_zero_left hr b]
  ring

end Lightlike.TV
