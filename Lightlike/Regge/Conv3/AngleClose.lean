import Lightlike.Regge.Conv3.DsqLipschitz
import Lightlike.Regge.Conv3.JetCore

/-!
# Replacing the true lengths by the jet polynomial changes the dihedral angle by `O(ε³)`

If the squared lengths `T` of a tetrahedron differ from `ε² (q + ε c + ε² ρ)` by at most `C5 ε⁵`, with `q`
admissible, `c`, `ρ` bounded and `Dsq` Lipschitz near `q`, then `Dsq T` and `Dsq (ε² (q + ε c + ε² ρ))`
differ by at most `C0 C5 ε³` (`dsq_close`). The dihedral angle is invariant under the scaling by `ε²`,
and both rescaled lengths stay within the Lipschitz ball of `q`.

## Main results

* `dsq_close`: the angle error of an `ε⁵` error in the squared lengths.

**Limits.** An estimate for one tetrahedron with the constants as hypotheses; it does not say where they
come from.
-/

open Real Matrix Lightlike Filter Topology Metric Set
namespace Lightlike.Regge.Conv3

/-- **Replacing the true lengths by the jet polynomial changes the angle by `O(ε³)`.** Let `q` be admissible
lengths with `a ≤ q 0`, `Dsq` Lipschitz with constant `C0` on the `δ`-ball around `q`, `δ ≤ a/2`, and
`T` lengths within `C5 ε⁵` of `ε² (q + ε c + ε² ρ)`, with `‖c‖, ‖ρ‖ ≤ B` and
`(2 B + |C5| + 1) ε ≤ δ/2`, `0 < ε ≤ 1`. Then `|Dsq T - Dsq (ε² (q + ε c + ε² ρ))| ≤ C0 C5 ε³`. -/
theorem dsq_close {q c ρ T : Fin 6 → ℝ} {ε δ a B C0 C5 : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq0 : a ≤ q 0) (ha : 0 < a) (hδ : δ ≤ a / 2) (hδ0 : 0 < δ) (hC0 : 0 ≤ C0)
    (hc : ‖c‖ ≤ B) (hρ : ‖ρ‖ ≤ B)
    (hT : ‖T - ε ^ 2 • (q + ε • c + ε ^ 2 • ρ)‖ ≤ C5 * ε ^ 5)
    (hεE : (2 * B + |C5| + 1) * ε ≤ δ / 2)
    (hlip : ∀ L L' : Fin 6 → ℝ, ‖L - q‖ ≤ δ → ‖L' - q‖ ≤ δ → |Dsq L' - Dsq L| ≤ C0 * ‖L' - L‖) :
    |Dsq T - Dsq (ε ^ 2 • (q + ε • c + ε ^ 2 • ρ))| ≤ C0 * C5 * ε ^ 3 := by
  have hε2pos : 0 < ε ^ 2 := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg c).trans hc
  set X2 : Fin 6 → ℝ := q + ε • c + ε ^ 2 • ρ with hX2
  set X1 : Fin 6 → ℝ := (ε ^ 2)⁻¹ • T with hX1
  have hinv : ε ^ 2 • X1 = T := by rw [hX1, smul_smul, mul_inv_cancel₀ hε2pos.ne', one_smul]
  have hd : ‖X1 - X2‖ ≤ C5 * ε ^ 3 := by
    have h1 := hT
    rw [← hinv, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hε2pos] at h1
    have : ε ^ 2 * ‖X1 - X2‖ ≤ ε ^ 2 * (C5 * ε ^ 3) := by
      calc ε ^ 2 * ‖X1 - X2‖ ≤ C5 * ε ^ 5 := h1
        _ = ε ^ 2 * (C5 * ε ^ 3) := by ring
    exact le_of_mul_le_mul_left this hε2pos
  have hX2q : ‖X2 - q‖ ≤ 2 * B * ε := by
    have : X2 - q = ε • c + ε ^ 2 • ρ := by rw [hX2]; abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε, abs_of_pos hε2pos]
    have e1 : ε * ‖c‖ ≤ ε * B := mul_le_mul_of_nonneg_left hc hε.le
    have e2 : ε ^ 2 * ‖ρ‖ ≤ ε * B := by
      calc ε ^ 2 * ‖ρ‖ ≤ ε ^ 2 * B := mul_le_mul_of_nonneg_left hρ hε2pos.le
        _ ≤ ε * B := by nlinarith [mul_nonneg hB0 (mul_nonneg hε.le (sub_nonneg.2 hε1))]
    linarith
  have hε3 : ε ^ 3 ≤ ε := by nlinarith [mul_pos hε hε]
  have hEε : 2 * B * ε ≤ δ / 2 := by
    have : 2 * B * ε ≤ (2 * B + |C5| + 1) * ε := by nlinarith [abs_nonneg C5]
    exact this.trans hεE
  have hX1q : ‖X1 - q‖ ≤ δ / 2 := by
    calc ‖X1 - q‖ = ‖(X1 - X2) + (X2 - q)‖ := by congr 1; abel
      _ ≤ C5 * ε ^ 3 + 2 * B * ε := (norm_add_le _ _).trans (add_le_add hd hX2q)
      _ ≤ |C5| * ε + 2 * B * ε := by
          have h1 := le_abs_self C5
          have : C5 * ε ^ 3 ≤ |C5| * ε := by
            calc C5 * ε ^ 3 ≤ |C5| * ε ^ 3 := mul_le_mul_of_nonneg_right h1 (by positivity)
              _ ≤ |C5| * ε := mul_le_mul_of_nonneg_left hε3 (abs_nonneg C5)
          linarith
      _ ≤ (2 * B + |C5| + 1) * ε := by nlinarith [abs_nonneg C5]
      _ ≤ δ / 2 := hεE
  have hpos : ∀ X : Fin 6 → ℝ, ‖X - q‖ ≤ δ / 2 → 0 < X 0 := by
    intro X hX
    have h0 := norm_le_pi_norm (X - q) 0
    rw [Real.norm_eq_abs] at h0
    have := abs_le.1 (h0.trans hX)
    simp only [Pi.sub_apply] at this
    linarith [this.1]
  have hs1 : Dsq T = Dsq X1 := by
    rw [← hinv]; exact Dsq_smul hε2pos (hpos X1 hX1q).ne'
  have hs2 : Dsq (ε ^ 2 • X2) = Dsq X2 := Dsq_smul hε2pos (hpos X2 (hX2q.trans hEε)).ne'
  rw [hs1, hs2]
  have := hlip X2 X1 ((hX2q.trans hEε).trans (by linarith)) (hX1q.trans (by linarith))
  calc |Dsq X1 - Dsq X2| ≤ C0 * ‖X1 - X2‖ := this
    _ ≤ C0 * (C5 * ε ^ 3) := mul_le_mul_of_nonneg_left hd hC0
    _ = C0 * C5 * ε ^ 3 := by ring

end Lightlike.Regge.Conv3
