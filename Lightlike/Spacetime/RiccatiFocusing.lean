import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The focusing lemma for the Riccati inequality

If a function `Θ` on `[0, L)` obeys `Θ' ≤ -Θ²/m` (`m > 0`) and starts negative, `Θ(0) < 0`, then `L ≤ m/|Θ(0)|`: `Θ` cannot
stay finite beyond the parameter `m/|Θ(0)|`, since `1/Θ - s/m` is nondecreasing and `1/Θ < 0`. This is the analytic step
of geodesic focusing from Raychaudhuri's equation (Kar and SenGupta, gr-qc/0611123, (12) and (16), with `m = n - 1`),
used for the comoving congruence of FLRW (`Lightlike/Cosmology/Raychaudhuri.lean`).
-/

open Set Filter Topology

namespace Lightlike

/-- **The focusing lemma**: if `Θ' ≤ -Θ²/m` on `[0, L)` (`m > 0`) and `Θ(0) < 0`, then `L ≤ m/|Θ(0)|`. -/
theorem focusing {Θ Θ' : ℝ → ℝ} {L m : ℝ} (hm : 0 < m)
    (hd : ∀ s ∈ Ico 0 L, HasDerivAt Θ (Θ' s) s) (hle : ∀ s ∈ Ico 0 L, Θ' s ≤ -(Θ s) ^ 2 / m)
    (h0 : Θ 0 < 0) : L ≤ m / |Θ 0| := by
  have hcont : ContinuousOn Θ (Ico 0 L) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hanti : AntitoneOn Θ (Ico 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 L) hcont ?_ ?_
    · exact fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      have h1 := hle s (interior_subset hs)
      have h3 : -(Θ s) ^ 2 / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (Θ s)]) hm.le
      linarith
  by_contra hcon
  push Not at hcon
  have hL0 : 0 < L := lt_trans (div_pos hm (abs_pos.2 h0.ne)) hcon
  have h00 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, hL0⟩
  have hneg : ∀ s ∈ Ico 0 L, Θ s < 0 := fun s hs => lt_of_le_of_lt (hanti h00 hs hs.1) h0
  -- `1/Θ - s/m` is nondecreasing
  set f : ℝ → ℝ := fun s => (Θ s)⁻¹ - s / m
  have hf : ∀ s ∈ Ico 0 L, HasDerivAt f (-(Θ' s) / (Θ s) ^ 2 - 1 / m) s := by
    intro s hs
    have h1 := (hd s hs).inv (hneg s hs).ne
    have h2 := (hasDerivAt_id s).div_const m
    convert h1.sub h2 using 1
    all_goals rfl
  have hfmono : MonotoneOn f (Ico 0 L) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 L) (fun s hs => (hf s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hf s (interior_subset hs)).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    have hs' := interior_subset hs
    rw [(hf s hs').deriv]
    have hΘ := hneg s hs'
    have hle' := hle s hs'
    have hsq : 0 < (Θ s) ^ 2 := by nlinarith [hΘ]
    rw [sub_nonneg, le_div_iff₀ hsq]
    calc 1 / m * (Θ s) ^ 2 = (Θ s) ^ 2 / m := by ring
      _ ≤ -Θ' s := by rw [neg_div] at hle'; linarith
  -- at `s = m/|Θ 0| < L`
  set s₀ := m / |Θ 0|
  have hs₀ : s₀ ∈ Ico 0 L := ⟨div_nonneg hm.le (abs_nonneg _), hcon⟩
  have hfs := hfmono h00 hs₀ hs₀.1
  have hneg₀ := hneg s₀ hs₀
  simp only [f, zero_div, sub_zero] at hfs
  have habs : |Θ 0| = -Θ 0 := abs_of_neg h0
  have : s₀ / m = -(Θ 0)⁻¹ := by
    simp only [s₀, habs]; field_simp
  rw [this] at hfs
  have : (Θ s₀)⁻¹ < 0 := inv_lt_zero.2 hneg₀
  linarith

end Lightlike
