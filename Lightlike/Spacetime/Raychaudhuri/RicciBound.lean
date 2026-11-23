import Lightlike.Spacetime.RiccatiFocusing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Focusing with a positive Ricci lower bound (GE3, Tier 1)

`focusing` (`Lightlike/Spacetime/RiccatiFocusing.lean`) treats `Θ' ≤ -Θ²/m`, which is what `Ric(V, V) ≥ 0` gives. A
uniform bound `Ric(V, V) ≥ c > 0` gives `Θ' ≤ -Θ²/m - c`, and then the expansion reaches `-∞` in a time that does not
even need `Θ(0) < 0`: the angle `arctan(Θ/√(mc))` decreases at the constant rate `√(c/m)` inside `(-π/2, π/2)`
(the timelike analogue of the Bonnet–Myers diameter bound). This file proves that analytic step.
-/

open Set Filter Topology Real

namespace Lightlike

/-- **Focusing with a positive Ricci bound.** If `Θ' ≤ -Θ²/m - c` on `[0, L)` with `m, c > 0`, then
`L ≤ (m/√(mc)) (π/2 + arctan(Θ(0)/√(mc)))`; in particular `L ≤ π m/√(mc) = π √(m/c)`, whatever `Θ(0)` is. -/
theorem focusing_ricci_bound {Θ Θ' : ℝ → ℝ} {L m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hd : ∀ s ∈ Ico 0 L, HasDerivAt Θ (Θ' s) s)
    (hle : ∀ s ∈ Ico 0 L, Θ' s ≤ -(Θ s) ^ 2 / m - c) :
    L ≤ m / √(m * c) * (π / 2 + arctan (Θ 0 / √(m * c))) := by
  have hmc : 0 < m * c := mul_pos hm hc
  set r := √(m * c) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hmc
  have hr2 : r ^ 2 = m * c := Real.sq_sqrt hmc.le
  set g : ℝ → ℝ := fun s => arctan (Θ s / r) + r / m * s with hg
  have hgd : ∀ s ∈ Ico 0 L, HasDerivAt g (1 / (1 + (Θ s / r) ^ 2) * (Θ' s / r) + r / m * 1) s := by
    intro s hs
    exact (((hd s hs).div_const r).arctan).add ((hasDerivAt_id s).const_mul (r / m))
  have hanti : AntitoneOn g (Ico 0 L) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ico 0 L) ?_ ?_ ?_
    · exact fun s hs => (hgd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hgd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      rw [(hgd s hs').deriv]
      have hP : 0 < 1 / (1 + (Θ s / r) ^ 2) := by positivity
      have h1 := hle s hs'
      have h2 : Θ' s / r ≤ (-(Θ s) ^ 2 / m - c) / r := div_le_div_of_nonneg_right h1 hr0.le
      have h3 : 1 / (1 + (Θ s / r) ^ 2) * (Θ' s / r) ≤
          1 / (1 + (Θ s / r) ^ 2) * ((-(Θ s) ^ 2 / m - c) / r) := mul_le_mul_of_nonneg_left h2 hP.le
      have h4 : 1 / (1 + (Θ s / r) ^ 2) * ((-(Θ s) ^ 2 / m - c) / r) = -(r / m) := by
        have hden : 1 + (Θ s / r) ^ 2 ≠ 0 := by positivity
        field_simp
        nlinarith [hr2]
      linarith
  by_contra hcon
  push Not at hcon
  set s₀ := m / r * (π / 2 + arctan (Θ 0 / r)) with hs₀
  have hpos : 0 < π / 2 + arctan (Θ 0 / r) := by linarith [neg_pi_div_two_lt_arctan (Θ 0 / r)]
  have hs0 : s₀ ∈ Ico 0 L := ⟨by positivity, hcon⟩
  have h00 : (0 : ℝ) ∈ Ico 0 L := ⟨le_rfl, lt_of_le_of_lt hs0.1 hs0.2⟩
  have hle0 := hanti h00 hs0 hs0.1
  have hlt := neg_pi_div_two_lt_arctan (Θ s₀ / r)
  simp only [hg, mul_zero, add_zero] at hle0
  have : r / m * s₀ = π / 2 + arctan (Θ 0 / r) := by
    rw [hs₀]; field_simp
  linarith

/-- The Bonnet–Myers-type form: `Θ' ≤ -Θ²/m - c` on `[0, L)` forces `L ≤ π m/√(mc)`, with no sign condition on `Θ(0)`. -/
theorem focusing_ricci_pi {Θ Θ' : ℝ → ℝ} {L m c : ℝ} (hm : 0 < m) (hc : 0 < c)
    (hd : ∀ s ∈ Ico 0 L, HasDerivAt Θ (Θ' s) s)
    (hle : ∀ s ∈ Ico 0 L, Θ' s ≤ -(Θ s) ^ 2 / m - c) : L ≤ π * (m / √(m * c)) := by
  refine (focusing_ricci_bound hm hc hd hle).trans ?_
  have hr0 : 0 < m / √(m * c) := div_pos hm (Real.sqrt_pos.2 (mul_pos hm hc))
  have := arctan_lt_pi_div_two (Θ 0 / √(m * c))
  nlinarith

end Lightlike
