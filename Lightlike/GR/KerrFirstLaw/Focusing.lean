import Mathlib
import Lightlike.Spacetime.RiccatiFocusing

/-!
# The analytic core of Hawking's area theorem: complete generators do not converge

Hawking's argument (Carlip, *Black hole thermodynamics*, Section 2, in the sources of SC5) has two steps. If the
expansion `θ` of the null generators of the future horizon were negative at one point, the null energy condition
(through Raychaudhuri's equation `θ' ≤ -θ²/m`) would focus the generators into a caustic within the finite
affine parameter `m/|θ|`; but the generators of an event horizon have no future end point, so they are defined for all
`s ≥ 0`. Hence `θ ≥ 0`, and the area element `A' = θ A` does not decrease.

* `expansion_nonneg_of_complete`: `θ' ≤ -θ²/m` on `[0, ∞)` forces `θ ≥ 0` there.
* `areaElement_monotone`: `A' = θ A` with `θ ≥ 0`, `A ≥ 0` gives `A` monotone on `[0, ∞)`.
* `area_nondecreasing_of_complete`: the two together.
-/

namespace Lightlike.Rows.G1_066

open Set

/-- **Complete generators do not converge.** If `Θ' ≤ -Θ²/m` (`m > 0`) holds on all of `[0, ∞)`, then `Θ ≥ 0`
there: a negative value `Θ(s₀)` would give `∞ ≤ s₀ + m/|Θ(s₀)|` by the focusing lemma `Lightlike.focusing`. -/
theorem expansion_nonneg_of_complete {Θ Θ' : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (hd : ∀ s, 0 ≤ s → HasDerivAt Θ (Θ' s) s) (hle : ∀ s, 0 ≤ s → Θ' s ≤ -(Θ s) ^ 2 / m) :
    ∀ s, 0 ≤ s → 0 ≤ Θ s := by
  intro s₀ hs₀
  by_contra hneg
  push Not at hneg
  set L : ℝ := m / |Θ s₀| + 1 with hL
  have key := Lightlike.focusing (Θ := fun t => Θ (s₀ + t)) (Θ' := fun t => Θ' (s₀ + t)) (L := L) hm
    (fun t ht => (hd (s₀ + t) (by linarith [ht.1])).comp_const_add s₀ t)
    (fun t ht => hle (s₀ + t) (by linarith [ht.1])) (by simpa using hneg)
  simp only [add_zero] at key
  rw [hL] at key
  linarith

/-- **The area element of a nonnegatively expanding congruence is monotone**: if `A' = θ A` on `[0, ∞)` with
`θ ≥ 0` and `A ≥ 0`, then `A` is monotone on `[0, ∞)`. -/
theorem areaElement_monotone {A Θ : ℝ → ℝ} (hA : ∀ s, 0 ≤ s → HasDerivAt A (Θ s * A s) s)
    (hΘ : ∀ s, 0 ≤ s → 0 ≤ Θ s) (hpos : ∀ s, 0 ≤ s → 0 ≤ A s) : MonotoneOn A (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun s hs => (hA s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hA s (le_of_lt (by simpa using hs))).differentiableAt.differentiableWithinAt) ?_
  intro s hs
  have hs' : 0 ≤ s := le_of_lt (by simpa using hs)
  rw [(hA s hs').deriv]
  exact mul_nonneg (hΘ s hs') (hpos s hs')

/-- **The area-theorem step.** Along generators defined for all `s ≥ 0`, with the focusing inequality
`θ' ≤ -θ²/m` (the null energy condition through Raychaudhuri's equation) and the area element `A' = θ A`, `A ≥ 0`,
the area element is nondecreasing. -/
theorem area_nondecreasing_of_complete {A Θ Θ' : ℝ → ℝ} {m : ℝ} (hm : 0 < m)
    (hd : ∀ s, 0 ≤ s → HasDerivAt Θ (Θ' s) s) (hle : ∀ s, 0 ≤ s → Θ' s ≤ -(Θ s) ^ 2 / m)
    (hA : ∀ s, 0 ≤ s → HasDerivAt A (Θ s * A s) s) (hpos : ∀ s, 0 ≤ s → 0 ≤ A s) :
    MonotoneOn A (Ici 0) :=
  areaElement_monotone hA (expansion_nonneg_of_complete hm hd hle) hpos

end Lightlike.Rows.G1_066
