import Mathlib
import Lightlike.Spacetime.RaychaudhuriNull
import Lightlike.Rows.G1_066.Focusing

/-!
# Hawking's area theorem along a complete null geodesic generator (coordinate form)

Connects the analytic core (`Focusing.lean`) with the null Raychaudhuri focusing of `RaychaudhuriNull.lean`.
For a null geodesic field `v` of a Lorentzian coordinate metric on `U ⊆ ℝⁿ` (`n ≥ 3`) with `R(v, v) ≥ 0` (the null
convergence condition, which the null energy condition gives through Einstein's equation) and an auxiliary null
vector with vanishing screen rotation along an integral curve `γ` defined for all `s ≥ 0` (a generator of an event
horizon has no future end point):

* `expansion_nonneg_of_complete_generator`: the expansion `θ = Θ(γ(s))` is `≥ 0` for all `s ≥ 0`;
* `area_nondecreasing_of_complete_generator`: any area element `A` with `A' = θ A`, `A ≥ 0` along `γ` is
  nondecreasing on `[0, ∞)`.
-/

open Set Matrix
open scoped ContDiff

namespace Lightlike.Rows.G1_066

open Lightlike

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {v : (Fin n → ℝ) → Fin n → ℝ}

/-- **Generators of a horizon do not converge** (Hawking's step, coordinate form): along an integral curve `γ` of a
null geodesic field, defined on all of `[0, ∞)`, with `R(v, v) ≥ 0` and vanishing screen rotation, the expansion
is nonnegative. A negative value at `s₀` would give `L ≤ (n-2)/|θ|` for every `L` by `raychaudhuri_null_focusing`
applied to the shifted curve `t ↦ γ (s₀ + t)`. -/
theorem expansion_nonneg_of_complete_generator (hgL : IsLorentzianCoordMetric g U)
    (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
    (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0) (hnull : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = 0)
    (hn : 2 < n) {γ : ℝ → Fin n → ℝ} (hγU : ∀ s, 0 ≤ s → γ s ∈ U)
    (hγ : ∀ s, 0 ≤ s → HasDerivAt γ (v (γ s)) s)
    (hN : ∀ s, 0 ≤ s → ∃ N : Fin n → ℝ, N ⬝ᵥ (g (γ s) *ᵥ N) = 0 ∧ v (γ s) ⬝ᵥ (g (γ s) *ᵥ N) = -1 ∧
      nullRotation g v (γ s) N = 0)
    (hR : ∀ s, 0 ≤ s → 0 ≤ ∑ a, ∑ b, ricci g a b (γ s) * v (γ s) a * v (γ s) b) :
    ∀ s, 0 ≤ s → 0 ≤ expansion g v (γ s) := by
  intro s₀ hs₀
  by_contra hneg
  push Not at hneg
  have key := raychaudhuri_null_focusing (g := g) (U := U) (v := v) hgL hv hgeo hnull hn
    (γ := fun t => γ (s₀ + t)) (L := (n - 2) / |expansion g v (γ s₀)| + 1)
    (fun t ht => hγU _ (by linarith [ht.1]))
    (fun t ht => by
      have := (hγ (s₀ + t) (by linarith [ht.1])).comp_const_add s₀ t
      simpa using this)
    (fun t ht => hN _ (by linarith [ht.1])) (fun t ht => hR _ (by linarith [ht.1]))
    (by simpa using hneg)
  simp only [add_zero] at key
  linarith

/-- **The area-theorem step along a complete generator**: with the hypotheses of
`expansion_nonneg_of_complete_generator` and an area element `A` with `A' = θ A`, `A ≥ 0` along `γ`,
`A` is nondecreasing on `[0, ∞)`. -/
theorem area_nondecreasing_of_complete_generator (hgL : IsLorentzianCoordMetric g U)
    (hv : ∀ a, ContDiffOn ℝ ∞ (fun y => v y a) U)
    (hgeo : ∀ y ∈ U, ∀ d, ∑ c, v y c * covD g v d c y = 0) (hnull : ∀ y ∈ U, v y ⬝ᵥ (g y *ᵥ v y) = 0)
    (hn : 2 < n) {γ : ℝ → Fin n → ℝ} (hγU : ∀ s, 0 ≤ s → γ s ∈ U)
    (hγ : ∀ s, 0 ≤ s → HasDerivAt γ (v (γ s)) s)
    (hN : ∀ s, 0 ≤ s → ∃ N : Fin n → ℝ, N ⬝ᵥ (g (γ s) *ᵥ N) = 0 ∧ v (γ s) ⬝ᵥ (g (γ s) *ᵥ N) = -1 ∧
      nullRotation g v (γ s) N = 0)
    (hR : ∀ s, 0 ≤ s → 0 ≤ ∑ a, ∑ b, ricci g a b (γ s) * v (γ s) a * v (γ s) b)
    {A : ℝ → ℝ} (hA : ∀ s, 0 ≤ s → HasDerivAt A (expansion g v (γ s) * A s) s)
    (hpos : ∀ s, 0 ≤ s → 0 ≤ A s) : MonotoneOn A (Ici 0) :=
  areaElement_monotone hA (expansion_nonneg_of_complete_generator hgL hv hgeo hnull hn hγU hγ hN hR) hpos

end Lightlike.Rows.G1_066
