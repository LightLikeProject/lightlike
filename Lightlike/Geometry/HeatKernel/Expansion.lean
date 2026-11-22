import Mathlib

/-!
# Asymptotic expansion of a heat trace

A *heat trace* is a function `K : ℝ → ℝ`, `K t = Tr e^{-tD}` for `t > 0`. For a Laplace-type
operator `D` on a compact `n`-manifold without boundary the Seeley–DeWitt expansion reads
`K t ∼ Σ_k a_k t^{k - n/2}` as `t → 0⁺` (odd-`t^{1/2}` powers vanish without boundary; this is the
indexing of the row's `a₀, a₁, a₂`, with `a₁ = (4π)^{-n/2} ∫ R/6` for `D = -Δ`).

## Main definitions

* `Lightlike.HeatKernel.HasHeatExpansion n K a`: for every `N`, the remainder after the first `N`
  terms is `O(t^{N - n/2})` as `t → 0⁺`.

## Main results

* `HasHeatExpansion.add`, `HasHeatExpansion.const_mul`: linearity.

## References

* Vassilevich, *Heat kernel expansion: user's manual* (key `vassilevich-2003`), eq. (4.27).
* Berline–Getzler–Vergne, *Heat Kernels and Dirac Operators* (key `bgv-1992`), chapter
  "Asymptotic Expansion of the Heat Kernel".
-/

open Filter Topology Asymptotics

noncomputable section

namespace Lightlike.HeatKernel

/-- **Heat-trace expansion.** `HasHeatExpansion n K a` says that, as `t → 0⁺`,
`K t ∼ Σ_k a k * t ^ (k - n/2)`: for every `N` the error after the first `N` terms is
`O(t ^ (N - n/2))`. Here `n` is the dimension of the manifold. -/
def HasHeatExpansion (n : ℕ) (K : ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, (fun t => K t - ∑ k ∈ Finset.range N, a k * t ^ ((k : ℝ) - n / 2)) =O[𝓝[>] (0 : ℝ)]
    fun t => t ^ ((N : ℝ) - n / 2)

variable {n : ℕ} {K L : ℝ → ℝ} {a b : ℕ → ℝ}

/-- Heat-trace expansions add. -/
theorem HasHeatExpansion.add (hK : HasHeatExpansion n K a) (hL : HasHeatExpansion n L b) :
    HasHeatExpansion n (fun t => K t + L t) (fun k => a k + b k) := by
  intro N
  refine ((hK N).add (hL N)).congr_left ?_
  intro t
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- Heat-trace expansions are stable under multiplication by a constant. -/
theorem HasHeatExpansion.const_mul (c : ℝ) (hK : HasHeatExpansion n K a) :
    HasHeatExpansion n (fun t => c * K t) (fun k => c * a k) := by
  intro N
  refine ((hK N).const_mul_left c).congr_left ?_
  intro t
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

end Lightlike.HeatKernel
