import Lightlike.Spacetime.Raychaudhuri.Hawking
import Lightlike.Spacetime.RaychaudhuriManifold

/-!
# Hawking's bound for a normal geodesic congruence on a manifold (GE3, Tier 2)

The manifold form of `focusing_hawking`: along an integral curve of a unit geodesic rotation-free vector field with
`Ric(V, V) ≥ 0`, a uniform bound `Θ(γ 0) ≤ C < 0` on the initial expansion bounds the parameter length `L` of the curve by
`(n-1)/|C|`, whatever the point `γ 0` is. This is the analytic step of Hawking's cosmological singularity theorem (the
causal part, maximal curves and Cauchy surfaces, needs GE2/GE4 and is not formalised here).
-/

open Filter Topology Set Matrix Bundle Manifold Real
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M] [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)

set_option backward.isDefEq.respectTransparency false in
/-- **Hawking's bound on a manifold**: for a Lorentzian metric with its Levi-Civita connection and a smooth vector field `V`,
along an integral curve `γ` of `V` on `[0, L)` near which `V` is unit, geodesic and rotation-free, with `Ric(V, V) ≥ 0`
along `γ` and uniformly converging initial expansion `Θ(γ 0) ≤ C < 0`: `L ≤ (n-1)/|C|`. -/
theorem hawking_bound_manifold (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (hn : 1 < n) {γ : ℝ → M} {L C : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u)
    (hR : ∀ s ∈ Ico 0 L, 0 ≤ cov.ricciAt (γ s) (V (γ s)) (V (γ s)))
    (hC : C < 0) (h0 : expansionM cov V (γ 0) ≤ C) : L ≤ ((n : ℝ) - 1) / |C| := by
  have hm : (0 : ℝ) < n - 1 := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have h1 := raychaudhuri_focusing_manifold cov gL h hV hn hγ hgeo hnorm hrot hR (lt_of_le_of_lt h0 hC)
  refine h1.trans (div_le_div_of_nonneg_left hm.le (abs_pos.2 hC.ne) ?_)
  rw [abs_of_neg hC, abs_of_neg (lt_of_le_of_lt h0 hC)]
  linarith

end Manifold

end Lightlike
