import Lightlike.Rows.G1_007.TimeSeparation
import Lightlike.Spacetime.Raychaudhuri.HawkingManifold

/-!
# Hawking's length bound, conditional on a maximizer (row G1-007, milestone CO3)

* `TimelikeConvergence cov`: the timelike convergence condition `Ric(v, v) ≥ 0` for every timelike `v`.
* `lorentzLength_integralCurve_unit`: an integral curve of a unit vector field on `[0, L)` has Lorentzian length `L`.
* `lorentzLength_le_hawking`: the Lorentzian length of the integral curve of a unit geodesic rotation-free field with
  expansion `≤ C < 0` at the start is at most `(n-1)/|C|`.

The existence of a maximizing curve (Avez-Seifert) and the normal congruence off a Cauchy surface are **not** proved here:
the curve being an integral curve of the normal geodesic field is a hypothesis (see `hawking_bound_manifold`).
-/

open Filter Topology Set Bundle Manifold MeasureTheory
open scoped ContDiff Manifold ENNReal

noncomputable section

namespace Lightlike

namespace Causal

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] (gL : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

set_option backward.isDefEq.respectTransparency false in
/-- An integral curve of a vector field `V` on `[0, L)` along which `V` is unit (`g(V, V) = -1`) has Lorentzian length
`L` on `[0, L]`. -/
theorem lorentzLength_integralCurve_unit {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {γ : ℝ → M} {L : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hnorm : ∀ s ∈ Ico 0 L, gL.g (γ s) (V (γ s)) (V (γ s)) = -1) :
    lorentzLength gL γ 0 L = ENNReal.ofReal L := by
  rcases le_or_gt L 0 with hL | hL
  · rcases hL.eq_or_lt with rfl | hL
    · simp [lorentzLength_self]
    · simp [lorentzLength, hL.not_ge, ENNReal.ofReal_of_nonpos hL.le]
  have hu : ∀ t ∈ Icc (0 : ℝ) L, UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) L) t := fun t ht =>
    (uniqueDiffOn_Icc hL t ht).uniqueMDiffWithinAt
  have h1 : ∀ t ∈ Ico (0 : ℝ) L, lorentzSpeed gL γ (Icc 0 L) t = 1 := by
    intro t ht
    have hv : velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 L) t = V (γ t) := by
      unfold velocity
      rw [(hγ t ht).hasMFDerivWithinAt.mfderivWithin (hu t ⟨ht.1, ht.2.le⟩)]
      exact one_smul ℝ _
    unfold lorentzSpeed
    rw [hv, hnorm t ht]
    simp
  unfold lorentzLength
  have h2 : ∫⁻ t in Icc (0 : ℝ) L, lorentzSpeed gL γ (Icc 0 L) t = ∫⁻ t in Ico (0 : ℝ) L, lorentzSpeed gL γ (Icc 0 L) t :=
    setLIntegral_congr Ico_ae_eq_Icc.symm
  rw [h2, setLIntegral_congr_fun measurableSet_Ico h1]
  simp

/-- The **timelike convergence condition** `Ric(v, v) ≥ 0` for every timelike tangent vector `v`. -/
def TimelikeConvergence (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) : Prop :=
  ∀ (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x), gL.g x v v < 0 → 0 ≤ cov.ricciAt x v v

set_option backward.isDefEq.respectTransparency false in
/-- **Hawking's length bound, conditional on the maximizer**: along an integral curve `γ` of a unit geodesic rotation-free
field `V` with `Θ(γ 0) ≤ C < 0`, the Lorentzian length on `[0, L]` is at most `(n-1)/|C|`, under the timelike convergence
condition. -/
theorem lorentzLength_le_hawking [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)
    [LocallySmoothConnection cov] (h : cov.IsLeviCivita gL.toNondegMetric) (hTC : TimelikeConvergence gL cov)
    {V : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p}
    (hV : ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M))) (hn : 1 < n) {γ : ℝ → M} {L C : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) γ s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ s))))
    (hgeo : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), cov V q (V q) = 0)
    (hnorm : ∀ s ∈ Ico 0 L, ∀ᶠ q in 𝓝 (γ s), gL.g q (V q) (V q) = -1)
    (hrot : ∀ s ∈ Ico 0 L, ∀ u w : TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ s),
      gL.g (γ s) (cov V (γ s) u) w = gL.g (γ s) (cov V (γ s) w) u)
    (hC : C < 0) (h0 : expansionM cov V (γ 0) ≤ C) :
    lorentzLength gL γ 0 L ≤ ENNReal.ofReal (((n : ℝ) - 1) / |C|) := by
  have hn' : ∀ s ∈ Ico (0 : ℝ) L, gL.g (γ s) (V (γ s)) (V (γ s)) = -1 := fun s hs => (hnorm s hs).self_of_nhds
  rw [lorentzLength_integralCurve_unit gL hγ hn']
  refine ENNReal.ofReal_le_ofReal ?_
  exact hawking_bound_manifold cov gL h hV hn hγ hgeo hnorm hrot
    (fun s hs => hTC _ _ (by rw [hn' s hs]; norm_num)) hC h0

end Causal

end Lightlike
