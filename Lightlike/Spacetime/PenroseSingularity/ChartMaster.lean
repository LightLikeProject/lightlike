import Lightlike.Spacetime.PenroseSingularity.CoeffNeg
import Lightlike.Spacetime.PenroseSingularity.FutureChart

/-!
# Local negativity of the variation in a chart (G1-012, step D4)

Chart-level master statement: for the variation with fields `W` and `Z = φ N` along a null geodesic, if
`φ' = ½ bQ + κ` with `κ > 0` at `t₀`, the second-order coefficient is `-2 κ < 0`, and hence `g(α_t, α_t) < 0` for all
small `s ≠ 0` and `t` near `t₀`.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ} {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}
  {γc W Z : ℝ → Fin n → ℝ} {V : Set (ℝ × ℝ)}

/-- **Local uniform negativity of the chart variation with `Z = φ N`.** -/
theorem chart_neg_master {φ : ℝ → ℝ} {N Zp : ℝ → Fin n → ℝ} {φ' κ : ℝ} (hg : Lightlike.IsCoordMetric g U)
    (hV : IsOpen V) (hD0 : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D) (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (j0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (j2 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) =
      Lightlike.Geodesic.accel g q w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D)
    (hcU : ∀ p ∈ V, varA Θ γc W Z p ∈ U) {t₀ : ℝ} (hp : ((0 : ℝ), t₀) ∈ V)
    (hγ : HasDerivAt (deriv γc) (Lightlike.Geodesic.accel g (γc t₀) (deriv γc t₀)) t₀)
    (hnull : ∀ᶠ t in 𝓝 t₀, gpairAt g (γc t) (deriv γc t) (deriv γc t) = 0)
    (hperp : ∀ᶠ t in 𝓝 t₀, gpairAt g (γc t) (deriv W t +
      Lightlike.Geodesic.gammaApply g (γc t) (W t) (deriv γc t)) (deriv γc t) = 0)
    (hN : ∀ᶠ r in 𝓝 t₀, gpairAt g (γc r) (N r) (deriv γc r) = -1)
    (hZp : ∀ᶠ r in 𝓝 t₀, gpairAt g (γc r) (Zp r) (deriv γc r) = 0)
    (hZ : ∀ᶠ r in 𝓝 t₀, Z r = φ r • N r + Zp r)
    (hφ : HasDerivAt φ φ' t₀) (hκ : 0 < κ)
    (hode : φ' = (1 / 2 : ℝ) * bQ g (γc t₀) (deriv γc t₀) (W t₀)
      (deriv W t₀ + Lightlike.Geodesic.gammaApply g (γc t₀) (W t₀) (deriv γc t₀)) + κ) :
    ∃ δ > 0, ∃ ε > 0, ∀ t, |t - t₀| < ε → ∀ s, |s| < δ → s ≠ 0 →
      gpairAt g (varA Θ γc W Z (s, t)) (jetY (varA Θ γc W Z) (s, t)) (jetY (varA Θ γc W Z) (s, t)) < 0 := by
  have hcoef := coeffK_eq_of_phi (U := U) hg hV hD0 hΘ hA j0 j1 j2 hVD hcU hp hγ hN hZp hZ hφ
  refine varA_uniform_neg hg hV hD0 hΘ hA j0 j1 hVD hcU hp ?_ ?_ ?_
  · exact hnull
  · exact hperp
  · rw [hcoef, hode]; linarith

end Lightlike.Penrose
