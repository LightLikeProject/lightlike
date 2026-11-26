import Lightlike.Spacetime.PenroseSingularity.VariationJets
import Lightlike.Spacetime.PenroseSingularity.IndexForm

/-!
# The second-order coefficient with the correction `Z = φ N` (G1-012, step D4)

With `Z = φ N`, `g(N, γc') = -1`, the coefficient of the variation at `s = 0` is `-2 φ' + bQ`, so it is negative as
soon as `φ' > bQ / 2`.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ} {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}
  {γc W Z : ℝ → Fin n → ℝ} {V : Set (ℝ × ℝ)}

/-- **The coefficient with `Z = φ N`.** -/
theorem coeffK_eq_of_phi {φ : ℝ → ℝ} {N Zp : ℝ → Fin n → ℝ} {φ' : ℝ} (hg : Lightlike.IsCoordMetric g U)
    (hV : IsOpen V) (hD0 : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D) (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (j0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (j2 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) =
      Lightlike.Geodesic.accel g q w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D)
    (hcU : ∀ p ∈ V, varA Θ γc W Z p ∈ U) {t : ℝ} (hp : ((0 : ℝ), t) ∈ V)
    (hγ : HasDerivAt (deriv γc) (Lightlike.Geodesic.accel g (γc t) (deriv γc t)) t)
    (hN : ∀ᶠ r in 𝓝 t, gpairAt g (γc r) (N r) (deriv γc r) = -1)
    (hZp : ∀ᶠ r in 𝓝 t, gpairAt g (γc r) (Zp r) (deriv γc r) = 0)
    (hZ : ∀ᶠ r in 𝓝 t, Z r = φ r • N r + Zp r)
    (hφ : HasDerivAt φ φ' t) :
    coeffK g (fun s t => varA Θ γc W Z (s, t)) (fun s t => jetC1 (varA Θ γc W Z) (s, t))
        (fun s t => jetC2 (varA Θ γc W Z) (s, t)) (fun s t => jetY (varA Θ γc W Z) (s, t))
        (fun s t => jetY1 (varA Θ γc W Z) (s, t)) (fun s t => jetY2 (varA Θ γc W Z) (s, t)) 0 t =
      -2 * φ' + bQ g (γc t) (deriv γc t) (W t)
        (deriv W t + Lightlike.Geodesic.gammaApply g (γc t) (W t) (deriv γc t)) := by
  have hpair := hasDerivAt_two_pair_of_phi (g := g) (U := U) (γc := γc) (Z := Z) hg hN hZp hφ hZ
  rw [varA_hasDerivAt_pair hg hV hD0 hΘ hA j0 j1 j2 hVD hcU hp hγ hpair]
  have hx : γc t ∈ U := by
    have := hcU _ hp
    have h0 := varA_zero_section (Θ := Θ) (γc := γc) (W := W) (Z := Z) (V := V) (D := D) j0 hVD hp
    rw [h0] at this
    exact this
  unfold bQ tide
  rw [tidal_swap hg hx]
  ring

end Lightlike.Penrose
