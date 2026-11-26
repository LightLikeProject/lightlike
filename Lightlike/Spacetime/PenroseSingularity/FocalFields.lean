import Lightlike.Spacetime.PenroseSingularity.IndexForm
import Lightlike.Spacetime.PenroseSingularity.ChartFocal

/-!
# The index form of the broken field in a chart (G1-012, step D4)

For a Jacobi field `Ĵ` with covariant derivative `P̂` along a null geodesic and a field `η` with covariant derivative
`Dη`, the quadratic form of `Ĵ + ε η` is `F' + 2 ε G' + ε² bQ(η, Dη)` with `F = g(P̂, Ĵ)` and `G = g(P̂, η)`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

open Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The quadratic form of the broken field**, with `F = g(P̂, Ĵ)` and `G = g(P̂, η)` as antiderivatives of the
Jacobi and cross terms. -/
theorem bQ_broken (hg : Lightlike.IsCoordMetric g U) {γ w J P η : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : IsJacobiOn g γ w J P I) (hγU : ∀ t ∈ I, γ t ∈ U) {t : ℝ} (ht : t ∈ I)
    {η' : Fin n → ℝ} (hη : HasDerivAt η η' t) (ε : ℝ) :
    bQ g (γ t) (w t) (J t + ε • η t) (P t + ε • (η' + gammaApply g (γ t) (w t) (η t))) =
      bQ g (γ t) (w t) (J t) (P t) +
        2 * ε * (gpairAt g (γ t) (P t) (η' + gammaApply g (γ t) (w t) (η t)) - tide g (γ t) (w t) (J t) (η t)) +
      ε ^ 2 * bQ g (γ t) (w t) (η t) (η' + gammaApply g (γ t) (w t) (η t)) :=
  bQ_add_smul hg (hγU t ht) (w t) (J t) (η t) (P t) _ ε

/-- **The derivatives of `F = g(P̂, Ĵ)` and `G = g(P̂, η)`.** -/
theorem hasDerivAt_F_G (hg : Lightlike.IsCoordMetric g U) {γ w J P η : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : IsJacobiOn g γ w J P I) (hγU : ∀ t ∈ I, γ t ∈ U) {t : ℝ} (ht : t ∈ I)
    {η' : Fin n → ℝ} (hη : HasDerivAt η η' t) :
    HasDerivAt (fun r => gpairAt g (γ r) (P r) (J r)) (bQ g (γ t) (w t) (J t) (P t)) t ∧
    HasDerivAt (fun r => gpairAt g (γ r) (P r) (η r))
      (gpairAt g (γ t) (P t) (η' + gammaApply g (γ t) (w t) (η t)) - tide g (γ t) (w t) (J t) (η t)) t :=
  ⟨hasDerivAt_pair_self_jacobi hg hJ hγU ht, hasDerivAt_pair_jacobi hg hJ hγU ht hη⟩

/-- **The correction function and its derivative.** `φ = ½ F + ε G + ½ ε² K + κ s + c` has derivative
`½ bQ(Ĵ + ε η, P̂ + ε Dη) + κ`, where `K' = bQ(η, Dη)`. -/
theorem hasDerivAt_phi (hg : Lightlike.IsCoordMetric g U) {γ w J P η : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hJ : IsJacobiOn g γ w J P I) (hγU : ∀ t ∈ I, γ t ∈ U) {t : ℝ} (ht : t ∈ I)
    {η' : Fin n → ℝ} (hη : HasDerivAt η η' t) (ε κ c : ℝ) {Kint : ℝ → ℝ}
    (hK : HasDerivAt Kint (bQ g (γ t) (w t) (η t) (η' + gammaApply g (γ t) (w t) (η t))) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * gpairAt g (γ s) (P s) (J s) + ε * gpairAt g (γ s) (P s) (η s) +
        (1 / 2 : ℝ) * ε ^ 2 * Kint s + κ * s + c)
      ((1 / 2 : ℝ) * bQ g (γ t) (w t) (J t + ε • η t) (P t + ε • (η' + gammaApply g (γ t) (w t) (η t))) + κ) t := by
  obtain ⟨hF, hG⟩ := hasDerivAt_F_G hg hJ hγU ht hη
  have h1 := ((hF.const_mul (1 / 2 : ℝ)).add (hG.const_mul ε)).add ((hK.const_mul ((1 / 2 : ℝ) * ε ^ 2)))
  have h2 := (h1.add ((hasDerivAt_id t).const_mul κ)).add_const c
  refine h2.congr_deriv ?_
  rw [bQ_broken hg hJ hγU ht hη ε]
  ring

end Lightlike.Penrose
