import Lightlike.Spacetime.Raychaudhuri.HawkingSEC
import Lightlike.Spacetime.Raychaudhuri.HawkingFLRW

/-!
# Hawking's bound for a contracting dust FLRW universe on the manifold (GE3, Tier 2)

On the FLRW manifold with scale factor `a`, suppose the Einstein equation `G = κ T` (`Λ = 0`, `κ > 0`) holds with `T` the
energy-momentum tensor of dust of density `ρ ≥ 0` with velocity `∂_t`. Dust satisfies the strong energy condition
(`flrwManifold_dust_strongEC`), so `hawking_bound_strongEC` applies, and with the closed-form expansion
`Θ = 3 ȧ/a` (`flrwManifold_comoving_expansion`) it gives: if `ȧ/a ≤ -h < 0` at `γ 0` then the comoving worldline has
length `L ≤ 1/h` (one Hubble time). Unlike `hawking_bound_flrw`, no hypothesis on the Ricci tensor is needed: it is derived
from the field equation and the energy condition.
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ)

/-- **Hubble-time bound for a contracting dust FLRW universe** (field equation version): if `G = κ T` with `T` dust of
density `ρ ≥ 0` on `I`, and along an integral curve of `∂_t` on `[0, L)` the Hubble rate at `γ 0` is `ȧ/a ≤ -h < 0`,
then `L ≤ 1/h`. -/
theorem hawking_bound_flrw_dust (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen hI k))
    [LocallySmoothConnection cov] (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric)
    {κ : ℝ} (hκ : 0 < κ) (ρ : ℝ → ℝ) (hρ : ∀ t ∈ I, 0 ≤ ρ t)
    (hE : (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric.EinsteinEq cov 0 κ
      (fun x v w => matForm (Matrix.of fun μ ν =>
        Cosmology.perfectFluid ρ (fun _ => 0) (Cosmology.flrwMetric a k) μ ν x.1) v w))
    {γ : ℝ → Cosmology.flrwOpen hI k} {L hub : ℝ} (hhub : 0 < hub)
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single 0 1 : Fin 4 → ℝ)))
    (h0 : deriv a ((γ 0 : Fin 4 → ℝ) 0) / a ((γ 0 : Fin 4 → ℝ) 0) ≤ -hub) : L ≤ 1 / hub := by
  have hΘ := flrwManifold_comoving_expansion hI ha hpos k cov h (γ 0)
  have := hawking_bound_strongEC (Cosmology.flrwManifoldMetric hI ha hpos k) cov h hκ hE
    (flrwManifold_dust_strongEC hI ha hpos k ρ hρ)
    (V := fun _ => (Pi.single 0 1 : Fin 4 → ℝ))
    (contMDiff_constField (U := Cosmology.flrwOpen hI k) (Pi.single 0 1)) (γ := γ) (L := L)
    (C := -3 * hub) hγ
    (fun s _ => Filter.Eventually.of_forall fun q => flrwManifold_comoving_geodesic hI ha hpos k cov h q)
    (fun s _ => Filter.Eventually.of_forall fun q => flrwManifold_comoving_unit hI ha hpos k q)
    (fun s _ u w => flrwManifold_comoving_rotationFree hI ha hpos k cov h _ u w) (by linarith)
    (by rw [hΘ]; linarith)
  rw [abs_of_neg (by linarith : -3 * hub < 0)] at this
  have e2 : 3 / (-(-3 * hub)) = 1 / hub := by field_simp
  rwa [e2] at this

end Lightlike
