import Lightlike.Spacetime.Raychaudhuri.HawkingManifold
import Lightlike.Spacetime.Raychaudhuri.CollapseExample

/-!
# Hawking's bound for the comoving congruence of FLRW on the manifold (GE3, Tier 2)

On the FLRW manifold `flrwOpen` with scale factor `a`, the comoving field `∂_t` is unit, geodesic and rotation-free with
`Θ = 3 ȧ/a` (`flrwManifold_comoving_expansion`). So `hawking_bound_manifold` gives: if `Ric(∂_t, ∂_t) ≥ 0` along an integral
curve of `∂_t` on `[0, L)` and the Hubble rate at `γ 0` is `ȧ/a ≤ -h < 0`, then `L ≤ 1 / h` (the lifetime of a contracting
FLRW universe is at most one Hubble time).
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ)

/-- **Hubble-time bound for the comoving congruence of a contracting FLRW universe**: if along an integral curve `γ` of `∂_t`
on `[0, L)` one has `Ric(∂_t, ∂_t) ≥ 0` and the Hubble rate at `γ 0` satisfies `ȧ/a ≤ -h < 0`, then `L ≤ 1/h`. -/
theorem hawking_bound_flrw (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen hI k))
    [LocallySmoothConnection cov] (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric)
    {γ : ℝ → Cosmology.flrwOpen hI k} {L hub : ℝ} (hhub : 0 < hub)
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single 0 1 : Fin 4 → ℝ)))
    (hR : ∀ s ∈ Ico 0 L, 0 ≤ cov.ricciAt (γ s) (Pi.single 0 1 : Fin 4 → ℝ) (Pi.single 0 1 : Fin 4 → ℝ))
    (h0 : deriv a ((γ 0 : Fin 4 → ℝ) 0) / a ((γ 0 : Fin 4 → ℝ) 0) ≤ -hub) : L ≤ 1 / hub := by
  have hΘ := flrwManifold_comoving_expansion hI ha hpos k cov h (γ 0)
  have := hawking_bound_manifold cov (Cosmology.flrwManifoldMetric hI ha hpos k) h
    (V := fun _ => (Pi.single 0 1 : Fin 4 → ℝ))
    (contMDiff_constField (U := Cosmology.flrwOpen hI k) (Pi.single 0 1)) (by norm_num) (γ := γ) (L := L)
    (C := -3 * hub) hγ
    (fun s _ => Filter.Eventually.of_forall fun q => flrwManifold_comoving_geodesic hI ha hpos k cov h q)
    (fun s _ => Filter.Eventually.of_forall fun q => flrwManifold_comoving_unit hI ha hpos k q)
    (fun s _ u w => flrwManifold_comoving_rotationFree hI ha hpos k cov h _ u w) hR (by linarith)
    (by rw [hΘ]; linarith)
  have e : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
  rw [e, abs_of_neg (by linarith : -3 * hub < 0)] at this
  have e2 : 3 / (-(-3 * hub)) = 1 / hub := by field_simp
  rwa [e2] at this

end Lightlike
