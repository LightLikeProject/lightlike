import Lightlike.Spacetime.Raychaudhuri.HawkingDust
import Lightlike.Spacetime.Raychaudhuri.CollapseExample

/-!
# Hawking's bound for the collapsing dust universe (GE3, Tier 2)

In the collapsing dust universe `a t = (c - t)^(2/3)` (`k = 0`, density `1 / (6 π G (c - t)²)`) the Hubble rate at time
`t₀ < c` is `-2 / (3 (c - t₀))`. `hawking_bound_flrw_dust` therefore bounds the proper length `L` of every comoving
worldline `γ` (an integral curve of `∂_t` on `[0, L)`) starting at time `t₀` by `L ≤ 3 (c - t₀) / 2`: one Hubble time.
The true singularity is at `L = c - t₀`, so the bound is within the factor `3/2` of sharp.
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {c : ℝ}

/-- **Hawking bound in the collapsing dust universe**: a comoving worldline starting at time `t₀ < c` has length
`L ≤ 3 (c - t₀) / 2`. -/
theorem collapse_hawking_bound {Gn : ℝ} (hG : 0 < Gn)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0)))
    [LocallySmoothConnection cov] [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) (fun _ ht => Cosmology.collapseA_pos c ht) 0).toNondegMetric)
    {γ : ℝ → Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0)} {L : ℝ}
    (hγ : ∀ s ∈ Ico 0 L, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin 4 → ℝ) γ s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single 0 1 : Fin 4 → ℝ))) :
    L ≤ 3 * (c - (γ 0 : Fin 4 → ℝ) 0) / 2 := by
  have hcpos := fun t (ht : t ∈ Iio c) => Cosmology.collapseA_pos c ht
  have ht0 : ((γ 0 : Fin 4 → ℝ) 0) < c := (γ 0).2.1
  have hpos : 0 < c - (γ 0 : Fin 4 → ℝ) 0 := sub_pos.2 ht0
  have hE : (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) hcpos 0).toNondegMetric.EinsteinEq cov 0 (8 * Real.pi * Gn)
      (fun x v w => matForm (Matrix.of fun μ ν => Cosmology.perfectFluid (Cosmology.collapseRho Gn c)
        (fun _ => 0) (Cosmology.flrwMetric (Cosmology.collapseA c) 0) μ ν x.1) v w) := by
    rw [Cosmology.flrwManifold_einstein_iff_friedmann isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0 cov h]
    exact fun t ht => Cosmology.collapse_friedmann hG c ht
  have key := hawking_bound_flrw_dust isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0 cov h
    (κ := 8 * Real.pi * Gn) (by positivity) (Cosmology.collapseRho Gn c) (fun t ht => by
      unfold Cosmology.collapseRho
      have : 0 < c - t := sub_pos.2 ht
      positivity) hE (γ := γ) (L := L) (hub := 2 / (3 * (c - (γ 0 : Fin 4 → ℝ) 0)))
    (by positivity) hγ (by
      rw [Cosmology.collapseA_hubble c ht0]
      apply le_of_eq
      field_simp)
  have e : 1 / (2 / (3 * (c - (γ 0 : Fin 4 → ℝ) 0))) = 3 * (c - (γ 0 : Fin 4 → ℝ) 0) / 2 := by
    field_simp
  rwa [e] at key

end Lightlike
