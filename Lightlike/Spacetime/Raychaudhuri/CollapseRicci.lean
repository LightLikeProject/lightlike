import Lightlike.Spacetime.Raychaudhuri.CollapseExample
import Lightlike.Spacetime.Raychaudhuri.FluidRicci

/-!
# The Ricci curvature of the collapsing dust universe along the flow (GE3, Tier 1)

On the manifold `flrwOpen` over `I = (-∞, c)` with `a t = (c - t)^(2/3)`, `k = 0` and dust of density
`1 / (6 π G (c - t)²)` (`CollapseExample.lean`), Einstein's equations give `Ric(∂_t, ∂_t) = 2 / (3 (c - t)²)` at every point
(`collapse_ricci_comoving`; compare `ä/a = -2/(9 (c-t)²)` and `Ric(∂_t, ∂_t) = -3 ä/a`). The Ricci bound is uniform on
the part `t ≤ c/2` of the flow: `Ric(∂_t, ∂_t) ≥ 2/(3c²)`, and the uniform-Ricci focusing theorem for a fluid
(`raychaudhuri_focusing_fluid`) applies with `σ = 1 / (6 π G c²)`.

**Limits.** One example.
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {c : ℝ}

/-- The collapsing dust manifold satisfies `G = 8π G_N T` with `T` the fluid field `fluidField ∂_t ρ 0`. -/
theorem collapse_einsteinEq_fluidField {Gn : ℝ} (hG : 0 < Gn)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0)))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) (fun _ ht => Cosmology.collapseA_pos c ht) 0).toNondegMetric) :
    (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) (fun _ ht => Cosmology.collapseA_pos c ht) 0).toNondegMetric.EinsteinEq cov 0
      (8 * Real.pi * Gn) (fun x v w => (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
        (Cosmology.collapse_contDiffOn c) (fun _ ht => Cosmology.collapseA_pos c ht) 0).fluidField
        (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) (fun y => Cosmology.collapseRho Gn c (y.1 0)) (fun _ => 0) x v w) := by
  have hcpos := fun t (ht : t ∈ Iio c) => Cosmology.collapseA_pos c ht
  have hE := (Cosmology.flrwManifold_einstein_iff_friedmann isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0 cov h
    (ρ := Cosmology.collapseRho Gn c) (p := fun _ => 0) (Gn := Gn) (Λ := 0)).2
    (fun t ht => Cosmology.collapse_friedmann hG c ht)
  have e : (fun x v w => (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
        (Cosmology.collapse_contDiffOn c) hcpos 0).fluidField
        (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) (fun y => Cosmology.collapseRho Gn c (y.1 0)) (fun _ => 0) x v w) =
      (fun x v w => matForm (Matrix.of fun μ ν => Cosmology.perfectFluid (Cosmology.collapseRho Gn c)
        (fun _ => 0) (Cosmology.flrwMetric (Cosmology.collapseA c) 0) μ ν x.1) v w) := by
    funext x v w
    exact flrwManifold_fluidField_eq isOpen_Iio (Cosmology.collapse_contDiffOn c) hcpos 0
      (Cosmology.collapseRho Gn c) (fun _ => 0) x v w
  rw [e]
  exact hE

/-- **The Ricci curvature of the collapsing dust universe along the flow**: `Ric(∂_t, ∂_t) = 2 / (3 (c - t)²)` at the
point of time coordinate `t < c`. -/
theorem collapse_ricci_comoving {Gn : ℝ} (hG : 0 < Gn)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0)))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) (fun _ ht => Cosmology.collapseA_pos c ht) 0).toNondegMetric)
    (x : Cosmology.flrwOpen (I := Iio c) isOpen_Iio (k := 0)) :
    cov.ricciAt x (Pi.single 0 1 : Fin 4 → ℝ) (Pi.single 0 1 : Fin 4 → ℝ) = 2 / (3 * (c - x.1 0) ^ 2) := by
  have hcpos := fun t (ht : t ∈ Iio c) => Cosmology.collapseA_pos c ht
  have := ricci_fluid_comoving (Cosmology.flrwManifoldMetric (a := Cosmology.collapseA c) isOpen_Iio
      (Cosmology.collapse_contDiffOn c) hcpos 0) cov (u := fun _ => (Pi.single 0 1 : Fin 4 → ℝ))
      (ρ := fun y => Cosmology.collapseRho Gn c (y.1 0)) (p := fun _ => 0)
      (collapse_einsteinEq_fluidField hG cov h) x (flrwManifold_comoving_unit isOpen_Iio
        (Cosmology.collapse_contDiffOn c) hcpos 0 x)
  rw [this]
  have hx : 0 < c - x.1 0 := sub_pos.2 x.2.1
  unfold Cosmology.collapseRho
  field_simp
  ring

end Lightlike
