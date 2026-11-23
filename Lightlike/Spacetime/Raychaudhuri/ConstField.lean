import Lightlike.Spacetime.RaychaudhuriManifold
import Lightlike.Spacetime.OpenCoordMetric
import Lightlike.Cosmology.Raychaudhuri

/-!
# Constant coordinate fields on open subsets of `ℝⁿ`: the manifold expansion is the coordinate one (GE3)

On `↥U` for an open `U ⊆ ℝⁿ` the tangent trivializations are the identity (`opens_continuousLinearMapAt`), so the constant
field `V = v` has constant components in every chart. This links the trust checks of `Lightlike/Cosmology/Raychaudhuri.lean`
(`expansionConst`, coordinate stage) to the manifold expansion `expansionM`:

* `hat_const`, `chartComp_const`: the components of a constant field are constant;
* `contMDiff_constField`: a constant field is smooth;
* `expansionM_constField` (**the bridge**): for the Levi-Civita connection of a Lorentzian metric on `↥U`,
  `expansionM cov (fun _ => v) q = expansionConst (coordMetric) v q`.

**Limits.** Open subsets of `ℝⁿ` (one global chart); constant fields only.
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {U : Opens (Fin 4 → ℝ)}

/-- On `↥U` the components of a constant field in the trivialization at `x₀` are the constant. -/
theorem hat_const (x₀ z : U) (v : Fin 4 → ℝ) : hat x₀ (fun _ : U => v) z = v := by
  have hz : z ∈ (tTriv (E := Fin 4 → ℝ) x₀).baseSet := by
    refine mem_baseSet_of_mem_source x₀ ?_
    simp [extChartAt, Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  unfold hat
  have h1 := Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (tTriv (E := Fin 4 → ℝ) x₀) hz v
  rw [opens_continuousLinearMapAt] at h1
  exact h1.symm

/-- A constant field on `↥U` is smooth. -/
theorem contMDiff_constField (v : Fin 4 → ℝ) :
    ContMDiff 𝓘(ℝ, Fin 4 → ℝ) (𝓘(ℝ, Fin 4 → ℝ).prod 𝓘(ℝ, Fin 4 → ℝ)) ∞
      (fun q : U => (⟨q, (fun _ : U => v) q⟩ : TangentBundle 𝓘(ℝ, Fin 4 → ℝ) U)) := by
  intro x₀
  rw [contMDiffAt_section (E := TangentSpace 𝓘(ℝ, Fin 4 → ℝ)) (s := fun _ : U => v)]
  have : (fun x => (trivializationAt (Fin 4 → ℝ) (TangentSpace 𝓘(ℝ, Fin 4 → ℝ)) x₀
      (⟨x, (fun _ : U => v) x⟩ : TotalSpace (Fin 4 → ℝ) (TangentSpace 𝓘(ℝ, Fin 4 → ℝ) : U → Type _))).2) =
      fun _ => v := funext fun z => hat_const x₀ z v
  rw [this]
  exact contMDiffAt_const

/-- The chart components of a constant field are the constant, on the chart target. -/
theorem chartComp_const (x₀ : U) (v : Fin 4 → ℝ) (y : Fin 4 → ℝ) :
    chartComp x₀ (fun _ : U => v) y = v := hat_const x₀ _ v

/-- **The bridge**: for a Lorentzian metric on `↥U` with Levi-Civita connection, the manifold expansion of a constant
coordinate field is the coordinate expansion `expansionConst` of the chart components of the metric. -/
theorem expansionM_constField (gL : LorentzianMetric 𝓘(ℝ, Fin 4 → ℝ) U 4)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) U) [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita gL.toNondegMetric) (x₀ q : U) (v : Fin 4 → ℝ) :
    expansionM cov (fun _ : U => v) q =
      Cosmology.expansionConst (gL.toNondegMetric.coordMetric x₀) v (q : Fin 4 → ℝ) := by
  have hq : q ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) x₀).source := by
    simp [extChartAt, Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  rw [expansionM_eq cov gL.toNondegMetric h (contMDiff_constField v) x₀ hq]
  rw [opens_extChartAt_apply]
  have hc : chartComp x₀ (fun _ : U => v) = fun _ => v := funext (chartComp_const x₀ v)
  simp only [expansion, covD, hc, Cosmology.expansionConst, Cosmology.covConst, pd]
  simp
end Lightlike
