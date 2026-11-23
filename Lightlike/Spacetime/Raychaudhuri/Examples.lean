import Lightlike.Spacetime.Raychaudhuri.ConstField
import Lightlike.Spacetime.FLRWSlice
import Lightlike.Spacetime.EHManifold.Locality

/-!
# Trust checks of the Raychaudhuri equation on the manifold layer: Minkowski, FLRW, de Sitter (GE3)

The coordinate trust checks of `Lightlike/Cosmology/Raychaudhuri.lean` (`flrw_comoving_expansion`,
`minkowski_comoving_expansion`, `deSitter_no_focusing`) are transported to the manifold expansion `expansionM`
(`Lightlike/Spacetime/RaychaudhuriManifold.lean`) of the comoving field `∂_t` on the manifold `flrwOpen`, for any Levi-Civita
connection of `flrwManifoldMetric`:

* `flrwManifold_comoving_expansion`: `Θ = expansionM ∇ ∂_t = 3 ȧ/a` at every point;
* `minkowskiManifold_comoving_expansion`: `Θ = 0` for `a = 1`, `k = 0` (Minkowski space as the FLRW manifold with `a = 1`);
* `deSitterManifold_no_focusing`: for `a = e^{Ht}`, `k = 0`, `Θ = 3H` at every point and the Ricci curvature of `∂_t`
  (`cov.ricciAt`) is `-3H²`: the hypothesis `Ric(V, V) ≥ 0` of `raychaudhuri_focusing_manifold` fails, and for `H ≥ 0` the
  convergence hypothesis `Θ < 0` of `raychaudhuri_focusing_strongEC` fails: the congruence does not focus.

**Limits.** The comoving field is the coordinate field `∂_t` of the chart domain `flrwOpen` (Minkowski space is the case
`a = 1`, `k = 0`, `I = ℝ`, the whole of `ℝ⁴`).
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ)

/-- The coordinate components of `flrwManifoldMetric` agree with `flrwMetric` near every point. -/
theorem flrw_coordMetric_eventuallyEq (x₀ y : Cosmology.flrwOpen hI k) :
    (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric.coordMetric x₀ =ᶠ[𝓝 (y : Fin 4 → ℝ)]
      Cosmology.flrwMetric a k := by
  filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, Fin 4 → ℝ)) x₀).mem_nhds (Cosmology.flrw_mem_target hI k x₀ y)]
    with z hz
  exact Cosmology.flrwManifoldMetric_coordMetric hI ha hpos k x₀ hz

/-- **The expansion of the comoving congruence of FLRW on the manifold is `Θ = 3ȧ/a`.** -/
theorem flrwManifold_comoving_expansion (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen hI k))
    [LocallySmoothConnection cov] (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric)
    (q : Cosmology.flrwOpen hI k) :
    expansionM cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) q =
      3 * (deriv a ((q : Fin 4 → ℝ) 0) / a ((q : Fin 4 → ℝ) 0)) := by
  rw [expansionM_constField _ cov h q q]
  have hev := flrw_coordMetric_eventuallyEq hI ha hpos k q q
  have hq0 : (q : Fin 4 → ℝ) 0 ∈ I := q.2.1
  have hdiff : DifferentiableAt ℝ a ((q : Fin 4 → ℝ) 0) :=
    ((ha.contDiffAt (hI.mem_nhds hq0)).differentiableAt (by simp))
  have hrw : Cosmology.expansionConst
      ((Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric.coordMetric q) (Pi.single 0 1) (q : Fin 4 → ℝ) =
      Cosmology.expansionConst (Cosmology.flrwMetric a k) (Pi.single 0 1) (q : Fin 4 → ℝ) := by
    unfold Cosmology.expansionConst Cosmology.covConst
    simp only [christoffel_congr_nhds hev]
  rw [hrw]
  exact Cosmology.flrw_comoving_expansion hdiff (hpos _ hq0).ne' (show 0 < Cosmology.Dn k _ from q.2.2).ne'

/-- **Minkowski space on the manifold layer** (`a = 1`, `k = 0`, `I = ℝ`): the comoving congruence has `Θ = 0`. -/
theorem minkowskiManifold_comoving_expansion
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ)
      (Cosmology.flrwOpen (I := univ) isOpen_univ (k := 0)))
    [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric (a := fun _ => (1 : ℝ)) isOpen_univ
      contDiffOn_const (fun _ _ => one_pos) 0).toNondegMetric)
    (q : Cosmology.flrwOpen (I := univ) isOpen_univ (k := 0)) :
    expansionM cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) q = 0 := by
  rw [flrwManifold_comoving_expansion isOpen_univ (a := fun _ => (1 : ℝ)) contDiffOn_const (fun _ _ => one_pos) 0
    cov h q]
  simp

/-- The scale factor `e^{Ht}` of de Sitter space is smooth. -/
theorem contDiffOn_expScale (H : ℝ) : ContDiffOn ℝ ∞ (fun t : ℝ => Real.exp (H * t)) univ :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn

/-- **de Sitter on the manifold layer does not focus** (`a = e^{Ht}`, `k = 0`, `I = ℝ`): the comoving congruence has the constant
expansion `Θ = 3H` and `Ric(∂_t, ∂_t) = -3H²` at every point. So `Ric(V, V) ≥ 0` fails for `H ≠ 0`, and for `H ≥ 0` the hypothesis
`Θ < 0` of the focusing theorem fails too. -/
theorem deSitterManifold_no_focusing (H : ℝ)
    (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen (I := univ) isOpen_univ (k := 0)))
    [LocallySmoothConnection cov]
    (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric (a := fun t => Real.exp (H * t)) isOpen_univ
      (contDiffOn_expScale H) (fun _ _ => Real.exp_pos _) 0).toNondegMetric)
    (q : Cosmology.flrwOpen (I := univ) isOpen_univ (k := 0)) :
    expansionM cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) q = 3 * H ∧
      cov.ricciAt q (Pi.single 0 1 : Fin 4 → ℝ) (Pi.single 0 1 : Fin 4 → ℝ) = -3 * H ^ 2 := by
  have hcd := Cosmology.deSitter_no_focusing H (q : Fin 4 → ℝ)
  refine ⟨?_, ?_⟩
  · rw [flrwManifold_comoving_expansion isOpen_univ (a := fun t => Real.exp (H * t))
      (contDiffOn_expScale H) (fun _ _ => Real.exp_pos _) 0 cov h q]
    have := hcd.1
    rw [Cosmology.flrw_comoving_expansion] at this
    · exact this
    · exact ((hasDerivAt_id _).const_mul H).exp.differentiableAt
    · exact (Real.exp_pos _).ne'
    · simp [Cosmology.Dn]
  · have hq : q ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) q).source := mem_extChartAt_source q
    have hev := flrw_coordMetric_eventuallyEq isOpen_univ (a := fun t => Real.exp (H * t))
      (contDiffOn_expScale H) (fun _ _ => Real.exp_pos _) 0 q q
    have hv1 : hv q q (Pi.single 0 1 : Fin 4 → ℝ) = Pi.single 0 1 := by
      simpa [hat] using hat_const q q (Pi.single 0 1 : Fin 4 → ℝ)
    have key := ricciAt_hv' q cov _ h hq (show TangentSpace 𝓘(ℝ, Fin 4 → ℝ) q from (Pi.single 0 1 : Fin 4 → ℝ))
    refine key.trans ?_
    rw [hv1, opens_extChartAt_apply]
    simp only [Fin.sum_univ_four, Pi.single_apply]
    simp only [ricci_congr hev]
    simp [hcd.2]

end Lightlike
