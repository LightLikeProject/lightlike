import Lightlike.Spacetime.Raychaudhuri.Examples

/-!
# The covariant derivative of the comoving field of FLRW on the manifold layer (GE3)

For the Levi-Civita connection of `flrwManifoldMetric` the comoving field `∂_t` (the constant field `e₀` on `flrwOpen`) has
`∇_u ∂_t = H · (u₁, u₂, u₃)` in the standard coordinates (`flrwManifold_comoving_cov`). Consequences used by the collapsing
dust example:

* `flrwManifold_comoving_geodesic`: `∇_{∂_t} ∂_t = 0`;
* `flrwManifold_comoving_rotationFree`: `g(∇_u ∂_t, w) = g(∇_w ∂_t, u)`.

**Limits.** The comoving field of the FLRW chart domain only; Levi-Civita connections of `flrwManifoldMetric`.
-/

open Manifold TopologicalSpace Bundle Filter Set
open scoped ContDiff Topology Matrix
noncomputable section
namespace Lightlike

/-- On `↥U` the components of a tangent vector in any chart trivialization are the vector itself. -/
theorem hv_opens {U : Opens (Fin 4 → ℝ)} (x₀ q : U) (u : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) q) :
    hv x₀ q u = u := by
  have hz : q ∈ (tTriv (E := Fin 4 → ℝ) x₀).baseSet := by
    refine mem_baseSet_of_mem_source x₀ ?_
    simp [extChartAt, Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_source]
  have h1 := Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) (tTriv (E := Fin 4 → ℝ) x₀) hz u
  rw [opens_continuousLinearMapAt] at h1
  exact h1.symm

variable {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k : ℝ)

/-- **The covariant derivative of the comoving field of FLRW**: `∇_u ∂_t = (0, H u₁, H u₂, H u₃)`. -/
theorem flrwManifold_comoving_cov (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen hI k))
    [LocallySmoothConnection cov] (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric)
    (q : Cosmology.flrwOpen hI k) (u : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) q) :
    cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) q u =
      fun i => if i ≠ 0 then Cosmology.Hf a (q : Fin 4 → ℝ) * u i else 0 := by
  have hq : q ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) q).source := mem_extChartAt_source q
  have key := hv_cov_eq' q cov _ h hq
    ((contMDiff_constField (U := Cosmology.flrwOpen hI k) (Pi.single 0 1)).mdifferentiableAt (by simp) (x := q)) u
  rw [hv_opens, hv_opens] at key
  rw [key]
  have hev := flrw_coordMetric_eventuallyEq hI ha hpos k q q
  have hq0 : (q : Fin 4 → ℝ) 0 ∈ I := q.2.1
  have hdiff : DifferentiableAt ℝ a ((q : Fin 4 → ℝ) 0) :=
    ((ha.contDiffAt (hI.mem_nhds hq0)).differentiableAt (by simp))
  have hcov := Cosmology.flrw_comoving_covDeriv (k := k) hdiff (hpos _ hq0).ne'
    (show 0 < Cosmology.Dn k _ from q.2.2).ne'
  funext i
  simp only [Matrix.mulVec, dotProduct, covDMat, Matrix.of_apply, covD]
  rw [opens_extChartAt_apply]
  have hc : chartComp q (fun _ : Cosmology.flrwOpen hI k => (Pi.single 0 1 : Fin 4 → ℝ)) = fun _ => Pi.single 0 1 :=
    funext (chartComp_const q _)
  rw [hc]
  have : ∀ j, (pd j (fun z : Fin 4 → ℝ => (Pi.single 0 1 : Fin 4 → ℝ) i) (q : Fin 4 → ℝ)) +
      ∑ c, christoffel ((Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric.coordMetric q) i j c
        (q : Fin 4 → ℝ) * (Pi.single 0 1 : Fin 4 → ℝ) c =
      if i ≠ 0 ∧ i = j then Cosmology.Hf a (q : Fin 4 → ℝ) else 0 := fun j => by
    have h0 : pd j (fun z : Fin 4 → ℝ => (Pi.single 0 1 : Fin 4 → ℝ) i) (q : Fin 4 → ℝ) = 0 := by
      simp [pd]
    rw [h0, zero_add]
    have := hcov i j
    unfold Cosmology.covConst at this
    simp only [christoffel_congr_nhds hev]
    exact this
  simp only [this]
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, Finset.sum_ite_eq]

/-- **The comoving observers of FLRW are geodesic** on the manifold: `∇_{∂_t} ∂_t = 0`. -/
theorem flrwManifold_comoving_geodesic (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen hI k))
    [LocallySmoothConnection cov] (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric)
    (q : Cosmology.flrwOpen hI k) :
    cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) q (Pi.single 0 1 : Fin 4 → ℝ) = 0 := by
  refine (flrwManifold_comoving_cov hI ha hpos k cov h q (Pi.single 0 1)).trans ?_
  funext i
  by_cases hi : i = 0 <;> simp [hi] <;> rfl

/-- **The comoving congruence of FLRW is rotation-free** on the manifold: `g(∇_u ∂_t, w) = g(∇_w ∂_t, u)`. -/
theorem flrwManifold_comoving_rotationFree (cov : Connection 𝓘(ℝ, Fin 4 → ℝ) (Cosmology.flrwOpen hI k))
    [LocallySmoothConnection cov] (h : cov.IsLeviCivita (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric)
    (q : Cosmology.flrwOpen hI k) (u w : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) q) :
    (Cosmology.flrwManifoldMetric hI ha hpos k).g q
        (cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) q u) w =
      (Cosmology.flrwManifoldMetric hI ha hpos k).g q
        (cov (fun _ => (Pi.single 0 1 : Fin 4 → ℝ)) q w) u := by
  have hq : q ∈ (extChartAt 𝓘(ℝ, Fin 4 → ℝ) q).source := mem_extChartAt_source q
  have hg : ∀ x y : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) q,
      (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric.g q x y =
        x ⬝ᵥ (Cosmology.flrwMetric a k (q : Fin 4 → ℝ) *ᵥ y) := fun x y => by
    have := g_hv' q (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric hq x y
    rw [hv_opens, hv_opens, opens_extChartAt_apply,
      Cosmology.flrwManifoldMetric_coordMetric hI ha hpos k q (Cosmology.flrw_mem_target hI k q q)] at this
    exact this
  change (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric.g q _ _ =
    (Cosmology.flrwManifoldMetric hI ha hpos k).toNondegMetric.g q _ _
  rw [hg, hg, flrwManifold_comoving_cov hI ha hpos k cov h q, flrwManifold_comoving_cov hI ha hpos k cov h q]
  unfold Cosmology.flrwMetric
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    ring

end Lightlike
