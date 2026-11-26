import Mathlib
import Lightlike.Spacetime.LaplaceBeltrami.Weak

/-!
# Green's formula for the Laplace–Beltrami operator on a compact manifold

For a smooth nondegenerate metric `g` on a compact Hausdorff manifold modelled on `ℝⁿ`, with its volume measure, and
smooth functions `f, h`:

* `NondegMetric.integral_mul_laplaceBeltrami` (**Green's first identity**): `∫_M h Δ_g f dvol_g = ∫_M g⁻¹(dh, df) dvol_g`;
* `NondegMetric.integral_mul_laplaceBeltrami_symm` (**symmetry**): `∫_M h Δ_g f = ∫_M f Δ_g h`;
* `NondegMetric.integral_laplaceBeltrami_eq_zero`: `∫_M Δ_g f = 0`;
* `NondegMetric.continuous_laplaceBeltrami`, `NondegMetric.continuous_dualPair`: both sides are continuous.

The proof glues the weak form in a chart (`NondegMetric.integral_mul_laplaceBeltrami_chart`) with a smooth partition of
unity subordinate to the chart domains, which on a compact manifold has finitely many nonzero members. For a Riemannian
metric the right side of Green's identity with `h = f` is `∫ |df|² ≥ 0`: the Laplacian is nonnegative
(`Lightlike/Spacetime/LaplaceBeltrami/Riemannian.lean`).

## References

* `rosenberg-1997`: S. Rosenberg, *The Laplacian on a Riemannian Manifold* (1997), §1.2 (Green's formula on a closed
  manifold). Comparison pending (not read at that location).
-/

open MeasureTheory Set Manifold Matrix Filter
open scoped ContDiff Topology
noncomputable section
namespace Lightlike

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M]
  [MeasurableSpace M] [BorelSpace M] (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M)

/-- A function that is continuous on every chart domain is continuous. -/
theorem continuous_of_continuousOn_extChartAt_source {F : M → ℝ}
    (hF : ∀ x₀ : M, ContinuousOn F (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source) : Continuous F :=
  continuous_iff_continuousAt.2 fun x =>
    (hF x).continuousAt ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))

/-- **The Laplace–Beltrami operator of a smooth function is continuous.** -/
theorem NondegMetric.continuous_laplaceBeltrami {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) :
    Continuous (g.laplaceBeltrami f) :=
  continuous_of_continuousOn_extChartAt_source fun x₀ =>
    (g.continuousOn_laplaceAt hf x₀).congr fun _ hx => g.laplaceBeltrami_eq_coord hf x₀ hx

/-- **`g⁻¹(dψ, df)` is continuous.** -/
theorem NondegMetric.continuous_dualPair {f ψ : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f)
    (hψ : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ ψ) : Continuous (g.dualPair ψ f) :=
  continuous_of_continuousOn_extChartAt_source fun x₀ => g.continuousOn_dualPair hf hψ x₀

/-- `g⁻¹(dψ, df)` is additive in `ψ` over a finite sum of smooth functions. -/
theorem NondegMetric.dualPair_sum {ι : Type*} (S : Finset ι) {ψ : ι → M → ℝ}
    (hψ : ∀ i, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (ψ i)) (f : M → ℝ) (x : M) :
    g.dualPair (fun y => ∑ i ∈ S, ψ i y) f x = ∑ i ∈ S, g.dualPair (ψ i) f x := by
  have hd : ∀ i, DifferentiableAt ℝ (ψ i ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) := fun i =>
    ((contDiffOn_chart_comp (hψ i) x).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).differentiableAt (by simp)
  have hcp : ∀ k, coordPartial x (fun y => ∑ i ∈ S, ψ i y) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) k =
      ∑ i ∈ S, coordPartial x (ψ i) (extChartAt 𝓘(ℝ, Fin n → ℝ) x x) k := by
    intro k
    unfold coordPartial
    have : ((fun y => ∑ i ∈ S, ψ i y) ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) =
        fun z => ∑ i ∈ S, (ψ i ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) z := by
      funext z; simp
    rw [this, fderiv_fun_sum fun i _ => hd i, ContinuousLinearMap.sum_apply]
  unfold NondegMetric.dualPair
  rw [NondegMetric.dualPairCoord]
  simp only [NondegMetric.dualPairCoord, hcp, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

/-- `g⁻¹(dh, df) = g⁻¹(df, dh)`. -/
theorem NondegMetric.dualPair_comm (f h : M → ℝ) (x : M) : g.dualPair h f x = g.dualPair f h x := by
  unfold NondegMetric.dualPair NondegMetric.dualPairCoord
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hsym : (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹ j i =
      (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹ i j := by
    have ht := g.coordMetric_transpose x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)
    have : ((g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹)ᵀ =
        (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x x))⁻¹ := by rw [Matrix.transpose_nonsing_inv, ht]
    exact (congrFun (congrFun this i) j).symm.trans rfl |>.symm
  rw [hsym]; ring

/-- `g⁻¹(d1, df) = 0`. -/
theorem NondegMetric.dualPair_const_left (c : ℝ) (f : M → ℝ) (x : M) : g.dualPair (fun _ => c) f x = 0 := by
  unfold NondegMetric.dualPair NondegMetric.dualPairCoord coordPartial
  simp [Function.comp_def]

variable [CompactSpace M]

/-- **Green's first identity on a compact manifold**: `∫_M h Δ_g f dvol_g = ∫_M g⁻¹(dh, df) dvol_g`. -/
theorem NondegMetric.integral_mul_laplaceBeltrami {f h : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f)
    (hh : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ h) :
    ∫ x, h x * g.laplaceBeltrami f x ∂g.volumeMeasure = ∫ x, g.dualPair h f x ∂g.volumeMeasure := by
  haveI := g.isFiniteMeasure_volumeMeasure
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, Fin n → ℝ) M
  have hfin : {i | (Function.support (χ i)).Nonempty}.Finite := χ.locallyFinite.finite_nonempty_of_compact
  set S := hfin.toFinset with hS
  have hsum : ∀ x, ∑ i ∈ S, χ i x = 1 := by
    intro x
    rw [← χ.sum_eq_one (mem_univ x), finsum_eq_sum_of_support_subset]
    intro i hi
    simp only [hS, Set.Finite.coe_toFinset, mem_setOf_eq]
    exact ⟨x, hi⟩
  set ψ := fun i x => χ i x * h x with hψdef
  have hψ : ∀ i, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ (ψ i) := fun i => (χ i).contMDiff.mul hh
  have hψs : ∀ i, tsupport (ψ i) ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) i).source := fun i =>
    (tsupport_mul_subset_left).trans (by rw [extChartAt_source]; exact hχ i)
  have hψc : ∀ i, HasCompactSupport (ψ i) := fun i => isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
    (subset_univ _)
  have hh_eq : h = fun x => ∑ i ∈ S, ψ i x := by
    funext x; simp only [hψdef, ← Finset.sum_mul, hsum, one_mul]
  have hΔ := g.continuous_laplaceBeltrami hf
  calc ∫ x, h x * g.laplaceBeltrami f x ∂g.volumeMeasure
      = ∫ x, ∑ i ∈ S, ψ i x * g.laplaceBeltrami f x ∂g.volumeMeasure := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only; conv_lhs => rw [hh_eq]
        rw [Finset.sum_mul]
    _ = ∑ i ∈ S, ∫ x, ψ i x * g.laplaceBeltrami f x ∂g.volumeMeasure :=
        integral_finsetSum _ fun i _ => ((hψ i).continuous.mul hΔ).integrable_of_hasCompactSupport
          (hψc i).mul_right
    _ = ∑ i ∈ S, ∫ x, g.dualPair (ψ i) f x ∂g.volumeMeasure :=
        Finset.sum_congr rfl fun i _ => g.integral_mul_laplaceBeltrami_chart hf (hψ i) (hψc i) i (hψs i)
    _ = ∫ x, ∑ i ∈ S, g.dualPair (ψ i) f x ∂g.volumeMeasure :=
        (integral_finsetSum _ fun i _ => (g.continuous_dualPair hf (hψ i)).integrable_of_hasCompactSupport
          (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))).symm
    _ = ∫ x, g.dualPair h f x ∂g.volumeMeasure := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [← g.dualPair_sum S hψ f x, ← hh_eq]

/-- **The Laplace–Beltrami operator is symmetric**: `∫_M h Δ_g f = ∫_M f Δ_g h`. -/
theorem NondegMetric.integral_mul_laplaceBeltrami_symm {f h : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f)
    (hh : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ h) :
    ∫ x, h x * g.laplaceBeltrami f x ∂g.volumeMeasure = ∫ x, f x * g.laplaceBeltrami h x ∂g.volumeMeasure := by
  rw [g.integral_mul_laplaceBeltrami hf hh, g.integral_mul_laplaceBeltrami hh hf]
  exact integral_congr_ae (Eventually.of_forall fun x => g.dualPair_comm f h x)

/-- **The integral of a Laplacian vanishes** on a compact manifold. -/
theorem NondegMetric.integral_laplaceBeltrami_eq_zero {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f) :
    ∫ x, g.laplaceBeltrami f x ∂g.volumeMeasure = 0 := by
  have := g.integral_mul_laplaceBeltrami hf (contMDiff_const (c := (1 : ℝ)))
  simp only [one_mul] at this
  rw [this]
  simp [g.dualPair_const_left]

end Lightlike
