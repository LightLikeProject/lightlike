import Lightlike.Spacetime.EHManifold.GraphDivergence
import Lightlike.Spacetime.VariationIntegral

/-!
# The divergence theorem on a domain whose boundary is locally a graph

* `integral_divergence_graph_below`: the divergence theorem on the region below a graph;
* `graphRegion σ γ i`: the region above (`σ = 1`) or below (`σ = -1`) the graph of `γ` in the `i`-th
  coordinate, or the whole space (`σ = 0`);
* `integral_divergence_patch`: localisation of the integral of a divergence with finitely many cut-off
  functions;
* `integral_divergence_of_graph_cover`: for a measurable set `D ⊆ ℝⁿ⁺¹`, a `C¹` vector field `F` with
  compact support and cut-off functions `ρ_a` such that on the support of `ρ_a` the set `D` is the region
  above or below a `C²` graph or everything, and `∑_a ρ_a F = F` near every point of `D`:

  `∫_D ∑_j ∂_j F_j = -∑_a σ_a ∫_{ℝⁿ} ρ_a (F_{i_a} - ∑_k ∂_k γ_a · F_{k'}) (y, γ_a(y)) dy`.

The right side is the integral of the flux of `F` through the boundary of `D`, written in the graph charts
with the partition of unity `ρ_a`: the outward normal times the surface element of the graph of `γ` is
`∓(e_i - ∇γ) dy`.

This follows the proof of the divergence theorem of Loomis–Sternberg: localisation by a partition of unity
and three cases (the support is outside the domain, inside the domain, or meets the boundary).

## References

* L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, section 6: Definition
  (domain with regular boundary), p. 419; Theorem 6.1, p. 421; proof, pp. 422–423.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- The partial derivatives of a `C¹` function are continuous. -/
lemma continuous_pd_of_contDiff_one {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) (j : Fin m) :
    Continuous (fun x => pd j F x) := by
  unfold pd
  exact (hF.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The partial derivatives of a compactly supported function are compactly supported. -/
lemma hasCompactSupport_pd {m : ℕ} {F : (Fin m → ℝ) → ℝ} (hc : HasCompactSupport F) (j : Fin m) :
    HasCompactSupport (fun x => pd j F x) := by
  unfold pd
  exact hc.fderiv_apply ℝ _

/-- A partial derivative vanishes where the function vanishes on a neighbourhood. -/
lemma pd_eq_zero_of_eventually_eq_zero {m : ℕ} {F : (Fin m → ℝ) → ℝ} {x : Fin m → ℝ}
    (h : ∀ᶠ y in 𝓝 x, F y = 0) (j : Fin m) : pd j F x = 0 := by
  unfold pd
  have h1 : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := h
  rw [h1.fderiv_eq]
  simp

/-- The divergence of a compactly supported `C¹` vector field is integrable. -/
lemma integrable_divergence {m : ℕ} (F : Fin m → (Fin m → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) :
    Integrable (fun x => ∑ j, pd j (F j) x) (volume : Measure (Fin m → ℝ)) :=
  integrable_finsetSum _ fun j _ =>
    (continuous_pd_of_contDiff_one (hF j) j).integrable_of_hasCompactSupport
      (hasCompactSupport_pd (hc j) j)

/-- The divergence of a compactly supported `C¹` vector field integrates to zero. -/
lemma integral_divergence_eq_zero {m : ℕ} (F : Fin m → (Fin m → ℝ) → ℝ)
    (hF : ∀ j, ContDiff ℝ 1 (F j)) (hc : ∀ j, HasCompactSupport (F j)) :
    ∫ x, ∑ j, pd j (F j) x = 0 := by
  rw [integral_finsetSum _ fun j _ =>
    (continuous_pd_of_contDiff_one (hF j) j).integrable_of_hasCompactSupport
      (hasCompactSupport_pd (hc j) j)]
  exact Finset.sum_eq_zero fun j _ => integral_pd_eq_zero (F j) (hF j) (hc j) j

/-- The graph of a measurable function has Lebesgue measure zero. -/
lemma volume_graph_eq_zero (γ : (Fin n → ℝ) → ℝ) (hγ : Measurable γ) (i : Fin (n + 1)) :
    volume {x : Fin (n + 1) → ℝ | x i = γ (i.removeNth x)} = 0 := by
  have hrem : Measurable (fun x : Fin (n + 1) → ℝ => i.removeNth x) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply (i.succAbove k)
  have hmeas : MeasurableSet {x : Fin (n + 1) → ℝ | x i = γ (i.removeNth x)} :=
    measurableSet_eq_fun (measurable_pi_apply i) (hγ.comp hrem)
  have hpre : shearFwd γ i ⁻¹' {x : Fin (n + 1) → ℝ | x i = γ (i.removeNth x)} =
      {x : Fin (n + 1) → ℝ | x i = 0} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, shearFwd_apply_same, removeNth_shearFwd]
    constructor <;> intro h <;> linarith
  rw [← (measurePreserving_shearFwd γ hγ i).measure_preimage hmeas.nullMeasurableSet, hpre]
  exact Measure.pi_hyperplane (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i 0

/-- **The divergence theorem on the region below a graph**, for a compactly supported `C¹` field. -/
theorem integral_divergence_graph_below (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 2 γ)
    (i : Fin (n + 1)) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) :
    ∫ x in {x : Fin (n + 1) → ℝ | x i ≤ γ (i.removeNth x)}, ∑ j, pd j (F j) x =
      ∫ y : Fin n → ℝ, (F i (Fin.insertNth (α := fun _ => ℝ) i (γ y) y) -
        ∑ k : Fin n, pd k γ y * F (i.succAbove k) (Fin.insertNth (α := fun _ => ℝ) i (γ y) y)) := by
  have hγm : Measurable γ := hγ.continuous.measurable
  have hrem : Measurable (fun x : Fin (n + 1) → ℝ => i.removeNth x) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply (i.succAbove k)
  have hmeas : MeasurableSet {x : Fin (n + 1) → ℝ | x i ≤ γ (i.removeNth x)} :=
    measurableSet_le (measurable_pi_apply i) (hγm.comp hrem)
  have hint := integrable_divergence F hF hc
  have hsplit := integral_add_compl hmeas hint
  rw [integral_divergence_eq_zero F hF hc] at hsplit
  -- the complement is the region above the graph, up to the graph
  have hae : ({x : Fin (n + 1) → ℝ | x i ≤ γ (i.removeNth x)}ᶜ : Set (Fin (n + 1) → ℝ)) =ᵐ[volume]
      {x : Fin (n + 1) → ℝ | γ (i.removeNth x) ≤ x i} := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · refine measure_mono_null (fun x hx => ?_) (measure_empty (μ := volume))
      simp only [Set.mem_sdiff, mem_compl_iff, mem_ofPred_eq, not_le] at hx
      exact (lt_asymm hx.1 hx.2).elim
    · refine measure_mono_null (fun x hx => ?_) (volume_graph_eq_zero γ hγm i)
      simp only [Set.mem_sdiff, mem_compl_iff, mem_ofPred_eq, not_not] at hx
      exact le_antisymm hx.2 hx.1
  rw [setIntegral_congr_set hae, integral_divergence_graph γ hγ i F hF hc] at hsplit
  linarith

/-- The region above (`σ = 1`) or below (`σ = -1`) the graph of `γ` in the `i`-th coordinate, or the whole
space (`σ = 0`). -/
def graphRegion (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)) : Set (Fin (n + 1) → ℝ) :=
  match σ with
  | SignType.pos => {x | γ (i.removeNth x) ≤ x i}
  | SignType.neg => {x | x i ≤ γ (i.removeNth x)}
  | SignType.zero => univ

/-- The flux of `F` through the graph of `γ`, in the graph chart:
`∫ (F_i - ∑_k ∂_k γ · F_{k'}) (y, γ(y)) dy`. -/
def graphFlux (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1))
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, (F i (Fin.insertNth (α := fun _ => ℝ) i (γ y) y) -
    ∑ k : Fin n, pd k γ y * F (i.succAbove k) (Fin.insertNth (α := fun _ => ℝ) i (γ y) y))

lemma measurableSet_graphRegion (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (hγ : Measurable γ)
    (i : Fin (n + 1)) : MeasurableSet (graphRegion σ γ i) := by
  have hrem : Measurable (fun x : Fin (n + 1) → ℝ => i.removeNth x) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply (i.succAbove k)
  cases σ
  · exact MeasurableSet.univ
  · exact measurableSet_le (measurable_pi_apply i) (hγ.comp hrem)
  · exact measurableSet_le (hγ.comp hrem) (measurable_pi_apply i)

/-- **The divergence theorem on a graph region** of either orientation, or on the whole space. -/
theorem integral_divergence_graphRegion (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (hγ : ContDiff ℝ 2 γ)
    (i : Fin (n + 1)) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) :
    ∫ x in graphRegion σ γ i, ∑ j, pd j (F j) x = -((σ : ℝ) * graphFlux γ i F) := by
  cases σ
  · show ∫ x in univ, ∑ j, pd j (F j) x = _
    rw [setIntegral_univ, integral_divergence_eq_zero F hF hc]
    simp
  · show ∫ x in {x : Fin (n + 1) → ℝ | x i ≤ γ (i.removeNth x)}, ∑ j, pd j (F j) x = _
    rw [integral_divergence_graph_below γ hγ i F hF hc]
    simp [graphFlux]
  · show ∫ x in {x : Fin (n + 1) → ℝ | γ (i.removeNth x) ≤ x i}, ∑ j, pd j (F j) x = _
    rw [integral_divergence_graph γ hγ i F hF hc]
    simp [graphFlux]

/-- **Localisation of the integral of a divergence.** If `∑_a ρ_a F = F` near every point of `D`, and on
the support of each `ρ_a` the set `D` agrees with a set `E_a`, then
`∫_D div F = ∑_a ∫_{E_a} div (ρ_a F)`. -/
theorem integral_divergence_patch {m : ℕ} {ι : Type*} [Fintype ι] (D : Set (Fin m → ℝ))
    (hD : MeasurableSet D) (F : Fin m → (Fin m → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) (ρ : ι → (Fin m → ℝ) → ℝ) (hρ : ∀ a, ContDiff ℝ 1 (ρ a))
    (E : ι → Set (Fin m → ℝ)) (hE : ∀ a, MeasurableSet (E a))
    (hDE : ∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ E a))
    (hsum : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, ∀ j, ∑ a, ρ a y * F j y = F j y) :
    ∫ x in D, ∑ j, pd j (F j) x = ∑ a, ∫ x in E a, ∑ j, pd j (fun y => ρ a y * F j y) x := by
  have hρF : ∀ a j, ContDiff ℝ 1 (fun y => ρ a y * F j y) := fun a j => (hρ a).mul (hF j)
  have hρFc : ∀ a j, HasCompactSupport (fun y => ρ a y * F j y) := fun a j => (hc j).mul_left
  have hint : ∀ a, Integrable (fun x => ∑ j, pd j (fun y => ρ a y * F j y) x)
      (volume : Measure (Fin m → ℝ)) := fun a =>
    integrable_divergence (fun j y => ρ a y * F j y) (hρF a) (hρFc a)
  -- on `D` the divergence is the sum of the divergences of the pieces
  have hpt : ∀ x ∈ D, ∑ j, pd j (F j) x = ∑ a, ∑ j, pd j (fun y => ρ a y * F j y) x := by
    intro x hx
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun y => ∑ a, ρ a y * F j y) =ᶠ[𝓝 x] F j := (hsum x hx).mono fun y hy => hy j
    have h2 : pd j (F j) x = pd j (fun y => ∑ a, ρ a y * F j y) x := by
      unfold pd
      rw [h1.fderiv_eq]
    rw [h2]
    exact pd_fun_sum Finset.univ (fun a y => ρ a y * F j y)
      (fun a _ => ((hρF a j).differentiable (by simp)).differentiableAt) j
  rw [setIntegral_congr_fun hD hpt, integral_finsetSum _ fun a _ => (hint a).integrableOn]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- outside the support of `ρ_a` the divergence of the piece vanishes
  have hzero : ∀ x, x ∉ tsupport (ρ a) → ∑ j, pd j (fun y => ρ a y * F j y) x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun j _ => pd_eq_zero_of_eventually_eq_zero ?_ j
    have hopen : (tsupport (ρ a))ᶜ ∈ 𝓝 x := (isClosed_tsupport _).isOpen_compl.mem_nhds hx
    filter_upwards [hopen] with y hy
    have : ρ a y = 0 := by
      by_contra hne
      exact hy (subset_tsupport _ hne)
    rw [this, zero_mul]
  rw [← integral_indicator hD, ← integral_indicator (hE a)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ tsupport (ρ a)
  · by_cases hxD : x ∈ D
    · rw [indicator_of_mem hxD, indicator_of_mem ((hDE a x hx).1 hxD)]
    · rw [indicator_of_notMem hxD, indicator_of_notMem fun h => hxD ((hDE a x hx).2 h)]
  · simp only [indicator, hzero x hx, ite_self]

/-- **The divergence theorem on a domain covered by graph charts**, with a given finite family of cut-off
functions. -/
theorem integral_divergence_of_graph_cover {ι : Type*} [Fintype ι] (D : Set (Fin (n + 1) → ℝ))
    (hD : MeasurableSet D) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ)
    (hρ : ∀ a, ContDiff ℝ 1 (ρ a)) (σ : ι → SignType) (γ : ι → (Fin n → ℝ) → ℝ)
    (hγ : ∀ a, ContDiff ℝ 2 (γ a)) (i : ι → Fin (n + 1))
    (hDE : ∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a)))
    (hsum : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, ∀ j, ∑ a, ρ a y * F j y = F j y) :
    ∫ x in D, ∑ j, pd j (F j) x =
      -∑ a, (σ a : ℝ) * graphFlux (γ a) (i a) (fun j y => ρ a y * F j y) := by
  rw [integral_divergence_patch D hD F hF hc ρ hρ (fun a => graphRegion (σ a) (γ a) (i a))
    (fun a => measurableSet_graphRegion (σ a) (γ a) (hγ a).continuous.measurable (i a)) hDE hsum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact integral_divergence_graphRegion (σ a) (γ a) (hγ a) (i a) (fun j y => ρ a y * F j y)
    (fun j => (hρ a).mul (hF j)) (fun j => (hc j).mul_left)

end Lightlike
