import Mathlib.Geometry.Manifold.PartitionOfUnity
import Lightlike.Spacetime.EHManifold.DomainDivergence

/-!
# The divergence theorem on a domain with regular boundary in `ℝⁿ⁺¹`

`exists_graph_atlas_integral_divergence`: let `D ⊆ ℝⁿ⁺¹` be measurable and such that every point of the
closure of `D` has a neighbourhood in which `D` is the region above or below the graph of a `C²` function
of the other coordinates, or the whole neighbourhood. Let `F` be a `C¹` vector field with compact support.
Then there are finitely many such graph charts and smooth cut-off functions `ρ_a ≥ 0`, each supported in
its chart, with `∑_a ρ_a = 1` on the part of the closure of `D` in the support of `F`, such that

`∫_D ∑_j ∂_j F_j = -∑_a σ_a ∫_{ℝⁿ} ρ_a (F_{i_a} - ∑_k ∂_k γ_a · F_{k'}) (y, γ_a(y)) dy`.

The right side is the integral over the boundary of `D` of the flux of `F` in the outward direction, in the
sense of the integral of a density over a manifold: by charts and a partition of unity.

**Difference from the source.** Loomis–Sternberg define a domain with regular boundary by charts in which
the domain is a half-space; here the boundary is locally a graph over a coordinate hyperplane. The two
classes of domains agree by the implicit function theorem, which is not used or proved here. The boundary
integral is written in the graph charts with a partition of unity; a surface measure on the boundary and
the unit normal do not appear.

## References

* L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, section 6: Definition
  (domain with regular boundary), p. 419; Theorem 6.1, p. 421; proof, pp. 422–423.
-/

open MeasureTheory Set Filter Topology Manifold
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **The divergence theorem on a domain with regular boundary**, the boundary being locally a graph. -/
theorem exists_graph_atlas_integral_divergence (D : Set (Fin (n + 1) → ℝ)) (hD : MeasurableSet D)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j))
    (hloc : ∀ x ∈ closure D, ∃ U ∈ 𝓝 x, ∃ (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)),
      ContDiff ℝ 2 γ ∧ ∀ y ∈ U, (y ∈ D ↔ y ∈ graphRegion σ γ i)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ y ∈ closure D, (∃ j, y ∈ tsupport (F j)) → ∑ a, ρ a y = 1) ∧
      ∫ x in D, ∑ j, pd j (F j) x =
        -∑ a, (σ a : ℝ) * graphFlux (γ a) (i a) (fun j y => ρ a y * F j y) := by
  classical
  choose! U hU σ γ i hγ hUD using hloc
  obtain ⟨K, hKdef⟩ : ∃ K : Set (Fin (n + 1) → ℝ), K = ⋃ j, tsupport (F j) := ⟨_, rfl⟩
  have hK : IsCompact K := by
    rw [hKdef]
    exact isCompact_iUnion fun j => (hc j).isCompact
  have hKD : IsCompact (K ∩ closure D) := hK.inter_right isClosed_closure
  obtain ⟨t, htK, htcov⟩ := hKD.elim_nhds_subcover (fun x => interior (U x))
    (fun x hx => interior_mem_nhds.2 (hU x hx.2))
  obtain ⟨V, hVdef⟩ : ∃ V : Option {x // x ∈ t} → Set (Fin (n + 1) → ℝ),
      V = fun o => o.elim (closure D)ᶜ (fun a => interior (U a.1)) := ⟨_, rfl⟩
  have hVnone : V none = (closure D)ᶜ := by rw [hVdef]; rfl
  have hVsome : ∀ a, V (some a) = interior (U a.1) := fun a => by rw [hVdef]; rfl
  have hVo : ∀ o, IsOpen (V o) := by
    rintro (_ | a)
    · rw [hVnone]
      exact isClosed_closure.isOpen_compl
    · rw [hVsome]
      exact isOpen_interior
  have hVcov : K ⊆ ⋃ o, V o := by
    intro y hy
    by_cases hyD : y ∈ closure D
    · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (htcov ⟨hy, hyD⟩)
      refine mem_iUnion.2 ⟨some ⟨x, hx⟩, ?_⟩
      rw [hVsome]
      exact hyx
    · refine mem_iUnion.2 ⟨none, ?_⟩
      rw [hVnone]
      exact hyD
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin (n + 1) → ℝ) hK.isClosed V
    hVo hVcov
  -- the cut-off of the exterior piece vanishes near the closure of `D`
  have hnone : ∀ y ∈ closure D, y ∉ tsupport (f none) := by
    intro y hy hmem
    have h1 : y ∈ V none := hf none hmem
    rw [hVnone] at h1
    exact h1 hy
  have hsum1 : ∀ y ∈ K, y ∉ tsupport (f none) → ∑ a : {x // x ∈ t}, f (some a) y = 1 := by
    intro y hy hyn
    have h1 := f.sum_eq_one hy
    rw [finsum_eq_sum_of_fintype, Fintype.sum_option] at h1
    have h0 : f none y = 0 := by
      by_contra hne
      exact hyn (subset_tsupport _ hne)
    rw [h0, zero_add] at h1
    exact h1
  have hmemD : ∀ a : {x // x ∈ t}, a.1 ∈ closure D := fun a => (htK a.1 a.2).2
  have hDE : ∀ (a : {x // x ∈ t}) (x : Fin (n + 1) → ℝ), x ∈ tsupport (f (some a)) →
      (x ∈ D ↔ x ∈ graphRegion (σ a.1) (γ a.1) (i a.1)) := by
    intro a x hx
    have h1 : x ∈ V (some a) := hf (some a) hx
    rw [hVsome] at h1
    exact hUD a.1 (hmemD a) x (interior_subset h1)
  refine ⟨{x // x ∈ t}, inferInstance, fun a y => f (some a) y, fun a => σ a.1, fun a => γ a.1,
    fun a => i a.1, fun a => contMDiff_iff_contDiff.1 (f (some a)).contMDiff,
    fun a y => f.nonneg (some a) y, fun a => hγ a.1 (hmemD a), hDE, ?_, ?_⟩
  · rintro y hy ⟨j, hj⟩
    refine hsum1 y ?_ (hnone y hy)
    rw [hKdef]
    exact mem_iUnion.2 ⟨j, hj⟩
  · refine integral_divergence_of_graph_cover D hD F hF hc (fun a y => f (some a) y)
      (fun a => (contMDiff_iff_contDiff.1 (f (some a)).contMDiff).of_le (by simp))
      (fun a => σ a.1) (fun a => γ a.1) (fun a => hγ a.1 (hmemD a)) (fun a => i a.1) hDE ?_
    intro x hx
    have hopen : (tsupport (f none))ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds (hnone x (subset_closure hx))
    filter_upwards [hopen] with y hy j
    by_cases hyK : y ∈ K
    · rw [← Finset.sum_mul, hsum1 y hyK hy, one_mul]
    · have hFj : ∀ j, F j y = 0 := by
        intro j
        by_contra hne
        refine hyK ?_
        rw [hKdef]
        exact mem_iUnion.2 ⟨j, subset_tsupport _ hne⟩
      simp [hFj]

end Lightlike
