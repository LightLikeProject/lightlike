import Lightlike.Spacetime.EHManifold.RegularDomainDivergence

/-!
# A finite graph atlas with a partition of unity for a domain with regular boundary

`exists_graph_atlas`: let `D ⊆ ℝⁿ⁺¹` be such that every point of its closure has a neighbourhood in which
`D` is the region above or below a `C²` graph, or the whole neighbourhood, and let `K` be compact. A property `Q` of the local descriptions that passes to
smaller neighbourhoods is carried along. Then
there are finitely many open sets `U_a` on which `D` is such a region, and smooth functions `ρ_a ≥ 0` with
support in `U_a`, such that `∑_a ρ_a = 1` on `K` near every point of the closure of `D`.

This is the construction inside `exists_graph_atlas_integral_divergence`, stated on its own for use with
other integrands (the boundary term of the Einstein–Hilbert action). Supporting; no catalogue entry.
-/

open Set Filter Topology Manifold
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **A finite graph atlas with a partition of unity**, for a set that is locally a graph region. -/
theorem exists_graph_atlas (D K : Set (Fin (n + 1) → ℝ)) (hK : IsCompact K)
    (Q : Set (Fin (n + 1) → ℝ) → SignType → ((Fin n → ℝ) → ℝ) → Fin (n + 1) → Prop)
    (hQ : ∀ (U U' : Set (Fin (n + 1) → ℝ)) (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)),
      U' ⊆ U → Q U σ γ i → Q U' σ γ i)
    (hloc : ∀ x ∈ closure D, ∃ U ∈ 𝓝 x, ∃ (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)),
      ContDiff ℝ 2 γ ∧ (∀ y ∈ U, (y ∈ D ↔ y ∈ graphRegion σ γ i)) ∧ Q U σ γ i) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)) (U : ι → Set (Fin (n + 1) → ℝ)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a, IsOpen (U a)) ∧ (∀ a, tsupport (ρ a) ⊆ U a) ∧
      (∀ a, ∀ x ∈ U a, (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ a, Q (U a) (σ a) (γ a) (i a)) ∧
      (∀ x ∈ closure D, ∀ᶠ y in 𝓝 x, y ∈ K → ∑ a, ρ a y = 1) := by
  classical
  choose! U hU σ γ i hγ hUD hQU using hloc
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
  refine ⟨{x // x ∈ t}, inferInstance, fun a y => f (some a) y, fun a => σ a.1, fun a => γ a.1,
    fun a => i a.1, fun a => interior (U a.1),
    fun a => contMDiff_iff_contDiff.1 (f (some a)).contMDiff,
    fun a y => f.nonneg (some a) y, fun a => hγ a.1 (hmemD a), fun a => isOpen_interior, ?_, ?_,
    fun a => hQ _ _ _ _ _ interior_subset (hQU a.1 (hmemD a)), ?_⟩
  · intro a x hx
    have h1 : x ∈ V (some a) := hf (some a) hx
    rw [hVsome] at h1
    exact h1
  · intro a x hx
    exact hUD a.1 (hmemD a) x (interior_subset hx)
  · intro x hx
    have hopen : (tsupport (f none))ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds (hnone x hx)
    filter_upwards [hopen] with y hy hyK
    exact hsum1 y hyK hy

end Lightlike
