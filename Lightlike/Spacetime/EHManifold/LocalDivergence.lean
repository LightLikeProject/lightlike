import Lightlike.Spacetime.EHManifold.DefiningFunction

/-!
# The divergence theorem in `ℝⁿ⁺¹` with a local hypothesis

The theorems of `RegularDomainDivergence.lean` and `DefiningFunction.lean` with the hypothesis on `D` asked only at the
points of the closure of `D` in the support of `F` (the proofs only use it there). This is the form needed in a chart of a
manifold, where the chart image of a domain is only known near the support of the field.
-/

open MeasureTheory Set Filter Topology Manifold
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- `exists_graph_atlas_integral_divergence` with the graph hypothesis only at the points of the closure of `D` in the
support of `F`., with open sets
`U a ⊇ tsupport (ρ a)` on which `D` is the graph region. -/
theorem exists_graph_atlas_integral_divergence_loc_open (D : Set (Fin (n + 1) → ℝ)) (hD : MeasurableSet D)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j))
    (hloc : ∀ x ∈ closure D, (∃ j, x ∈ tsupport (F j)) → ∃ U ∈ 𝓝 x, ∃ (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)),
      ContDiff ℝ 2 γ ∧ ∀ y ∈ U, (y ∈ D ↔ y ∈ graphRegion σ γ i)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)) (U : ι → Set (Fin (n + 1) → ℝ)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a, IsOpen (U a)) ∧ (∀ a, tsupport (ρ a) ⊆ U a) ∧
      (∀ a x, x ∈ U a → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
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
  have hKF : ∀ x ∈ K, ∃ j, x ∈ tsupport (F j) := fun x hx => by
    rw [hKdef] at hx; exact mem_iUnion.1 hx
  obtain ⟨t, htK, htcov⟩ := hKD.elim_nhds_subcover (fun x => interior (U x))
    (fun x hx => interior_mem_nhds.2 (hU x hx.2 (hKF x hx.1)))
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
  have hmemK : ∀ a : {x // x ∈ t}, ∃ j, a.1 ∈ tsupport (F j) := fun a => hKF a.1 (htK a.1 a.2).1
  have hDE : ∀ (a : {x // x ∈ t}) (x : Fin (n + 1) → ℝ), x ∈ tsupport (f (some a)) →
      (x ∈ D ↔ x ∈ graphRegion (σ a.1) (γ a.1) (i a.1)) := by
    intro a x hx
    have h1 : x ∈ V (some a) := hf (some a) hx
    rw [hVsome] at h1
    exact hUD a.1 (hmemD a) (hmemK a) x (interior_subset h1)
  have hUo : ∀ a : {x // x ∈ t}, tsupport (f (some a)) ⊆ interior (U a.1) := fun a x hx => by
    have h1 : x ∈ V (some a) := hf (some a) hx
    rwa [hVsome] at h1
  refine ⟨{x // x ∈ t}, inferInstance, fun a y => f (some a) y, fun a => σ a.1, fun a => γ a.1,
    fun a => i a.1, fun a => interior (U a.1), fun a => contMDiff_iff_contDiff.1 (f (some a)).contMDiff,
    fun a y => f.nonneg (some a) y, fun a => hγ a.1 (hmemD a) (hmemK a), fun a => isOpen_interior, hUo,
    fun a x hx => hUD a.1 (hmemD a) (hmemK a) x (interior_subset hx), ?_, ?_⟩
  · rintro y hy ⟨j, hj⟩
    refine hsum1 y ?_ (hnone y hy)
    rw [hKdef]
    exact mem_iUnion.2 ⟨j, hj⟩
  · refine integral_divergence_of_graph_cover D hD F hF hc (fun a y => f (some a) y)
      (fun a => (contMDiff_iff_contDiff.1 (f (some a)).contMDiff).of_le (by simp))
      (fun a => σ a.1) (fun a => γ a.1) (fun a => hγ a.1 (hmemD a) (hmemK a)) (fun a => i a.1) hDE ?_
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

/-- `exists_graph_atlas_integral_divergence` with the graph hypothesis only at the points of the closure of `D` in the
support of `F`. -/
theorem exists_graph_atlas_integral_divergence_loc (D : Set (Fin (n + 1) → ℝ)) (hD : MeasurableSet D)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j))
    (hloc : ∀ x ∈ closure D, (∃ j, x ∈ tsupport (F j)) → ∃ U ∈ 𝓝 x, ∃ (σ : SignType) (γ : (Fin n → ℝ) → ℝ) (i : Fin (n + 1)),
      ContDiff ℝ 2 γ ∧ ∀ y ∈ U, (y ∈ D ↔ y ∈ graphRegion σ γ i)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ y ∈ closure D, (∃ j, y ∈ tsupport (F j)) → ∑ a, ρ a y = 1) ∧
      ∫ x in D, ∑ j, pd j (F j) x =
        -∑ a, (σ a : ℝ) * graphFlux (γ a) (i a) (fun j y => ρ a y * F j y) := by
  obtain ⟨ι, hι, ρ, σ, γ, i, U, hρ, hρ0, hγ, -, hsU, hUD, hsum, hint⟩ :=
    exists_graph_atlas_integral_divergence_loc_open D hD F hF hc hloc
  exact ⟨ι, hι, ρ, σ, γ, i, hρ, hρ0, hγ, fun a x hx => hUD a x (hsU a hx), hsum, hint⟩

/-- `exists_graph_atlas_integral_divergence_of_defining_function` with the hypothesis only at the points of the closure
of `D` in the support of `F`., with open sets
`U a ⊇ tsupport (ρ a)` on which `D` is the graph region. -/
theorem exists_graph_atlas_integral_divergence_of_defining_function_loc_open (D : Set (Fin (n + 1) → ℝ))
    (hD : MeasurableSet D) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j))
    (hreg : ∀ x ∈ closure D, (∃ j, x ∈ tsupport (F j)) → ∃ u : (Fin (n + 1) → ℝ) → ℝ, ContDiffAt ℝ 2 u x ∧
      (u x = 0 → fderiv ℝ u x ≠ 0) ∧ ∀ᶠ y in 𝓝 x, (y ∈ D ↔ 0 ≤ u y)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)) (U : ι → Set (Fin (n + 1) → ℝ)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a, IsOpen (U a)) ∧ (∀ a, tsupport (ρ a) ⊆ U a) ∧
      (∀ a x, x ∈ U a → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ y ∈ closure D, (∃ j, y ∈ tsupport (F j)) → ∑ a, ρ a y = 1) ∧
      ∫ x in D, ∑ j, pd j (F j) x =
        -∑ a, (σ a : ℝ) * graphFlux (γ a) (i a) (fun j y => ρ a y * F j y) := by
  refine exists_graph_atlas_integral_divergence_loc_open D hD F hF hc fun x hx hxF => ?_
  obtain ⟨u, hu, hdu, hDu⟩ := hreg x hx hxF
  rcases lt_trichotomy (u x) 0 with hneg | hzero | hpos
  · -- impossible: no point of `D` near `x`
    exfalso
    have hev : ∀ᶠ y in 𝓝 x, y ∉ D := by
      filter_upwards [hDu, hu.continuousAt.eventually (gt_mem_nhds hneg)] with y hy1 hy2 hyD
      exact absurd (hy1.1 hyD) (not_le.2 hy2)
    obtain ⟨y, hyD, hyn⟩ := ((mem_closure_iff_frequently.1 hx).and_eventually hev).exists
    exact hyn hyD
  · exact exists_graphRegion_of_defining_function D x u hu hzero (hdu hzero) hDu
  · refine ⟨{y | (y ∈ D ↔ 0 ≤ u y) ∧ 0 < u y},
      hDu.and (hu.continuousAt.eventually (lt_mem_nhds hpos)), SignType.zero, fun _ => 0, 0,
      contDiff_const, fun y hy => ⟨fun _ => Set.mem_univ y, fun _ => hy.1.2 hy.2.le⟩⟩


/-- `exists_graph_atlas_integral_divergence_of_defining_function` with the hypothesis only at the points of the closure
of `D` in the support of `F`. -/
theorem exists_graph_atlas_integral_divergence_of_defining_function_loc (D : Set (Fin (n + 1) → ℝ))
    (hD : MeasurableSet D) (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j))
    (hreg : ∀ x ∈ closure D, (∃ j, x ∈ tsupport (F j)) → ∃ u : (Fin (n + 1) → ℝ) → ℝ, ContDiffAt ℝ 2 u x ∧
      (u x = 0 → fderiv ℝ u x ≠ 0) ∧ ∀ᶠ y in 𝓝 x, (y ∈ D ↔ 0 ≤ u y)) :
    ∃ (ι : Type) (_ : Fintype ι) (ρ : ι → (Fin (n + 1) → ℝ) → ℝ) (σ : ι → SignType)
      (γ : ι → (Fin n → ℝ) → ℝ) (i : ι → Fin (n + 1)),
      (∀ a, ContDiff ℝ ∞ (ρ a)) ∧ (∀ a y, 0 ≤ ρ a y) ∧ (∀ a, ContDiff ℝ 2 (γ a)) ∧
      (∀ a x, x ∈ tsupport (ρ a) → (x ∈ D ↔ x ∈ graphRegion (σ a) (γ a) (i a))) ∧
      (∀ y ∈ closure D, (∃ j, y ∈ tsupport (F j)) → ∑ a, ρ a y = 1) ∧
      ∫ x in D, ∑ j, pd j (F j) x =
        -∑ a, (σ a : ℝ) * graphFlux (γ a) (i a) (fun j y => ρ a y * F j y) := by
  obtain ⟨ι, hι, ρ, σ, γ, i, U, hρ, hρ0, hγ, -, hsU, hUD, hsum, hint⟩ :=
    exists_graph_atlas_integral_divergence_of_defining_function_loc_open D hD F hF hc hreg
  exact ⟨ι, hι, ρ, σ, γ, i, hρ, hρ0, hγ, fun a x hx => hUD a x (hsU a hx), hsum, hint⟩

end Lightlike
