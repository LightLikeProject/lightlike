import Lightlike.PL.SliceSwap
import Lightlike.PL.Realisation
import Lightlike.PL.RadialCell
import Lightlike.PL.CellPolytope
import Lightlike.PL.ImageSB
import Lightlike.PL.DerivedGeom

/-!
# Derived boundaries of cells are stellar spheres

The radial argument: the derived boundary of a cell of a slicing is, after the chosen points are
replaced by the cell's centre, the boundary of a bounded polytope in the cell's affine subspace.
By the radial bijection it is a subdivision of the boundary of a simplex of the same dimension,
and a subdivision of a simplex boundary is a stellar sphere once subdivisions of lower dimension
are stellar equivalent.

## Main results

* `SComplex.derivedBoundary_isSphere_vertex`: a cell on one vertex has the empty sphere as
  derived boundary.
* `SComplex.derivedBoundary_isSphere`: the derived boundary of a cell is a stellar sphere of
  dimension at most `n`, given that subdivisions with at most `n` vertices per face are stellar
  equivalent.
-/

open Finset Module

namespace Lightlike.PL
namespace SComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

open Classical in
/-- **S for a vertex cell.** A cell on a single vertex has no proper faces among the nonempty
cells, so its derived boundary is the empty sphere (the boundary of a point). -/
theorem derivedBoundary_isSphere_vertex [Infinite (CellIdx E ι)] {K : SComplex E}
    (H : ι → E →ᵃ[ℝ] ℝ) {C : CellIdx E ι} (hC : C ∈ cells K (fun i => ⇑(H i)))
    (hv : C.1.card = 1) :
    IsSB false 0 (orderComplex ((cells K (fun i => ⇑(H i))).filter (· < C))) := by
  have hempty : (cells K (fun i => ⇑(H i))).filter (· < C) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun D hD hlt => ?_
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hv
    have hDne : D.1.Nonempty := by
      obtain ⟨y, hy⟩ := (mem_cells.1 hD).2
      exact nonempty_of_mem_openHull hy.1
    have hsub : D.1 ⊆ {x} := hx ▸ hlt.le.1
    have hDx : D.1 = {x} := Finset.Subset.antisymm hsub (by
      obtain ⟨y, hy⟩ := hDne
      simpa [Finset.mem_singleton.1 (hsub hy)] using hy)
    have hsign : ∀ F : CellIdx E ι, F ∈ cells K (fun i => ⇑(H i)) → F.1 = {x} →
        ∀ i, F.2 i = SignType.sign (H i x) := by
      intro F hF hFx i
      obtain ⟨y, hy1, hy2⟩ := (mem_cells.1 hF).2
      have : y = x := by
        rw [hFx] at hy1
        obtain ⟨w, hw, h1, hy⟩ := hy1
        have h1' : w x = 1 := by simpa using h1
        have hy' : w x • x = y := by simpa using hy
        rw [h1', one_smul] at hy'
        exact hy'.symm
      rw [← hy2 i, this]
    refine hlt.ne (Prod.ext (hDx.trans hx.symm) (funext fun i => ?_))
    rw [hsign D hD hDx i, hsign C hC hx i]
  rw [hempty]
  obtain ⟨a⟩ : Nonempty (CellIdx E ι) := ⟨C⟩
  refine .inl ⟨{a}, by simp, ?_⟩
  rw [boundary_singleton]
  have : orderComplex (∅ : Finset (CellIdx E ι)) = simplex ∅ := by
    refine ext_mem fun s => ?_
    simp only [mem_orderComplex, mem_simplex, Finset.subset_empty]
    constructor
    · rintro ⟨h, _⟩; exact h
    · rintro rfl; simp
  rw [this]

open Classical in
/-- **S: the derived boundary of a cell is a stellar sphere**, given stellar equivalence of
subdivisions of lower dimension. In the slicing of a geometric complex `K` (with at most `n + 1`
vertices per face) by affine functionals `H`, the faces strictly below a cell `C` form a complex
that is a stellar sphere of dimension `d ≤ n`, the dimension of the affine subspace of `C`. -/
theorem derivedBoundary_isSphere [Infinite E] {n : ℕ} (hT : SubdivStellar E (n - 1))
    {K : SComplex E} (hK : IsGeom K) (hKn : ∀ s ∈ K, #s ≤ n + 1)
    (H : ι → E →ᵃ[ℝ] ℝ) {C : CellIdx E ι} (hC : C ∈ cells K (fun i => ⇑(H i))) :
    ∃ d ≤ n, finrank ℝ (cellA H C).direction = d ∧
      IsSB false d (orderComplex ((cells K (fun i => ⇑(H i))).filter (· < C))) := by
  haveI : Infinite (CellIdx E ι) :=
    Infinite.of_injective (fun x : E => ((({x} : Finset E), fun _ => (0 : SignType)) :
      CellIdx E ι)) (fun a b h => by simpa using congrArg (fun c : CellIdx E ι => c.1) h)
  set S := sliceStructure K hK H with hS
  have hCS : C ∈ S.cells := hC
  have hs : AffineIndependent ℝ ((↑) : C.1 → E) := hK.indep C.1 (mem_cells.1 hC).1
  obtain ⟨w, hw⟩ := exists_barycentric C.1 hs
  have hle : (cellA H C).direction ≤ vectorSpan ℝ (C.1 : Set E) := by
    rw [← direction_affineSpan]; exact AffineSubspace.direction_le (fun x hx => hx.1)
  haveI : FiniteDimensional ℝ (vectorSpan ℝ (C.1 : Set E)) :=
    finiteDimensional_vectorSpan_of_finite ℝ C.1.finite_toSet
  haveI hfin : FiniteDimensional ℝ (cellA H C).direction := Submodule.finiteDimensional_of_le hle
  set d := finrank ℝ (cellA H C).direction with hd
  have hdn : d ≤ n := by
    have hne : Nonempty C.1 := by
      obtain ⟨x, hx⟩ := (mem_cells.1 hC).2
      exact (nonempty_of_mem_openHull hx.1).to_subtype
    have h1 : finrank ℝ (vectorSpan ℝ (C.1 : Set E)) + 1 = #C.1 := by
      have h := hs.finrank_vectorSpan_add_one
      rw [Fintype.card_coe] at h
      have hv : vectorSpan ℝ (Set.range ((↑) : C.1 → E)) = vectorSpan ℝ (C.1 : Set E) := by
        rw [Subtype.range_coe]
      have : finrank ℝ (vectorSpan ℝ (Set.range ((↑) : C.1 → E))) =
          finrank ℝ (vectorSpan ℝ (C.1 : Set E)) := by rw [hv]
      omega
    have h2 := Submodule.finrank_mono hle
    have h3 := hKn C.1 (mem_cells.1 hC).1
    omega
  refine ⟨d, hdn, rfl, ?_⟩
  have hne : C.1.Nonempty := by
    obtain ⟨x, hx⟩ := (mem_cells.1 hC).2
    exact nonempty_of_mem_openHull hx.1
  haveI : Nonempty (C.1 ⊕ ι) := ⟨.inl ⟨hne.choose, hne.choose_spec⟩⟩
  have hcell := cellSet_eq H C w hw
  have hvC : S.pt C ∈ cellSet (fun i => ⇑(H i)) C := S.pt_mem C hCS
  have hvO : S.pt C ∈ openHull C.1 := hvC.1
  rw [hcell] at hvC
  obtain ⟨hvA, hneg⟩ := hvC
  have hsph : IsSB false d (S.chainsBelow C) := by
    refine isSB_of_polytope_boundary
      (fun M N hMN h0M h0N hN => hT M N hMN h0M h0N fun s hs => le_trans (hN s hs) (by omega))
      (cellA H C) rfl hvA (cellG H C w) hneg ?_ (S.isGeom_chainsBelow C) (S.empty_mem_chainsBelow C) ?_ ?_
    · intro y hyA hyv
      by_contra hcon
      have hge : ∀ k, cellG H C w k y ≤ cellG H C w k (S.pt C) :=
        fun k => not_lt.1 fun h => hcon ⟨k, h⟩
      obtain ⟨u, hu1, huy⟩ := exists_weights_of_mem_affineSpan (mem_cellA.1 hyA).1
      obtain ⟨u0, hu0, hu01, hu0v⟩ := hvO
      have hwy : ∀ z ∈ C.1, w z y = u z := fun z hz => by
        have := hw u hu1 z hz; rwa [huy] at this
      have hwv : ∀ z ∈ C.1, w z (S.pt C) = u0 z := fun z hz => by
        have := hw u0 hu01 z hz; rwa [hu0v] at this
      have hdiff : ∀ z ∈ C.1, u0 z ≤ u z := fun z hz => by
        have := hge (.inl ⟨z, hz⟩)
        simp only [cellG_inl] at this
        rw [hwy z hz, hwv z hz] at this
        linarith
      have hsum : ∑ z ∈ C.1, (u z - u0 z) = 0 := by
        rw [Finset.sum_sub_distrib, hu1, hu01]; ring
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun z hz => sub_nonneg.2 (hdiff z hz))).1 hsum
      apply hyv
      rw [← huy, ← hu0v]
      exact Finset.sum_congr rfl fun z hz' => by rw [sub_eq_zero.1 (hz z hz')]
    · intro s hsγ
      obtain ⟨D, hDsub, hDch, rfl⟩ := S.mem_chainsBelow.1 hsγ
      rcases D.eq_empty_or_nonempty with rfl | hDne
      · simp
      obtain ⟨m, hmD, hmax⟩ := Finset.exists_maximal hDne
      have hmC : m < C := (Finset.mem_filter.1 (hDsub hmD)).2
      obtain ⟨k, hk⟩ := exists_facet H hmC w hw
      have hle : ∀ x ∈ D, x ≤ m := fun x hx => by
        rcases eq_or_ne x m with rfl | hxm
        · exact le_rfl
        · rcases hDch hx hmD hxm with h | h
          · exact h
          · exact hmax hx h
      have hin : ∀ x ∈ D, S.pt x ∈ sliceHull H m := fun x hx => by
        have hxc := (Finset.mem_filter.1 (hDsub hx)).1
        have hmc := (Finset.mem_filter.1 (hDsub hmD)).1
        exact S.hull_mono m hmc x hxc (hle x hx) (S.cell_subset_hull x hxc (S.pt_mem x hxc))
      refine card_le_finrank_of_hyperplane (cellA H C) (cellG H C w k) hvA
        (hneg k).ne _ ((S.isGeom_chainsBelow C).indep _ hsγ) ?_ ?_
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq E) S.pt D z).1 hz
        have hmc := (Finset.mem_filter.1 (hDsub hmD)).1
        have h2 : S.pt x ∈ sliceHull H C := S.hull_mono C hCS m hmc hmC.le (hin x hx)
        rw [sliceHull_eq H C w hw] at h2
        exact h2.1
      · intro z hz
        obtain ⟨x, hx, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq E) S.pt D z).1 hz
        exact hk _ (hin x hx)
    · have hsp : (S.chainsBelow C).space = sliceHull H C \ cellSet (fun i => ⇑(H i)) C :=
        space_chainsBelow_slice K hK H hCS
      rw [hsp, sliceHull_eq H C w hw, hcell]
      ext x
      simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hA, hle⟩, hnot⟩
        refine ⟨hA, hle, ?_⟩
        by_contra hcon
        exact hnot ⟨hA, fun k => lt_of_le_of_ne (hle k) fun h => hcon ⟨k, h⟩⟩
      · rintro ⟨hA, hle, k, hk⟩
        exact ⟨⟨hA, hle⟩, fun h => (h.2 k).ne hk⟩
  have hsph' : IsSB false d ((orderComplex ((cells K (fun i => ⇑(H i))).filter (· < C))).image S.pt) := by
    convert hsph
    unfold CellStructure.chainsBelow
    congr!
  exact isSB_of_image (S.pt_injOn.mono fun x hx =>
    (Finset.mem_filter.1 (mem_of_mem_verts_orderComplex hx)).1) hsph'

end SComplex
end Lightlike.PL
