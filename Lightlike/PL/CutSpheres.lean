import Lightlike.PL.RadialSphere
import Lightlike.PL.SliceSwap

/-!
# The boundary spheres of the cut cells

When a functional `h` cuts a cell `A` of a slicing, the new cells over `A` on which `h` is positive
or negative are cells of the slicing by the functionals `H` and `h` together. The cells strictly
below such a new cell form a stellar sphere (`derivedBoundary_isSphere`), and the mixed poset only
renames them. Both new cells have the same affine subspace as `A`, so both spheres have its
dimension, which is at least one because `h` takes both signs on `A`.

## Main results

* `SComplex.cutSpheres`: the boundary-sphere hypothesis of the slicing walk holds, given stellar
  equivalence of subdivisions of dimension one lower.
-/

open Finset Module

namespace Lightlike.PL
namespace SComplex

/-- A stellar sphere or ball stays one after renaming the vertices by an embedding. -/
lemma isSB_map' {V W : Type*} [DecidableEq V] [DecidableEq W] [Infinite V] [Infinite W]
    {b : Bool} {m : ℕ} {D : SComplex V} (f : V ↪ W) (hD : IsSB b m D) : IsSB b m (D.map f) := by
  have hm : D.map f = D.image f := by
    refine ext_mem fun s => ?_
    show s ∈ (D.map f).faces ↔ s ∈ (D.image f).faces
    simp only [SComplex.map, SComplex.image, Finset.map_eq_image, Finset.mem_image]
  rw [hm]
  have hf : Set.InjOn f ↑D.verts := f.injective.injOn
  obtain ⟨g, hgf, hg⟩ := exists_leftInv_injOn D.verts f hf ∅
  have hg' : Set.InjOn g ↑(D.image f).verts := by
    rw [verts_image, coe_image]
    simpa using hg
  refine isSB_of_image hg' ?_
  have e : D.image (g ∘ f) = D := image_eq_self_of_fixed (g := g ∘ f) fun x hx => hgf x hx
  rwa [image_image_eq, e]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E] {ι : Type*} [Fintype ι]
  [DecidableEq ι] {K : SComplex E} {H : ι → E →ᵃ[ℝ] ℝ} {h : E →ᵃ[ℝ] ℝ}

open Classical in
/-- The cells of the mixed poset below the new cell over `A` with sign `e` are the cells of the
extended slicing below that new cell, renamed. -/
lemma mixed_filter_lt_newOver {D : Finset (CellIdx E ι)} {A : CellIdx E ι} {e : SignType}
    (hD : ∀ x ∈ cells K (fun i => ⇑(H i)), x < A → x ∈ D) :
    (mixedCells K H h (insert A D)).filter (· < newOver A e) =
      ((cells K (extH H h)).filter (· < mkCell A.1 (extSign A.2 e))).map Mixed.newEmb := by
  classical
  refine Finset.ext fun m => ?_
  rw [Finset.mem_filter, Finset.mem_map]
  rcases m with a | b
  · constructor
    · rintro ⟨-, hl⟩
      exact absurd hl.le Mixed.not_old_le_new
    · rintro ⟨x, -, hx⟩
      cases hx
  · rw [new_mem_mixedCells]
    constructor
    · rintro ⟨⟨hb, -⟩, hl⟩
      exact ⟨b, Finset.mem_filter.2 ⟨hb, lt_of_le_of_ne (Mixed.new_le_new.1 hl.le)
        fun he => hl.ne (by rw [he]; rfl)⟩, rfl⟩
    · rintro ⟨b', hb', hbb⟩
      have e1 : b = b' := (Mixed.new.inj hbb).symm
      subst e1
      obtain ⟨hb, hl⟩ := Finset.mem_filter.1 hb'
      refine ⟨⟨hb, ?_⟩, lt_of_le_of_ne (Mixed.new_le_new.2 hl.le) fun he => hl.ne ?_⟩
      · have h1 : b.restr ≤ A := CellIdx.restr_mono hl.le
        have h2 : b.restr ∈ cells K (fun i => ⇑(H i)) := by
          rw [mem_cells] at hb ⊢
          obtain ⟨hσ, x, hx⟩ := hb
          exact ⟨hσ, x, ⟨hx.1, fun i => hx.2 (Sum.inl i)⟩⟩
        rcases eq_or_lt_of_le h1 with h3 | h3
        · rw [h3]; exact mem_insert_self _ _
        · exact mem_insert_of_mem (hD _ h2 h3)
      · exact Mixed.new.inj he

/-- The family `H` with `h` adjoined, as a family of affine functionals. -/
noncomputable def extFun (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) : ι ⊕ Unit → E →ᵃ[ℝ] ℝ :=
  Sum.elim H (fun _ => h)

omit [DecidableEq E] [Fintype ι] [DecidableEq ι] in
lemma extH_eq_extFun (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) :
    extH H h = fun j => ⇑(extFun H h j) := by
  funext j; rcases j with i | ⟨⟩ <;> rfl

omit [DecidableEq E] [Fintype ι] [DecidableEq ι] in
/-- A new cell with a nonzero sign for `h` has the same affine subspace as the cell under it. -/
lemma cellA_ext {A : CellIdx E ι} {e : SignType} (he : e ≠ 0) :
    cellA (extFun H h) (mkCell A.1 (extSign A.2 e)) = cellA H A := by
  ext x
  simp only [mem_cellA]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hx i hi
    exact hx (Sum.inl i) hi
  · intro hx j hj
    rcases j with i | ⟨⟩
    · exact hx i hj
    · exact absurd hj he

/-- The dimension of the affine subspace of a cut cell is positive. -/
lemma finrank_cellA_pos (hK : IsGeom K) {A : CellIdx E ι} (hA : A ∈ cells K (fun i => ⇑(H i)))
    (hp : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, 0 < h x)
    (hn : ∃ x ∈ cellSet (fun i => ⇑(H i)) A, h x < 0) :
    0 < finrank ℝ (cellA H A).direction := by
  have hAK : A.1 ∈ K := (mem_cells.1 hA).1
  obtain ⟨w, hw⟩ := exists_barycentric A.1 (hK.indep A.1 hAK)
  obtain ⟨p, hp1, hp2⟩ := hp
  obtain ⟨q, hq1, hq2⟩ := hn
  have hmem : ∀ x ∈ cellSet (fun i => ⇑(H i)) A, x ∈ cellA H A := fun x hx => by
    rw [cellSet_eq H A w hw] at hx; exact hx.1
  have hfin : FiniteDimensional ℝ (cellA H A).direction := by
    have hle : (cellA H A).direction ≤ vectorSpan ℝ ((A.1 : Finset E) : Set E) := by
      rw [← direction_affineSpan]
      exact AffineSubspace.direction_le fun x hx => hx.1
    have := finiteDimensional_vectorSpan_of_finite ℝ A.1.finite_toSet
    exact Submodule.finiteDimensional_of_le hle
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨⟨p -ᵥ q, AffineSubspace.vsub_mem_direction (hmem p hp1) (hmem q hq1)⟩, ?_⟩
  intro hz
  have : p -ᵥ q = 0 := congrArg Subtype.val hz
  rw [vsub_eq_zero_iff_eq] at this
  rw [this] at hp2
  linarith

open Classical in
/-- **The cut spheres exist.** Given stellar equivalence of subdivisions with at most `n` vertices
per face, and a geometric complex with at most `n + 1` vertices per face, the boundary spheres of
the new cells over a cut cell exist. -/
theorem cutSpheres [Infinite E] {n : ℕ} (hT : SubdivStellar E (n - 1)) (hK : IsGeom K)
    (hKn : ∀ s ∈ K, #s ≤ n + 1) (H : ι → E →ᵃ[ℝ] ℝ) (h : E →ᵃ[ℝ] ℝ) : CutSpheres K H h := by
  intro D A hA _ _ hD hp hz hn
  have hpos := finrank_cellA_pos hK hA hp hn
  have key : ∀ e : SignType, e ≠ 0 →
      mkCell A.1 (extSign A.2 e) ∈ cells K (extH H h) →
      IsSB false (finrank ℝ (cellA H A).direction)
        (orderComplex ((mixedCells K H h (insert A D)).filter (· < newOver A e))) := by
    intro e he hCx
    rw [mixed_filter_lt_newOver hD, orderComplex_map Mixed.newEmb Mixed.newEmb_le]
    have hCx' : mkCell A.1 (extSign A.2 e) ∈ cells K (fun j => ⇑(extFun H h j)) := by
      rw [← extH_eq_extFun]; exact hCx
    have : Infinite (CellIdx E (ι ⊕ Unit)) :=
      Infinite.of_injective (fun x : E => ((({x} : Finset E), fun _ => (0 : SignType)) :
        CellIdx E (ι ⊕ Unit))) (fun a b h => by simpa using congrArg (fun c => c.1) h)
    have : Infinite (Mixed E ι) := Infinite.of_injective (Mixed.newEmb (E := E) (ι := ι))
      Mixed.newEmb.injective
    obtain ⟨d, hdn, hdS⟩ := derivedBoundary_isSphere hT hK hKn (extFun H h) hCx'
    obtain ⟨hd, hS⟩ := hdS
    rw [cellA_ext he] at hd
    rw [hd, extH_eq_extFun]
    exact isSB_map' Mixed.newEmb hS
  have hc : ∀ e : SignType, mkCell A.1 (extSign A.2 e) ∈ cells K (extH H h) :=
    fun e => ext_cell_mem_of_cut (mem_cells.1 hA).1 hp hz hn e
  refine ⟨finrank ℝ (cellA H A).direction - 1, ?_, ?_⟩ <;> rw [Nat.sub_add_cancel hpos]
  · exact key 1 (by decide) (hc 1)
  · exact key (-1) (by decide) (hc (-1))
