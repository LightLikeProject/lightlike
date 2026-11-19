import Lightlike.SpinFoam.ForcingMove33

/-!
# Forcing is hitting every blocking set

A set `X` of triangles of a 4D complex `K` is *blocking* if no tetrahedron of `K` has exactly one of
its four triangles in `X`. A nonzero Ooguri colouring has such a support: a tetrahedron cannot have
exactly one triangle of nonzero spin, by the triangle condition at the tetrahedron.

The forcing rule of the gauge-fixed state sum ("a tetrahedron with three of its triangles in the set
forces the fourth") is dual to blocking sets: a set `T` of triangles forces every triangle of `K`
if and only if every nonempty blocking set meets `T` (`forces_iff_meets_blocking`). Over the field with
two elements, every 2-cocycle of `K` (a set of triangles with an even number in each tetrahedron) is
blocking, so a forcing set meets every nonzero 2-cocycle.
-/

open Finset Lightlike.FourD Complex4

namespace Lightlike.SpinFoam

variable {V : Type*} [LinearOrder V]

/-- **Blocking sets.** A set `X` of triangles of `K` such that no tetrahedron of `K` has exactly one of
its four triangles in `X`. -/
def Blocking (K : Complex4 V) (X : Finset (Finset V)) : Prop :=
  X ⊆ K.tris ∧ ∀ t ∈ K.tets, #((t.powersetCard 3).filter (· ∈ X)) ≠ 1

/-- The triangles of a tetrahedron of `K` are triangles of `K`. -/
lemma powersetCard_three_subset_tris {K : Complex4 V} {t : Finset V} (ht : t ∈ K.tets) :
    t.powersetCard 3 ⊆ K.tris := by
  intro g hg
  obtain ⟨S, hS, htS, -⟩ := Complex4.mem_faces.mp ht
  obtain ⟨hgt, hgc⟩ := mem_powersetCard.mp hg
  exact Complex4.mem_faces.mpr ⟨S, hS, hgt.trans htS, hgc⟩

/-- **Forcing is hitting every blocking set.** A set `T` of triangles of `K` forces every triangle of
`K` if and only if it meets every nonempty blocking set. -/
theorem forces_iff_meets_blocking (K : Complex4 V) {T : Finset (Finset V)} (hT : T ⊆ K.tris) :
    Forces K K.tris T ↔ ∀ X, Blocking K X → X.Nonempty → (X ∩ T).Nonempty := by
  classical
  constructor
  · intro hF X hX hne
    by_contra hdisj
    rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdisj
    have hcl : ClosedUnder K.tets (K.tris \ X) := by
      intro t ht f hf hothers
      have hsub := powersetCard_three_subset_tris ht
      by_contra hfn
      have hfX : f ∈ X := by
        by_contra h'
        exact hfn (mem_sdiff.mpr ⟨hsub hf, h'⟩)
      have h1 : (t.powersetCard 3).filter (· ∈ X) = {f} := by
        ext g
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hg, hgX⟩
          by_contra hgf
          exact (mem_sdiff.mp (hothers g hg hgf)).2 hgX
        · rintro rfl
          exact ⟨hf, hfX⟩
      exact hX.2 t ht (by rw [h1]; simp)
    have hW := ((Forcing33.forces_iff_forcesIn K _ _).mp hF).sound hcl
      (fun f hf => mem_sdiff.mpr ⟨hT hf, fun hfX => disjoint_left.mp hdisj hfX hf⟩)
    obtain ⟨x, hx⟩ := hne
    exact (mem_sdiff.mp (hW (hX.1 hx))).2 hx
  · intro h
    rw [Forcing33.forces_iff_forcesIn]
    set A : Finset (Finset V) := K.tris.filter (fun f => ForcesIn K.tets {f} T) with hA
    have hAcl : ClosedUnder K.tets A := by
      intro t ht f hf hothers
      exact mem_filter.mpr ⟨powersetCard_three_subset_tris ht hf,
        ForcesIn.of_forced_others ht hf fun g hg hne => (mem_filter.mp (hothers g hg hne)).2⟩
    have hX : Blocking K (K.tris \ A) := by
      refine ⟨sdiff_subset, fun t ht hc => ?_⟩
      obtain ⟨f, hf⟩ := card_eq_one.mp hc
      have hfm : f ∈ (t.powersetCard 3).filter (· ∈ K.tris \ A) := by rw [hf]; simp
      obtain ⟨hft, hfX⟩ := mem_filter.mp hfm
      refine (mem_sdiff.mp hfX).2 (hAcl t ht f hft fun g hg hgf => ?_)
      by_contra hgA
      have : g ∈ (t.powersetCard 3).filter (· ∈ K.tris \ A) :=
        mem_filter.mpr ⟨hg, mem_sdiff.mpr ⟨powersetCard_three_subset_tris ht hg, hgA⟩⟩
      rw [hf] at this
      exact hgf (mem_singleton.mp this)
    have hempty : K.tris \ A = ∅ := by
      by_contra hne
      obtain ⟨x, hx⟩ := h _ hX (nonempty_iff_ne_empty.mpr hne)
      obtain ⟨hxX, hxT⟩ := mem_inter.mp hx
      exact (mem_sdiff.mp hxX).2 (mem_filter.mpr ⟨hT hxT, .done (by simpa using hxT)⟩)
    have hall : ∀ g ∈ K.tris, g ∈ A := by
      intro g hg
      by_contra hgA
      have : g ∈ K.tris \ A := mem_sdiff.mpr ⟨hg, hgA⟩
      rw [hempty] at this
      simp at this
    exact ForcesIn.of_singles fun g hg => (mem_filter.mp (hall g hg)).2

/-- **Cocycles are blocking.** A set of triangles of `K` with an even number of triangles in every
tetrahedron (a 2-cocycle over the field with two elements) is blocking. -/
theorem blocking_of_even (K : Complex4 V) {X : Finset (Finset V)} (hX : X ⊆ K.tris)
    (heven : ∀ t ∈ K.tets, Even #((t.powersetCard 3).filter (· ∈ X))) : Blocking K X :=
  ⟨hX, fun t ht h1 => by simpa [h1] using heven t ht⟩

/-- **A forcing set meets every nonzero 2-cocycle.** If `T` forces every triangle of `K`, then every
nonempty set of triangles with an even number in each tetrahedron meets `T`. This is the necessary
condition behind the size of forcing sets: the restriction of the 2-cocycles to `T` is injective, so
`T` has at least `dim Z²(K; 𝔽₂)` triangles; only this inequality is proved. Observed
(`scripts/spinfoam/forcing_cocycle_check.py`, not proved): `dim Z² = E − V + 1` on the boundary of
the 5-simplex and on three 4-spheres reached from it by Pachner moves, random minimal forcing sets
have exactly that size, and the converse is false (a minimal set with injective restriction that does
not force, reproduced from a seed in the script). -/
theorem meets_cocycle_of_forces (K : Complex4 V) {T : Finset (Finset V)} (hT : T ⊆ K.tris)
    (hF : Forces K K.tris T) {X : Finset (Finset V)} (hX : X ⊆ K.tris)
    (heven : ∀ t ∈ K.tets, Even #((t.powersetCard 3).filter (· ∈ X))) (hne : X.Nonempty) :
    (X ∩ T).Nonempty :=
  (forces_iff_meets_blocking K hT).mp hF X (blocking_of_even K hX heven) hne

end Lightlike.SpinFoam
