import Lightlike.SpinFoam.EPRLStateSum.TwoToOneIncidence
import Lightlike.FourD.Boundary

/-!
# The incidence bijection of a closed 4-complex

For a complex `K` let `X = K.simps × Fin 5` be the pairs (4-simplex `s`, sorted position `a` of an
omitted vertex) and `incTet : X → K.tets` the map `(s, a) ↦ s∖{s_a}`. For a closed complex each
tetrahedron lies in exactly two 4-simplices (`IsClosed4`), so every fibre of `incTet` has two
elements (`card_incFiber`) and `exists_complex_incidence` gives the bijection
`e : K.tets × Bool ≃ K.simps × Fin 5` used by `global_gluing_nodeI`.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The tetrahedron `s∖{s_a}` of a 4-simplex `s` of `K` at the sorted position `a`. -/
def incSet (K : Complex4 V) (x : K.simps × Fin 5) : Finset V :=
  x.1.1.erase (x.1.1.orderEmbOfFin (K.card_eq _ x.1.2) x.2)

lemma incSet_card (K : Complex4 V) (x : K.simps × Fin 5) : #(incSet K x) = 4 := by
  unfold incSet
  rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), K.card_eq _ x.1.2]

/-- `incSet K x` is a tetrahedron of `K`. -/
lemma incSet_mem_tets (K : Complex4 V) (x : K.simps × Fin 5) : incSet K x ∈ K.tets :=
  Complex4.mem_faces.mpr ⟨x.1.1, x.1.2, Finset.erase_subset _ _, incSet_card K x⟩

/-- The tetrahedron of an incidence `(s, a)`, as an element of `K.tets`. -/
def incTet (K : Complex4 V) (x : K.simps × Fin 5) : K.tets := ⟨incSet K x, incSet_mem_tets K x⟩

/-- The fibre of `incTet` over a tetrahedron `t` is in bijection with the 4-simplices containing
`t`: the omitted vertex is the unique vertex of `s ∖ t`. -/
theorem card_incFiber (K : Complex4 V) (t : K.tets) :
    Fintype.card {x : K.simps × Fin 5 // incTet K x = t} = #(K.star t.1) := by
  have key : ∀ x : {x : K.simps × Fin 5 // incTet K x = t}, x.1.1.1 ∈ K.star t.1 := by
    intro x
    have h : incSet K x.1 = t.1 := congrArg Subtype.val x.2
    refine Complex4.mem_star.mpr ⟨x.1.1.2, ?_⟩
    rw [← h]; exact Finset.erase_subset _ _
  rw [← Fintype.card_coe (K.star t.1)]
  refine Fintype.card_of_bijective (f := fun x => ⟨x.1.1.1, key x⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨⟨s, hs⟩, a⟩, ha⟩ ⟨⟨⟨s', hs'⟩, a'⟩, ha'⟩ hxy
    have hss : s = s' := congrArg Subtype.val hxy
    subst hss
    have h1 : incSet K (⟨s, hs⟩, a) = incSet K (⟨s, hs⟩, a') :=
      (congrArg Subtype.val ha).trans (congrArg Subtype.val ha').symm
    have hva : s.orderEmbOfFin (K.card_eq _ hs) a = s.orderEmbOfFin (K.card_eq _ hs) a' := by
      by_contra hne
      have hmem : s.orderEmbOfFin (K.card_eq _ hs) a ∈ incSet K (⟨s, hs⟩, a') :=
        Finset.mem_erase.mpr ⟨hne, Finset.orderEmbOfFin_mem _ _ _⟩
      rw [← h1] at hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
    have := (s.orderEmbOfFin (K.card_eq _ hs)).injective hva
    subst this
    rfl
  · rintro ⟨s, hs⟩
    obtain ⟨hsK, hts⟩ := Complex4.mem_star.mp hs
    have hcs : #s = 5 := K.card_eq s hsK
    have hct : #t.1 = 4 := Complex4.card_of_mem_faces t.2
    have hd : #(s \ t.1) = 1 := by rw [Finset.card_sdiff_of_subset hts, hcs, hct]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hd
    have hxs : x ∈ s := (Finset.mem_sdiff.mp (hx ▸ Finset.mem_singleton_self x)).1
    have hxt : x ∉ t.1 := (Finset.mem_sdiff.mp (hx ▸ Finset.mem_singleton_self x)).2
    have hrange : x ∈ Set.range (s.orderEmbOfFin hcs) := by
      rw [Finset.range_orderEmbOfFin]; exact hxs
    obtain ⟨a, ha⟩ := hrange
    have hteq : s.erase x = t.1 := by
      refine (Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_).symm
      · exact Finset.mem_erase.mpr ⟨fun h => hxt (h ▸ hy), hts hy⟩
      · rw [Finset.card_erase_of_mem hxs, hcs, hct]
    refine ⟨⟨(⟨s, hsK⟩, a), ?_⟩, rfl⟩
    refine Subtype.ext ?_
    show incSet K (⟨s, hsK⟩, a) = t.1
    unfold incSet
    simp only
    rw [show s.orderEmbOfFin (K.card_eq _ hsK) a = x from ha, hteq]

/-- **Incidence bijection of a closed complex**: `e : K.tets × Bool ≃ K.simps × Fin 5` with
`e (t, b) = (s, a)` exactly when `s∖{s_a} = t`. -/
theorem exists_complex_incidence (K : Complex4 V) (hK : K.IsClosed4) :
    ∃ e : K.tets × Bool ≃ K.simps × Fin 5, ∀ t b, incTet K (e (t, b)) = t :=
  exists_incidence_equiv (incTet K) fun t => by
    rw [card_incFiber]; exact hK t.1 t.2

end Lightlike.SpinFoam.EPRLStateSum
