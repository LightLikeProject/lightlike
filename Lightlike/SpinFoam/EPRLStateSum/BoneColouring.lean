import Lightlike.SpinFoam.EPRLStateSum.BoneAmplitude

/-!
# The bone colouring of an edge of `∂Δ⁵`

The bone colouring of the edge `{u, w}` of `∂Δ⁵` has doubled spin `1` on the triangles and the tetrahedra containing the edge
(`boneB`) and the virtual spin `boneLf` on the tetrahedra. It is admitted by the triangle constraints at every tetrahedron
(`bone_admitted`), for every edge. For `{0, 1}` it is the cutoff `col0` of `amplitudeI_sphere6_low_spin`.
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum.Trust

/-- The bone colouring of the edge `{u, w}`: doubled spin `1` on the triangles and tetrahedra containing it. -/
def boneB (u w : Fin 6) (f : Finset (Fin 6)) : ℕ := if {u, w} ⊆ f ∧ 3 ≤ #f ∧ #f ≤ 4 then 1 else 0

/-- The virtual spin of the bone colouring on a tetrahedron `f`: `1` if `f` contains the edge and the number of
vertices of `f` strictly between `u` and `w` is not `1` (the two bone legs are then in the channels `(0,1)`, `(0,3)`,
`(1,2)` or `(2,3)` of the sorted legs), and `0` otherwise. -/
def boneLf (u w : Fin 6) (f : Finset (Fin 6)) : ℕ :=
  if {u, w} ⊆ f ∧ #(f.filter fun x => u < x ∧ x < w) ≠ 1 then 1 else 0

/-- The bone colouring of `{0, 1}` is `col0`. -/
lemma boneB_zero_one : boneB 0 1 = col0 := rfl

/-- The legs and the tetrahedron of the first incidence, for given omitted vertices. -/
lemma legs_of_pos (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (t : sphere6.tets) (g : Finset (Fin 6) → ℕ) (p p' : Fin 6) (hs : p.succAbove (e (t, false)).2 = p')
    (h1 : (e (t, false)).1.1 = univ.erase p) (ht' : incSet sphere6 (e (t, false)) = t.1) :
    t.1 = univ \ {p, p'} ∧ ∀ i : Fin 4, complexJ sphere6 g (e (t, false)).1 (e (t, false)).2
        ((e (t, false)).2.succAbove i) = g (univ \ {p, p', p.succAbove ((e (t, false)).2.succAbove i)}) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [incSet_sphere6 _ p h1] at ht'
    rw [← ht', hs]
    ext x; simp only [mem_erase, mem_univ, and_true, mem_sdiff, mem_insert, mem_singleton]; tauto
  · rw [complexJ_sphere6 g _ p h1, hs]

/-- The virtual spins `boneLf` satisfy the triangle constraints at the sorted legs of the bone colouring. -/
lemma bone_tri_ok : ∀ u w : Fin 6, u < w → ∀ (p p' : Fin 6) (a : Fin 5), p ≠ p' → p.succAbove a = p' →
    Lightlike.Pentagon.Tri (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 0)}))
        (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 2)})) (boneLf u w (univ \ {p, p'})) ∧
      Lightlike.Pentagon.Tri (boneLf u w (univ \ {p, p'}))
        (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 1)}))
        (boneB u w (univ \ {p, p', p.succAbove (a.succAbove 3)})) := by
  unfold Lightlike.Pentagon.Tri boneB boneLf; decide +kernel

/-- **The bone colouring of any edge is admitted by the triangle constraints**, so its term occurs in the Ooguri sum. -/
theorem bone_admitted (u w : Fin 6) (huw : u < w) (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (g : Finset (Fin 6) → ℕ)
    (hg : ∀ f, #f = 3 → g f = boneB u w f) (t : sphere6.tets) :
    IndP e g (fun t => boneLf u w t.1) t := by
  obtain ⟨p, p', h1, h2, hne, hs, hs'⟩ := sphere6_positions e he t
  have ht' : incSet sphere6 (e (t, false)) = t.1 := congrArg Subtype.val (he t false)
  obtain ⟨ht, hl⟩ := legs_of_pos e t g p p' hs h1 ht'
  have hcard := fun i => legs_card p p' (e (t, false)).2 i hne hs
  unfold IndP legJ
  rw [hl 0, hl 1, hl 2, hl 3, hg _ (hcard 0), hg _ (hcard 1), hg _ (hcard 2), hg _ (hcard 3)]
  show _ ∧ _
  have := bone_tri_ok u w huw p p' (e (t, false)).2 hne hs
  rw [← ht] at this
  exact this

end Lightlike.SpinFoam.EPRLStateSum.Trust
