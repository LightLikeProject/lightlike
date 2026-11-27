import Lightlike.SpinFoam.EPRLStateSum.ComplexIntrinsicAmp
import Lightlike.FourD.Tests

/-!
# The EPRL (γ = 1) amplitude on the boundary of the 5-simplex

On the smallest closed 4-complex `sphere6` (the boundary of the 5-simplex on `Fin 6`) the simplices are `univ.erase p`,
the tetrahedra are `univ \ {p, p'}` (`p ≠ p'`), and the two incidences of such a tetrahedron are the simplices
`univ.erase p` and `univ.erase p'` with the positions `a = rank of p'` in `univ.erase p` and `a' = rank of p` in
`univ.erase p'` (`sphere6_positions`: `p.succAbove a = p'`, `p'.succAbove a' = p`). `eprlIntrinsicAmp_sphere6` is
`eprlIntrinsicAmp_eq_signed_ooguri` on `sphere6`.
-/

open Finset Lightlike.FourD Lightlike.FourD.Tests Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

/-- Every 4-simplex of `sphere6` is `univ.erase p`. -/
lemma sphere6_simp_eq (s : sphere6.simps) : ∃ p : Fin 6, s.1 = univ.erase p := by
  have hc : #s.1 = 5 := sphere6.card_eq _ s.2
  have h1 : #(s.1ᶜ) = 1 := by
    rw [Finset.card_compl, hc]; rfl
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
  refine ⟨p, ?_⟩
  ext y
  have := congrArg (y ∈ ·) hp
  simp only [Finset.mem_compl, Finset.mem_singleton, eq_iff_iff] at this
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- The sorted embedding of `univ.erase p` is `p.succAbove`. -/
lemma orderEmbOfFin_erase (p : Fin 6) (h : #(univ.erase p) = 5) (a : Fin 5) :
    (univ.erase p).orderEmbOfFin h a = p.succAbove a :=
  (congrFun (Finset.orderEmbOfFin_unique h (f := p.succAbove)
    (fun x => by simp) (Fin.strictMono_succAbove p)) a).symm

/-- The tetrahedron of the incidence `(univ.erase p, a)` is `(univ.erase p).erase (p.succAbove a)`. -/
lemma incSet_sphere6 (x : sphere6.simps × Fin 5) (p : Fin 6) (hp : x.1.1 = univ.erase p) :
    incSet sphere6 x = (univ.erase p).erase (p.succAbove x.2) := by
  unfold incSet
  have h5 : #(univ.erase p) = 5 := by simp
  have : x.1.1.orderEmbOfFin (sphere6.card_eq _ x.1.2) x.2 = p.succAbove x.2 := by
    have key : ∀ (s : Finset (Fin 6)) (hs : s = univ.erase p) (h : #s = 5),
        s.orderEmbOfFin h x.2 = p.succAbove x.2 := by
      rintro s rfl h
      exact orderEmbOfFin_erase p h x.2
    exact key _ hp _
  rw [this, hp]

/-- Brute-force: two incidences with the same tetrahedron have distinct simplices, and each simplex omits the
vertex that the other one lacks. -/
lemma sphere6_pair_decide : ∀ (p p' : Fin 6) (a a' : Fin 5),
    (univ.erase p).erase (p.succAbove a) = (univ.erase p').erase (p'.succAbove a') →
      (p = p' → a = a') ∧ (p ≠ p' → p.succAbove a = p' ∧ p'.succAbove a' = p) := by
  decide +kernel

/-- **Positions of a tetrahedron of `sphere6`.** For any incidence bijection `e`, the two incidences of a
tetrahedron lie in the simplices `univ.erase p`, `univ.erase p'` with `p ≠ p'`, and their positions satisfy
`p.succAbove a = p'`, `p'.succAbove a' = p`. -/
theorem sphere6_positions (e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5)
    (he : ∀ t b, incTet sphere6 (e (t, b)) = t) (t : sphere6.tets) :
    ∃ p p' : Fin 6, (e (t, false)).1.1 = univ.erase p ∧ (e (t, true)).1.1 = univ.erase p' ∧ p ≠ p' ∧
      p.succAbove (e (t, false)).2 = p' ∧ p'.succAbove (e (t, true)).2 = p := by
  obtain ⟨p, hp⟩ := sphere6_simp_eq (e (t, false)).1
  obtain ⟨p', hp'⟩ := sphere6_simp_eq (e (t, true)).1
  have h1 := congrArg Subtype.val (he t false)
  have h2 := congrArg Subtype.val (he t true)
  have h12 : incSet sphere6 (e (t, false)) = incSet sphere6 (e (t, true)) := h1.trans h2.symm
  rw [incSet_sphere6 _ p hp, incSet_sphere6 _ p' hp'] at h12
  have hd := sphere6_pair_decide p p' _ _ h12
  have hne : p ≠ p' := by
    intro hpp
    have ha := hd.1 hpp
    have : e (t, false) = e (t, true) := by
      refine Prod.ext (Subtype.ext ?_) ha
      rw [hp, hp', hpp]
    have := e.injective this
    simp at this
  exact ⟨p, p', hp, hp', hne, (hd.2 hne).1, (hd.2 hne).2⟩

/-- **Z_EPRL = Z_Ooguri with the link signs on the boundary of the 5-simplex.** For an incidence bijection `e` (it exists), the
intrinsic EPRL (γ = 1) amplitude is the sum over triangle colourings and virtual spins of the triangle constraints
times the sign `linkSign` (a function of the colouring) times the Ooguri weight of the coloured
complex. -/
theorem eprlIntrinsicAmp_sphere6 (cut : Finset (Fin 6) → ℕ) :
    ∃ e : sphere6.tets × Bool ≃ sphere6.simps × Fin 5, (∀ t b, incTet sphere6 (e (t, b)) = t) ∧
      eprlIntrinsicAmp sphere6 cut e =
        ∑ c ∈ sphere6.tris.pi (fun f => range (cut f + 1)),
          ∑ L ∈ Fintype.piFinset (fun t : sphere6.tets =>
              simpBox (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1)
                  (e (t, false)).2 ∩
                simpBox (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, true)).1)
                  (e (t, true)).2),
            (∏ t : sphere6.tets, if
                Lightlike.Pentagon.Tri
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 0))
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 2))
                  (L t) ∧
                Lightlike.Pentagon.Tri (L t)
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 1))
                  (complexJ sphere6 (Lightlike.PR.extS sphere6.tris c) (e (t, false)).1
                    (e (t, false)).2 ((e (t, false)).2.succAbove 3))
              then (1 : ℝ) else 0) *
              (linkSign sphere6 (Lightlike.PR.extS sphere6.tris c) *
                Lightlike.SpinFoam.weight sphere6
                  (extL sphere6 (Lightlike.PR.extS sphere6.tris c) L)) := by
  obtain ⟨e, he⟩ := exists_complex_incidence sphere6 sphere6_checks.2.2
  exact ⟨e, he, eprlIntrinsicAmp_eq_signed_ooguri sphere6 cut e he⟩

end Lightlike.SpinFoam.EPRLStateSum
