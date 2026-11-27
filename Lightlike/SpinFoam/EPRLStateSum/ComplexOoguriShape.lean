import Lightlike.SpinFoam.EPRLStateSum.ComplexLabelSum
import Lightlike.SpinFoam.Ooguri

/-!
# The vertex weights of the Ooguri model on a coloured complex, in the shape of `vertexF`

`extL K col L` is the colouring of the faces of `K` by the triangle spins `col` and the virtual
spins `L t` of the tetrahedra. `simpW_extL` says that the Ooguri vertex amplitude `simpW (extL K col L) s`
of a 4-simplex `s` is `ampP (complexJ K col s) (fun a => L (incTet K (s, a)))`, the factor of `vertexF`
that does not carry the sign `(-1)^(triPart J)`. `ampP` and `recoupSign` read only the off-diagonal entries of
the matrix of triangle spins (`ampP_congr_offdiag`, `recoupSign_congr_offdiag`).
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- `ampP` reads only the off-diagonal entries of the matrix of triangle spins. -/
theorem ampP_congr_offdiag {J J' : Fin 5 → Fin 5 → ℕ} (h : ∀ p q, p ≠ q → J p q = J' p q)
    (K : Fin 5 → ℕ) : ampP J K = ampP J' K := by
  unfold ampP
  rw [h 0 2 (by decide), h 0 4 (by decide), h 2 4 (by decide), h 1 3 (by decide),
    h 0 1 (by decide), h 1 2 (by decide), h 2 3 (by decide), h 3 4 (by decide),
    h 1 4 (by decide), h 0 3 (by decide)]

/-- `recoupSign` reads only the off-diagonal entries of the matrix of triangle spins. -/
theorem recoupSign_congr_offdiag {J J' : Fin 5 → Fin 5 → ℕ} (h : ∀ p q, p ≠ q → J p q = J' p q)
    (K : Fin 5 → ℕ) : recoupSign J K = recoupSign J' K := by
  unfold recoupSign ampSign
  rw [h 0 2 (by decide), h 0 4 (by decide), h 2 4 (by decide), h 1 3 (by decide),
    h 0 1 (by decide), h 1 2 (by decide), h 2 3 (by decide), h 3 4 (by decide),
    h 1 4 (by decide)]

/-- The colouring of the faces of `K`: the virtual spin `L t` on a tetrahedron `t`, `col f` elsewhere. -/
noncomputable def extL (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ) : Finset V → ℕ :=
  fun f => if h : f ∈ K.tets then L ⟨f, h⟩ else col f

/-- `extL` is the virtual spin on the tetrahedron `s∖{s_a}` of a 4-simplex. -/
theorem extL_incSet (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ) (s : K.simps)
    (a : Fin 5) :
    extL K col L (s.1.erase (s.1.orderEmbOfFin (K.card_eq _ s.2) a)) = L (incTet K (s, a)) := by
  have h : s.1.erase (s.1.orderEmbOfFin (K.card_eq _ s.2) a) ∈ K.tets := incSet_mem_tets K (s, a)
  simp only [extL, h, dite_true]
  rfl

/-- `extL` does not change the colour of a triangle `s∖{s_p, s_q}`, `p ≠ q`. -/
theorem extL_tri (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ) (s : K.simps)
    {p q : Fin 5} (hpq : p ≠ q) :
    extL K col L ((s.1.erase (s.1.orderEmbOfFin (K.card_eq _ s.2) p)).erase
      (s.1.orderEmbOfFin (K.card_eq _ s.2) q)) =
    col ((s.1.erase (s.1.orderEmbOfFin (K.card_eq _ s.2) p)).erase
      (s.1.orderEmbOfFin (K.card_eq _ s.2) q)) := by
  have hne : s.1.orderEmbOfFin (K.card_eq _ s.2) q ≠ s.1.orderEmbOfFin (K.card_eq _ s.2) p :=
    fun h => hpq ((s.1.orderEmbOfFin (K.card_eq _ s.2)).injective h).symm
  have hcard : #((s.1.erase (s.1.orderEmbOfFin (K.card_eq _ s.2) p)).erase
      (s.1.orderEmbOfFin (K.card_eq _ s.2) q)) = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne, Finset.orderEmbOfFin_mem _ _ _⟩),
      Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), K.card_eq _ s.2]
  have hn : ¬ ((s.1.erase (s.1.orderEmbOfFin (K.card_eq _ s.2) p)).erase
      (s.1.orderEmbOfFin (K.card_eq _ s.2) q) ∈ K.tets) := fun h => by
    have := Complex4.card_of_mem_faces h
    omega
  simp only [extL, hn, dite_false]

/-- **The Ooguri vertex amplitude of the colouring `extL`** is `ampP` of the triangle spins of `s` and
the virtual spins of its five tetrahedra. -/
theorem simpW_extL (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ) (s : K.simps) :
    simpW (extL K col L) s.1 =
      ampP (complexJ K col s) (fun a => L (incTet K (s, a))) := by
  unfold simpW
  simp only [K.card_eq _ s.2, dite_true]
  rw [vertexAmp_eq_ampP]
  rw [ampP_congr_offdiag (J' := complexJ K col s)]
  · congr 1
    funext a
    exact extL_incSet K col L s a
  · intro p q hpq
    exact extL_tri K col L s hpq

/-- **The sorted vertex weight is the link sign times the Ooguri vertex amplitude of `extL`.** -/
theorem vertexF_eq_triSign_mul_simpW (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (s : K.simps) :
    vertexF (complexJ K col s) (fun a => L (incTet K (s, a))) =
      (-1) ^ triPart (complexJ K col s) * simpW (extL K col L) s.1 := by
  rw [simpW_extL]
  rfl

/-- **The tetrahedron-label sum of the EPRL weight in Ooguri form**: a sum over one virtual spin per
tetrahedron of `Π_t [triangle constraints] · Π_s (-1)^(triPart J_s) · Π_s simpW (extL K col L) s`, the second
product being the Ooguri vertex factor of the coloured complex `(col, L)` (`weight` without the face
factors). The remaining difference with the Ooguri model is the sign `Π_s (-1)^(triPart J_s)` of the link
orientations, which does not depend on `L`. -/
theorem complex_tetSum_labels_ooguri (K : Complex4 V) (col : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    ∑ i ∈ Fintype.piFinset (fun t : K.tets =>
        range (complexJ K col (e (t, false)).1 (e (t, false)).2
          ((e (t, false)).2.succAbove 0) +
          complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1) + 1)),
      tetSumTerm K col i =
    ∑ L ∈ Fintype.piFinset (fun t : K.tets =>
        simpBox (complexJ K col (e (t, false)).1) (e (t, false)).2 ∩
          simpBox (complexJ K col (e (t, true)).1) (e (t, true)).2),
      (∏ t : K.tets, if
            Lightlike.Pentagon.Tri
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
              (L t) ∧
            Lightlike.Pentagon.Tri (L t)
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
              (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3))
          then (1 : ℝ) else 0) *
        ((∏ s : K.simps, (-1 : ℝ) ^ triPart (complexJ K col s)) *
          ∏ s : K.simps, simpW (extL K col L) s.1) := by
  rw [complex_tetSum_labels K col e he]
  refine Finset.sum_congr rfl fun L _ => ?_
  congr 1
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ => vertexF_eq_triSign_mul_simpW K col L s

end Lightlike.SpinFoam.EPRLStateSum
