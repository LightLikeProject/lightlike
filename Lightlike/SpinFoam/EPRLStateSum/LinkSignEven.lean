import Lightlike.SpinFoam.EPRLStateSum.InversionParity

/-!
# The sign of the link orientations is `1` on every closed complex

`linkSign K col = (-1)^(Σ_s triPart J_s)` with `triPart J = J₁₂ + J₁₄ + J₃₄ + J₀₂ + J₀₄ + J₂₄`. When every tetrahedron has an even sum of its four leg colours
(`TetPar`) this exponent is even, on every closed 4-complex and for every order of the vertices. In one simplex, modulo `2`,
`triPart J` is the sum of the leg colours of the tetrahedra omitting the positions `2` and `3` (each is even) plus the sum over the five tetrahedra of the simplex of their legs
`0` and `1`; a tetrahedron of a closed complex lies in two simplices, so the last sum counts every tetrahedron twice.
-/

open Finset Lightlike.FourD Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- **The local identity**: for a symmetric `J`, `triPart J` plus the leg sums of the tetrahedra omitting the positions `2` and `3` plus the legs `0` and `1` of the
five tetrahedra is even. -/
lemma triPart_local (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) :
    Even (triPart J + (∑ k : Fin 4, J 2 ((2 : Fin 5).succAbove k)) + (∑ k : Fin 4, J 3 ((3 : Fin 5).succAbove k)) +
      ∑ a : Fin 5, (J a (a.succAbove 0) + J a (a.succAbove 1))) := by
  simp only [Fin.sum_univ_five, Fin.sum_univ_four, triPart]
  rw [Nat.even_iff]
  have := hJ 0 1; have := hJ 0 2; have := hJ 0 3; have := hJ 0 4; have := hJ 1 2; have := hJ 1 3
  have := hJ 1 4; have := hJ 2 3; have := hJ 2 4; have := hJ 3 4
  simp [Fin.succAbove, Fin.lt_def]
  omega

/-- Every tetrahedron has two incidences: the sum over all nodes of a function of the tetrahedron is twice the sum over the tetrahedra. -/
lemma sum_nodes_even (K : Complex4 V) (hK : K.IsClosed4) (F : K.tets → ℕ) :
    Even (∑ x : K.simps × Fin 5, F (incTet K x)) := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (K.simps × Fin 5)) (incTet K)]
  refine Finset.even_sum _ fun t _ => ?_
  have h : ∀ x ∈ Finset.univ.filter (fun x : K.simps × Fin 5 => incTet K x = t), F (incTet K x) = F t :=
    fun x hx => by rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, show Finset.univ.filter (fun x : K.simps × Fin 5 => incTet K x = t) =
    fiberOf K t from rfl, fiberOf_card K hK t]
  exact ⟨F t, by simp only [smul_eq_mul]; ring⟩

/-- **The exponent of the link sign is even** on a closed complex and a colouring whose tetrahedra have an even leg sum. -/
theorem triPart_total_even (K : Complex4 V) (hK : K.IsClosed4) (col : Finset V → ℕ) (hp : TetPar K col) :
    Even (∑ s : K.simps, triPart (complexJ K col s)) := by
  classical
  have hloc : ∀ s : K.simps, Even (triPart (complexJ K col s) +
      (∑ k : Fin 4, complexJ K col s 2 ((2 : Fin 5).succAbove k)) +
      (∑ k : Fin 4, complexJ K col s 3 ((3 : Fin 5).succAbove k)) +
      ∑ a : Fin 5, (complexJ K col s a (a.succAbove 0) + complexJ K col s a (a.succAbove 1))) :=
    fun s => triPart_local _ (simplexJ_symm s.1 (K.card_eq _ s.2) col)
  have hT : ∀ (s : K.simps) (a : Fin 5), Even (∑ k : Fin 4, complexJ K col s a (a.succAbove k)) := by
    intro s a
    have h := sum_legSpins K col (s, a)
    exact h ▸ hp _ (incTet K (s, a)).2
  have hL : Even (∑ s : K.simps, ∑ a : Fin 5,
      (complexJ K col s a (a.succAbove 0) + complexJ K col s a (a.succAbove 1))) := by
    have h : (∑ s : K.simps, ∑ a : Fin 5,
        (complexJ K col s a (a.succAbove 0) + complexJ K col s a (a.succAbove 1))) =
        ∑ x : K.simps × Fin 5, (tetLeg K col (incTet K x) 0 + tetLeg K col (incTet K x) 1) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
      rw [complexJ_succAbove, complexJ_succAbove]
    rw [h]
    exact sum_nodes_even K hK (fun t => tetLeg K col t 0 + tetLeg K col t 1)
  have hsum : Even (∑ s : K.simps, (triPart (complexJ K col s) +
      (∑ k : Fin 4, complexJ K col s 2 ((2 : Fin 5).succAbove k)) +
      (∑ k : Fin 4, complexJ K col s 3 ((3 : Fin 5).succAbove k)) +
      ∑ a : Fin 5, (complexJ K col s a (a.succAbove 0) + complexJ K col s a (a.succAbove 1)))) :=
    Finset.even_sum _ fun s _ => hloc s
  simp only [Finset.sum_add_distrib] at hsum hL
  have h2 : Even (∑ s : K.simps, ∑ k : Fin 4, complexJ K col s 2 ((2 : Fin 5).succAbove k)) :=
    Finset.even_sum _ fun s _ => hT s 2
  have h3 : Even (∑ s : K.simps, ∑ k : Fin 4, complexJ K col s 3 ((3 : Fin 5).succAbove k)) :=
    Finset.even_sum _ fun s _ => hT s 3
  rw [Nat.even_iff] at hsum h2 h3 hL ⊢
  omega

/-- **The sign of the link orientations is `1`** on every closed complex and every colouring with even tetrahedron sums, for every order of the vertices. -/
theorem linkSign_of_tetPar (K : Complex4 V) (hK : K.IsClosed4) (col : Finset V → ℕ) (hp : TetPar K col) :
    linkSign K col = 1 := by
  unfold linkSign
  exact (triPart_total_even K hK col hp).neg_one_pow

/-- The four leg colours of a tetrahedron sum to the colour sum around it. -/
lemma sum_tetLeg (K : Complex4 V) (col : Finset V → ℕ) (t : K.tets) :
    ∑ v ∈ t.1, col (t.1.erase v) = tetLeg K col t 0 + tetLeg K col t 1 + tetLeg K col t 2 + tetLeg K col t 3 := by
  rw [sum_orderEmb t.1 (Complex4.card_of_mem_faces t.2), Fin.sum_univ_four]
  rfl

/-- **The Ooguri state sum of a closed complex**: the sum over the triangle colourings `col ≤ cut` and the virtual spins `L` of the tetrahedra (in their
boxes) of the triangle constraints times the Ooguri weight `Lightlike.SpinFoam.weight` of the coloured complex `(col, L)`. -/
noncomputable def ooguriSum (K : Complex4 V) (cut : Finset V → ℕ) (e : K.tets × Bool ≃ K.simps × Fin 5) : ℝ :=
  ∑ c ∈ K.tris.pi (fun f => range (cut f + 1)),
    ∑ L ∈ Fintype.piFinset (fun t : K.tets =>
        simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1) (e (t, false)).2 ∩
          simpBox (complexJ K (Lightlike.PR.extS K.tris c) (e (t, true)).1) (e (t, true)).2),
      (∏ t : K.tets, if
          Tri
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 0))
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 2))
            (L t) ∧
          Tri (L t)
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 1))
            (complexJ K (Lightlike.PR.extS K.tris c) (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 3))
        then (1 : ℝ) else 0) *
        Lightlike.SpinFoam.weight K (extL K (Lightlike.PR.extS K.tris c) L)

/-- **At the BF point the EPRL state sum of a closed 4-complex is the Ooguri state sum**, with no sign: the sign `linkSign` of the link orientations is `1`
on every colouring that has non-zero triangle constraints. -/
theorem amplitudeI_one_eq_ooguriSum (K : Complex4 V) (hK : K.IsClosed4) (cut : Finset V → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    amplitudeI 1 K cut = ((ooguriSum K cut e : ℝ) : ℂ) := by
  rw [amplitudeI_one_eq_signed_ooguri K cut e he]
  unfold ooguriSum
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun L _ => ?_
  set col := Lightlike.PR.extS K.tris c with hcol
  by_cases hall : ∀ t : K.tets,
      (Tri (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2)) (L t) ∧
      Tri (L t) (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3)))
  · have hp : TetPar K col := by
      intro g hg
      have h := hall ⟨g, hg⟩
      have e0 := complexJ_succAbove K col (e (⟨g, hg⟩, false)).1 (e (⟨g, hg⟩, false)).2 0
      have e1 := complexJ_succAbove K col (e (⟨g, hg⟩, false)).1 (e (⟨g, hg⟩, false)).2 1
      have e2 := complexJ_succAbove K col (e (⟨g, hg⟩, false)).1 (e (⟨g, hg⟩, false)).2 2
      have e3 := complexJ_succAbove K col (e (⟨g, hg⟩, false)).1 (e (⟨g, hg⟩, false)).2 3
      rw [he] at e0 e1 e2 e3
      rw [e0, e2] at h
      rw [e1, e3] at h
      have h' := sum_tetLeg K col ⟨g, hg⟩
      obtain ⟨⟨_, h0⟩, ⟨_, h1⟩⟩ := (⟨h.1, h.2⟩ : _ ∧ _)
      rw [Nat.even_iff]
      show (∑ v ∈ g, col (g.erase v)) % 2 = 0
      rw [show (∑ v ∈ g, col (g.erase v)) = _ from h']
      have a1 := h.1.1
      have a2 := h.2.1
      omega
    rw [linkSign_of_tetPar K hK col hp, one_mul]
  · simp only [not_forall] at hall
    obtain ⟨t, ht⟩ := hall
    have hz : (∏ t : K.tets, if
          Tri
            (complexJ K col (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 0))
            (complexJ K col (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 2))
            (L t) ∧
          Tri (L t)
            (complexJ K col (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 1))
            (complexJ K col (e (t, false)).1 (e (t, false)).2
              ((e (t, false)).2.succAbove 3))
        then (1 : ℝ) else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ t) (ite_eq_right_iff.2 fun h => absurd h ht)
    rw [hz, zero_mul, zero_mul]

end Lightlike.SpinFoam.EPRLStateSum
