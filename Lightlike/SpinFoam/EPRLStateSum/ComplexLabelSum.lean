import Lightlike.SpinFoam.EPRLStateSum.ComplexTetSum

/-!
# The gluing-constrained sum over virtual spins as a sum over tetrahedron labels

`sum_agree_reindex`: for an incidence bijection `e : T × Bool ≃ S × Fin 5`, a sum over the virtual
spins `l : S → Fin 5 → ℕ` of a box with the agreement constraints `l (e (t,false)) = l (e (t,true))`
and a constraint `P t (l (e (t,false)))` is the sum over the labels `L : T → ℕ` in the intersection
of the two boxes of each `t`, with the virtual spin `L (τ (s,a))` at the position `a` of `s`.

`complex_tetSum_labels`: on a complex `K` the sum over the tetrahedron labels of the intrinsic EPRL
weight is a sum over one virtual spin `L t` per tetrahedron `t`, the Ooguri shape: the same `L t` is
the virtual spin of `t` in both 4-simplices containing it.
-/

open Finset Lightlike.FourD

namespace Lightlike.SpinFoam.EPRLStateSum

section Abstract

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

/-- **Agreement-constrained virtual-spin sums are sums over tetrahedron labels.** -/
theorem sum_agree_reindex (e : T × Bool ≃ S × Fin 5) (τ : S × Fin 5 → T)
    (hτ : ∀ t b, τ (e (t, b)) = t) (B : S → Fin 5 → Finset ℕ) (P : T → ℕ → Prop)
    [∀ t n, Decidable (P t n)] (F : (S → Fin 5 → ℕ) → ℝ) :
    ∑ l ∈ Fintype.piFinset (fun s => Fintype.piFinset (B s)),
      (∏ t, if l (e (t, false)).1 (e (t, false)).2 = l (e (t, true)).1 (e (t, true)).2 ∧
          P t (l (e (t, false)).1 (e (t, false)).2) then (1 : ℝ) else 0) * F l =
    ∑ L ∈ Fintype.piFinset (fun t =>
        B (e (t, false)).1 (e (t, false)).2 ∩ B (e (t, true)).1 (e (t, true)).2),
      (∏ t, if P t (L t) then (1 : ℝ) else 0) * F (fun s a => L (τ (s, a))) := by
  classical
  simp only [Fintype.prod_boole, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hτ' : ∀ x, τ x = (e.symm x).1 := fun x => by
    have := hτ (e.symm x).1 (e.symm x).2
    rw [Prod.mk.eta, Equiv.apply_symm_apply] at this
    exact this
  have hleft : ∀ l : S → Fin 5 → ℕ, (∀ t, l (e (t, false)).1 (e (t, false)).2 =
      l (e (t, true)).1 (e (t, true)).2 ∧ P t (l (e (t, false)).1 (e (t, false)).2)) →
      (fun s a => (fun t => l (e (t, false)).1 (e (t, false)).2) (τ (s, a))) = l := by
    intro l hl
    have h1 : ∀ p : T × Bool, l (e (p.1, false)).1 (e (p.1, false)).2 = l (e p).1 (e p).2 := by
      rintro ⟨t, b⟩
      cases b
      · rfl
      · exact (hl t).1
    funext s a
    have h2 := h1 (e.symm (s, a))
    rw [Equiv.apply_symm_apply] at h2
    show l (e (τ (s, a), false)).1 (e (τ (s, a), false)).2 = l s a
    rw [hτ']
    exact h2
  refine Finset.sum_nbij' (fun l t => l (e (t, false)).1 (e (t, false)).2)
    (fun L s a => L (τ (s, a))) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hl ⊢
    obtain ⟨hl1, hl2⟩ := hl
    refine ⟨fun t => Finset.mem_inter.2 ⟨hl1 _ _, ?_⟩, fun t => (hl2 t).2⟩
    rw [(hl2 t).1]
    exact hl1 _ _
  · intro L hL
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hL ⊢
    obtain ⟨hL1, hL2⟩ := hL
    have hp : ∀ p : T × Bool, L p.1 ∈ B (e p).1 (e p).2 := by
      rintro ⟨t, b⟩
      cases b
      · exact (Finset.mem_inter.1 (hL1 t)).1
      · exact (Finset.mem_inter.1 (hL1 t)).2
    refine ⟨fun s a => ?_, fun t => ?_⟩
    · have := hp (e.symm (s, a))
      rw [Equiv.apply_symm_apply] at this
      rw [hτ']
      exact this
    · simp only [hτ]
      exact ⟨trivial, hL2 t⟩
  · intro l hl
    simp only [Finset.mem_filter] at hl
    exact hleft l hl.2
  · intro L _
    funext t
    simp [hτ]
  · intro l hl
    simp only [Finset.mem_filter] at hl
    exact congrArg F (hleft l hl.2).symm

end Abstract

variable {V : Type*} [LinearOrder V]

/-- **The tetrahedron-label sum of the intrinsic EPRL weight, one virtual spin per tetrahedron.**
The labels `L t` range over the intersection of the two boxes of `t` (one for each of the two
4-simplices containing it); the triangle constraints are those of the tetrahedron `t` at
`e (t, false)`, and the vertex weights `vertexF` of the 4-simplex `s` see the labels `L` of its five
tetrahedra. -/
theorem complex_tetSum_labels (K : Complex4 V) (col : Finset V → ℕ)
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
        ∏ s : K.simps, vertexF (complexJ K col s) (fun a => L (incTet K (s, a))) := by
  classical
  rw [complex_tetSum K col e he]
  exact sum_agree_reindex e (incTet K) he (fun s => simpBox (complexJ K col s))
    (fun t n => Lightlike.Pentagon.Tri
      (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
      (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2)) n ∧
      Lightlike.Pentagon.Tri n
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
        (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3)))
    (fun l => ∏ s : K.simps, vertexF (complexJ K col s) (l s))

end Lightlike.SpinFoam.EPRLStateSum
