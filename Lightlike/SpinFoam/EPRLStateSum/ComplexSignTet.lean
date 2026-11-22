import Lightlike.SpinFoam.EPRLStateSum.ComplexSignParity
import Lightlike.SpinFoam.EPRLStateSum.SignDecomp

/-!
# The global sign `Π_s recoupSign` as a triangle sign times tetrahedron-local signs

On a closed complex with incidence bijection `e : K.tets × Bool ≃ K.simps × Fin 5`
(`exists_complex_incidence`), the sign of the glued EPRL(γ = 1) vertex sum against the Ooguri weight is
`Π_s recoupSign (complexJ s) (L at s)`. Using `recoupSign_eq` (`SignDecomp.lean`) it equals

`(-1)^(Σ_s triPart (complexJ K col s)) * Π_t (-1)^(tetExpAt t false + tetExpAt t true)`,

where `tetExpAt t b = tetSignExp (position of t in its b-th simplex) (legs of t, sorted) (L t)`; the legs
of `t` are the same in both incidences (`complex_hleg`), so the tetrahedron-local sign depends on `t`
only through its legs, its virtual spin `L t` and the two positions `(e (t,false)).2, (e (t,true)).2`.
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The exponent `nodeExp` of the incidence `x = (s, a)` of the complex `K` in the colouring
`col` and the label `L`. -/
noncomputable def simpNodeExp (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (x : K.simps × Fin 5) : ℕ :=
  nodeExp (complexJ K col x.1) (fun a => L (incTet K (x.1, a))) x.2

/-- The tetrahedron-local exponent of `t` at its `b`-th incidence, written with the legs of the
`false` incidence (which are those of the `true` incidence by `complex_hleg`). -/
noncomputable def tetExpAt (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets) (b : Bool) : ℕ :=
  tetSignExp (e (t, b)).2
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3)) (L t)

theorem simpNodeExp_e (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t)
    (t : K.tets) (b : Bool) : simpNodeExp K col L (e (t, b)) = tetExpAt K col L e t b := by
  have hL : L (incTet K (e (t, b))) = L t := congrArg L (he t b)
  unfold simpNodeExp tetExpAt nodeExp
  show tetSignExp (e (t, b)).2 _ _ _ _ (L (incTet K (e (t, b)))) = _
  rw [hL]
  cases b
  · rfl
  · show tetSignExp (e (t, true)).2
      (complexJ K col (e (t, true)).1 (e (t, true)).2 ((e (t, true)).2.succAbove 0))
      (complexJ K col (e (t, true)).1 (e (t, true)).2 ((e (t, true)).2.succAbove 1))
      (complexJ K col (e (t, true)).1 (e (t, true)).2 ((e (t, true)).2.succAbove 2))
      (complexJ K col (e (t, true)).1 (e (t, true)).2 ((e (t, true)).2.succAbove 3)) (L t) = _
    rw [← complex_hleg K col e he t 0, ← complex_hleg K col e he t 1,
      ← complex_hleg K col e he t 2, ← complex_hleg K col e he t 3]

/-- **The global sign.** On a closed complex,
`Π_s recoupSign = (-1)^(Σ_s triPart) * Π_t (-1)^(tetExpAt t false + tetExpAt t true)`. -/
theorem prod_recoupSign_eq_tri_mul_tet (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    ∏ s : K.simps, recoupSign (complexJ K col s) (fun a => L (incTet K (s, a))) =
      (-1 : ℝ) ^ (∑ s : K.simps, triPart (complexJ K col s)) *
        ∏ t : K.tets, (-1 : ℝ) ^ (tetExpAt K col L e t false + tetExpAt K col L e t true) := by
  have h1 : ∀ s : K.simps, recoupSign (complexJ K col s) (fun a => L (incTet K (s, a))) =
      (-1 : ℝ) ^ (triPart (complexJ K col s) + ∑ a : Fin 5, simpNodeExp K col L (s, a)) := by
    intro s
    have hsym : ∀ p q, complexJ K col s p q = complexJ K col s q p :=
      fun p q => simplexJ_symm s.1 (K.card_eq _ s.2) col p q
    rw [recoupSign_eq (complexJ K col s) hsym, Fin.sum_univ_five]
    rfl
  simp only [h1]
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_add_distrib, pow_add, Finset.prod_pow_eq_pow_sum]
  congr 2
  have h2 : ∑ s : K.simps, ∑ a : Fin 5, simpNodeExp K col L (s, a) =
      ∑ x : K.simps × Fin 5, simpNodeExp K col L x :=
    (Fintype.sum_prod_type (f := fun x : K.simps × Fin 5 => simpNodeExp K col L x)).symm
  rw [h2, ← Equiv.sum_comp e (fun x => simpNodeExp K col L x), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fintype.sum_bool, simpNodeExp_e K col L e he, simpNodeExp_e K col L e he, add_comm]

end Lightlike.SpinFoam.EPRLStateSum
