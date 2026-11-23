import Lightlike.SpinFoam.EPRLStateSum.ComplexSignPair

/-!
# The global EPRL sign in terms of position sign types

On a closed complex with admissible tetrahedron legs, the global sign
`Π_s recoupSign` is `(-1)^(Σ_s triPart)` times a product over tetrahedra of
`(-1)^(εU_t * e₁(t) + εV_t * e₃(t))`, where `εU_t = sgnU r + sgnU r'`, `εV_t = sgnV r + sgnV r'`
are the sign-type differences of the two positions `r, r'` of the tetrahedron `t`, and
`e₁(t), e₃(t)` are the exponents at the positions `1` and `3` (`tetE1`, `tetE3`).  A tetrahedron whose
two positions have the same sign type contributes `1` (`tetPairSign_of_type`).
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The exponent at position `1` of the tetrahedron `t` (legs of its `false` incidence). -/
noncomputable def tetE1 (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets) : ℕ :=
  tetSignExp 1
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3)) (L t)

/-- The exponent at position `3` of the tetrahedron `t` (legs of its `false` incidence). -/
noncomputable def tetE3 (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets) : ℕ :=
  tetSignExp 3
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2))
    (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3)) (L t)

/-- Admissibility of the legs of the tetrahedron `t` with label `L t`. -/
def TetAdm (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets) : Prop :=
  Even (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0) +
      complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2) + L t) ∧
  Even (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1) +
      complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3) + L t)

/-- **Sign types of the pair of positions.** For an admissible tetrahedron, the total exponent is,
modulo `2`, `(sgnU r + sgnU r') * e₁ + (sgnV r + sgnV r') * e₃`. -/
theorem tetExpAt_add_mod (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets) (h : TetAdm K col L e t) :
    (tetExpAt K col L e t false + tetExpAt K col L e t true) % 2 =
      ((sgnU (e (t, false)).2 + sgnU (e (t, true)).2) * tetE1 K col L e t +
        (sgnV (e (t, false)).2 + sgnV (e (t, true)).2) * tetE3 K col L e t) % 2 := by
  have a1 := tetSignExp_mod (e (t, false)).2 _ _ _ _ (L t) h.1 h.2
  have a2 := tetSignExp_mod (e (t, true)).2 _ _ _ _ (L t) h.1 h.2
  unfold tetExpAt tetE1 tetE3
  rw [add_mul, add_mul]
  omega

/-- **Global sign by sign types.** On a closed complex with admissible tetrahedra,
`Π_s recoupSign = (-1)^(Σ_s triPart) * Π_t (-1)^((εU_t) e₁ + (εV_t) e₃)`. -/
theorem prod_recoupSign_eq_tri_mul_types (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t)
    (hadm : ∀ t, TetAdm K col L e t) :
    ∏ s : K.simps, recoupSign (complexJ K col s) (fun a => L (incTet K (s, a))) =
      (-1 : ℝ) ^ (∑ s : K.simps, triPart (complexJ K col s)) *
        ∏ t : K.tets, (-1 : ℝ) ^ ((sgnU (e (t, false)).2 + sgnU (e (t, true)).2) * tetE1 K col L e t +
          (sgnV (e (t, false)).2 + sgnV (e (t, true)).2) * tetE3 K col L e t) := by
  rw [prod_recoupSign_eq_tri_mul_tet K col L e he]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [neg_one_pow_eq_pow_mod_two, tetExpAt_add_mod K col L e t (hadm t),
    ← neg_one_pow_eq_pow_mod_two]

/-- A tetrahedron whose two positions have the same sign type contributes the sign `1`. -/
theorem tetPairSign_of_type (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets)
    (hU : sgnU (e (t, false)).2 = sgnU (e (t, true)).2)
    (hV : sgnV (e (t, false)).2 = sgnV (e (t, true)).2) :
    (-1 : ℝ) ^ ((sgnU (e (t, false)).2 + sgnU (e (t, true)).2) * tetE1 K col L e t +
          (sgnV (e (t, false)).2 + sgnV (e (t, true)).2) * tetE3 K col L e t) = 1 := by
  rw [← hU, ← hV]
  refine Even.neg_one_pow ⟨sgnU (e (t, false)).2 * tetE1 K col L e t +
    sgnV (e (t, false)).2 * tetE3 K col L e t, by ring⟩

end Lightlike.SpinFoam.EPRLStateSum
