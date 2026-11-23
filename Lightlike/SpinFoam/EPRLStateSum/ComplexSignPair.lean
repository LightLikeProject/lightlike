import Lightlike.SpinFoam.EPRLStateSum.ComplexSignTet
import Lightlike.SpinFoam.EPRLStateSum.SignedVertex

/-!
# The tetrahedron-local sign of a glued tetrahedron: position types

`tetSignExp r t₀ t₁ t₂ t₃ l` depends on the position `r` of the tetrahedron in its simplex only through
its *sign type* `(sgnU r, sgnV r)`: on admissible legs

`tetSignExp r ≡ sgnU r * e₁ + sgnV r * e₃  (mod 2)`,   `e₁ = tetSignExp 1`, `e₃ = tetSignExp 3`,

with `(sgnU, sgnV) = (0,0), (1,0), (1,1), (0,1), (0,0)` at `r = 0, 1, 2, 3, 4`.  Hence a tetrahedron
glued between two positions of the same sign type (in particular the same position, or both of `{0, 4}`)
contributes no sign to `prod_recoupSign_eq_tri_mul_tet`; the remaining pairs of positions
(e.g. `(0, 1)`) contribute `(-1)^(e₁)` or `(-1)^(e₃)` or `(-1)^(e₁+e₃)`, which depends on the
virtual spin `l` (`tetSignExp_position_dependent`).
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- First coordinate of the sign type of a position: `1` at the positions `1, 2`. -/
def sgnU (r : Fin 5) : ℕ := if r = 1 ∨ r = 2 then 1 else 0

/-- Second coordinate of the sign type of a position: `1` at the positions `2, 3`. -/
def sgnV (r : Fin 5) : ℕ := if r = 3 ∨ r = 2 then 1 else 0

/-- **Sign type of a position.** On admissible legs, the exponent at the position `r` is, modulo `2`,
`sgnU r * e₁ + sgnV r * e₃`. -/
theorem tetSignExp_mod (r : Fin 5) (t₀ t₁ t₂ t₃ l : ℕ) (h₁ : Even (t₀ + t₂ + l))
    (h₂ : Even (t₁ + t₃ + l)) :
    tetSignExp r t₀ t₁ t₂ t₃ l % 2 =
      (sgnU r * tetSignExp 1 t₀ t₁ t₂ t₃ l + sgnV r * tetSignExp 3 t₀ t₁ t₂ t₃ l) % 2 := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  fin_cases r <;> simp [sgnU, sgnV, tetSignExp]
  all_goals omega

/-- A tetrahedron glued between two positions of the same sign type contributes an even total
exponent. -/
theorem tetSignExp_add_even (r r' : Fin 5) (hU : sgnU r = sgnU r') (hV : sgnV r = sgnV r')
    (t₀ t₁ t₂ t₃ l : ℕ) (h₁ : Even (t₀ + t₂ + l)) (h₂ : Even (t₁ + t₃ + l)) :
    Even (tetSignExp r t₀ t₁ t₂ t₃ l + tetSignExp r' t₀ t₁ t₂ t₃ l) := by
  have a1 := tetSignExp_mod r t₀ t₁ t₂ t₃ l h₁ h₂
  have a2 := tetSignExp_mod r' t₀ t₁ t₂ t₃ l h₁ h₂
  rw [hU, hV] at a1
  rw [Nat.even_iff]
  omega

/-- The positions `0` and `4` have the trivial sign type. -/
theorem sgnType_zero_four (r : Fin 5) (h : r = 0 ∨ r = 4) : sgnU r = 0 ∧ sgnV r = 0 := by
  rcases h with rfl | rfl <;> simp [sgnU, sgnV]

/-- Two positions of the same sign type: the total sign on admissible legs is `1`. -/
theorem tetSgn_mul_of_type (r r' : Fin 5) (hU : sgnU r = sgnU r') (hV : sgnV r = sgnV r')
    (t₀ t₁ t₂ t₃ l : ℕ) (h₁ : Even (t₀ + t₂ + l)) (h₂ : Even (t₁ + t₃ + l)) :
    tetSgn r t₀ t₁ t₂ t₃ l * tetSgn r' t₀ t₁ t₂ t₃ l = 1 := by
  unfold tetSgn
  rw [← pow_add]
  exact (tetSignExp_add_even r r' hU hV t₀ t₁ t₂ t₃ l h₁ h₂).neg_one_pow

/-- A tetrahedron at the same position of both of its simplices has even total exponent
(no admissibility needed). -/
theorem tetExpAt_even_of_pos_eq (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets)
    (h : (e (t, true)).2 = (e (t, false)).2) :
    Even (tetExpAt K col L e t false + tetExpAt K col L e t true) := by
  unfold tetExpAt
  rw [h]
  exact ⟨_, rfl⟩

/-- A tetrahedron whose two positions both lie in `{0, 4}` has total exponent `0`. -/
theorem tetExpAt_add_eq_zero_of_zero_four (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets)
    (h0 : (e (t, false)).2 = 0 ∨ (e (t, false)).2 = 4)
    (h1 : (e (t, true)).2 = 0 ∨ (e (t, true)).2 = 4) :
    tetExpAt K col L e t false + tetExpAt K col L e t true = 0 := by
  unfold tetExpAt
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp only [h0, h1, tetSignExp_zero, tetSignExp_four]

/-- A tetrahedron whose two positions have the same sign type has an even total exponent, provided
its legs are admissible (the legs of the `false` incidence). -/
theorem tetExpAt_even_of_type (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (t : K.tets)
    (hU : sgnU (e (t, false)).2 = sgnU (e (t, true)).2)
    (hV : sgnV (e (t, false)).2 = sgnV (e (t, true)).2)
    (h₁ : Even (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 0) +
      complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 2) + L t))
    (h₂ : Even (complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 1) +
      complexJ K col (e (t, false)).1 (e (t, false)).2 ((e (t, false)).2.succAbove 3) + L t)) :
    Even (tetExpAt K col L e t false + tetExpAt K col L e t true) := by
  unfold tetExpAt
  exact tetSignExp_add_even _ _ hU hV _ _ _ _ _ h₁ h₂

end Lightlike.SpinFoam.EPRLStateSum
