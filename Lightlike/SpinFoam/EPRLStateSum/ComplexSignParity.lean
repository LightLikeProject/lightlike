import Lightlike.SpinFoam.EPRLStateSum.ComplexOoguriShape

/-!
# The virtual-spin parity of the sign `Π_s recoupSign` cancels on a closed complex

`recoupSign J K = (-1)^(K₀+…+K₄) * recoupRest J K`, where `recoupRest J K = (-1)^(J₁₂+J₁₄+J₃₄) * ampSign J K`.
On a closed complex every tetrahedron lies in exactly two 4-simplices (an equivalence
`e : K.tets × Bool ≃ K.simps × Fin 5` with `incTet K (e (t, b)) = t`), so the virtual spin `L t` is counted
twice in `Σ_s Σ_a L (incTet K (s, a))` and `Π_s (-1)^(Σ_a L (incTet K (s,a))) = 1`
(`prod_neg_one_pow_incTet`). Hence `Π_s recoupSign = Π_s recoupRest`
(`prod_recoupSign_eq_prod_recoupRest`): the remaining sign of the EPRL(γ=1) amplitude against the
Ooguri weight does not involve the `(-1)^{l}` factors.
-/

open Finset Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- `recoupSign` without the parity of the virtual spins. -/
def recoupRest (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) : ℝ :=
  (-1) ^ (J 1 2 + J 1 4 + J 3 4) * ampSign J K

theorem recoupSign_eq_mul_rest (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) :
    recoupSign J K = (-1) ^ (K 0 + K 1 + K 2 + K 3 + K 4) * recoupRest J K := by
  unfold recoupSign recoupRest
  rw [pow_add]
  ring

/-- **Each virtual spin is counted twice.** On a closed complex, `Π_s (-1)^(Σ_a L(incTet(s,a))) = 1`. -/
theorem prod_neg_one_pow_incTet (K : Complex4 V) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    ∏ s : K.simps, (-1 : ℝ) ^ (∑ a : Fin 5, L (incTet K (s, a))) = 1 := by
  rw [Finset.prod_pow_eq_pow_sum]
  have h1 : ∑ s : K.simps, ∑ a : Fin 5, L (incTet K (s, a)) =
      ∑ x : K.simps × Fin 5, L (incTet K x) := 
    (Fintype.sum_prod_type (f := fun x : K.simps × Fin 5 => L (incTet K x))).symm
  have h2 : ∑ y : K.tets × Bool, L (incTet K (e y)) = ∑ x : K.simps × Fin 5, L (incTet K x) :=
    Equiv.sum_comp e (fun x => L (incTet K x))
  have h3 : ∑ y : K.tets × Bool, L (incTet K (e y)) = ∑ t : K.tets, 2 * L t := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp [he, two_mul]
  rw [h1, ← h2, h3, ← Finset.mul_sum, pow_mul]
  simp

/-- **The virtual-spin parity cancels**: `Π_s recoupSign = Π_s recoupRest` on a closed complex. -/
theorem prod_recoupSign_eq_prod_recoupRest (K : Complex4 V) (col : Finset V → ℕ) (L : K.tets → ℕ)
    (e : K.tets × Bool ≃ K.simps × Fin 5) (he : ∀ t b, incTet K (e (t, b)) = t) :
    ∏ s : K.simps, recoupSign (complexJ K col s) (fun a => L (incTet K (s, a))) =
      ∏ s : K.simps, recoupRest (complexJ K col s) (fun a => L (incTet K (s, a))) := by
  have h : ∀ s : K.simps, recoupSign (complexJ K col s) (fun a => L (incTet K (s, a))) =
      (-1 : ℝ) ^ (∑ a : Fin 5, L (incTet K (s, a))) *
        recoupRest (complexJ K col s) (fun a => L (incTet K (s, a))) := by
    intro s
    rw [recoupSign_eq_mul_rest, Fin.sum_univ_five]
  simp only [h]
  rw [Finset.prod_mul_distrib, prod_neg_one_pow_incTet K L e he, one_mul]

end Lightlike.SpinFoam.EPRLStateSum
