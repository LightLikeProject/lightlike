import Lightlike.Rows.G2_014.Volume

/-!
# The spin-`1/2` operators in coordinates, and the action of an edge operator on a vector

Fifth piece of row G2-014 (milestone CA4), preparing the explicit four-valent computation.
`spinOp_one_zero`, `spinOp_one_one`, `spinOp_one_two` give the matrices `J_a` of the spin-`1/2`
representation (`n = 1`), and `edgeOp_mulVec_apply` gives the action of `J_e^a` on a vector of the
node Hilbert space as a sum over the `e`-th magnetic number.
-/

open Matrix Lightlike.SU2 Lightlike.Spin4 Lightlike.Poincare

namespace Lightlike.Rows.G2_014

/-- `J_x = -σ_x / 2` on spin `1/2` (in the convention of `spinOp`). -/
lemma spinOp_one_zero :
    spinOp 1 0 = !![0, -1 / 2; -1 / 2, 0] := by
  rw [spinOp_zero_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dSpin_E_apply, dSpin_F_apply, lad]

/-- `J_y = σ_y / 2` on spin `1/2`. -/
lemma spinOp_one_one :
    spinOp 1 1 = !![0, -Complex.I / 2; Complex.I / 2, 0] := by
  rw [spinOp_one_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dSpin_E_apply, dSpin_F_apply, lad]
  all_goals ring

/-- `J_z = -σ_z / 2` on spin `1/2`. -/
lemma spinOp_one_two :
    spinOp 1 2 = !![-1 / 2, 0; 0, 1 / 2] := by
  rw [spinOp_two_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dSpin_H_apply]
  all_goals norm_num

/-- The action of `J_e^a` on a vector of the node Hilbert space. -/
lemma edgeOp_mulVec_apply {K : ℕ} {n : Fin K → ℕ} (e : Fin K) (a : Fin 3) (ψ : Idx n → ℂ)
    (m : Idx n) :
    (edgeOp n e a *ᵥ ψ) m =
      ∑ x : Fin (n e + 1), Lightlike.Poincare.spinOp (n e) a (m e) x * ψ (Function.update m e x) := by
  unfold edgeOp
  rw [mulVec, dotProduct, sum_eq_update e m]
  · simp only [liftOp_apply, Function.update_self]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ite_eq_left]
    intro f hf
    rw [Function.update_of_ne hf]
  · intro m'' hm''
    simp only [liftOp_apply, ite_eq_right hm'', zero_mul]

end Lightlike.Rows.G2_014
