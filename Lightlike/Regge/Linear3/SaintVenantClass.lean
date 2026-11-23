import Lightlike.Regge.Conv3.FlatStar
import Lightlike.Regge.Conv3.KuhnCore
import Lightlike.Regge.Conv3.JetCore

/-!
# Class sums of the angle derivative for the zeroth- and first-order interpolated variations

For a symmetric matrix `H`, the interpolated squared-length variation `qf H Δ` of an edge of direction `Δ` and, for symmetric
first derivatives `dh`, the first-order variation `d1q dh s Δ = Σ s_k ∂_k h_ij Δ_i Δ_j` (midpoint offset `s`) have vanishing class
sums of the angle derivative `dth` in every edge class (`class_A0`, `class_A1`): the angle sums stay `2π` for a constant
metric and to first order, so only the second-order term of the interpolated lengths contributes to the linearized Regge action.

## Main results

* `d1q`: the first-order form.
* `class_A0`, `class_A1`: the vanishing class sums.

**Limits.** Identities at one point for symmetric `H` and symmetric first derivatives.
-/

open Real
namespace Lightlike.Regge.Linear3
open Lightlike.Regge.Conv3

/-- The first-derivative form `Σ s_k ∂_k h_ij Δ_i Δ_j` of the interpolated squared length. -/
noncomputable def d1q (dh : Fin 3 → Fin 3 → Fin 3 → ℝ) (s Δ : Fin 3 → ℝ) : ℝ :=
  ∑ k, ∑ i, ∑ j, s k * dh k i j * Δ i * Δ j

theorem class_A0 (H : Fin 3 → Fin 3 → ℝ) (hH : ∀ i j, H i j = H j i) (k : Fin 7) :
    clsSum (dirs k) (fun σ h => dth h (incVec (fun _ Δ => qf H Δ) σ h)) = 0 := by
  fin_cases k <;>
  · simp only [clsSum, InClass, dirs, Fin.sum_univ_six, Fin.forall_fin_succ,
      perms, hP, hQ, kv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    norm_num [Matrix.cons_val_zero]
    simp only [incVec, dth, qf, kpos, perms, hP, hQ, hR, hS, kv, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    norm_num
    simp only [hH 1 0, hH 2 0, hH 2 1]
    ring


-- needs about 0.66 million heartbeats (measured with `#count_heartbeats`); the cap is about twice that
set_option maxHeartbeats 1400000 in
theorem class_A1 (dh : Fin 3 → Fin 3 → Fin 3 → ℝ) (hd : ∀ k i j, dh k i j = dh k j i) (k : Fin 7) :
    clsSum (dirs k) (fun σ h => dth h (incVec (fun s Δ => d1q dh s Δ) σ h)) = 0 := by
  fin_cases k <;>
  · simp only [clsSum, InClass, dirs, Fin.sum_univ_six, Fin.forall_fin_succ,
      perms, hP, hQ, kv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    norm_num [Matrix.cons_val_zero]
    simp only [incVec, dth, d1q, kpos, perms, hP, hQ, hR, hS, kv, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    norm_num
    simp only [hd _ 1 0, hd _ 2 0, hd _ 2 1]
    ring

end Lightlike.Regge.Linear3
