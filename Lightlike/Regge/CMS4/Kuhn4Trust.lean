import Lightlike.Regge.CMS4.Kuhn4Core

/-!
# Trust checks for the algebraic core of the 4D convergence

* flat curvature operator (`K = 0`) gives zero;
* a curvature density without the hinge-area weights fails: for `Eoff 0 1` (scalar curvature `0`)
  the weighted sum is `0` and the unweighted one is `-1 + 1/√3 ≠ 0`.
-/

namespace Lightlike.Regge4

/-- A curvature operator with the single entry `K i i = 1` at one bivector pair. -/
def Ediag (i : Fin 6) : Fin 6 → Fin 6 → ℝ := fun a b => if a = i ∧ b = i then 1 else 0

/-- A curvature operator with the single off-diagonal pair `K i j = 1`. -/
def Eoff (i j : Fin 6) : Fin 6 → Fin 6 → ℝ := fun a b => if a = i ∧ b = j then 1 else 0

/-- Flat triangulations: the zero curvature operator gives zero. -/
theorem kuhn4_sum_flat :
    ∑ h : Fin 10, ∑ σ : Fin 24, wlin h (kds4 (fun _ _ => 0) σ h) = 0 := by
  rw [kuhn4_sum]; simp [scal4]

/-- The hinge sum with the area weights dropped (a curvature density without the volume weights). -/
noncomputable def unweighted (K : Fin 6 → Fin 6 → ℝ) : ℝ :=
  ∑ h : Fin 10, ∑ σ : Fin 24, kuhn4_dih_lin h (kds4 K σ h)

set_option maxHeartbeats 20000000 in
theorem unweighted_Eoff : unweighted (Eoff 0 1) = -1 + (Real.sqrt 3)⁻¹ := by
  simp (config := {maxSteps := 200000000}) only [unweighted, Fin.sum_univ_succ, Fin.sum_univ_zero, kds4,
    Qc4, kpos4, pl, pa, pb, perms4, hP, hQ, hR, kv4, kuhn4_dih_lin, Eoff]
  simp (config := {maxSteps := 200000000})
  ring_nf

/-- Trust check: for the curvature operator `Eoff 0 1` (scalar curvature `0`) the area-weighted sum
is `0`, but the sum without the area weights is not: dropping the volume weights breaks the
convergence. -/
theorem kuhn4_unweighted_fails :
    (∑ h : Fin 10, ∑ σ : Fin 24, wlin h (kds4 (Eoff 0 1) σ h)) = 0 ∧ unweighted (Eoff 0 1) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [kuhn4_sum]; simp [scal4, Eoff]
  · rw [unweighted_Eoff]
    intro h
    have h3 : Real.sqrt 3 = 1 := by
      have hp : 0 < Real.sqrt 3 := by positivity
      field_simp at h
      linarith
    have := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    rw [h3] at this
    norm_num at this

end Lightlike.Regge4
