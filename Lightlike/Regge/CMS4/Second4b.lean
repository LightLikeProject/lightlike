import Lightlike.Regge.CMS4.Second4

/-!
# Only the curvature part of the metric 2-jet remains (dimension 4)

`angC24` differs from the gauge coefficient `angC2t` by the linear term `D(incAng4) (incR4 - Rt)`.
By `second_gauge4` the class sum of `angC2t` vanishes, so the class sum of `angC24` is the class sum
of the linearisation of the dihedral angle along the matrix `incR4 - Rt`.

## Main results

* `clsSum4_add`: `clsSum4` is additive.
* `angC24_eq`: `angC24 = angC2t + D(incAng4) (incR4 - Rt)`.
* `clsSum_angC24`: `clsSum4 c angC24 = clsSum4 c (D(incAng4) (incR4 - Rt))`.
-/

open Lightlike Real
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3 Lightlike.Geodesic

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

open Classical in
/-- `clsSum4` is additive in the summand. -/
theorem clsSum4_add (c : Fin 4 → Fin 3) (f f' : Fin 24 → Fin 10 → ℝ) :
    clsSum4 c (fun σ h => f σ h + f' σ h) = clsSum4 c f + clsSum4 c f' := by
  unfold clsSum4
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> simp

/-- The second-order coefficient is the gauge coefficient plus the linearisation along
`incR4 - Rt`. -/
theorem angC24_eq (m : Fin 4 → ℝ) (σ : Fin 24) (h : Fin 10) :
    angC24 g m σ h = angC2t g m σ h
      + fderiv ℝ (incAng4 h) (incQ4 g m σ h) (incR4 g m σ h - Rt g m σ h) := by
  unfold angC24 angC2t
  rw [map_sub]
  ring

/-- **Reduction to the curvature part of the 2-jet.** In every admissible class the class sum of
`angC24` is the class sum of the linearisation of the dihedral angle along `incR4 - Rt`. -/
theorem clsSum_angC24 {m : Fin 4 → ℝ} (hG : (g m).PosDef) (hs : ∀ y, (g y)ᵀ = g y)
    (c : Fin 4 → Fin 3) (hc : ClsOK c) :
    clsSum4 c (angC24 g m)
      = clsSum4 c (fun σ h => fderiv ℝ (incAng4 h) (incQ4 g m σ h) (incR4 g m σ h - Rt g m σ h)) := by
  have e : angC24 g m = fun σ h => angC2t g m σ h
      + fderiv ℝ (incAng4 h) (incQ4 g m σ h) (incR4 g m σ h - Rt g m σ h) :=
    funext fun σ => funext fun h => angC24_eq g m σ h
  rw [e, clsSum4_add, second_gauge4 g hG hs c hc, zero_add]

end Lightlike.Regge4
