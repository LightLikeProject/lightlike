import Lightlike.SpinFoam.TetrahedronSixJ
import Lightlike.Tests.SixJ

/-!
# Trust checks for the tetrahedron amplitude

`tetraInt_eq_sixJ_sq` identifies the integral over `SU(2)^4` of the six characters of a
tetrahedron with the square of a 6j symbol. The checks below compare it with known values and
with a deliberately wrong input.

| check | value | theorem |
|---|---|---|
| all six doubled spins `0` | `1` | `tetraInt_zero` |
| all six doubled spins `2` (spin 1) | `(1/6)² = 1/36` | `tetraInt_two` |
| a vertex `(1,1,1)` that is not a triad | `0` | `tetraInt_eq_zero_of_not_tri`, `tetraInt_ones_vertex` |

The value `{1 1 1; 1 1 1} = 1/6` is evaluated from Physlib's definition (the method of
`Lightlike/Tests/SixJ.lean`), independently of the proof of the identity.
-/

open PhyslibAlpha.Sl2 Finset Lightlike.Pentagon

namespace Lightlike.SpinFoam.Tests

/-- Evaluate a 6j symbol with small spins from Physlib's definition. -/
local macro "sixj_value" : tactic => `(tactic| (
  rw [Lightlike.SixJAudit.sixJSym_eq_triple]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Lightlike.SixJAudit.mTuple]
  norm_num (config := { maxSteps := 10000000 }) [sixJTerm, threeJ, Adm3, threeJR, reggeJ,
    Lightlike.SixJAudit.sixSum_eq_sum, Lightlike.SixJAudit.sum_Icc_int, sixTerm, invFact,
    Finset.sum_range_succ, Fin.prod_univ_three, Nat.factorial]
  ring_nf
  try simp only [Lightlike.SixJAudit.sqrt_four, sqrt_nine]
  surd_finish))

/-- `{1 1 1; 1 1 1} = 1/6` (doubled `2 2 2 2 2 2`). -/
lemma sixJ_all_two : sixJSym 2 2 2 2 2 2 = 1 / 6 := by sixj_value

/-- The tetrahedron with all edges of spin 0 has amplitude `1`. -/
theorem tetraInt_zero : tetraInt (fun _ => 0) = 1 := by
  rw [tetraInt_eq_sixJ_sq]
  have : sixJSym 0 0 0 0 0 0 = 1 := Lightlike.SixJAudit.sixJ_000000
  simp only [this]; norm_num

/-- The tetrahedron with all edges of spin 1 has amplitude `(1/6)² = 1/36`. -/
theorem tetraInt_two : tetraInt (fun _ => 2) = 1 / 36 := by
  rw [tetraInt_eq_sixJ_sq]
  have : sixJSym 2 2 2 2 2 2 = 1 / 6 := sixJ_all_two
  simp only [this]; norm_num

/-- **Wrong-model control**: if the three edges at vertex `0` do not form a triad, the amplitude
vanishes. -/
theorem tetraInt_eq_zero_of_not_tri (s : Fin 6 → ℕ) (h : ¬ Tri (s 0) (s 1) (s 2)) :
    tetraInt s = 0 := by
  have h0 : uV (fun k => s (ev0 k)) = 0 := (avgP_three_rank_one _).choose_spec.2.2 h
  rw [tetraInt_eq]
  have : Zt s = 0 := by
    unfold Zt
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [h0]
  simp [this]

/-- Spins `(1, 1, 1)` at a vertex are not a triad (odd perimeter), so the amplitude vanishes,
whatever the other three spins are. -/
theorem tetraInt_ones_vertex (s3 s4 s5 : ℕ) :
    tetraInt ![1, 1, 1, s3, s4, s5] = 0 :=
  tetraInt_eq_zero_of_not_tri _ (by simp [Tri])

end Lightlike.SpinFoam.Tests
