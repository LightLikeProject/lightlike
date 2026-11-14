import Lightlike.Asymptotics.Contour
import Lightlike.Asymptotics.Tests

/-!
# Trust checks for the continued phase

For the regular tetrahedron with unit edges the face sums are `Aᵢ = 3` and the quadrilateral
sums `Bₖ = 4`.

* **Known values.** The boundary value `Im ψ(u)` of the continued phase on the real axis is
  `12π` at `u = 0`, `7π/2` at `u = 7/2` (the interval `[A_max, B_min]`, where it equals `πu`) and
  `2π` at `u = 5`, matching `π(ΣB − 2u)` from the behaviour at infinity.
* **Wrong model fails.** The naive boundary value `πu`, correct on `[A_max, B_min]`, is wrong at
  `u = 0` (`bdry_regular_ne_naive`): the continued phase is not the real-axis formula.
* **Non-vacuity.** The strict monotonicity lemma applies to the regular tetrahedron
  (`bdry_regular_strictAnti`), the lower bound for `|ψ'|` applies at `z = i`
  (`norm_dphaseC_regular_I`), and the continued phase is critical at the regular saddle
  (`dphaseC_saddle_regular`).
* **At infinity.** The bound `|ψ(z) + 2πiz − πiΣB| ≤ 2(ΣA² + ΣB²)/|z|` applies to the regular
  tetrahedron at `z = 10i` (`norm_phaseC_regular_ten_I`). Its balance hypothesis `ΣA = ΣB` is
  needed: for `A = (1, 0, 0, 0)`, `B = 0` the bound fails at `z = 8i`, where the left side is
  at least `log 8 + 6/7` (`phaseC_unbalanced_not_le`).
-/

open Complex
open scoped Real

namespace Lightlike.Asymptotics

lemma faceSum_regular : faceSum (fun _ => 1) = fun _ => 3 := by
  funext i; fin_cases i <;> simp <;> norm_num

lemma quadSum_regular : quadSum (fun _ => 1) = fun _ => 4 := by
  funext k; fin_cases k <;> simp [quadSum] <;> norm_num

/-- **Known value**: `Im ψ(0) = 12π` for the regular unit tetrahedron. -/
theorem bdry_regular_zero : bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) 0 = 12 * π := by
  rw [faceSum_regular, quadSum_regular]
  simp only [bdry, Fin.sum_univ_four, Fin.sum_univ_three]; norm_num; ring

/-- **Known value**: `Im ψ(7/2) = 7π/2` for the regular unit tetrahedron (the middle interval). -/
theorem bdry_regular_mid :
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (7 / 2) = π * (7 / 2) := by
  rw [faceSum_regular, quadSum_regular]
  simp only [bdry, Fin.sum_univ_four, Fin.sum_univ_three]; norm_num [min_def]

/-- **Known value**: `Im ψ(5) = 2π = π(ΣB − 2·5)` for the regular unit tetrahedron. -/
theorem bdry_regular_five : bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) 5 = 2 * π := by
  rw [faceSum_regular, quadSum_regular]
  simp only [bdry, Fin.sum_univ_four, Fin.sum_univ_three]; norm_num [min_def]; ring

/-- **Wrong model fails**: the naive boundary value `πu` is wrong at `u = 0`. -/
theorem bdry_regular_ne_naive :
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) 0 ≠ π * 0 := by
  rw [bdry_regular_zero, mul_zero]; positivity

/-- **Non-vacuity** of `bdry_strictAnti_left`: `Im ψ(1) < Im ψ(0)` for the regular tetrahedron. -/
theorem bdry_regular_strictAnti :
    bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) 1 <
      bdry (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) 0 := by
  have hA : ∀ i, 0 < faceSum (fun _ => 1) i := by rw [faceSum_regular]; norm_num
  have hAB : ∀ i k, faceSum (fun _ => 1) i < quadSum (fun _ => 1) k := by
    rw [faceSum_regular, quadSum_regular]; norm_num
  refine bdry_strictAnti_left (i₀ := 0) hA hAB one_pos (by rw [faceSum_regular]; norm_num) ?_
  rw [faceSum_regular, quadSum_regular]
  simp only [bdry, Fin.sum_univ_four, Fin.sum_univ_three]; norm_num [min_def]
  nlinarith [Real.pi_pos]

/-- **Non-vacuity** of `IsEuclid.norm_dphaseC_ge`, at the regular tetrahedron and `z = i`. -/
theorem norm_dphaseC_regular_I :
    min 1 (qa (fun _ => 1) * ‖I - saddle (fun _ => 1)‖ * (saddle (fun _ => 1)).im /
        (2 * ‖∏ i, (I - faceSum (fun _ => 1) i)‖)) ≤
      ‖dphaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) I‖ :=
  isEuclid_regular.norm_dphaseC_ge (by simp)

/-- **Consistency**: the continued phase is critical at the regular saddle `11/3 + i√2/6`. -/
theorem dphaseC_saddle_regular :
    dphaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) ⟨11 / 3, √2 / 6⟩ = 0 := by
  rw [← saddle_regular]; exact isEuclid_regular.dphaseC_saddle

/-- **Non-vacuity** of `norm_phaseC_add_le`, at the regular tetrahedron and `z = 10i`. -/
theorem norm_phaseC_regular_ten_I :
    ‖phaseC (faceSum (fun _ => 1)) (quadSum (fun _ => 1)) (10 * I) + 2 * π * I * (10 * I) -
        π * I * ∑ k, (quadSum (fun _ => 1) k : ℂ)‖ ≤
      2 * (∑ i, faceSum (fun _ => 1) i ^ 2 + ∑ k, quadSum (fun _ => 1) k ^ 2) / ‖10 * I‖ := by
  have hn : ‖(10 : ℂ) * I‖ = 10 := by simp
  refine norm_phaseC_add_le (sum_faceSum_eq_sum_quadSum _) (by simp) (fun i => ?_) (fun k => ?_)
  · rw [hn, faceSum_regular]; norm_num
  · rw [hn, quadSum_regular]; norm_num

/-- **Wrong input fails**: without the balance `ΣA = ΣB` the bound at infinity is false. For
`A = (1, 0, 0, 0)`, `B = 0` and `z = 8i` the left side exceeds the right side `1/4`. -/
theorem phaseC_unbalanced_not_le :
    ¬ ‖phaseC ![1, 0, 0, 0] 0 (8 * I) + 2 * π * I * (8 * I) -
        π * I * ∑ k, ((0 : Fin 3 → ℝ) k : ℂ)‖ ≤
      2 * (∑ i, (![1, 0, 0, 0] : Fin 4 → ℝ) i ^ 2 + ∑ k, (0 : Fin 3 → ℝ) k ^ 2) / ‖8 * I‖ := by
  set z : ℂ := 8 * I with hzdef
  have hn : ‖z‖ = 8 := by simp [hzdef]
  have hz : 0 < z.im := by simp [hzdef]
  set E : ℂ := xlog (z - (1 : ℝ)) - xlog z + (1 : ℝ) * (log z + 1) with hE
  have hEn : ‖E‖ ≤ 1 / 7 := by
    refine (norm_xlog_sub_le hz (c := 1) (by rw [hn]; norm_num)).trans ?_
    rw [hn]; norm_num
  have key : phaseC ![1, 0, 0, 0] 0 z + 2 * π * I * z - π * I * ∑ k, ((0 : Fin 3 → ℝ) k : ℂ) =
      (log z + 1) - E := by
    simp only [hE, phaseC, Fin.sum_univ_four, Fin.sum_univ_three]
    simp
    ring
  have hre : Real.log 8 + 1 ≤ ‖log z + 1‖ := by
    refine le_trans (le_of_eq ?_) (re_le_norm _)
    rw [add_re, log_re, hn, one_re]
  have hlog : 0 < Real.log 8 := Real.log_pos (by norm_num)
  rw [key, hn]
  intro h
  have h2 := norm_sub_norm_le (log z + 1) E
  simp only [Fin.sum_univ_four, Fin.sum_univ_three] at h
  norm_num at h
  linarith

end Lightlike.Asymptotics
