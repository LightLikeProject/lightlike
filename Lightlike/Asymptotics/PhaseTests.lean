import Lightlike.Asymptotics.Racah

/-!
# Trust checks for the Ponzano–Regge formula: the phase

`PonzanoReggeFormulaWith φ` is `PR.PonzanoReggeFormula` with the phase offset `π/4` replaced by
`φ`; for `φ = π/4` it is the core statement (`ponzanoReggeFormulaWith_quarter`).

* **The statement fixes the phase.** Two offsets `φ, ψ` can both hold only if
  `sin((φ − ψ)/2) = 0` (`sin_half_sub_eq_zero_of_formulaWith`). At the regular tetrahedron the
  Regge action is `6θ λ + 3θ`, with `θ = π − arccos ⅓` (`reggeAction_lengths_one`), and
  `sin 6θ ≠ 0` (`sin_six_extAngle_ne_zero`), so `sin(6θ λ + b)` does not tend to `0`
  (`not_tendsto_sin_mul_add`). The bound is sharp: shifting the offset by `2π` changes nothing
  (`ponzanoReggeFormulaWith_add_two_pi`).
* **Wrong phase fails.** The formula without the phase `π/4` contradicts the true one
  (`not_formulaWith_zero`), so it is false once `RacahSumAsymptotics` holds
  (`not_formulaWith_zero_of_racahSumAsymptotics`). The same holds for the offset `−π/4`.
-/

open Real Filter Topology

namespace Lightlike.Asymptotics

/-- `PR.PonzanoReggeFormula` with the phase offset `π/4` replaced by `φ`. -/
def PonzanoReggeFormulaWith (φ : ℝ) : Prop :=
  ∀ j : Fin 6 → ℕ,
    PR.IsTriad (j 0) (j 1) (j 2) → PR.IsTriad (j 0) (j 4) (j 5) → PR.IsTriad (j 3) (j 1) (j 5) →
    PR.IsTriad (j 3) (j 4) (j 2) →
    0 < PR.vol2 (j 0) (j 1) (j 2) (j 3) (j 4) (j 5) →
    Tendsto (fun lam : ℕ =>
      Real.sqrt (12 * π * Real.sqrt (PR.vol2 (PR.lengths j lam 0) (PR.lengths j lam 1)
          (PR.lengths j lam 2) (PR.lengths j lam 3) (PR.lengths j lam 4) (PR.lengths j lam 5))) *
          PR.sixJScaled j lam -
        Real.cos (PR.reggeAction (PR.lengths j lam) + φ)) atTop (𝓝 0)

/-- With the offset `π/4`, `PonzanoReggeFormulaWith` is the core statement. -/
theorem ponzanoReggeFormulaWith_quarter :
    PonzanoReggeFormulaWith (π / 4) ↔ PR.PonzanoReggeFormula := Iff.rfl

/-- **Positive control**: offsets that differ by `2π` give the same statement. -/
theorem ponzanoReggeFormulaWith_add_two_pi (φ : ℝ) :
    PonzanoReggeFormulaWith (φ + 2 * π) ↔ PonzanoReggeFormulaWith φ := by
  simp only [PonzanoReggeFormulaWith, ← add_assoc, Real.cos_add_two_pi]

/-- If `sin a ≠ 0`, then `sin (a n + b)` does not tend to `0` along the integers: otherwise
`cos (a n + b) = (sin (a (n+1) + b) − sin (a n + b) cos a) / sin a` would tend to `0` as well,
against `sin² + cos² = 1`. -/
lemma not_tendsto_sin_mul_add {a : ℝ} (ha : Real.sin a ≠ 0) (b : ℝ) :
    ¬ Tendsto (fun n : ℕ => Real.sin (a * n + b)) atTop (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun n : ℕ => Real.sin (a * (n + 1 : ℕ) + b)) atTop (𝓝 0) :=
    h.comp (tendsto_add_atTop_nat 1)
  have hc : Tendsto (fun n : ℕ => Real.cos (a * n + b)) atTop (𝓝 0) := by
    have hl := (h1.sub (h.mul_const (Real.cos a))).div_const (Real.sin a)
    rw [show ((0 : ℝ) - 0 * Real.cos a) / Real.sin a = 0 by simp] at hl
    refine hl.congr fun n => ?_
    rw [div_eq_iff ha, show a * ((n + 1 : ℕ) : ℝ) + b = (a * n + b) + a by push_cast; ring,
      Real.sin_add]
    ring
  have hsq := (h.pow 2).add (hc.pow 2)
  simp only [Real.sin_sq_add_cos_sq] at hsq
  rw [show (0 : ℝ) ^ 2 + 0 ^ 2 = 0 by norm_num] at hsq
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds (x := (1 : ℝ))) hsq)

/-- For the exterior dihedral angle `θ = π − arccos ⅓` of the regular tetrahedron,
`sin 6θ = 2 sin θ (3 − 4 sin² θ)(4 cos³ θ − 3 cos θ) = 2 sin θ · (−5/9) · (23/27) ≠ 0`. -/
lemma sin_six_extAngle_ne_zero : Real.sin (6 * (π - Real.arccos (1 / 3))) ≠ 0 := by
  have hcos : Real.cos (π - Real.arccos (1 / 3)) = -1 / 3 := by
    rw [Real.cos_pi_sub, Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
  have hsin : Real.sin (π - Real.arccos (1 / 3)) ≠ 0 := by
    rw [Real.sin_pi_sub, Real.sin_arccos]
    exact Real.sqrt_ne_zero'.mpr (by norm_num)
  have hs2 : Real.sin (π - Real.arccos (1 / 3)) ^ 2 = 8 / 9 := by
    have := Real.sin_sq_add_cos_sq (π - Real.arccos (1 / 3))
    rw [hcos] at this
    linarith
  rw [show 6 * (π - Real.arccos (1 / 3)) = 2 * (3 * (π - Real.arccos (1 / 3))) by ring,
    Real.sin_two_mul, Real.sin_three_mul, Real.cos_three_mul, hcos,
    show 3 * Real.sin (π - Real.arccos (1 / 3)) - 4 * Real.sin (π - Real.arccos (1 / 3)) ^ 3 =
      Real.sin (π - Real.arccos (1 / 3)) * (3 - 4 * Real.sin (π - Real.arccos (1 / 3)) ^ 2) by ring,
    hs2]
  norm_num
  simpa [Real.sin_pi_sub] using hsin

/-- **Known value**: at the regular tetrahedron `j = (1, …, 1)` the lengths are `λ + ½` and the
Regge action is `6(λ + ½)θ = 6θ λ + 3θ`, with `θ = π − arccos ⅓`. -/
theorem reggeAction_lengths_one (lam : ℕ) :
    PR.reggeAction (PR.lengths (fun _ => 1) lam) =
      6 * (π - Real.arccos (1 / 3)) * lam + 3 * (π - Real.arccos (1 / 3)) := by
  have hL : PR.lengths (fun _ => 1) lam = fun _ => (lam : ℝ) + 1 / 2 := by
    funext e; simp [PR.lengths]
  have hc : PR.cosDihedral ((lam : ℝ) + 1 / 2) ((lam : ℝ) + 1 / 2) ((lam : ℝ) + 1 / 2)
      ((lam : ℝ) + 1 / 2) ((lam : ℝ) + 1 / 2) ((lam : ℝ) + 1 / 2) = 1 / 3 :=
    PR.cos_dihedral_regular (by positivity)
  rw [hL]
  simp only [PR.reggeAction, PR.extAngles, PR.dihedral, Fin.sum_univ_six, hc]
  simp
  ring

/-- **The statement fixes the phase**: if the formula holds with offsets `φ` and `ψ`, then
`sin((φ − ψ)/2) = 0`. At the regular tetrahedron the two limits give
`cos(S + φ) − cos(S + ψ) = −2 sin(S + (φ+ψ)/2) sin((φ−ψ)/2) → 0` with `S = 6θ λ + 3θ`. -/
theorem sin_half_sub_eq_zero_of_formulaWith {φ ψ : ℝ} (hφ : PonzanoReggeFormulaWith φ)
    (hψ : PonzanoReggeFormulaWith ψ) : Real.sin ((φ - ψ) / 2) = 0 := by
  by_contra hne
  have hT : PR.IsTriad 1 1 1 := by unfold PR.IsTriad; decide
  have hV : 0 < PR.vol2 (((fun _ : Fin 6 => (1 : ℕ)) 0 : ℕ) : ℝ) ((fun _ : Fin 6 => (1 : ℕ)) 1 : ℕ)
      ((fun _ : Fin 6 => (1 : ℕ)) 2 : ℕ) ((fun _ : Fin 6 => (1 : ℕ)) 3 : ℕ)
      ((fun _ : Fin 6 => (1 : ℕ)) 4 : ℕ) ((fun _ : Fin 6 => (1 : ℕ)) 5 : ℕ) := by
    simp only [Nat.cast_one, PR.vol2_regular]; norm_num
  have hd := ((hψ (fun _ => 1) hT hT hT hT hV).sub (hφ (fun _ => 1) hT hT hT hT hV)).div_const
    (-2 * Real.sin ((φ - ψ) / 2))
  rw [show ((0 : ℝ) - 0) / (-2 * Real.sin ((φ - ψ) / 2)) = 0 by simp] at hd
  refine not_tendsto_sin_mul_add sin_six_extAngle_ne_zero
    (3 * (π - Real.arccos (1 / 3)) + (φ + ψ) / 2) (hd.congr fun n => ?_)
  have hk : Real.cos (6 * (π - Real.arccos (1 / 3)) * n + 3 * (π - Real.arccos (1 / 3)) + φ) -
      Real.cos (6 * (π - Real.arccos (1 / 3)) * n + 3 * (π - Real.arccos (1 / 3)) + ψ) =
      -2 * Real.sin (6 * (π - Real.arccos (1 / 3)) * n +
        (3 * (π - Real.arccos (1 / 3)) + (φ + ψ) / 2)) * Real.sin ((φ - ψ) / 2) := by
    rw [Real.cos_sub_cos]; ring_nf
  rw [div_eq_iff (mul_ne_zero (by norm_num) hne), reggeAction_lengths_one]
  linear_combination hk

/-- **Wrong phase fails**: the formula without the phase `π/4` contradicts the true formula,
since `sin(π/8) ≠ 0`. -/
theorem not_formulaWith_zero (h : PR.PonzanoReggeFormula) : ¬ PonzanoReggeFormulaWith 0 :=
  fun h0 => by
    have h8 := sin_half_sub_eq_zero_of_formulaWith (ponzanoReggeFormulaWith_quarter.2 h) h0
    have : 0 < Real.sin ((π / 4 - 0) / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    linarith

/-- **Wrong sign of the phase fails**: the offset `−π/4` contradicts the true formula, since
`sin(π/4) ≠ 0`. -/
theorem not_formulaWith_neg_quarter (h : PR.PonzanoReggeFormula) :
    ¬ PonzanoReggeFormulaWith (-(π / 4)) := fun h0 => by
  have h8 := sin_half_sub_eq_zero_of_formulaWith (ponzanoReggeFormulaWith_quarter.2 h) h0
  have : 0 < Real.sin ((π / 4 - -(π / 4)) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  linarith

/-- Given the asymptotics of Racah's sum, the formula without the phase `π/4` is false. -/
theorem not_formulaWith_zero_of_racahSumAsymptotics (hS : RacahSumAsymptotics) :
    ¬ PonzanoReggeFormulaWith 0 :=
  not_formulaWith_zero (ponzanoReggeFormula_of_racahSumAsymptotics hS)

end Lightlike.Asymptotics
