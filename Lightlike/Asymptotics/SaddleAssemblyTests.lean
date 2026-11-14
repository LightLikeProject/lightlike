import Lightlike.Asymptotics.SaddleAssembly
import Lightlike.Asymptotics.Tests
import Lightlike.Asymptotics.PhaseTests

/-!
# Trust checks for the asymptotics of Racah's sum

* **Known value.** At the regular tetrahedron `j = (1, …, 1)` the lengths are `λ + ½` and the
  Regge action is `6θ λ + 3θ` with `θ = π − arccos ⅓`, so `racahSumAsymptotics` gives the explicit
  limit `V^{1/4} e^{−λ c} R(λ, …, λ) − cos(6θ λ + 3θ + π/4)/(√(12π) (2π)²) → 0`
  (`racahSumAsymptotics_regular`).
* **Wrong input fails.** With the theorem proved, the formula with the phase `0` or `−π/4` in
  place of `π/4` is false (`not_ponzanoReggeFormulaWith_zero`,
  `not_ponzanoReggeFormulaWith_neg_quarter`).
* **Non-vacuity.** The hypotheses of the Ponzano–Regge formula hold at the regular tetrahedron
  (four triangular faces, `V² > 0`), so `ponzanoReggeFormula` gives the limit there
  (`ponzanoReggeFormula_regular`). The kernel region is non-empty: `q = 0` lies in it
  (`kernelRegion_one_zero`).
* **Junk values.** Lean's `2/0 = 0` puts `q = 4` into `kernelRegion (1, …, 1) 0`
  (`kernelRegion_zero_four`), while for `λ = 1` the point `4` lies between the face sums `3` and
  the shifted quadrilateral sums `4 + 2`, outside the region (`not_kernelRegion_one_four`). The
  kernel bound and the outer estimate are therefore only used for `λ ≠ 0`.
-/

open Complex Set Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-- **Known value**: Racah's sum at the regular tetrahedron `j = (1, …, 1)`, with the Regge action
`6θ λ + 3θ`, `θ = π − arccos ⅓`, written out. -/
theorem racahSumAsymptotics_regular :
    Tendsto (fun lam : ℕ =>
      √(√(vol2l (PR.lengths (fun _ => 1) lam))) *
          Real.exp (-prefactorRate (PR.lengths (fun _ => 1) lam)) * racahSum (fun _ => lam) -
        Real.cos (6 * (π - Real.arccos (1 / 3)) * lam + 3 * (π - Real.arccos (1 / 3)) + π / 4) /
          (√(12 * π) * (2 * π) ^ 2)) atTop (𝓝 0) := by
  have hE : IsEuclid (toReal fun _ => 1) := by unfold toReal; simpa using isEuclid_regular
  exact (racahSumAsymptotics (fun _ => 1) hE).congr fun lam => by
    simp only [reggeAction_lengths_one, mul_one]

/-- **Wrong input fails**: the Ponzano–Regge formula without the phase `π/4` is false. -/
theorem not_ponzanoReggeFormulaWith_zero : ¬ PonzanoReggeFormulaWith 0 :=
  not_formulaWith_zero ponzanoReggeFormula

/-- **Wrong input fails**: the Ponzano–Regge formula with the phase `−π/4` is false. -/
theorem not_ponzanoReggeFormulaWith_neg_quarter : ¬ PonzanoReggeFormulaWith (-(π / 4)) :=
  not_formulaWith_neg_quarter ponzanoReggeFormula

/-- **Non-vacuity**: the hypotheses of the Ponzano–Regge formula hold at the regular tetrahedron
`j = (1, …, 1)`, which gives the limit
`√(12π √V²(ℓ)) {λ, …, λ} − cos(6θ λ + 3θ + π/4) → 0`, `θ = π − arccos ⅓`. -/
theorem ponzanoReggeFormula_regular :
    Tendsto (fun lam : ℕ =>
      Real.sqrt (12 * π * Real.sqrt (PR.vol2 (PR.lengths (fun _ => 1) lam 0)
          (PR.lengths (fun _ => 1) lam 1) (PR.lengths (fun _ => 1) lam 2)
          (PR.lengths (fun _ => 1) lam 3) (PR.lengths (fun _ => 1) lam 4)
          (PR.lengths (fun _ => 1) lam 5))) * PR.sixJScaled (fun _ => 1) lam -
        Real.cos (6 * (π - Real.arccos (1 / 3)) * lam + 3 * (π - Real.arccos (1 / 3)) + π / 4))
      atTop (𝓝 0) := by
  have hT : PR.IsTriad 1 1 1 := by unfold PR.IsTriad; decide
  have hV : 0 < PR.vol2 (((fun _ : Fin 6 => (1 : ℕ)) 0 : ℕ) : ℝ) ((fun _ : Fin 6 => (1 : ℕ)) 1 : ℕ)
      ((fun _ : Fin 6 => (1 : ℕ)) 2 : ℕ) ((fun _ : Fin 6 => (1 : ℕ)) 3 : ℕ)
      ((fun _ : Fin 6 => (1 : ℕ)) 4 : ℕ) ((fun _ : Fin 6 => (1 : ℕ)) 5 : ℕ) := by
    simp only [Nat.cast_one, PR.vol2_regular]; norm_num
  exact (ponzanoReggeFormulaWith_quarter.2 ponzanoReggeFormula (fun _ => 1) hT hT hT hT
    hV).congr fun lam => by simp only [reggeAction_lengths_one]

/-- **Non-vacuity**: `q = 0` lies in the kernel region of `j = (1, …, 1)`, `λ = 1`. -/
theorem kernelRegion_one_zero : kernelRegion (fun _ => 1) 1 0 :=
  Or.inl ⟨le_rfl, 0, Nat.cast_nonneg _⟩

/-- The face sums of `j = (1, …, 1)` are `3`. -/
lemma faceN_ones (i : Fin 4) : faceN (fun _ => 1) i = 3 := by fin_cases i <;> rfl

/-- The quadrilateral sums of `j = (1, …, 1)` are `4`. -/
lemma quadN_ones (k : Fin 3) : quadN (fun _ => 1) k = 4 := by fin_cases k <;> rfl

/-- **Junk value**: for `λ = 0`, Lean's `2/0 = 0` puts `q = 4` into the kernel region. -/
theorem kernelRegion_zero_four : kernelRegion (fun _ => 1) 0 4 :=
  Or.inr ⟨0, by rw [quadN_ones]; norm_num⟩

/-- **Junk value**: for `λ = 1` the point `q = 4` is not in the kernel region, since `4 > 3` and
`4 < 4 + 2`. -/
theorem not_kernelRegion_one_four : ¬ kernelRegion (fun _ => 1) 1 4 := by
  rintro (⟨-, i, hi⟩ | ⟨k, hk⟩)
  · rw [faceN_ones] at hi; norm_num at hi
  · rw [quadN_ones] at hk; norm_num at hk

end Lightlike.Asymptotics
