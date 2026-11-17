import Lightlike.Asymptotics.Lorentzian.ActionSmooth

/-!
# A Cayley chart of `SL(2,ℂ)` near the identity

For `c ∈ ℂ³` let `M = ½ Σ c_i σ_i` (`chartGen c`, traceless, `M² = (c·c)/4`). The Cayley transform
`(1 + M/2)(1 - M/2)⁻¹` has determinant one because `tr M = 0`; for traceless `M` it is the explicit
rational function `((1 + s) 1 + M)/(1 - s)` with `s = c·c/16` (`cayleyMat`), defined where `s ≠ 1`.
It is a chart of `SL(2,ℂ)` near `1` with `cayley 0 = 1` and derivative `M` at `0`, the tangent map
used by BDFHP Appendix A (`X ↦ X exp(M)`), without the matrix exponential (Mathlib has no
`det exp = exp tr`). The entries are smooth on the open set `s ≠ 1`.

## Main results

* `cayley`: the chart `ℂ³ → SL(2,ℂ)` (the identity where `s = 1`).
* `cayley_zero`, `hasDerivAt_cayleyMat_zero`: value `1` and derivative `chartGen c` at `0`.
* `contDiffOn_cayleyMat`: the entries are smooth where `s ≠ 1`.
-/

open Complex
open scoped ComplexConjugate ContDiff Matrix
open Lightlike.Lorentz (SL2C)

namespace Lightlike.Asymptotics.Lorentzian

/-- The matrix `½ Σ c_i σ_i` of `sl(2,ℂ)` with complex coefficients `c`. -/
noncomputable def chartGen (c : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![c 2 / 2, (c 0 - Complex.I * c 1) / 2; (c 0 + Complex.I * c 1) / 2, -(c 2) / 2]

/-- `s = (c·c)/16`. -/
noncomputable def cayleyS (c : Fin 3 → ℂ) : ℂ := (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) / 16

/-- The Cayley transform of `chartGen c` as an explicit matrix: `((1 + s) 1 + M)/(1 - s)`. -/
noncomputable def cayleyMat (c : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 - cayleyS c)⁻¹ • ((1 + cayleyS c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + chartGen c)

/-- `det ((1 + s) 1 + M) = (1 - s)²` for the traceless `M = chartGen c`. -/
theorem det_cayley_num (c : Fin 3 → ℂ) :
    ((1 + cayleyS c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + chartGen c).det = (1 - cayleyS c) ^ 2 := by
  simp only [cayleyS, chartGen, Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  simp
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Where `s ≠ 1`, `cayleyMat c` has determinant one. -/
theorem det_cayleyMat {c : Fin 3 → ℂ} (h : cayleyS c ≠ 1) : (cayleyMat c).det = 1 := by
  have h1 : (1 - cayleyS c) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  unfold cayleyMat
  rw [Matrix.det_smul, det_cayley_num]
  simp only [Fintype.card_fin]
  field_simp

/-- **The Cayley chart** `ℂ³ → SL(2,ℂ)`: `cayleyMat c` where `s ≠ 1`, the identity elsewhere. -/
noncomputable def cayley (c : Fin 3 → ℂ) : SL2C :=
  if h : cayleyS c ≠ 1 then ⟨cayleyMat c, det_cayleyMat h⟩ else 1

/-- On the open set `s ≠ 1` the chart is `cayleyMat`. -/
theorem coe_cayley {c : Fin 3 → ℂ} (h : cayleyS c ≠ 1) :
    (cayley c : Matrix (Fin 2) (Fin 2) ℂ) = cayleyMat c := by
  simp [cayley, h]

theorem chartGen_zero : chartGen 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [chartGen]

/-- The chart sends `0` to the identity. -/
theorem cayley_zero : cayley 0 = 1 := by
  have h : cayleyS 0 ≠ 1 := by simp [cayleyS]
  apply Subtype.ext
  rw [coe_cayley h]
  simp [cayleyMat, cayleyS, chartGen_zero]

/-- The set `s ≠ 1` is open. -/
theorem isOpen_cayley_domain : IsOpen {c : Fin 3 → ℂ | cayleyS c ≠ 1} := by
  have : Continuous cayleyS := by unfold cayleyS; fun_prop
  exact isOpen_ne_fun this continuous_const

/-- The entries of `cayleyMat` are smooth on the open set `s ≠ 1`. -/
theorem contDiffOn_cayleyMat (i k : Fin 2) :
    ContDiffOn ℝ ∞ (fun c : Fin 3 → ℂ => cayleyMat c i k) {c | cayleyS c ≠ 1} := by
  have hs : ContDiff ℝ ∞ cayleyS := by unfold cayleyS; fun_prop
  have hinv : ContDiffOn ℝ ∞ (fun c : Fin 3 → ℂ => (1 - cayleyS c)⁻¹) {c | cayleyS c ≠ 1} := by
    refine ContDiffOn.inv (contDiff_const.sub hs).contDiffOn fun c hc => ?_
    exact sub_ne_zero.mpr (Ne.symm hc)
  have hg : ContDiff ℝ ∞ (fun c : Fin 3 → ℂ => ((1 + cayleyS c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      chartGen c) i k) := by
    fin_cases i <;> fin_cases k <;> simp [chartGen, Matrix.one_apply] <;> (try unfold cayleyS) <;> fun_prop
  have : (fun c : Fin 3 → ℂ => cayleyMat c i k) = fun c => (1 - cayleyS c)⁻¹ *
      ((1 + cayleyS c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + chartGen c) i k := by
    funext c; simp [cayleyMat]
  rw [this]
  exact hinv.mul hg.contDiffOn

/-- **The derivative of the chart at `0`**: along the line `t ↦ t c` the entries of `cayleyMat` have
derivative the entries of `chartGen c`. -/
theorem hasDerivAt_cayleyMat_zero (c : Fin 3 → ℂ) (i k : Fin 2) :
    HasDerivAt (fun t : ℝ => cayleyMat (fun m => (t : ℂ) * c m) i k) (chartGen c i k) 0 := by
  set S : ℂ := cayleyS c with hS
  set G : ℂ := chartGen c i k with hG
  have hfun : (fun t : ℝ => cayleyMat (fun m => (t : ℂ) * c m) i k) = fun t : ℝ =>
      (1 - (t : ℂ) ^ 2 * S)⁻¹ * (((1 + (t : ℂ) ^ 2 * S) * (1 : Matrix (Fin 2) (Fin 2) ℂ) i k) +
        (t : ℂ) * G) := by
    funext t
    have h1 : cayleyS (fun m => (t : ℂ) * c m) = (t : ℂ) ^ 2 * S := by
      simp only [cayleyS, hS]; ring
    have h2 : chartGen (fun m => (t : ℂ) * c m) i k = (t : ℂ) * G := by
      fin_cases i <;> fin_cases k <;> simp [chartGen, hG] <;> ring
    simp only [cayleyMat, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, h1, h2]
  rw [hfun]
  have hS2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * S) 0 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).pow 2).mul_const S
    simpa using this
  have hu := ((hasDerivAt_const (0 : ℝ) (1 : ℂ)).sub hS2).inv (by simp)
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have hv := (((hasDerivAt_const (0 : ℝ) (1 : ℂ)).add hS2).mul_const
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) i k)).add (ht.mul_const G)
  have := hu.mul hv
  refine this.congr_deriv ?_
  simp [hG]

end Lightlike.Asymptotics.Lorentzian
