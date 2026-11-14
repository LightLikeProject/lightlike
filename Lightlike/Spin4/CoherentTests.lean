import Lightlike.Spin4.CoherentTwoValent
import Lightlike.Spin4.CoherentSuppression
import Lightlike.Tests.SU2

/-!
# Trust checks for the coherent states and coherent intertwiners (SF5e)

* **Known values.** The spin-1 coherent state of the rotation by `π/2` about the `y`-axis is
  `(1/2, 1/√2, 1/2)`. This is the first column of the textbook Wigner matrix `d¹(π/2)` of
  `Lightlike.SU2.Test.spinMat_two_rotY`, which is computed there independently of the binomial formula.
  The normals of `1`, of the flip `iσ_y` and of that rotation are `e_z`, `-e_z` and `e_x`.
* **Norm of a coherent intertwiner from its normals** (two links of spin `j`): closed normals
  `(e_z, -e_z)` give `1/(2j+1)`, parallel normals `(e_z, e_z)` give `0`, and orthogonal normals
  `(e_z, e_x)` give `2^{-2j}/(2j+1)`. The last is the exponential suppression in `j` of normals that
  do not close (Livine–Speziale 2007; Conrady–Freidel 2009).
* **Suppression at any valence.** The hypothesis of `cohInt_suppressed` holds for four links with
  normals `(e_z, e_z, -e_z, e_x)`, whose closure defect is `(1, 0, 1)`. Dropping the hypothesis
  fails: the closed normals `(e_z, -e_z)` give `1/(2j+1)`, which no `rⁿ` with `r < 1` bounds.
* **Wrong inputs.** The state `|1, 0⟩` is not a coherent state: its overlaps break the
  coherent-state formula `((gᴴh)₀₀)^{2j}`. Without the factor `2j+1` the resolution of the
  identity fails.
-/

open Matrix MeasureTheory

namespace Lightlike.Spin4.Test

open Lightlike.Spin4 SU2 Lightlike.SU2.Test

/-- The flip `iσ_y = [[0, -1], [1, 0]]` in SU(2), turning `e_z` into `-e_z`. -/
noncomputable def flipSU2 : SU2 :=
  ⟨!![0, -1; 1, 0], by
    rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff, star_eq_conjTranspose]
    refine ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
    · simp [det_fin_two_of]⟩

lemma sqrt_two_mul_c2 : ((Real.sqrt 2 : ℝ) : ℂ) * c2 = 1 := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [c2, mul_inv_cancel₀ hs]

/-- **Known value, independent check of the binomial form**: `cohState_apply` at the rotation by
`π/2` gives `(1/2, 1/√2, 1/2)`, the first column of the Wigner matrix `d¹(π/2)` of
`Lightlike.SU2.Test.spinMat_two_rotY`. -/
theorem cohState_two_rotY :
    (fun a : Fin 3 => (Real.sqrt (Nat.choose 2 a) : ℂ) * (rotY : Matrix (Fin 2) (Fin 2) ℂ) 0 0 ^
      (2 - (a : ℕ)) * (rotY : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ^ (a : ℕ)) =
      fun a => spinMat 2 rotY a 0 := by
  have h := c2_mul_self
  have h2 := sqrt_two_mul_c2
  funext a
  rw [spinMat_two_rotY, rotY_coe]
  fin_cases a <;> simp [Nat.choose] <;>
    first
      | linear_combination h
      | linear_combination (c2 : ℂ) * h2

/-! ## Normals -/

/-- The normal of `1` is `e_z`. -/
theorem bloch_one : bloch ((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = ![0, 0, 1] := by
  funext i; fin_cases i <;> simp [bloch]

/-- The normal of the flip is `-e_z`. -/
theorem bloch_flip : bloch (flipSU2 : Matrix (Fin 2) (Fin 2) ℂ) = ![0, 0, -1] := by
  funext i; fin_cases i <;> simp [bloch, flipSU2]

/-- The normal of the rotation by `π/2` about the `y`-axis is `e_x`. -/
theorem bloch_rotY : bloch (rotY : Matrix (Fin 2) (Fin 2) ℂ) = ![1, 0, 0] := by
  have h := c2_mul_self
  have hre : (c2 * c2).re = 1 / 2 := by rw [h]; norm_num
  have him : (c2 * c2).im = 0 := by rw [h]; norm_num
  funext i
  fin_cases i <;> simp [bloch, rotY_coe, star_c2, hre, him, Complex.normSq_apply]

/-! ## Norms of 2-valent coherent intertwiners -/

/-- **Closed normals** `(e_z, -e_z)`: `‖ι‖² = 1/(2j+1)`. -/
theorem two_valent_closed (n : ℕ) :
    star (cohInt (fun _ : Fin 2 => n) ![1, flipSU2]) ⬝ᵥ cohInt (fun _ : Fin 2 => n) ![1, flipSU2] =
      ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  refine cohInt_two_closed ?_
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [bloch_flip, bloch_one]
  funext i; fin_cases i <;> simp

/-- **Parallel normals** `(e_z, e_z)`: `‖ι‖² = 0` for `j > 0`. -/
theorem two_valent_parallel {n : ℕ} (hn : 0 < n) :
    star (cohInt (fun _ : Fin 2 => n) ![1, 1]) ⬝ᵥ cohInt (fun _ : Fin 2 => n) ![1, 1] = 0 :=
  cohInt_two_parallel rfl hn

/-- **Orthogonal normals** `(e_z, e_x)`, which do not close: `‖ι‖² = 2^{-2j}/(2j+1)`. -/
theorem two_valent_orthogonal (n : ℕ) :
    star (cohInt (fun _ : Fin 2 => n) ![1, rotY]) ⬝ᵥ cohInt (fun _ : Fin 2 => n) ![1, rotY] =
      ((((1 : ℝ) / 2) ^ n / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  rw [norm_sq_cohInt_two]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [bloch_one, bloch_rotY]
  simp [dotProduct, Fin.sum_univ_three]

/-- **The suppression**: for `j > 0` the non-closing normals `(e_z, e_x)` give a strictly smaller
norm than the closed normals `(e_z, -e_z)`, by the factor `2^{-2j}`. -/
theorem two_valent_suppressed {n : ℕ} (hn : 0 < n) :
    (((1 : ℝ) / 2) ^ n / ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
  apply div_lt_div_of_pos_right _ (by positivity)
  exact pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'

/-! ## Wrong inputs -/

/-- **Wrong input**: the state `|1, 0⟩ = e₁` of spin 1 is not a coherent state; its overlap
`⟨e₁, D(rotY) e₁⟩ = 0` differs from the coherent-state value `((1ᴴ rotY)₀₀)² = 1/2`. -/
theorem middle_state_not_coherent :
    star (spinMat 2 1 *ᵥ (Pi.single 1 1 : Fin 3 → ℂ)) ⬝ᵥ
        (spinMat 2 rotY *ᵥ (Pi.single 1 1 : Fin 3 → ℂ)) ≠
      ((((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * rotY) 0 0) ^ 2 := by
  have h := c2_mul_self
  rw [spinMat_one, one_mulVec, mulVec_single_one, spinMat_two_rotY]
  simp [dotProduct, rotY_coe, Pi.single_apply, sq, h]

/-- **Wrong normalisation**: without the factor `2j+1`, `∫ |j, g⟩⟨j, g| dg ≠ 1` for `j > 0`. -/
theorem resolution_needs_dimension {n : ℕ} (hn : 0 < n) :
    matInt (fun g : SU2 => vecMulVec (cohState n g) (star (cohState n g))) ≠ 1 := by
  intro h
  have h1 := resolution_cohState n
  rw [h] at h1
  have := congrFun (congrFun h1 0) 0
  simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at this
  have : (n : ℂ) = 0 := by linear_combination this
  exact hn.ne' (by exact_mod_cast this)

/-- **Non-vacuity of the EPRL property**: for `γ = 1/2`, `j = 2`, the EPRL map sends the coherent
state of `rotY` to `|3/2, rotY⟩ ⊗ |1/2, rotY⟩`. -/
theorem eprlMap_cohState_half : eprlMap 3 1 *ᵥ cohState (3 + 1) rotY = cohState4 3 1 (rotY, rotY) :=
  eprlMap_cohState rotY

/-! ## Suppression at any valence -/

/-- **Non-vacuity at four links**: the normals `(e_z, e_z, -e_z, e_x)` do not close, so their
coherent intertwiners with all spins `j` are exponentially suppressed in `j`. -/
theorem four_valent_suppressed :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∑ k, Complex.normSq
      (cohInt (fun a => n * (fun _ : Fin 4 => 1) a) ![1, 1, flipSU2, rotY] k) ≤ r ^ n := by
  refine cohInt_suppressed _ _ fun h => ?_
  have h2 := congrFun h 2
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, bloch_one, bloch_flip,
    bloch_rotY] at h2
  norm_num at h2

/-- **The hypothesis cannot be dropped**: for the closed normals `(e_z, -e_z)` the norm
`1/(2j+1)` is not bounded by `rⁿ` for any `r < 1`. -/
theorem closed_not_suppressed :
    ¬ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n : ℕ, ∑ k, Complex.normSq
      (cohInt (fun a => n * (fun _ : Fin 2 => 1) a) ![1, flipSU2] k) ≤ r ^ n := by
  rintro ⟨r, hr0, hr1, h⟩
  have hval : ∀ n : ℕ, ∑ k, Complex.normSq
      (cohInt (fun a => n * (fun _ : Fin 2 => 1) a) ![1, flipSU2] k) = 1 / ((n : ℝ) + 1) := by
    intro n
    have e := two_valent_closed n
    have hJ : (fun a : Fin 2 => n * (fun _ : Fin 2 => 1) a) = fun _ => n := by funext; simp
    rw [hJ]
    rw [star_dotProduct_self_eq] at e
    exact_mod_cast e
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) * r ^ n + r ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds zero_lt_one)).exists
  have hb := h n
  rw [hval, div_le_iff₀ (by positivity)] at hb
  linarith

end Lightlike.Spin4.Test
