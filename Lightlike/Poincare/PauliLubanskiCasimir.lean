import Lightlike.Poincare.PauliLubanskiRest
import Lightlike.Poincare.PauliLubanskiAlgebra

/-!
# The Casimir of the Pauli–Lubanski combination in a spin representation

For a family `Y^μ` (`μ = 0, …, 3`) of `2 × 2` matrices, the Minkowski square `Σ_μ η_{μμ} dSpin(Y^μ)²` in the spin
representation depends only on the tensor `T_{ijkl} = Σ_μ η_{μμ} Y^μ_{ij} Y^μ_{kl}` (`casimir_eq_of_tensor`), and
conjugating the family by `L` (`Y^μ = L⁻¹ X^μ L`) leaves the Fierz tensor `2 δ_{il} δ_{jk} − δ_{ij} δ_{kl}` fixed
(`tensor_conj_fierz`). By the Fierz identity for the Pauli–Lubanski combination (`plGen_fierz`) the tensor of
`L⁻¹ X^μ_P L` at a momentum `P` with `p² = m²` is the tensor of the rest-frame combination `X^μ_{rest} = (0, m (i/2) σ)`,
so their Casimirs agree (`casimir_plGen_conj`), and the rest-frame value is `m² s(s+1)` (`casimir_plGen_rest`).

Supporting lemmas for the Pauli–Lubanski operator; no catalogue entry.
-/

noncomputable section

open Matrix Lightlike.Lorentz Lightlike.SU2 Complex

namespace Lightlike.Poincare

/-- `dSpin n` as a `ℂ`-linear map. -/
def dSpinL (n : ℕ) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ where
  toFun := dSpin n
  map_add' := dSpin_add
  map_smul' := dSpin_smul

lemma dSpin_zero (n : ℕ) : dSpin n 0 = 0 := (dSpinL n).map_zero

/-- `dSpin` in terms of the matrix units. -/
lemma dSpin_expand (n : ℕ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    dSpin n Y = ∑ i, ∑ j, Y i j • dSpin n (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  change dSpinL n _ = _
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (Y i j) = Y i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact (dSpinL n).map_smul _ _

/-- **The Casimir depends only on the tensor.** -/
theorem casimir_expand (n : ℕ) (w : Fin 4 → ℂ) (Y : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ μ, w μ • (dSpin n (Y μ) * dSpin n (Y μ)) =
      ∑ i, ∑ j, ∑ k, ∑ l, (∑ μ, w μ * (Y μ k l * Y μ i j)) •
        (dSpin n (Matrix.single k l 1) * dSpin n (Matrix.single i j 1)) := by
  simp only [dSpin_expand n (Y _), Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Finset.smul_sum,
    smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_smul]

theorem casimir_eq_of_tensor (n : ℕ) (w : Fin 4 → ℂ) (Y Z : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ i j k l, ∑ μ, w μ * (Y μ i j * Y μ k l) = ∑ μ, w μ * (Z μ i j * Z μ k l)) :
    ∑ μ, w μ • (dSpin n (Y μ) * dSpin n (Y μ)) = ∑ μ, w μ • (dSpin n (Z μ) * dSpin n (Z μ)) := by
  rw [casimir_expand, casimir_expand]
  simp only [h]

/-- The tensor of a conjugated family. -/
lemma tensor_conj (w : Fin 4 → ℂ) (X : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) (N M : Matrix (Fin 2) (Fin 2) ℂ)
    (i j k l : Fin 2) :
    ∑ μ, w μ * ((N * X μ * M) i j * (N * X μ * M) k l) =
      ∑ a, ∑ b, ∑ c, ∑ d, N i a * M b j * N k c * M d l * ∑ μ, w μ * (X μ a b * X μ c d) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four]
  ring

/-- The Fierz tensor `2 δ_{ad} δ_{bc} − δ_{ab} δ_{cd}`. -/
def fierz (a b c d : Fin 2) : ℂ :=
  2 * ((1 : Matrix (Fin 2) (Fin 2) ℂ) a d * (1 : Matrix (Fin 2) (Fin 2) ℂ) b c) -
    (1 : Matrix (Fin 2) (Fin 2) ℂ) a b * (1 : Matrix (Fin 2) (Fin 2) ℂ) c d

/-- **The Fierz tensor is invariant under conjugation.** -/
lemma tensor_conj_fierz (g : ℂ) (N M : Matrix (Fin 2) (Fin 2) ℂ) (hNM : N * M = 1) (i j k l : Fin 2) :
    ∑ a, ∑ b, ∑ c, ∑ d, N i a * M b j * N k c * M d l * (g * fierz a b c d) = g * fierz i j k l := by
  have e : ∀ i j, (N * M) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j => by rw [hNM]
  have key : ∑ a, ∑ b, ∑ c, ∑ d, N i a * M b j * N k c * M d l * (g * fierz a b c d) =
      g * (2 * ((N * M) i l * (N * M) k j) - (N * M) i j * (N * M) k l) := by
    simp only [fierz, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
    ring
  have hs : (1 : Matrix (Fin 2) (Fin 2) ℂ) k j = (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by simp [Matrix.one_apply, eq_comm]
  rw [key, e, e, e, e, fierz, hs]

/-- The rest-frame Pauli–Lubanski combination in the basis of the rotation velocities. -/
lemma plGen_rest_rotVel (m : ℝ) :
    plGen m 0 0 = 0 ∧ plGen m 0 1 = ((m : ℂ) / 2) • rotVel 0 ∧ plGen m 0 2 = (-(m : ℂ) / 2) • rotVel 1 ∧
      plGen m 0 3 = ((m : ℂ) / 2) • rotVel 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [plGen, pauliM, rotVel, matE, matF, matH] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- **The rest-frame Casimir**: `Σ_μ η_{μμ} dSpin(X^μ_{rest})² = m² s(s+1)`. -/
theorem casimir_plGen_rest (m : ℝ) (n : ℕ) :
    ∑ μ, minkW μ • (dSpin n (plGen m 0 μ) * dSpin n (plGen m 0 μ)) =
      ((m : ℂ) ^ 2 * ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1))) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  obtain ⟨e0, e1, e2, e3⟩ := plGen_rest_rotVel m
  have key : ∑ μ, minkW μ • (dSpin n (plGen m 0 μ) * dSpin n (plGen m 0 μ)) =
      ((m : ℂ) ^ 2) • ∑ a, spinOp n a * spinOp n a := by
    have hI2 : Complex.I / 2 * (Complex.I / 2) = -(1 / 4) := by
      rw [div_mul_div_comm, Complex.I_mul_I]; norm_num
    simp only [Fin.sum_univ_four, Fin.sum_univ_three, e0, e1, e2, e3, spinOp, dSpin_smul, dSpin_zero,
      smul_mul_smul_comm, hI2, minkW, Matrix.zero_mul, smul_zero, zero_add]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, smul_add, smul_smul]
    module
  rw [key, sum_spinOp_sq, smul_smul]

/-- **The Casimir of the conjugated Pauli–Lubanski combination** at a momentum with `p² = m²` is the rest-frame
one, `m² s(s+1)`. -/
theorem casimir_plGen_conj (m : ℝ) (n : ℕ) (p0 : ℝ) (p : Fin 3 → ℝ)
    (hp : p0 ^ 2 - p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 = m ^ 2) (N M : Matrix (Fin 2) (Fin 2) ℂ) (hNM : N * M = 1) :
    ∑ μ, minkW μ • (dSpin n (N * plGen p0 p μ * M) * dSpin n (N * plGen p0 p μ * M)) =
      ((m : ℂ) ^ 2 * ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1))) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [← casimir_plGen_rest m n]
  refine casimir_eq_of_tensor n minkW (fun μ => N * plGen p0 p μ * M) (plGen m 0) fun i j k l => ?_
  rw [tensor_conj minkW (plGen p0 p) N M]
  have hL : ∀ a b c d, ∑ μ, minkW μ * (plGen p0 p μ a b * plGen p0 p μ c d) =
      ((m ^ 2 : ℝ) : ℂ) / 4 * fierz a b c d := by
    intro a b c d; rw [plGen_fierz, hp]; rfl
  have hR : ∑ μ, minkW μ * (plGen m 0 μ i j * plGen m 0 μ k l) = ((m ^ 2 : ℝ) : ℂ) / 4 * fierz i j k l := by
    rw [plGen_fierz]; simp [fierz]
  simp only [hL]
  rw [hR]
  exact tensor_conj_fierz _ N M hNM i j k l

end Lightlike.Poincare
