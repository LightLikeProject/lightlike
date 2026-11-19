import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Data.Matrix.Basis

/-!
# States on a matrix algebra are density matrices

Jakšić, Ogata, Pautrat and Pillet, arXiv:1106.3786, Section 2.4 "States", p. 42 (read): a state is a density matrix `ρ ≥ 0`,
`tr ρ = 1`, identified with the functional `A ↦ tr(ρ A)`, and the states are exactly the linear functionals that are positive and
normalized. Here: `densityOf φ` with `(densityOf φ) i j = φ (single j i 1)` represents every linear functional (`apply_eq_trace_densityOf`);
for a positive `φ` it is positive semidefinite (`posSemidef_densityOf`), and `tr(ρ ·)` is positive for `ρ ≥ 0` (`trace_mul_nonneg`).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Lightlike.OperatorAlgebras

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The density matrix of a linear functional on `Matrix n n ℂ`: `ρ i j = φ (single j i 1)`. -/
noncomputable def densityOf (φ : Matrix n n ℂ →ₗ[ℂ] ℂ) : Matrix n n ℂ := Matrix.of fun i j => φ (single j i 1)

/-- **Every linear functional is `A ↦ tr(ρ A)`**, with `ρ = densityOf φ`. -/
lemma apply_eq_trace_densityOf (φ : Matrix n n ℂ →ₗ[ℂ] ℂ) (A : Matrix n n ℂ) : φ A = (densityOf φ * A).trace := by
  have h : φ A = ∑ i, ∑ j, A i j * φ (single i j 1) := by
    conv_lhs => rw [matrix_eq_sum_single A]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show single i j (A i j) = A i j • single i j (1 : ℂ) by rw [smul_single, smul_eq_mul, mul_one], map_smul,
      smul_eq_mul]
  rw [h, trace, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [densityOf, mul_comm]

/-- `tr(ρ A) ≥ 0` for positive semidefinite `ρ` and `A`. -/
lemma trace_mul_nonneg {ρ A : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hA : A.PosSemidef) : 0 ≤ (ρ * A).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  exact (hρ.mul_mul_conjTranspose_same B).trace_nonneg

lemma star_single_one (i j : n) : star (single i j (1 : ℂ)) = single j i 1 := by
  ext k l
  rw [star_eq_conjTranspose, conjTranspose_apply, single_apply, single_apply]
  by_cases h1 : i = l <;> by_cases h2 : j = k <;> simp [h1, h2]

lemma dotProduct_mulVec_eq_trace (ρ : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (ρ *ᵥ x) = (ρ * vecMulVec x (star x)).trace := by
  simp only [dotProduct, mulVec, trace, diag_apply, mul_apply, vecMulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [Pi.star_apply]
  ring

/-- **The density matrix of a positive functional is positive semidefinite** (Jakšić-Ogata-Pautrat-Pillet, Section 2.4, p. 42). The
functional is star-preserving (Mathlib's `StarHomClass` instance for positive linear maps), so `densityOf φ` is Hermitian, and
`x* ρ x = φ(x x*) ≥ 0`. -/
theorem posSemidef_densityOf (φ : Matrix n n ℂ →ₚ[ℂ] ℂ) : (densityOf φ.toLinearMap).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    rw [conjTranspose_apply]
    show star (φ (single i j 1)) = φ (single j i 1)
    rw [← map_star φ, star_single_one]
  · rw [dotProduct_mulVec_eq_trace, ← apply_eq_trace_densityOf]
    exact φ.map_nonneg (posSemidef_vecMulVec_self_star x).nonneg

/-- **States are density matrices** (Jakšić-Ogata-Pautrat-Pillet, Section 2.4, p. 42): a positive linear functional `φ` on
`Matrix n n ℂ` with `φ 1 = 1` is `A ↦ tr(ρ A)` for a positive semidefinite `ρ` of trace `1`. -/
theorem exists_density_of_state (φ : Matrix n n ℂ →ₚ[ℂ] ℂ) (h1 : φ 1 = 1) :
    ∃ ρ : Matrix n n ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧ ∀ A, φ A = (ρ * A).trace := by
  refine ⟨densityOf φ.toLinearMap, posSemidef_densityOf φ, ?_, fun A => apply_eq_trace_densityOf _ A⟩
  have := apply_eq_trace_densityOf φ.toLinearMap 1
  rw [Matrix.mul_one] at this
  rw [← this]
  exact h1

/-- Conversely, a density matrix gives a state: `A ↦ tr(ρ A)` is positive and normalized. -/
theorem state_of_density {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    (∀ A : Matrix n n ℂ, A.PosSemidef → 0 ≤ (ρ * A).trace) ∧ (ρ * 1).trace = 1 :=
  ⟨fun _ hA => trace_mul_nonneg hρ hA, by rw [Matrix.mul_one, htr]⟩

/-- The density matrix is unique: `tr(ρ A) = tr(σ A)` for all `A` gives `ρ = σ`. -/
theorem density_unique {ρ σ : Matrix n n ℂ} (h : ∀ A : Matrix n n ℂ, (ρ * A).trace = (σ * A).trace) : ρ = σ := by
  ext i j
  have := h (single j i 1)
  rw [trace_mul_single, trace_mul_single] at this
  simpa using this

end Lightlike.OperatorAlgebras
