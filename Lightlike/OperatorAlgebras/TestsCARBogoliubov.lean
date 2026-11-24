import Lightlike.OperatorAlgebras.CARBogoliubov

/-!
# Tests for the fermionic Bogoliubov transformations

* the particle-hole transformation `α = 0`, `β = 1` swaps `a` and `c`;
* one mode: the conditions force `αβ = 0` (so only phases and the particle-hole swap), unlike the bosonic `|α|² − |β|² = 1`;
* two modes: `α = cos θ`, `β = sin θ · [[0, 1], [-1, 0]]` is a genuine mixing, it satisfies the conditions, and so the
  Jordan-Wigner representation of two modes has a unitary implementing it.
-/

open Matrix

namespace Lightlike.OperatorAlgebras

section

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {a c : Fin n → A}

/-- The particle-hole transformation exchanges annihilation and creation operators. -/
example (i : Fin n) : bogAnn (0 : Matrix (Fin n) (Fin n) ℂ) 1 a c i = c i := by
  simp [bogAnn, Matrix.one_apply]

/-- The identity transformation. -/
example (i : Fin n) : bogAnn (1 : Matrix (Fin n) (Fin n) ℂ) 0 a c i = a i := by
  simp [bogAnn, Matrix.one_apply]

end

/-- One mode: the conditions `|α|² + |β|² = 1`, `2αβ = 0` force `α = 0` or `β = 0`. -/
theorem one_mode_trivial (α β : Matrix (Fin 1) (Fin 1) ℂ) (_h1 : α * αᴴ + β * βᴴ = 1) (h2 : α * βᵀ + β * αᵀ = 0) :
    α 0 0 = 0 ∨ β 0 0 = 0 := by
  have := congrFun (congrFun h2 0) 0
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.univ_unique, Finset.sum_singleton,
    Matrix.zero_apply] at this
  have h3 : α 0 0 * β 0 0 = 0 := by linear_combination this / 2
  exact mul_eq_zero.mp h3

/-- The two-mode mixing matrices `α = c · 1`. -/
def mixAlpha (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(c : ℂ), 0; 0, (c : ℂ)]

/-- The antisymmetric part of the two-mode mixing, `β = s · [[0, 1], [-1, 0]]`. -/
def mixBeta (s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, (s : ℂ); -(s : ℂ), 0]

theorem mix_cond1 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    mixAlpha c * (mixAlpha c)ᴴ + mixBeta s * (mixBeta s)ᴴ = 1 := by
  have h : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
  simp [mixAlpha, mixBeta, sq] at h ⊢ <;>
  linear_combination h

theorem mix_cond2 (c s : ℝ) : mixAlpha c * (mixBeta s)ᵀ + mixBeta s * (mixAlpha c)ᵀ = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;>
  simp [mixAlpha, mixBeta] <;> ring

/-- **A genuine two-mode Bogoliubov transformation of the Fock (Jordan-Wigner) representation is implemented by a
unitary.** -/
theorem mix_implementable (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ U : EuclideanSpace ℂ (Fin 2 → Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 → Fin 2),
      ∀ k v, U (Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 k) v) =
        bogFam (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner 2 a)) (mixAlpha c) (mixBeta s) k (U v) := by
  have : Nontrivial (EuclideanSpace ℂ (Fin 2 → Fin 2)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_euclideanSpace]; exact Fintype.card_pos)
  exact bogoliubov_implementable (isCAROn_jordanWigner 2) (isIrreducibleCAR_jordanWigner 2) _ _ (mix_cond1 c s hcs)
    (mix_cond2 c s)

end Lightlike.OperatorAlgebras
