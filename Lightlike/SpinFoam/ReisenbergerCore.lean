import Mathlib

/-!
# The linear-algebra core of Reisenberger's uniqueness argument

Reisenberger (1999), §3 (proof of the Theorem, equations (7)–(16)): on the space `Inv(j)` of
`d` intertwiners of four spins, in the basis `|J⟩` of the pairing `(12)(34)`, the operator `G₁₂²`
is diagonal with the pairwise distinct eigenvalues `J(J+1)`, and the matrix of `G₁₃²` has non-zero
entries `⟨J|[G₁₃², G₁₂²]|J−1⟩` (Lévy-Leblond–Lévy-Nahas) between consecutive `J`. A linear map
`X` of `Inv(j)` that is diagonal in the trivalent tree bases of the pairings `(12)(34)` and
`(13)(24)` commutes with both operators, and is then a scalar.

This file proves that last step, for matrices: `scalar_of_commute_chain`. The non-vanishing of the
entries of `G₁₃²` between consecutive `J` is the input taken from Reisenberger (1999), equation
(13), and is a hypothesis here (`hM`); it is not proved in this library. The theorem of the paper
about the Barrett–Crane intertwiner is therefore not stated or proved by this file.
-/

open Matrix

namespace Lightlike.SpinFoam.BC

/-- **The commutant of a simple diagonal matrix and a chain matrix is the scalars.** If `c` has
pairwise distinct entries, `X` commutes with `diagonal c`, and `X` commutes with `M`, whose entries
`M (k+1) k` are all non-zero, then `X` is a scalar matrix. -/
theorem scalar_of_commute_chain {d : ℕ} (c : Fin d → ℂ) (hc : Function.Injective c)
    (M X : Matrix (Fin d) (Fin d) ℂ) (hX1 : X * diagonal c = diagonal c * X)
    (hX2 : X * M = M * X)
    (hM : ∀ (k : ℕ) (h : k + 1 < d), M ⟨k + 1, h⟩ ⟨k, by omega⟩ ≠ 0) :
    ∃ a : ℂ, X = a • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  -- `X` is diagonal
  have hdiag : ∀ i j : Fin d, i ≠ j → X i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hX1 i) j
    simp only [mul_diagonal, diagonal_mul] at h
    have h2 : X i j * (c j - c i) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (hc (sub_eq_zero.1 h3).symm) hij
  -- consecutive diagonal entries agree
  have hstep : ∀ (k : ℕ) (h : k + 1 < d), X ⟨k + 1, h⟩ ⟨k + 1, h⟩ = X ⟨k, by omega⟩ ⟨k, by omega⟩ := by
    intro k h
    have e := congrFun (congrFun hX2 ⟨k + 1, h⟩) ⟨k, by omega⟩
    simp only [mul_apply] at e
    have hs : ∀ (f : Fin d → ℂ) (i : Fin d), ∑ x, X i x * f x = X i i * f i := by
      intro f i
      rw [Finset.sum_eq_single i]
      · intro b _ hb; rw [hdiag i b (Ne.symm hb), zero_mul]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    have hs2 : ∀ (f : Fin d → ℂ) (i : Fin d), ∑ x, f x * X x i = f i * X i i := by
      intro f i
      rw [Finset.sum_eq_single i]
      · intro b _ hb; rw [hdiag b i hb, mul_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hs (fun x => M x ⟨k, by omega⟩), hs2 (fun x => M ⟨k + 1, h⟩ x)] at e
    have h2 : (X ⟨k + 1, h⟩ ⟨k + 1, h⟩ - X ⟨k, by omega⟩ ⟨k, by omega⟩) *
        M ⟨k + 1, h⟩ ⟨k, by omega⟩ = 0 := by linear_combination e
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 (hM k h)
  -- hence all diagonal entries agree with the first
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hall : ∀ i : Fin d, X i i = X ⟨0, hd⟩ ⟨0, hd⟩ := by
    intro ⟨n, hn⟩
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hstep n hn]
      exact ih (by omega)
  refine ⟨X ⟨0, hd⟩ ⟨0, hd⟩, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij; simp [hall i]
  · simp [hdiag i j hij, one_apply_ne hij]

end Lightlike.SpinFoam.BC
