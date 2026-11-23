import Lightlike.Recoupling.FifteenJ
import Lightlike.Recoupling.Intertwiner

/-!
# The 4-simplex contraction is linear in each vertex intertwiner

Preparation for the relation of the EPRL state sum at `γ = 1` to the Ooguri model: at `γ = 1` the
EPRL vertex is `fifteenJSimplex` in the `(01)(23)` channel at every tetrahedron, the Ooguri vertex
is the same contraction in the `(02)(13)` channel, and the two differ by the orthogonal
recoupling matrix `fourRecoupling` at each tetrahedron. This file proves the first ingredient for
the vertex `0` of `K₅`: `fifteenJSimplex` is the contraction `simplexContr` of the intertwiner
tensor at vertex `0`, which is linear in that tensor (`simplexContr_sum`), and so
`fifteenJSimplex_recouple₀` expands the virtual spin `i₀` in the other channel.
-/

open Finset Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

open Lightlike.Recoupling

/-- The part of the 4-simplex contraction that does not depend on the tensor at the vertex `0`:
the sum over the six projections `m₁₂, …, m₃₄` of the other four intertwiners, at fixed
`m₀₁, …, m₀₄`. -/
noncomputable def simplexRest
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ : ℕ) (m₀₁ m₀₂ m₀₃ m₀₄ : ℤ) : ℝ :=
  ∑ m₁₂ ∈ Icc (-(j₁₂ : ℤ)) j₁₂, ∑ m₁₃ ∈ Icc (-(j₁₃ : ℤ)) j₁₃,
  ∑ m₁₄ ∈ Icc (-(j₁₄ : ℤ)) j₁₄, ∑ m₂₃ ∈ Icc (-(j₂₃ : ℤ)) j₂₃, ∑ m₂₄ ∈ Icc (-(j₂₄ : ℤ)) j₂₄,
  ∑ m₃₄ ∈ Icc (-(j₃₄ : ℤ)) j₃₄,
    edgeSign j₁₂ m₁₂ * edgeSign j₁₃ m₁₃ * edgeSign j₁₄ m₁₄ * edgeSign j₂₃ m₂₃ *
      edgeSign j₂₄ m₂₄ * edgeSign j₃₄ m₃₄ *
    (fourJ j₁₂ j₁₃ j₁₄ j₀₁ i₁ m₁₂ m₁₃ m₁₄ (-m₀₁) *
      fourJ j₂₃ j₂₄ j₀₂ j₁₂ i₂ m₂₃ m₂₄ (-m₀₂) (-m₁₂) *
      fourJ j₃₄ j₀₃ j₁₃ j₂₃ i₃ m₃₄ (-m₀₃) (-m₁₃) (-m₂₃) *
      fourJ j₀₄ j₁₄ j₂₄ j₃₄ i₄ (-m₀₄) (-m₁₄) (-m₂₄) (-m₃₄))

/-- The contraction of the 4-simplex `fifteenJSimplex` with the intertwiner tensor at the vertex
`0` replaced by an arbitrary `T₀` of the four projections `m₀₁, m₀₂, m₀₃, m₀₄`. -/
noncomputable def simplexContr (T₀ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ : ℕ) : ℝ :=
  ∑ m₀₁ ∈ Icc (-(j₀₁ : ℤ)) j₀₁, ∑ m₀₂ ∈ Icc (-(j₀₂ : ℤ)) j₀₂, ∑ m₀₃ ∈ Icc (-(j₀₃ : ℤ)) j₀₃,
  ∑ m₀₄ ∈ Icc (-(j₀₄ : ℤ)) j₀₄,
    edgeSign j₀₁ m₀₁ * edgeSign j₀₂ m₀₂ * edgeSign j₀₃ m₀₃ * edgeSign j₀₄ m₀₄ *
      T₀ m₀₁ m₀₂ m₀₃ m₀₄ *
      simplexRest j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ m₀₁ m₀₂ m₀₃ m₀₄

/-- `fifteenJSimplex` is `simplexContr` of the tensor `fourJ … i₀` at the vertex `0`. -/
theorem fifteenJSimplex_eq_simplexContr
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ : ℕ) :
    fifteenJSimplex j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ =
      simplexContr (fun a b c d => fourJ j₀₁ j₀₂ j₀₃ j₀₄ i₀ a b c d)
        j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ := by
  unfold fifteenJSimplex simplexContr
  refine sum_congr rfl fun m₀₁ _ => sum_congr rfl fun m₀₂ _ => sum_congr rfl fun m₀₃ _ =>
    sum_congr rfl fun m₀₄ _ => ?_
  unfold simplexRest
  rw [mul_assoc, Finset.mul_sum]
  simp only [Finset.mul_sum]
  refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
  ring

/-- Four nested sums commute with an outer-indexed sum `Σ_l`. -/
theorem sum4_comm (A B C D : Finset ℤ) (S : Finset ℕ) (f : ℤ → ℤ → ℤ → ℤ → ℕ → ℝ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, ∑ l ∈ S, f a b c d l =
      ∑ l ∈ S, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d l := by
  calc _ = ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ l ∈ S, ∑ d ∈ D, f a b c d l :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ a ∈ A, ∑ b ∈ B, ∑ l ∈ S, ∑ c ∈ C, ∑ d ∈ D, f a b c d l :=
        sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_comm
    _ = ∑ a ∈ A, ∑ l ∈ S, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d l :=
        sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_comm

/-- **Linearity** of `simplexContr` in the tensor at the vertex `0`. -/
theorem simplexContr_sum (S : Finset ℕ) (c : ℕ → ℝ) (U : ℕ → ℤ → ℤ → ℤ → ℤ → ℝ)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ : ℕ) :
    simplexContr (fun a b d e => ∑ l ∈ S, c l * U l a b d e)
        j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ =
      ∑ l ∈ S, c l * simplexContr (U l)
        j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ := by
  unfold simplexContr
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Eq.trans (sum4_comm _ _ _ _ _ _) ?_
  refine sum_congr rfl fun l _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ =>
    sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => ?_
  ring

/-- **Recoupling at the vertex `0`**: the 4-simplex contraction with virtual spin `i₀` on the pair
`(01)` is the combination, with the coefficients `fourRecoupling`, of the contractions whose vertex
`0` intertwiner has the pair `(01)` replaced by `(02)` (`fourJ j₀₁ j₀₃ j₀₂ j₀₄ l`, with the
projections `m₀₂, m₀₃` exchanged). -/
theorem fifteenJSimplex_recouple₀
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ : ℕ) :
    fifteenJSimplex j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ =
      ∑ l ∈ range (j₀₁ + j₀₃ + 1), fourRecoupling j₀₁ j₀₂ j₀₃ j₀₄ i₀ l *
        simplexContr (fun a b c d => fourJ j₀₁ j₀₃ j₀₂ j₀₄ l a c b d)
          j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₁ i₂ i₃ i₄ := by
  rw [fifteenJSimplex_eq_simplexContr, ← simplexContr_sum]
  congr 1
  funext a b c d
  exact fourJ_eq_sum_fourRecoupling j₀₁ j₀₂ j₀₃ j₀₄ i₀ a b c d

end Lightlike.SpinFoam.EPRLStateSum
