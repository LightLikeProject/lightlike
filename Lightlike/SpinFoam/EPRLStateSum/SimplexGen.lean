import Lightlike.Recoupling.FifteenJ
import Lightlike.Recoupling.Intertwiner

/-!
# The 4-simplex contraction with a free tensor at every vertex

`simplexGen T₀ … T₄` is the contraction of the 4-simplex `fifteenJSimplex` with the five
intertwiner tensors replaced by arbitrary functions `T_a` of the four projections at the vertex
`a`. It is a sum over a product box of the ten edge projections, so its linearity in each tensor
is a single exchange of sums (`simplexGen_rec₀`, …, `simplexGen_rec₄`). The theorem
`fifteenJSimplex_recouple` expands the five virtual spins `i₀, …, i₄` of `fifteenJSimplex` in
the other channel at all five vertices at once; it is the per-simplex step in the relation of the
EPRL state sum at `γ = 1` to the Ooguri model.
-/

open Finset Lightlike.Pentagon

namespace Lightlike.SpinFoam.EPRLStateSum

open Lightlike.Recoupling

/-- The box of the ten edge projections of a 4-simplex, as a product of intervals. -/
def simplexBox (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) :
    Finset (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  Icc (-(j₀₁ : ℤ)) j₀₁ ×ˢ Icc (-(j₀₂ : ℤ)) j₀₂ ×ˢ Icc (-(j₀₃ : ℤ)) j₀₃ ×ˢ Icc (-(j₀₄ : ℤ)) j₀₄ ×ˢ
    Icc (-(j₁₂ : ℤ)) j₁₂ ×ˢ Icc (-(j₁₃ : ℤ)) j₁₃ ×ˢ Icc (-(j₁₄ : ℤ)) j₁₄ ×ˢ
    Icc (-(j₂₃ : ℤ)) j₂₃ ×ˢ Icc (-(j₂₄ : ℤ)) j₂₄ ×ˢ Icc (-(j₃₄ : ℤ)) j₃₄

/-- The summand of the 4-simplex contraction at the projections `x = (m₀₁, …, m₃₄)`, with the
vertex tensors `T₀, …, T₄` and the edge spins `j`. -/
noncomputable def simplexTerm (T₀ T₁ T₂ T₃ T₄ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) (x : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :
    ℝ :=
  edgeSign j₀₁ x.1 * edgeSign j₀₂ x.2.1 * edgeSign j₀₃ x.2.2.1 * edgeSign j₀₄ x.2.2.2.1 *
    edgeSign j₁₂ x.2.2.2.2.1 * edgeSign j₁₃ x.2.2.2.2.2.1 * edgeSign j₁₄ x.2.2.2.2.2.2.1 *
    edgeSign j₂₃ x.2.2.2.2.2.2.2.1 * edgeSign j₂₄ x.2.2.2.2.2.2.2.2.1 *
    edgeSign j₃₄ x.2.2.2.2.2.2.2.2.2 *
  (T₀ x.1 x.2.1 x.2.2.1 x.2.2.2.1 *
    T₁ x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 (-x.1) *
    T₂ x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 (-x.2.1) (-x.2.2.2.2.1) *
    T₃ x.2.2.2.2.2.2.2.2.2 (-x.2.2.1) (-x.2.2.2.2.2.1) (-x.2.2.2.2.2.2.2.1) *
    T₄ (-x.2.2.2.1) (-x.2.2.2.2.2.2.1) (-x.2.2.2.2.2.2.2.2.1) (-x.2.2.2.2.2.2.2.2.2))

/-- The contraction of the 4-simplex with the intertwiner tensors `T₀, …, T₄` at the five
vertices: the sum of `simplexTerm` over the box of the ten edge projections. -/
noncomputable def simplexGen (T₀ T₁ T₂ T₃ T₄ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) : ℝ :=
  ∑ x ∈ simplexBox j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄,
    simplexTerm T₀ T₁ T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ x

/-- `fifteenJSimplex` is `simplexGen` of its five intertwiner tensors `fourJ`. -/
theorem fifteenJSimplex_eq_simplexGen
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ : ℕ) :
    fifteenJSimplex j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ =
      simplexGen (fourJ j₀₁ j₀₂ j₀₃ j₀₄ i₀) (fourJ j₁₂ j₁₃ j₁₄ j₀₁ i₁) (fourJ j₂₃ j₂₄ j₀₂ j₁₂ i₂)
        (fourJ j₃₄ j₀₃ j₁₃ j₂₃ i₃) (fourJ j₀₄ j₁₄ j₂₄ j₃₄ i₄)
        j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  simp only [fifteenJSimplex, simplexGen, simplexBox, simplexTerm, Finset.sum_product]

/-- Linearity of `simplexGen` in the tensor at the vertex `0`. -/
theorem simplexGen_rec₀ (S : Finset ℕ) (c : ℕ → ℝ) (U : ℕ → ℤ → ℤ → ℤ → ℤ → ℝ)
    (T₀ T₁ T₂ T₃ T₄ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h : ∀ a b d e, T₀ a b d e = ∑ l ∈ S, c l * U l a b d e)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) :
    simplexGen T₀ T₁ T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ =
      ∑ l ∈ S, c l * simplexGen (U l) T₁ T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  unfold simplexGen
  simp only [simplexTerm, h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun x _ => by ring

/-- Linearity of `simplexGen` in the tensor at the vertex `1`. -/
theorem simplexGen_rec₁ (S : Finset ℕ) (c : ℕ → ℝ) (U : ℕ → ℤ → ℤ → ℤ → ℤ → ℝ)
    (T₀ T₁ T₂ T₃ T₄ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h : ∀ a b d e, T₁ a b d e = ∑ l ∈ S, c l * U l a b d e)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) :
    simplexGen T₀ T₁ T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ =
      ∑ l ∈ S, c l * simplexGen T₀ (U l) T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  unfold simplexGen
  simp only [simplexTerm, h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun x _ => by ring

/-- Linearity of `simplexGen` in the tensor at the vertex `2`. -/
theorem simplexGen_rec₂ (S : Finset ℕ) (c : ℕ → ℝ) (U : ℕ → ℤ → ℤ → ℤ → ℤ → ℝ)
    (T₀ T₁ T₂ T₃ T₄ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h : ∀ a b d e, T₂ a b d e = ∑ l ∈ S, c l * U l a b d e)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) :
    simplexGen T₀ T₁ T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ =
      ∑ l ∈ S, c l * simplexGen T₀ T₁ (U l) T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  unfold simplexGen
  simp only [simplexTerm, h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun x _ => by ring

/-- Linearity of `simplexGen` in the tensor at the vertex `3`. -/
theorem simplexGen_rec₃ (S : Finset ℕ) (c : ℕ → ℝ) (U : ℕ → ℤ → ℤ → ℤ → ℤ → ℝ)
    (T₀ T₁ T₂ T₃ T₄ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h : ∀ a b d e, T₃ a b d e = ∑ l ∈ S, c l * U l a b d e)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) :
    simplexGen T₀ T₁ T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ =
      ∑ l ∈ S, c l * simplexGen T₀ T₁ T₂ (U l) T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  unfold simplexGen
  simp only [simplexTerm, h, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun x _ => by ring

/-- Linearity of `simplexGen` in the tensor at the vertex `4`. -/
theorem simplexGen_rec₄ (S : Finset ℕ) (c : ℕ → ℝ) (U : ℕ → ℤ → ℤ → ℤ → ℤ → ℝ)
    (T₀ T₁ T₂ T₃ T₄ : ℤ → ℤ → ℤ → ℤ → ℝ)
    (h : ∀ a b d e, T₄ a b d e = ∑ l ∈ S, c l * U l a b d e)
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ : ℕ) :
    simplexGen T₀ T₁ T₂ T₃ T₄ j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ =
      ∑ l ∈ S, c l * simplexGen T₀ T₁ T₂ T₃ (U l) j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  unfold simplexGen
  simp only [simplexTerm, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun x _ => by ring

/-- **Recoupling at all five vertices.** The 4-simplex contraction with virtual spins
`i₀, …, i₄` (each in the channel `(j j')(j'' j''')` of its four legs) is the combination, with
the products of five `fourRecoupling` coefficients, of the contractions whose five intertwiners
are in the channel with the second and third legs exchanged. -/
theorem fifteenJSimplex_recouple
    (j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ : ℕ) :
    fifteenJSimplex j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ i₀ i₁ i₂ i₃ i₄ =
      ∑ l₀ ∈ range (j₀₁ + j₀₃ + 1), ∑ l₁ ∈ range (j₁₂ + j₁₄ + 1),
      ∑ l₂ ∈ range (j₂₃ + j₀₂ + 1), ∑ l₃ ∈ range (j₃₄ + j₁₃ + 1), ∑ l₄ ∈ range (j₀₄ + j₂₄ + 1),
        fourRecoupling j₀₁ j₀₂ j₀₃ j₀₄ i₀ l₀ * fourRecoupling j₁₂ j₁₃ j₁₄ j₀₁ i₁ l₁ *
        fourRecoupling j₂₃ j₂₄ j₀₂ j₁₂ i₂ l₂ * fourRecoupling j₃₄ j₀₃ j₁₃ j₂₃ i₃ l₃ *
        fourRecoupling j₀₄ j₁₄ j₂₄ j₃₄ i₄ l₄ *
        simplexGen (fun a b c d => fourJ j₀₁ j₀₃ j₀₂ j₀₄ l₀ a c b d)
          (fun a b c d => fourJ j₁₂ j₁₄ j₁₃ j₀₁ l₁ a c b d)
          (fun a b c d => fourJ j₂₃ j₀₂ j₂₄ j₁₂ l₂ a c b d)
          (fun a b c d => fourJ j₃₄ j₁₃ j₀₃ j₂₃ l₃ a c b d)
          (fun a b c d => fourJ j₀₄ j₂₄ j₁₄ j₃₄ l₄ a c b d)
          j₀₁ j₀₂ j₀₃ j₀₄ j₁₂ j₁₃ j₁₄ j₂₃ j₂₄ j₃₄ := by
  rw [fifteenJSimplex_eq_simplexGen,
    simplexGen_rec₀ (range (j₀₁ + j₀₃ + 1)) (fun l => fourRecoupling j₀₁ j₀₂ j₀₃ j₀₄ i₀ l)
      (fun l a b c d => fourJ j₀₁ j₀₃ j₀₂ j₀₄ l a c b d) _ _ _ _ _
      (fourJ_eq_sum_fourRecoupling j₀₁ j₀₂ j₀₃ j₀₄ i₀ · · · ·)]
  refine sum_congr rfl fun l₀ _ => ?_
  rw [simplexGen_rec₁ (range (j₁₂ + j₁₄ + 1)) (fun l => fourRecoupling j₁₂ j₁₃ j₁₄ j₀₁ i₁ l)
      (fun l a b c d => fourJ j₁₂ j₁₄ j₁₃ j₀₁ l a c b d) _ _ _ _ _
      (fourJ_eq_sum_fourRecoupling j₁₂ j₁₃ j₁₄ j₀₁ i₁ · · · ·), mul_sum]
  refine sum_congr rfl fun l₁ _ => ?_
  rw [simplexGen_rec₂ (range (j₂₃ + j₀₂ + 1)) (fun l => fourRecoupling j₂₃ j₂₄ j₀₂ j₁₂ i₂ l)
      (fun l a b c d => fourJ j₂₃ j₀₂ j₂₄ j₁₂ l a c b d) _ _ _ _ _
      (fourJ_eq_sum_fourRecoupling j₂₃ j₂₄ j₀₂ j₁₂ i₂ · · · ·), mul_sum, mul_sum]
  refine sum_congr rfl fun l₂ _ => ?_
  rw [simplexGen_rec₃ (range (j₃₄ + j₁₃ + 1)) (fun l => fourRecoupling j₃₄ j₀₃ j₁₃ j₂₃ i₃ l)
      (fun l a b c d => fourJ j₃₄ j₁₃ j₀₃ j₂₃ l a c b d) _ _ _ _ _
      (fourJ_eq_sum_fourRecoupling j₃₄ j₀₃ j₁₃ j₂₃ i₃ · · · ·), mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun l₃ _ => ?_
  rw [simplexGen_rec₄ (range (j₀₄ + j₂₄ + 1)) (fun l => fourRecoupling j₀₄ j₁₄ j₂₄ j₃₄ i₄ l)
      (fun l a b c d => fourJ j₀₄ j₂₄ j₁₄ j₃₄ l a c b d) _ _ _ _ _
      (fourJ_eq_sum_fourRecoupling j₀₄ j₁₄ j₂₄ j₃₄ i₄ · · · ·), mul_sum, mul_sum, mul_sum,
    mul_sum]
  refine sum_congr rfl fun l₄ _ => ?_
  ring

end Lightlike.SpinFoam.EPRLStateSum
