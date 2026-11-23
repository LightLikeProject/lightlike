import Lightlike.SpinFoam.EPRLStateSum.SignDecomp

/-!
# The intrinsic EPRL vertex as a signed Ooguri vertex, and the algebra of the tetrahedron signs

* `simpEIAux_signed`: for symmetric triangle spins `J`, `simpEIAux J i` is the sum over the virtual
  spins `l` of the five node matrices, times `(-1)^(triPart J)`, times the five tetrahedron signs
  `(-1)^(nodeExp J l a)`, times the Ooguri vertex amplitude `ampP J l` (before the sign `ampSign`
  inside `ampP` is removed, see `recoupSign_mul_ampP`).
* `tetSgn a t₀ t₁ t₂ t₃ l = (-1)^(tetSignExp a t₀ t₁ t₂ t₃ l)`: the sign of a tetrahedron at the
  position `a` of a simplex. `tetSgn_sq`: a sign squared is `1`, so a tetrahedron sitting at the same
  position in both its simplices contributes no sign (`tetSgn_mul_self_pos`); `tetSgn_two`: on
  admissible legs `s₂ = s₁ s₃`, hence every pair of positions gives a product of `s₁, s₃` only
  (`tetSgn_pair`).
-/

open Finset Lightlike.Recoupling Lightlike.Spin4 Lightlike.FourD Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

variable {V : Type*} [LinearOrder V]

/-- The sign of a tetrahedron at the position `a` of a simplex (legs `t₀ … t₃` sorted, virtual
spin `l`). -/
def tetSgn (a : Fin 5) (t₀ t₁ t₂ t₃ l : ℕ) : ℝ := (-1) ^ tetSignExp a t₀ t₁ t₂ t₃ l

theorem tetSgn_sq (a : Fin 5) (t₀ t₁ t₂ t₃ l : ℕ) :
    tetSgn a t₀ t₁ t₂ t₃ l * tetSgn a t₀ t₁ t₂ t₃ l = 1 := by
  unfold tetSgn
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- A tetrahedron at the same position in both of its simplices contributes no sign. -/
theorem tetSgn_mul_self_pos (a : Fin 5) (t₀ t₁ t₂ t₃ l : ℕ) :
    tetSgn a t₀ t₁ t₂ t₃ l * tetSgn a t₀ t₁ t₂ t₃ l = 1 :=
  tetSgn_sq a t₀ t₁ t₂ t₃ l

theorem tetSgn_zero (t₀ t₁ t₂ t₃ l : ℕ) : tetSgn 0 t₀ t₁ t₂ t₃ l = 1 := by
  simp [tetSgn, tetSignExp_zero]

theorem tetSgn_four (t₀ t₁ t₂ t₃ l : ℕ) : tetSgn 4 t₀ t₁ t₂ t₃ l = 1 := by
  simp [tetSgn, tetSignExp_four]

/-- Positions `0` and `4` of the same tetrahedron carry the same (trivial) sign. -/
theorem tetSgn_zero_four (t₀ t₁ t₂ t₃ l : ℕ) :
    tetSgn 0 t₀ t₁ t₂ t₃ l = tetSgn 4 t₀ t₁ t₂ t₃ l := by
  rw [tetSgn_zero, tetSgn_four]

theorem neg_one_pow_eq_of_mod {A B : ℕ} (h : A % 2 = B % 2) : ((-1 : ℝ)) ^ A = (-1) ^ B := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]


/-- On admissible legs the sign at position `2` is the product of those at `1` and `3`. -/
theorem tetSgn_two (t₀ t₁ t₂ t₃ l : ℕ) (h₁ : Even (t₀ + t₂ + l)) (h₂ : Even (t₁ + t₃ + l)) :
    tetSgn 2 t₀ t₁ t₂ t₃ l = tetSgn 1 t₀ t₁ t₂ t₃ l * tetSgn 3 t₀ t₁ t₂ t₃ l := by
  unfold tetSgn
  rw [← pow_add]
  exact neg_one_pow_eq_of_mod (tetSignExp_two t₀ t₁ t₂ t₃ l h₁ h₂)

/-- **The sign of a tetrahedron glued between positions `a, b`**, on admissible legs, is a product of
the signs at the positions `1` and `3` (and `1` if `a, b ∈ {0, 4}`). -/
theorem tetSgn_pair (a : Fin 5) (t₀ t₁ t₂ t₃ l : ℕ) (h₁ : Even (t₀ + t₂ + l))
    (h₂ : Even (t₁ + t₃ + l)) :
    tetSgn a t₀ t₁ t₂ t₃ l = tetSgn 1 t₀ t₁ t₂ t₃ l ^ (if a = 1 ∨ a = 2 then 1 else 0) *
      tetSgn 3 t₀ t₁ t₂ t₃ l ^ (if a = 3 ∨ a = 2 then 1 else 0) := by
  fin_cases a
  · simp [tetSgn_zero]
  · simp
  · simp [tetSgn_two t₀ t₁ t₂ t₃ l h₁ h₂]
  · simp
  · simp [tetSgn_four]

/-- The product of the five tetrahedron signs of a simplex. -/
theorem neg_one_pow_sum_nodeExp (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) :
    ((-1 : ℝ)) ^ (nodeExp J K 0 + nodeExp J K 1 + nodeExp J K 2 + nodeExp J K 3 + nodeExp J K 4) =
      (-1) ^ nodeExp J K 0 * (-1) ^ nodeExp J K 1 * (-1) ^ nodeExp J K 2 *
        (-1) ^ nodeExp J K 3 * (-1) ^ nodeExp J K 4 := by
  simp only [pow_add]

/-- **The intrinsic EPRL vertex is a signed Ooguri vertex.** For symmetric `J`, `simpEIAux J i` is
the sum over the virtual spins of the node matrices times
`(-1)^(triPart J) · Π_a (-1)^(nodeExp J l a) · ampP J l`. -/
theorem simpEIAux_signed (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (i : Fin 5 → ℕ) :
    simpEIAux J i =
      ∑ l₀ ∈ range (J 0 1 + J 0 3 + 1), ∑ l₁ ∈ range (J 1 2 + J 1 4 + 1),
      ∑ l₂ ∈ range (J 2 3 + J 0 2 + 1), ∑ l₃ ∈ range (J 3 4 + J 1 3 + 1),
      ∑ l₄ ∈ range (J 0 4 + J 2 4 + 1),
        nodeI J 0 (i 0) l₀ * nodeI J 1 (i 1) l₁ * nodeI J 2 (i 2) l₂ * nodeI J 3 (i 3) l₃ *
          nodeI J 4 (i 4) l₄ *
        ((-1) ^ (triPart J) *
          ((-1) ^ nodeExp J ![l₀, l₁, l₂, l₃, l₄] 0 * (-1) ^ nodeExp J ![l₀, l₁, l₂, l₃, l₄] 1 *
            (-1) ^ nodeExp J ![l₀, l₁, l₂, l₃, l₄] 2 * (-1) ^ nodeExp J ![l₀, l₁, l₂, l₃, l₄] 3 *
            (-1) ^ nodeExp J ![l₀, l₁, l₂, l₃, l₄] 4) *
          ampP J ![l₀, l₁, l₂, l₃, l₄]) := by
  unfold simpEIAux
  refine Finset.sum_congr rfl fun l₀ _ => Finset.sum_congr rfl fun l₁ _ =>
    Finset.sum_congr rfl fun l₂ _ => Finset.sum_congr rfl fun l₃ _ =>
    Finset.sum_congr rfl fun l₄ _ => ?_
  rw [recoupSign_eq J hJ, pow_add, neg_one_pow_sum_nodeExp]

end Lightlike.SpinFoam.EPRLStateSum
