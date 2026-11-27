import Lightlike.SpinFoam.EPRLStateSum.SignDecomp

/-!
# The algebra of the tetrahedron signs: positional against sorted node tensors

* `recoupSign_mul_ampP_eq`: for symmetric triangle spins `J`, the positional weight `recoupSign J l * ampP J l` is the sorted
  weight `(-1)^(triPart J) * ampP J l` times the five tetrahedron signs `(-1)^(nodeExp J l a)`.
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

/-- **The positional vertex weight is the sorted one times the tetrahedron signs.** For symmetric `J`,
`recoupSign J l * ampP J l = ((-1)^(triPart J) * ampP J l) * Π_a (-1)^(nodeExp J l a)`: the positional (cyclic-order) and the
sorted-order intertwiners of the channel `(0 2 | 1 3)` differ at the nodes `a = 1, 2, 3` by the signs `(-1)^(nodeExp J l a)`. -/
theorem recoupSign_mul_ampP_eq (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (l : Fin 5 → ℕ) :
    recoupSign J l * ampP J l =
      ((-1) ^ triPart J * ampP J l) *
        ((-1) ^ nodeExp J l 0 * (-1) ^ nodeExp J l 1 * (-1) ^ nodeExp J l 2 * (-1) ^ nodeExp J l 3 *
          (-1) ^ nodeExp J l 4) := by
  rw [recoupSign_eq J hJ, pow_add, neg_one_pow_sum_nodeExp]
  ring

end Lightlike.SpinFoam.EPRLStateSum
