import Lightlike.SpinFoam.EPRLStateSum.SimplexIntrinsic

/-!
# The sign of the 4-simplex expansion splits into a triangle part and tetrahedron-local parts

`recoupSign J K` (`SimplexAmpP.lean`) is the sign in front of `ampP J K` in the expansion of the 15j
symbol of a 4-simplex. Here it is written as

`(-1)^(triPart J) * Π_a (-1)^(tetSignExp a (legs of node a) (K a))`

where `triPart J = J₁₂+J₁₄+J₃₄+J₀₂+J₀₄+J₂₄` involves the triangle spins only, and `tetSignExp a`
depends only on the position `a` of the tetrahedron in the simplex, its four legs in the sorted order
(`Fin.succAbove`) and its virtual spin `l = K a`:

* `a = 0, 4`: `0`;
* `a = 1`: `l + (t₀+t₂+l)/2`;  `a = 2`: `(t₀+t₂+l)/2 + (t₁+t₃+l)/2`;  `a = 3`: `l + (t₁+t₃+l)/2`.

So the failure of `recoupSign · ampP` to be the Ooguri weight on a closed complex is governed by the
position-dependent tetrahedron signs: a tetrahedron lying at positions `r, r'` in its two simplices
contributes `(-1)^(e_r + e_r')`, which vanishes when `r, r' ∈ {0, 4}` and is otherwise a function of
`(t₀…t₃, l)` (`tetSignExp_two`: `e₂ ≡ e₁ + e₃` mod 2).
-/

open Finset

namespace Lightlike.SpinFoam.EPRLStateSum

/-- The tetrahedron-local exponent of the sign, by position `a` of the tetrahedron in the simplex;
`t₀ … t₃` are the four legs in sorted order and `l` the virtual spin. -/
def tetSignExp (a : Fin 5) (t₀ t₁ t₂ t₃ l : ℕ) : ℕ :=
  if a = 1 then l + (t₀ + t₂ + l) / 2
  else if a = 2 then (t₀ + t₂ + l) / 2 + (t₁ + t₃ + l) / 2
  else if a = 3 then l + (t₁ + t₃ + l) / 2 else 0

/-- The exponent of the node `a` of a simplex: `tetSignExp` of its sorted legs and `K a`. -/
def nodeExp (J : Fin 5 → Fin 5 → ℕ) (K : Fin 5 → ℕ) (a : Fin 5) : ℕ :=
  tetSignExp a (J a (a.succAbove 0)) (J a (a.succAbove 1)) (J a (a.succAbove 2))
    (J a (a.succAbove 3)) (K a)

theorem neg_one_pow_of_eq_add {A B m : ℕ} (h : A = B + 2 * m) : ((-1 : ℝ)) ^ A = (-1) ^ B := by
  rw [h, pow_add, pow_mul]
  simp

/-- **Sign decomposition.** For symmetric triangle spins, `recoupSign J K` is the triangle sign
`(-1)^(triPart J)` times the five tetrahedron-local signs `(-1)^(nodeExp J K a)`. -/
theorem recoupSign_eq (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (K : Fin 5 → ℕ) :
    recoupSign J K =
      (-1) ^ (triPart J + (nodeExp J K 0 + nodeExp J K 1 + nodeExp J K 2 + nodeExp J K 3 +
        nodeExp J K 4)) := by
  unfold recoupSign ampSign
  rw [← pow_add]
  have h1 := hJ 1 0
  have h2 := hJ 2 0
  have h3 := hJ 2 1
  have h4 := hJ 3 0
  have h5 := hJ 3 1
  have h6 := hJ 3 2
  have h7 := hJ 4 3
  have h8 := hJ 3 4
  have h9 := hJ 2 4
  have h10 := hJ 4 2
  apply neg_one_pow_of_eq_add (m := K 0 + K 4 + K 2)
  simp only [nodeExp, tetSignExp, triPart, Fin.succAbove, Fin.lt_def]
  simp
  omega

/-- Within one tetrahedron the exponents at the positions `1, 2, 3` satisfy `e₂ ≡ e₁ + e₃`
modulo `2`, when the legs are admissible (`t₀+t₂+l`, `t₁+t₃+l` even). -/
theorem tetSignExp_two (t₀ t₁ t₂ t₃ l : ℕ) (h₁ : Even (t₀ + t₂ + l)) (h₂ : Even (t₁ + t₃ + l)) :
    tetSignExp 2 t₀ t₁ t₂ t₃ l % 2 = (tetSignExp 1 t₀ t₁ t₂ t₃ l + tetSignExp 3 t₀ t₁ t₂ t₃ l) % 2 := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  simp only [tetSignExp]
  simp
  omega

/-- The positions `0` and `4` carry no sign. -/
theorem tetSignExp_zero (t₀ t₁ t₂ t₃ l : ℕ) : tetSignExp 0 t₀ t₁ t₂ t₃ l = 0 := by
  simp [tetSignExp]

theorem tetSignExp_four (t₀ t₁ t₂ t₃ l : ℕ) : tetSignExp 4 t₀ t₁ t₂ t₃ l = 0 := by
  simp [tetSignExp]

/-- The tetrahedron sign genuinely depends on the position: for the admissible legs `(1,1,1,1)` and
`l = 0` (doubled spins) the exponents at the positions `0, 1, 2` have parities `0, 1, 0`. -/
theorem tetSignExp_position_dependent :
    tetSignExp 0 1 1 1 1 0 % 2 = 0 ∧ tetSignExp 1 1 1 1 1 0 % 2 = 1 ∧
      tetSignExp 2 1 1 1 1 0 % 2 = 0 := by
  decide

end Lightlike.SpinFoam.EPRLStateSum
