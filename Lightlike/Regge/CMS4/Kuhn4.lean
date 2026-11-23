import Lightlike.Regge.D4.Dihedral

/-!
# The Kuhn orthoscheme of the 4-cube and its ten hinges

The unit 4-cube is cut into the `24` Kuhn 4-simplices, one for each permutation `σ` of the four
coordinates: the vertices are `0, e_{σ0}, e_{σ0}+e_{σ1}, …, e_{σ0}+⋯+e_{σ3}`. This file fixes the
orthoscheme `kv4` of the identity permutation and computes its ten dihedral angles (one at each
triangle) with `Lightlike.Regge4.cosDihedral4` from the squared edge lengths alone.

## Main results

* `kv4`: the vertices of the orthoscheme in `ℝ⁴`.
* `hP, hQ, hR, hS, hU`: the ten hinges `pqr` with opposite vertices `s, u`; `hS, hU` is the pair of
  omitted vertices.
* `kuhn4_cos`: the cosine of the dihedral angle at every hinge, for any lengths `ℓ` that are the
  Euclidean distances of `kv4`; `kuhn4_dihedral`: the angles are `π/4, π/3, π/3, π/4` at the four
  hinges whose omitted vertices are consecutive and `π/2` at the other six.
-/

open Real

namespace Lightlike.Regge4

/-- The vertices `0, e₀, e₀+e₁, e₀+e₁+e₂, e₀+e₁+e₂+e₃` of the Kuhn orthoscheme of the unit 4-cube. -/
def kv4 : Fin 5 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1]]

/-- The squared Euclidean distance of two vertices of the orthoscheme. -/
def kd4 (a b : Fin 5) : ℝ := ∑ i, (kv4 a i - kv4 b i) ^ 2

/-- First vertex of the hinge (a triangle `pqr`). -/
def hP : Fin 10 → Fin 5 := ![2, 1, 1, 1, 0, 0, 0, 0, 0, 0]
/-- Second vertex of the hinge. -/
def hQ : Fin 10 → Fin 5 := ![3, 3, 2, 2, 3, 2, 2, 1, 1, 1]
/-- Third vertex of the hinge. -/
def hR : Fin 10 → Fin 5 := ![4, 4, 4, 3, 4, 4, 3, 4, 3, 2]
/-- First omitted vertex: the tetrahedron `pqru` has the opposite vertex `u`. -/
def hS : Fin 10 → Fin 5 := ![0, 0, 0, 0, 1, 1, 1, 2, 2, 3]
/-- Second omitted vertex. -/
def hU : Fin 10 → Fin 5 := ![1, 2, 3, 4, 2, 3, 4, 3, 4, 4]

/-- The cosines of the ten dihedral angles of the orthoscheme. -/
noncomputable def hcos : Fin 10 → ℝ :=
  ![√2 / 2, 0, 0, 0, 1 / 2, 0, 0, 1 / 2, 0, √2 / 2]

variable {ℓ : Finset (Fin 5) → ℝ}

theorem sq_kd4 (hℓ : ∀ a b : Fin 5, a ≠ b → ℓ {a, b} ^ 2 = kd4 a b) (a b : Fin 5) :
    sq ℓ a b = kd4 a b := by
  by_cases h : a = b
  · subst h; simp [sq, kd4]
  · simp [sq, h, hℓ a b h]

theorem cos_of (m X c : ℝ) (hc : 0 < c) (hX : X = (m / c) ^ 2) (hm : 0 < m) :
    m / √X = c := by
  rw [hX, Real.sqrt_sq (div_nonneg hm.le hc.le)]
  field_simp

theorem kuhn4_cos (hℓ : ∀ a b : Fin 5, a ≠ b → ℓ {a, b} ^ 2 = kd4 a b) (h : Fin 10) :
    cosDihedral4 ℓ (hP h) (hQ h) (hR h) (hS h) (hU h) = hcos h := by
  have e : ∀ a b, sq ℓ a b = kd4 a b := sq_kd4 hℓ
  fin_cases h <;>
    simp [cosDihedral4, mixed, gram3, ip, det3, e, kd4, kv4, hP, hQ, hR, hS, hU, hcos,
      Fin.sum_univ_four] <;> norm_num
  all_goals
    have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have h2p : 0 < √2 := by positivity
    field_simp
    linarith

/-- The dihedral angles of the orthoscheme: `π/4, π/3, π/3, π/4` where the omitted vertices are
consecutive, `π/2` elsewhere. -/
theorem kuhn4_dihedral (hℓ : ∀ a b : Fin 5, a ≠ b → ℓ {a, b} ^ 2 = kd4 a b) (h : Fin 10) :
    dihedral4 ℓ (hP h) (hQ h) (hR h) (hS h) (hU h) =
      ![π / 4, π / 2, π / 2, π / 2, π / 3, π / 2, π / 2, π / 3, π / 2, π / 4] h := by
  unfold dihedral4
  rw [kuhn4_cos hℓ h]
  fin_cases h <;> simp [hcos]
  · rw [show √2 / 2 = cos (π / 4) by rw [cos_pi_div_four], arccos_cos] <;> linarith [pi_pos]
  · rw [show (2 : ℝ)⁻¹ = cos (π / 3) by rw [cos_pi_div_three]; norm_num, arccos_cos] <;>
      linarith [pi_pos]
  · rw [show (2 : ℝ)⁻¹ = cos (π / 3) by rw [cos_pi_div_three]; norm_num, arccos_cos] <;>
      linarith [pi_pos]
  · rw [show √2 / 2 = cos (π / 4) by rw [cos_pi_div_four], arccos_cos] <;> linarith [pi_pos]

end Lightlike.Regge4
