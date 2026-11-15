import Mathlib
import Lightlike.Regge.Linear.AngleDeriv
import Lightlike.Regge.Geodesic.Metric

/-!
# The linearized deficit angle at a vertex of the diagonal grid

A symmetric matrix field `h` perturbs the flat metric to `δ + ε h`. At the flat background the
straight edges are geodesics, and the first variation of the squared length of the edge from `x`
to `y` is `∫₀¹ h(x + t (y - x))(y - x, y - x) dt` (the Regge finite-element interpolant of `h`).
For the vertex `P` of the grid of mesh `s`, with the six neighbours `P + s·off j` of the diagonal
triangulation, `linDef h s P` is the derivative at `ε = 0` of the deficit angle
`2π - ∑ⱼ θⱼ(ε)` computed from these edge lengths (`hasDerivAt_vertexDeficit`).
-/

open Real Lightlike.CMS Lightlike.Geodesic MeasureTheory

namespace Lightlike.Regge.Linear

/-- The six neighbours of a vertex of the diagonal grid, in cyclic order (grid units). -/
def off : Fin 6 → Fin 2 → ℝ := ![![1, 0], ![1, 1], ![0, 1], ![-1, 0], ![-1, -1], ![0, -1]]

/-- The first variation of the squared length of the edge from `P + s p` to `P + s q`, divided by
`s²`: the integral of `h(τ, τ)` along the edge in grid units, with `τ = q - p`. -/
noncomputable def edgeVar (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (P p q : Fin 2 → ℝ) :
    ℝ :=
  ∫ t in (0 : ℝ)..1, normSq h (P + s • (p + t • (q - p))) (q - p)

/-- Squared grid length of the spoke `0 → off j`. -/
def sqA (j : Fin 6) : ℝ := off j 0 ^ 2 + off j 1 ^ 2

/-- Squared grid length of the spoke `0 → off (j+1)`. -/
def sqB (j : Fin 6) : ℝ := sqA (j + 1)

/-- Squared grid length of the rim `off j → off (j+1)`. -/
def sqC (j : Fin 6) : ℝ := (off j 0 - off (j + 1) 0) ^ 2 + (off j 1 - off (j + 1) 1) ^ 2

/-- The edge variations of the triangle `(P, P + s off j, P + s off (j+1))`: spokes and rim. -/
noncomputable def varA (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (P : Fin 2 → ℝ)
    (j : Fin 6) : ℝ := edgeVar h s P 0 (off j)

/-- The variation of the second spoke. -/
noncomputable def varB (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (P : Fin 2 → ℝ)
    (j : Fin 6) : ℝ := edgeVar h s P 0 (off (j + 1))

/-- The variation of the rim. -/
noncomputable def varC (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (P : Fin 2 → ℝ)
    (j : Fin 6) : ℝ := edgeVar h s P (off (j + 1)) (off j)

/-- The **linearized deficit angle** at the vertex `P` of the grid of mesh `s` for the perturbation
`h`: minus the sum over the six triangles of the first variation of the angle at `P`, as a linear
functional of the edge variations. -/
noncomputable def linDef (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ) (P : Fin 2 → ℝ) :
    ℝ :=
  -∑ j : Fin 6, (2 * varC h s P j - (sqA j - sqB j + sqC j) * varA h s P j / sqA j
    - (sqB j - sqA j + sqC j) * varB h s P j / sqB j) / 4

/-- Every triangle of the star is nondegenerate with `D = 4` in grid units, and its sides are
positive. -/
lemma sq_facts (j : Fin 6) : 0 < sqA j ∧ 0 < sqB j ∧ disc (sqA j) (sqB j) (sqC j) = 4 := by
  fin_cases j <;> simp [sqA, sqB, sqC, off, disc] <;> norm_num

/-- **The first variation of the vertex deficit.** The deficit angle `2π - ∑ⱼ θⱼ(ε)`, computed from
the squared lengths `s² (a + ε a₁)` of the edges of the star, has derivative `linDef h s P` at
`ε = 0`, for `s > 0`. -/
theorem hasDerivAt_vertexDeficit (h : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) {s : ℝ}
    (hs : 0 < s) (P : Fin 2 → ℝ) :
    HasDerivAt (fun ε : ℝ => 2 * π - ∑ j : Fin 6,
      triAngle (s ^ 2 * (sqA j + ε * varA h s P j)) (s ^ 2 * (sqB j + ε * varB h s P j))
        (s ^ 2 * (sqC j + ε * varC h s P j))) (linDef h s P) 0 := by
  have hj : ∀ j : Fin 6, HasDerivAt (fun ε : ℝ =>
      triAngle (s ^ 2 * (sqA j + ε * varA h s P j)) (s ^ 2 * (sqB j + ε * varB h s P j))
        (s ^ 2 * (sqC j + ε * varC h s P j)))
      ((2 * varC h s P j - (sqA j - sqB j + sqC j) * varA h s P j / sqA j
        - (sqB j - sqA j + sqC j) * varB h s P j / sqB j) / 4) 0 := by
    intro j
    obtain ⟨ha, hb, hD⟩ := sq_facts j
    have hs2 : 0 < s ^ 2 := by positivity
    have := hasDerivAt_triAngle (a := s ^ 2 * sqA j) (b := s ^ 2 * sqB j) (c := s ^ 2 * sqC j)
      (a₁ := s ^ 2 * varA h s P j) (b₁ := s ^ 2 * varB h s P j) (c₁ := s ^ 2 * varC h s P j)
      (by positivity) (by positivity) (by
        have : disc (s ^ 2 * sqA j) (s ^ 2 * sqB j) (s ^ 2 * sqC j) =
            (s ^ 2) ^ 2 * disc (sqA j) (sqB j) (sqC j) := by unfold disc; ring
        rw [this, hD]; positivity)
    convert this using 1
    · ext ε; congr 1 <;> ring
    · have hd : disc (s ^ 2 * sqA j) (s ^ 2 * sqB j) (s ^ 2 * sqC j) = (s ^ 2) ^ 2 * 4 := by
        have : disc (s ^ 2 * sqA j) (s ^ 2 * sqB j) (s ^ 2 * sqC j) =
            (s ^ 2) ^ 2 * disc (sqA j) (sqB j) (sqC j) := by unfold disc; ring
        rw [this, hD]
      have hr : √((s ^ 2) ^ 2 * 4) = s ^ 2 * 2 := by
        rw [show (s ^ 2) ^ 2 * 4 = (s ^ 2 * 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
      rw [hd, hr]
      have : sqA j ≠ 0 := ha.ne'
      have : sqB j ≠ 0 := hb.ne'
      field_simp
      ring
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 6))) fun j _ => hj j
  have := (hasDerivAt_const (0 : ℝ) (2 * π)).sub hsum
  convert this using 1
  simp [linDef]

/-- The angle is scale invariant. -/
lemma triAngle_smul {k : ℝ} (hk : 0 < k) (a b c : ℝ) :
    triAngle (k * a) (k * b) (k * c) = triAngle a b c := by
  unfold triAngle
  congr 1
  rw [show k * a * (k * b) = k ^ 2 * (a * b) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hk.le]
  by_cases h : √(a * b) = 0
  · simp [h]
  · field_simp

/-- The angles of the six triangles of the flat star: `π/4, π/4, π/2, π/4, π/4, π/2`. -/
lemma triAngle_star (j : Fin 6) : triAngle (sqA j) (sqB j) (sqC j) =
    ![π / 4, π / 4, π / 2, π / 4, π / 4, π / 2] j := by
  have h4 : arccos (√2 / 2) = π / 4 := by
    rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hq : (1 + 1) / (2 * √(1 + 1 : ℝ)) = √2 / 2 := by
    have : (1 + 1 : ℝ) = 2 := by norm_num
    rw [this]
    have h2 : 0 < √2 := by positivity
    field_simp
    nlinarith
  fin_cases j <;> simp [triAngle, sqA, sqB, sqC, off]
  all_goals rw [hq, h4]

/-- **The flat background has zero deficit.** The angles at the vertex add up to `2π`. -/
theorem flat_vertexDeficit {s : ℝ} (hs : 0 < s) :
    2 * π - ∑ j : Fin 6, triAngle (s ^ 2 * sqA j) (s ^ 2 * sqB j) (s ^ 2 * sqC j) = 0 := by
  simp only [triAngle_smul (pow_pos hs 2), triAngle_star, Fin.sum_univ_six]
  simp
  ring

end Lightlike.Regge.Linear
