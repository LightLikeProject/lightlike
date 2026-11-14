import Lightlike.Asymptotics.Contour

/-!
# Homogeneity of the phase of Racah's sum

The edge lengths of the Ponzano–Regge limit are `ℓ = λj + ½ = λ m_λ` with `m_λ = j + 1/(2λ)`.
The saddle-point estimate of Racah's sum at `ℓ` is carried out in the rescaled variable
`σ = λx`, where every quantity of the phase becomes `λ` times the same quantity for `m_λ`, and
`m_λ → j`. This file proves these scaling laws exactly, for every real `c > 0`:

* the face sums and quadrilateral sums are linear (`faceSum_smul`, `quadSum_smul`);
* `xlog (c w) = c xlog w + c log c · w` (`xlog_ofReal_mul`);
* the continued phase satisfies `phaseC (cA) (cB) (cz) = c phaseC A B z + c log c (ΣA − ΣB)`
  (`phaseC_smul_add`), so it is homogeneous of degree one when `ΣA = ΣB` (`phaseC_smul`), which
  holds for every tetrahedron (`phaseC_faceSum_smul`); the same holds for Racah's phase
  (`phase_smul`);
* the derivative `dphaseC` is homogeneous of degree zero on the open upper half-plane
  (`dphaseC_smul`), and the second derivative `d2phase` of degree `−1` (`d2phase_smul`);
* the coefficients of the saddle-point quadratic have degrees two and three (`qa_smul`,
  `qb_smul`), the squared volume degree six (`vol2l_smul`), and the saddle point degree one
  (`saddle_smul`);
* a tetrahedron is Euclidean exactly when its rescaled copy is (`isEuclid_smul_iff`);
* `PR.lengths j λ = λ • m_λ` (`lengths_eq_smul`) and `m_λ → j` (`tendsto_lengthsDir`).
* Euclidean tetrahedra form an open set (`isOpen_isEuclid`), so for Euclidean spins `j` both
  `m_λ` and `ℓ` are Euclidean for all large `λ` (`eventually_isEuclid_lengths`).

The degree-one law needs `ΣA = ΣB`: the logarithmic terms `c log c · w` of the seven `xlog` terms
add up to `c log c (ΣA − ΣB)`, independent of `z`.
-/

open Complex Filter Topology
open scoped Real

namespace Lightlike.Asymptotics

/-! ## Face sums, quadrilateral sums and `xlog` -/

/-- The face sums are linear in the edge lengths. -/
lemma faceSum_smul (c : ℝ) (l : Fin 6 → ℝ) (i : Fin 4) :
    faceSum (c • l) i = c * faceSum l i := by
  fin_cases i <;> simp [faceSum] <;> ring

/-- The quadrilateral sums are linear in the edge lengths. -/
lemma quadSum_smul (c : ℝ) (l : Fin 6 → ℝ) (k : Fin 3) :
    quadSum (c • l) k = c * quadSum l k := by
  fin_cases k <;> simp [quadSum] <;> ring

/-- `xlog (c w) = c xlog w + c log c · w` for real `c > 0` and every `w` (at `w = 0` both sides
vanish). -/
lemma xlog_ofReal_mul {c : ℝ} (hc : 0 < c) (w : ℂ) :
    xlog ((c : ℂ) * w) = c * xlog w + (c * Real.log c : ℝ) * w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [xlog]
  · rw [xlog, xlog, log_ofReal_mul hc hw]
    push_cast
    ring

/-! ## The continued phase and its derivatives -/

/-- **Scaling of the continued phase**: for real `c > 0`,
`phaseC (cA) (cB) (cz) = c phaseC A B z + c log c (ΣA − ΣB)`. -/
theorem phaseC_smul_add (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {c : ℝ} (hc : 0 < c) (z : ℂ) :
    phaseC (c • A) (c • B) (c * z) =
      c * phaseC A B z + (c * Real.log c : ℝ) * (∑ i, (A i : ℂ) - ∑ k, (B k : ℂ)) := by
  have h : ∀ r : ℝ, (c : ℂ) * z - (c : ℂ) * (r : ℂ) = c * (z - r) := fun r => by ring
  simp only [phaseC, Fin.sum_univ_four, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [h, xlog_ofReal_mul hc]
  push_cast
  ring

/-- **Homogeneity of the continued phase**: if `ΣA = ΣB`, then
`phaseC (cA) (cB) (cz) = c phaseC A B z` for every real `c > 0`. -/
theorem phaseC_smul {A : Fin 4 → ℝ} {B : Fin 3 → ℝ} (hAB : ∑ i, A i = ∑ k, B k) {c : ℝ}
    (hc : 0 < c) (z : ℂ) : phaseC (c • A) (c • B) (c * z) = c * phaseC A B z := by
  have h : (∑ i, (A i : ℂ)) - ∑ k, (B k : ℂ) = 0 := by
    rw [sub_eq_zero]; exact_mod_cast hAB
  rw [phaseC_smul_add A B hc z, h, mul_zero, add_zero]

/-- **Homogeneity of the phase of a tetrahedron**: with `A = faceSum l`, `B = quadSum l`,
`phaseC A(cl) B(cl) (cz) = c phaseC A(l) B(l) z` for every real `c > 0`. -/
theorem phaseC_faceSum_smul (l : Fin 6 → ℝ) {c : ℝ} (hc : 0 < c) (z : ℂ) :
    phaseC (faceSum (c • l)) (quadSum (c • l)) (c * z) =
      c * phaseC (faceSum l) (quadSum l) z := by
  have hA : faceSum (c • l) = c • faceSum l := funext fun i => by
    rw [faceSum_smul, Pi.smul_apply, smul_eq_mul]
  have hB : quadSum (c • l) = c • quadSum l := funext fun k => by
    rw [quadSum_smul, Pi.smul_apply, smul_eq_mul]
  rw [hA, hB]
  exact phaseC_smul (sum_faceSum_eq_sum_quadSum l) hc z

/-- **Homogeneity of Racah's phase**: `phase (cl) (cx) = c phase l x` for every real `c > 0`. -/
theorem phase_smul (l : Fin 6 → ℝ) {c : ℝ} (hc : 0 < c) (x : ℂ) :
    phase (c • l) (c * x) = c * phase l x := by
  have hS : (∑ i, (faceSum l i : ℂ)) = ∑ k, (quadSum l k : ℂ) := by
    exact_mod_cast sum_faceSum_eq_sum_quadSum l
  have hA : ∀ i, (c : ℂ) * x - (faceSum (c • l) i : ℝ) = c * (x - faceSum l i) := fun i => by
    rw [faceSum_smul]; push_cast; ring
  have hB : ∀ k, ((quadSum (c • l) k : ℝ) : ℂ) - c * x = c * (quadSum l k - x) := fun k => by
    rw [quadSum_smul]; push_cast; ring
  have hx := xlog_ofReal_mul hc x
  have hxA := fun i => xlog_ofReal_mul hc (x - faceSum l i)
  have hxB := fun k => xlog_ofReal_mul hc ((quadSum l k : ℂ) - x)
  simp only [xlog] at hx hxA hxB
  simp only [phase, hA, hB, hx, hxA, hxB]
  simp only [Fin.sum_univ_four, Fin.sum_univ_three] at hS ⊢
  linear_combination ((c * Real.log c : ℝ) : ℂ) * hS

/-- **The derivative of the continued phase is homogeneous of degree zero** on the open upper
half-plane: `dphaseC (cA) (cB) (cz) = dphaseC A B z` for real `c > 0` (the four `log c` of the
face terms cancel the three of the quadrilateral terms and the one of `log z`). -/
theorem dphaseC_smul (A : Fin 4 → ℝ) (B : Fin 3 → ℝ) {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : 0 < z.im) : dphaseC (c • A) (c • B) (c * z) = dphaseC A B z := by
  have hne : ∀ r : ℝ, z - r ≠ 0 := fun r h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hz0 : z ≠ 0 := by simpa using hne 0
  have hA : ∀ i, (c : ℂ) * z - ((c • A) i : ℝ) = c * (z - A i) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
  have hB : ∀ k, (c : ℂ) * z - ((c • B) k : ℝ) = c * (z - B k) := fun k => by
    simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
  simp only [dphaseC, hA, hB, log_ofReal_mul hc hz0, log_ofReal_mul hc (hne _),
    Fin.sum_univ_four, Fin.sum_univ_three]
  ring

/-- **The second derivative of the phase is homogeneous of degree `−1`**:
`d2phase (cl) (cx) = d2phase l x / c` for real `c > 0` (also at the poles, where both sides use
Lean's `1/0 = 0`). -/
theorem d2phase_smul (l : Fin 6 → ℝ) {c : ℝ} (hc : 0 < c) (x : ℂ) :
    d2phase (c • l) (c * x) = d2phase l x / c := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hA : ∀ i, (c : ℂ) * x - (faceSum (c • l) i : ℝ) = c * (x - faceSum l i) := fun i => by
    rw [faceSum_smul]; push_cast; ring
  have hB : ∀ k, (c : ℂ) * x - (quadSum (c • l) k : ℝ) = c * (x - quadSum l k) := fun k => by
    rw [quadSum_smul]; push_cast; ring
  simp only [d2phase, hA, hB, one_div, mul_inv, Fin.sum_univ_four, Fin.sum_univ_three]
  field_simp

/-! ## The saddle point -/

/-- The quadratic coefficient `qa` has degree two. -/
lemma qa_smul (c : ℝ) (l : Fin 6 → ℝ) : qa (c • l) = c ^ 2 * qa l := by
  simp only [qa, Pi.smul_apply, smul_eq_mul]
  ring

/-- The linear coefficient `qb` has degree three. -/
lemma qb_smul (c : ℝ) (l : Fin 6 → ℝ) : qb (c • l) = c ^ 3 * qb l := by
  simp only [qb, faceSum_smul, quadSum_smul]
  ring

/-- The squared volume has degree six. -/
lemma vol2l_smul (c : ℝ) (l : Fin 6 → ℝ) : vol2l (c • l) = c ^ 6 * vol2l l := by
  simp only [vol2l, PR.vol2, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The saddle point has degree one**: `saddle (cl) = c saddle l` for real `c > 0`. -/
theorem saddle_smul (l : Fin 6 → ℝ) {c : ℝ} (hc : 0 < c) : saddle (c • l) = c * saddle l := by
  have hs : √(vol2l (c • l)) = c ^ 3 * √(vol2l l) := by
    rw [vol2l_smul, Real.sqrt_mul (by positivity), show c ^ 6 = (c ^ 3) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  apply Complex.ext
  · simp only [saddle, qa_smul, qb_smul, re_ofReal_mul]
    rcases eq_or_ne (qa l) 0 with h | h
    · simp [h]
    · field_simp
  · simp only [saddle, qa_smul, hs, im_ofReal_mul]
    rcases eq_or_ne (qa l) 0 with h | h
    · simp [h]
    · field_simp

/-- **Rescaling keeps a tetrahedron Euclidean**: for real `c > 0`,
`IsEuclid (cl) ↔ IsEuclid l`. -/
theorem isEuclid_smul_iff (l : Fin 6 → ℝ) {c : ℝ} (hc : 0 < c) :
    IsEuclid (c • l) ↔ IsEuclid l := by
  simp only [IsEuclid, faceSum_smul, quadSum_smul, vol2l_smul, mul_lt_mul_iff_right₀ hc,
    mul_pos_iff_of_pos_left (pow_pos hc 6)]

/-! ## The lengths of the Ponzano–Regge limit -/

/-- The direction `m_λ = j + 1/(2λ)` of the lengths `ℓ = λj + ½`. -/
noncomputable def lengthsDir (j : Fin 6 → ℕ) (lam : ℕ) : Fin 6 → ℝ :=
  fun e => (j e : ℝ) + 1 / (2 * lam)

/-- `PR.lengths j λ = λ • m_λ` for `λ ≠ 0`. -/
theorem lengths_eq_smul (j : Fin 6 → ℕ) {lam : ℕ} (hlam : lam ≠ 0) :
    PR.lengths j lam = (lam : ℝ) • lengthsDir j lam := by
  have h : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam
  funext e
  simp only [PR.lengths, lengthsDir, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- `m_λ = j + 1/(2λ) → j` as `λ → ∞`. -/
theorem tendsto_lengthsDir (j : Fin 6 → ℕ) :
    Tendsto (lengthsDir j) atTop (𝓝 fun e => (j e : ℝ)) := by
  rw [tendsto_pi_nhds]
  intro e
  have h : Tendsto (fun lam : ℕ => 1 / (2 * (lam : ℝ))) atTop (𝓝 0) := by
    simp only [one_div, mul_inv]
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2⁻¹ : ℝ)
  simpa [lengthsDir] using h.const_add (j e : ℝ)

/-- The face sums are continuous in the edge lengths. -/
lemma continuous_faceSum (i : Fin 4) : Continuous fun l : Fin 6 → ℝ => faceSum l i := by
  fin_cases i <;> simp only [faceSum] <;> fun_prop

/-- The quadrilateral sums are continuous in the edge lengths. -/
lemma continuous_quadSum (k : Fin 3) : Continuous fun l : Fin 6 → ℝ => quadSum l k := by
  fin_cases k <;> simp only [quadSum] <;> fun_prop

/-- The squared volume is continuous in the edge lengths. -/
lemma continuous_vol2l : Continuous vol2l := by
  unfold vol2l PR.vol2
  fun_prop

/-- **Euclidean tetrahedra form an open set** of edge lengths (twelve strict triangle
inequalities and `vol2 > 0`). -/
theorem isOpen_isEuclid : IsOpen {l : Fin 6 → ℝ | IsEuclid l} := by
  have h1 : IsOpen {l : Fin 6 → ℝ | ∀ i k, faceSum l i < quadSum l k} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k =>
      isOpen_lt (continuous_faceSum i) (continuous_quadSum k)
  exact h1.inter (isOpen_lt continuous_const continuous_vol2l)

/-- For Euclidean integer spins `j`, the direction `m_λ` and the lengths `ℓ = λj + ½` are
Euclidean for all large `λ`. -/
theorem eventually_isEuclid_lengths {j : Fin 6 → ℕ} (h : IsEuclid fun e => (j e : ℝ)) :
    ∀ᶠ lam : ℕ in atTop, IsEuclid (lengthsDir j lam) ∧ IsEuclid (PR.lengths j lam) := by
  have hd : ∀ᶠ lam : ℕ in atTop, IsEuclid (lengthsDir j lam) :=
    tendsto_lengthsDir j (isOpen_isEuclid.mem_nhds h)
  filter_upwards [hd, eventually_ne_atTop 0] with lam hlam h0
  refine ⟨hlam, ?_⟩
  rw [lengths_eq_smul j h0, isEuclid_smul_iff _ (by exact_mod_cast Nat.pos_of_ne_zero h0)]
  exact hlam

end Lightlike.Asymptotics
