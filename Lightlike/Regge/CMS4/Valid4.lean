import Lightlike.Regge.CMS4.JetCore4

/-!
# The Gram tetrahedra of a positive definite metric are admissible (dimension 4)

For a positive definite `g m`, the squared lengths of every incidence `(σ, h)` of the Kuhn
triangulation of the 4-cube are admissible for the dihedral angle (`Valid4`). This is the `valid`
field of `JetStarCore4` for a general metric jet.

## Main results

* `valid4_gram`: five vertices in `ℝ⁴` for which the four edge vectors from `p` are independent
  have admissible squared lengths for every positive definite quadratic form, with the
  Desnanot–Jacobi identity `dj4` giving `mixed² < gram₃ · gram₃`.
* `valid4_incQ`: the `valid` field, `Valid4 … (incQ4 g m σ h)` for `(g m).PosDef`.
-/

open Real Matrix
open scoped Matrix

namespace Lightlike.Regge4

open Lightlike.Regge.Conv3

/-- The Desnanot–Jacobi identity for a symmetric `4 × 4` matrix, in the form used by the
dihedral angle: `gram₃(qrs) · gram₃(qru) - mixed² = gram₂(qr) · det`. -/
theorem dj4 (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : ∀ j k, M j k = M k j) :
    det3 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) *
      det3 (M 0 0) (M 0 1) (M 0 3) (M 1 0) (M 1 1) (M 1 3) (M 3 0) (M 3 1) (M 3 3)
      - det3 (M 0 0) (M 0 1) (M 0 3) (M 1 0) (M 1 1) (M 1 3) (M 2 0) (M 2 1) (M 2 3) ^ 2
      = (M 0 0 * M 1 1 - M 0 1 * M 1 0) * M.det := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, det3]
  simp [Fin.succAbove, Fin.lt_def]
  rw [hM 1 0, hM 2 0, hM 3 0, hM 2 1, hM 3 1, hM 3 2]
  ring

/-- Polarization for a symmetric bilinear form. -/
theorem polar4 {B : Matrix (Fin 4) (Fin 4) ℝ} (hs : Bᵀ = B) (a b : Fin 4 → ℝ) :
    (a ⬝ᵥ (B *ᵥ a) + b ⬝ᵥ (B *ᵥ b) - (b - a) ⬝ᵥ (B *ᵥ (b - a))) / 2 = a ⬝ᵥ (B *ᵥ b) := by
  have hsym : ∀ a b : Fin 4 → ℝ, a ⬝ᵥ (B *ᵥ b) = b ⬝ᵥ (B *ᵥ a) := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct]
  rw [hsym b a]
  ring

/-- **Five vertices with independent edge vectors have admissible squared lengths.** -/
theorem valid4_gram {B : Matrix (Fin 4) (Fin 4) ℝ} (hB : B.PosDef) (x : Fin 5 → Fin 4 → ℝ)
    (p q r t u : Fin 5)
    (hA : Function.Injective (Matrix.of fun i j : Fin 4 =>
      (![x q, x r, x t, x u] j - x p) i).mulVec) :
    Valid4 p q r t u (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) := by
  have hs : Bᵀ = B := by
    have := hB.1
    simpa [Matrix.IsSymm] using this
  have ip_eq : ∀ a b : Fin 5, ipS (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p a b
      = (x a - x p) ⬝ᵥ (B *ᵥ (x b - x p)) := by
    intro a b
    unfold ipS
    rw [← polar4 hs (x a - x p) (x b - x p), sub_sub_sub_cancel_right]
  set w : Fin 4 → Fin 4 → ℝ := ![x q - x p, x r - x p, x t - x p, x u - x p] with hw
  have hwA : (Matrix.of fun i j : Fin 4 => (![x q, x r, x t, x u] j - x p) i) =
      Matrix.of fun i j => w j i := by
    ext i j
    fin_cases j <;> simp [hw]
  set M : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun j k => w j ⬝ᵥ (B *ᵥ w k) with hMdef
  have hMeq : M = (Matrix.of fun i j => w j i)ᴴ * B * (Matrix.of fun i j => w j i) := by
    ext j k
    simp [hMdef, Matrix.mul_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_four]
    ring
  have hM : M.PosDef := by
    rw [hMeq]
    rw [hwA] at hA
    exact hB.conjTranspose_mul_mul_same hA
  have hsym : ∀ j k, M j k = M k j := fun j k => by
    simp only [hMdef, Matrix.of_apply]
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
  have inj1 : Function.Injective (![0, 1, 2] : Fin 3 → Fin 4) := by decide
  have inj2 : Function.Injective (![0, 1, 3] : Fin 3 → Fin 4) := by decide
  have inj3 : Function.Injective (![0, 1] : Fin 2 → Fin 4) := by decide
  have g1 := (hM.submatrix (e := ![0, 1, 2]) inj1).det_pos
  have g2 := (hM.submatrix (e := ![0, 1, 3]) inj2).det_pos
  have g3 := (hM.submatrix (e := ![0, 1]) inj3).det_pos
  have g4 := hM.det_pos
  have dj := dj4 M hsym
  rw [Matrix.det_fin_three] at g1 g2
  rw [Matrix.det_fin_two] at g3
  simp at g1 g2 g3
  have E1 : gram3S (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p q r t =
      det3 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) := by
    simp only [gram3S, ip_eq, hMdef, hw]
    simp
  have E2 : gram3S (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p q r u =
      det3 (M 0 0) (M 0 1) (M 0 3) (M 1 0) (M 1 1) (M 1 3) (M 3 0) (M 3 1) (M 3 3) := by
    simp only [gram3S, ip_eq, hMdef, hw]
    simp
  have E3 : mixedS (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p q r t u =
      det3 (M 0 0) (M 0 1) (M 0 3) (M 1 0) (M 1 1) (M 1 3) (M 2 0) (M 2 1) (M 2 3) := by
    simp only [mixedS, ip_eq, hMdef, hw]
    simp
  have G1 : 0 < det3 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) := by
    simp only [det3]; linarith
  have G2 : 0 < det3 (M 0 0) (M 0 1) (M 0 3) (M 1 0) (M 1 1) (M 1 3) (M 3 0) (M 3 1) (M 3 3) := by
    simp only [det3]; linarith
  refine ⟨by rw [E1]; exact G1, by rw [E2]; exact G2, ?_⟩
  unfold cosS
  rw [E1, E2, E3]
  have hlt : det3 (M 0 0) (M 0 1) (M 0 3) (M 1 0) (M 1 1) (M 1 3) (M 2 0) (M 2 1) (M 2 3) ^ 2 <
      det3 (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2) *
        det3 (M 0 0) (M 0 1) (M 0 3) (M 1 0) (M 1 1) (M 1 3) (M 3 0) (M 3 1) (M 3 3) := by
    have hg3 : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0 := by linarith
    nlinarith [mul_pos hg3 g4]
  rw [div_pow, Real.sq_sqrt (mul_pos G1 G2).le, sub_pos, div_lt_one (mul_pos G1 G2)]
  exact hlt

/-- The edge vectors from `hP h` of the orthoscheme, as the columns of a matrix. -/
def edgeMat4 (h : Fin 10) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => (![kv4 (hQ h) i, kv4 (hR h) i, kv4 (hS h) i, kv4 (hU h) i] j
    - kv4 (hP h) i)

/-- The four edge vectors of the orthoscheme from the first hinge vertex are independent. -/
theorem edgeMat4_det_ne (h : Fin 10) : (edgeMat4 h).det ≠ 0 := by
  fin_cases h <;>
    simp [edgeMat4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, kv4,
      hP, hQ, hR, hS, hU]

/-- Every coordinate permutation `perms4 σ` is surjective. -/
theorem perms4_surj (σ : Fin 24) : Function.Surjective (perms4 σ) := by
  fin_cases σ <;> decide

variable (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)

/-- **The Gram tetrahedra are admissible (dimension 4).** For a positive definite `g m` every
incidence of the Kuhn triangulation has admissible squared lengths: this is the `valid` field of
`JetStarCore4`. -/
theorem valid4_incQ {m : Fin 4 → ℝ} (hG : (g m).PosDef) (σ : Fin 24) (h : Fin 10) :
    Valid4 (hP h) (hQ h) (hR h) (hS h) (hU h) (incQ4 g m σ h) := by
  have hinj0 : Function.Injective (edgeMat4 h).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (edgeMat4_det_ne h)))
  have hcoef : ∀ (j : Fin 4) (i : Fin 4),
      (![kpos4 σ h (hQ h), kpos4 σ h (hR h), kpos4 σ h (hS h), kpos4 σ h (hU h)] j
        - kpos4 σ h (hP h)) i = edgeMat4 h (perms4 σ i) j := by
    intro j i
    fin_cases j <;> simp [kpos4, edgeMat4]
  have hinj : Function.Injective (Matrix.of fun i j : Fin 4 =>
      (![kpos4 σ h (hQ h), kpos4 σ h (hR h), kpos4 σ h (hS h), kpos4 σ h (hU h)] j
        - kpos4 σ h (hP h)) i).mulVec := by
    intro c c' hcc
    apply hinj0
    funext k
    obtain ⟨i, rfl⟩ := perms4_surj σ k
    have := congrFun hcc i
    simpa [Matrix.mulVec, dotProduct, hcoef] using this
  have key := valid4_gram hG (kpos4 σ h) (hP h) (hQ h) (hR h) (hS h) (hU h) hinj
  have e : incQ4 g m σ h =
      fun a b => (kpos4 σ h b - kpos4 σ h a) ⬝ᵥ (g m *ᵥ (kpos4 σ h b - kpos4 σ h a)) := by
    funext a b
    rfl
  rw [e]
  exact key

end Lightlike.Regge4
