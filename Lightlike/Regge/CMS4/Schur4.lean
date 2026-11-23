import Mathlib
import Lightlike.Regge.CMS4.Valid4

/-!
# Schur complement of a `4 × 4` determinant with a `2 × 2` corner

The dihedral angle at a triangle of a 4-simplex is an angle in the plane quotient by the two edge
vectors of the triangle. The quotient form is a Schur complement. This file proves, for an
arbitrary `4 × 4` matrix with invertible upper-left `2 × 2` block, the block-determinant formula in
the explicit form used for the Gram identities of the plane fan.

## Main results

* `schur4`: `det n = det n₁₁ * det (n₂₂ - n₂₁ n₁₁⁻¹ n₁₂)`, with the inverse written out.
-/

open Matrix

namespace Lightlike.Regge4

/-- The Schur complement entry `(i, j)` of a `4 × 4` matrix with respect to its upper-left
`2 × 2` block, `n(2+i, 2+j) - (n(2+i, 0), n(2+i, 1)) · N₁₁⁻¹ · (n(0, 2+j), n(1, 2+j))ᵀ`, with the
inverse of the block written out. -/
noncomputable def schurE (n : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 2) : ℝ :=
  n (i.succ.succ) (j.succ.succ)
    - (n i.succ.succ 0 * (n 1 1 * n 0 j.succ.succ - n 0 1 * n 1 j.succ.succ)
      + n i.succ.succ 1 * (n 0 0 * n 1 j.succ.succ - n 1 0 * n 0 j.succ.succ))
      / (n 0 0 * n 1 1 - n 0 1 * n 1 0)

/-- **Block determinant formula**: for a `4 × 4` matrix with invertible upper-left `2 × 2` block,
`det n = det (block) * det (Schur complement)`. -/
theorem schur4 (n : Matrix (Fin 4) (Fin 4) ℝ) (hD : n 0 0 * n 1 1 - n 0 1 * n 1 0 ≠ 0) :
    n.det = (n 0 0 * n 1 1 - n 0 1 * n 1 0) *
      (schurE n 0 0 * schurE n 1 1 - schurE n 0 1 * schurE n 1 0) := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, schurE]
  simp [Fin.succAbove, Fin.lt_def]
  field_simp
  ring

/-- The `G`-pairing matrix of two families of four vectors: entry `(i, j)` is `aᵢᵀ G bⱼ`. -/
def pairMat (G : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4 → Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => a i ⬝ᵥ (G *ᵥ b j)

/-- `det (aᵢᵀ G bⱼ) = det a * det G * det b`. -/
theorem det_pairMat (G : Matrix (Fin 4) (Fin 4) ℝ) (a b : Fin 4 → Fin 4 → ℝ) :
    (pairMat G a b).det = (Matrix.of a).det * G.det * (Matrix.of b).det := by
  have : pairMat G a b = Matrix.of a * G * (Matrix.of b)ᵀ := by
    ext i j
    simp [pairMat, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]

/-- The `2 × 2` Gram determinant of the axis `(w₁, w₂)` for the form `G`. -/
def gramW (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ : Fin 4 → ℝ) : ℝ :=
  (w₁ ⬝ᵥ (G *ᵥ w₁)) * (w₂ ⬝ᵥ (G *ᵥ w₂)) - (w₁ ⬝ᵥ (G *ᵥ w₂)) * (w₂ ⬝ᵥ (G *ᵥ w₁))

/-- The quotient form of `G` by the plane `span (w₁, w₂)`: the Schur complement
`uᵀGv - (uᵀG W)(Wᵀ G W)⁻¹ (Wᵀ G v)`. -/
noncomputable def bf2 (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ u v : Fin 4 → ℝ) : ℝ :=
  u ⬝ᵥ (G *ᵥ v)
    - ((u ⬝ᵥ (G *ᵥ w₁)) * ((w₂ ⬝ᵥ (G *ᵥ w₂)) * (w₁ ⬝ᵥ (G *ᵥ v))
        - (w₁ ⬝ᵥ (G *ᵥ w₂)) * (w₂ ⬝ᵥ (G *ᵥ v)))
      + (u ⬝ᵥ (G *ᵥ w₂)) * ((w₁ ⬝ᵥ (G *ᵥ w₁)) * (w₂ ⬝ᵥ (G *ᵥ v))
        - (w₂ ⬝ᵥ (G *ᵥ w₁)) * (w₁ ⬝ᵥ (G *ᵥ v)))) / gramW G w₁ w₂

/-- The oriented area form on the plane quotient: `det (w₁, w₂, u, v)`. -/
def det4 (w₁ w₂ u v : Fin 4 → ℝ) : ℝ := (Matrix.of ![w₁, w₂, u, v]).det

/-- **Polarized Gram identity for the plane quotient**: for two pairs `(t, u)` and `(t', v)`
the `2 × 2` determinant of the quotient form is
`det G · det(w₁,w₂,t,u) · det(w₁,w₂,t',v) / gramW`. -/
theorem bf2_gram (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ t u t' v : Fin 4 → ℝ)
    (hD : gramW G w₁ w₂ ≠ 0) :
    bf2 G w₁ w₂ t t' * bf2 G w₁ w₂ u v - bf2 G w₁ w₂ t v * bf2 G w₁ w₂ u t'
      = G.det * det4 w₁ w₂ t u * det4 w₁ w₂ t' v / gramW G w₁ w₂ := by
  have h := schur4 (pairMat G ![w₁, w₂, t, u] ![w₁, w₂, t', v]) (by
    simpa [pairMat, gramW] using hD)
  rw [det_pairMat] at h
  have e : ∀ i j : Fin 2, schurE (pairMat G ![w₁, w₂, t, u] ![w₁, w₂, t', v]) i j =
      bf2 G w₁ w₂ (![t, u] i) (![t', v] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [schurE, pairMat, bf2, gramW]
  rw [e, e, e, e] at h
  have hD' : (pairMat G ![w₁, w₂, t, u] ![w₁, w₂, t', v]) 0 0 *
      (pairMat G ![w₁, w₂, t, u] ![w₁, w₂, t', v]) 1 1
      - (pairMat G ![w₁, w₂, t, u] ![w₁, w₂, t', v]) 0 1 *
      (pairMat G ![w₁, w₂, t, u] ![w₁, w₂, t', v]) 1 0 = gramW G w₁ w₂ := by
    simp [pairMat, gramW]
  rw [hD'] at h
  rw [eq_div_iff hD]
  unfold det4
  have h' : (Matrix.of ![w₁, w₂, t, u]).det * G.det * (Matrix.of ![w₁, w₂, t', v]).det =
      gramW G w₁ w₂ * (bf2 G w₁ w₂ t t' * bf2 G w₁ w₂ u v
        - bf2 G w₁ w₂ t v * bf2 G w₁ w₂ u t') := h
  linarith

/-- A `3 × 3` determinant of `G`-pairings against the axis is the axis Gram determinant times the
quotient form: `det [[⟨w₁,w₁⟩, ⟨w₁,w₂⟩, ⟨w₁,b⟩], [⟨w₂,w₁⟩, ⟨w₂,w₂⟩, ⟨w₂,b⟩],
[⟨a,w₁⟩, ⟨a,w₂⟩, ⟨a,b⟩]] = gramW * bf2 a b`. -/
theorem det3_eq_gramW_mul_bf2 (G : Matrix (Fin 4) (Fin 4) ℝ) (w₁ w₂ a b : Fin 4 → ℝ)
    (hD : gramW G w₁ w₂ ≠ 0) :
    det3 (w₁ ⬝ᵥ (G *ᵥ w₁)) (w₁ ⬝ᵥ (G *ᵥ w₂)) (w₁ ⬝ᵥ (G *ᵥ b))
      (w₂ ⬝ᵥ (G *ᵥ w₁)) (w₂ ⬝ᵥ (G *ᵥ w₂)) (w₂ ⬝ᵥ (G *ᵥ b))
      (a ⬝ᵥ (G *ᵥ w₁)) (a ⬝ᵥ (G *ᵥ w₂)) (a ⬝ᵥ (G *ᵥ b)) = gramW G w₁ w₂ * bf2 G w₁ w₂ a b := by
  unfold bf2
  field_simp
  simp only [det3, gramW]
  ring

/-- **The dihedral angle of a Gram simplex is an angle in the plane quotient.** For five points `x`
of `ℝ⁴` with the squared lengths of a symmetric form `B`, the cosine of the dihedral angle at the
triangle `pqr` between the tetrahedra `pqrt` and `pqru` is
`bf2 a b / √(bf2 a a · bf2 b b)` for `a = x t - x p`, `b = x u - x p`, with axis
`(x q - x p, x r - x p)`. -/
theorem cosS_gram {B : Matrix (Fin 4) (Fin 4) ℝ} (hs : Bᵀ = B) (x : Fin 5 → Fin 4 → ℝ)
    (p q r t u : Fin 5) (hD : 0 < gramW B (x q - x p) (x r - x p)) :
    cosS (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p q r t u =
      bf2 B (x q - x p) (x r - x p) (x t - x p) (x u - x p) /
        √(bf2 B (x q - x p) (x r - x p) (x t - x p) (x t - x p) *
          bf2 B (x q - x p) (x r - x p) (x u - x p) (x u - x p)) := by
  have ip_eq : ∀ a b : Fin 5, ipS (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p a b
      = (x a - x p) ⬝ᵥ (B *ᵥ (x b - x p)) := by
    intro a b
    unfold ipS
    rw [← polar4 hs (x a - x p) (x b - x p), sub_sub_sub_cancel_right]
  have h1 := det3_eq_gramW_mul_bf2 B (x q - x p) (x r - x p) (x t - x p) (x u - x p) hD.ne'
  have h2 := det3_eq_gramW_mul_bf2 B (x q - x p) (x r - x p) (x t - x p) (x t - x p) hD.ne'
  have h3 := det3_eq_gramW_mul_bf2 B (x q - x p) (x r - x p) (x u - x p) (x u - x p) hD.ne'
  have hsym : ∀ a b : Fin 4 → ℝ, a ⬝ᵥ (B *ᵥ b) = b ⬝ᵥ (B *ᵥ a) := fun a b => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs, dotProduct_comm]
  have eM : mixedS (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p q r t u =
      gramW B (x q - x p) (x r - x p) *
        bf2 B (x q - x p) (x r - x p) (x t - x p) (x u - x p) := by
    rw [← h1]
    simp only [mixedS, ip_eq]
  have eT : gram3S (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p q r t =
      gramW B (x q - x p) (x r - x p) *
        bf2 B (x q - x p) (x r - x p) (x t - x p) (x t - x p) := by
    rw [← h2]
    simp only [gram3S, ip_eq]
  have eU : gram3S (fun a b => (x b - x a) ⬝ᵥ (B *ᵥ (x b - x a))) p q r u =
      gramW B (x q - x p) (x r - x p) *
        bf2 B (x q - x p) (x r - x p) (x u - x p) (x u - x p) := by
    rw [← h3]
    simp only [gram3S, ip_eq]
  unfold cosS
  rw [eM, eT, eU]
  have : gramW B (x q - x p) (x r - x p) * bf2 B (x q - x p) (x r - x p) (x t - x p) (x t - x p) *
      (gramW B (x q - x p) (x r - x p) * bf2 B (x q - x p) (x r - x p) (x u - x p) (x u - x p))
      = (gramW B (x q - x p) (x r - x p)) ^ 2 *
        (bf2 B (x q - x p) (x r - x p) (x t - x p) (x t - x p) *
          bf2 B (x q - x p) (x r - x p) (x u - x p) (x u - x p)) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD.le]
  by_cases hz : √(bf2 B (x q - x p) (x r - x p) (x t - x p) (x t - x p) *
      bf2 B (x q - x p) (x r - x p) (x u - x p) (x u - x p)) = 0
  · rw [hz]; simp
  · field_simp

end Lightlike.Regge4
