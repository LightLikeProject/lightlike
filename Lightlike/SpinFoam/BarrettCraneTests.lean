import Lightlike.SpinFoam.BarrettCrane
import Lightlike.Spin4.VertexTests

/-!
# Checks of the Barrett–Crane vertex

* **Value at spin `0`:** `1`.
* **The closed loop.** Spin `j/2` on the four edges of the cycle `0-3-1-4-0` of `K₅` and `0`
  elsewhere: every node has a single intertwiner, and the vertex is `1/(j + 1)²`, the square of the
  15j value `1/(j + 1)` (`fifteenJSimplex_cycle_spin`). For `j = 1` (spin `1/2`) this is `1/4`.
* **Wrong input:** the representation `(1/2, 0)` is not simple, and the weak simplicity constraint
  fails for it, while it holds for `(1/2, 1/2)`.
-/

open Finset Matrix Lightlike.Recoupling Lightlike.Spin4 Lightlike.Pentagon

namespace Lightlike.SpinFoam.BC.Tests

/-- The doubled spins of the closed loop. -/
def cyc (j : ℕ) : Fin 10 → ℕ := ![0, 0, j, j, 0, j, j, 0, 0, 0]

lemma channel_zero4 : channel 0 0 0 0 = {0} := by decide

lemma channel_00jj (j : ℕ) : channel 0 0 j j = {0} := by
  ext z; simp only [channel, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, h1, -⟩
    have := h1.2.1; have := h1.2.2; have := h1.1; omega
  · rintro rfl; refine ⟨by omega, ?_⟩; unfold Tri; omega

lemma channel_jj00 (j : ℕ) : channel j j 0 0 = {0} := by
  ext z; simp only [channel, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, -, h1⟩
    unfold Tri at h1; omega
  · rintro rfl; refine ⟨by omega, ?_⟩; unfold Tri; omega

lemma channel_0jj0 (j : ℕ) : channel 0 j j 0 = {j} := by
  ext z; simp only [channel, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, h1, h2⟩
    unfold Tri at h1 h2; omega
  · rintro rfl; refine ⟨by omega, ?_⟩; unfold Tri; omega

/-- **Value check (the closed loop).** The vertex of the loop is `1/(j + 1)²`, for every `j`. -/
theorem bcVertex_cyc (j : ℕ) : bcVertex (cyc j) = (((1 : ℝ) / ((j : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
  rw [bcVertex_eq_sum]
  have hch : nodeChans (cyc j) = fun a => {(![0, j, 0, j, 0] : Fin 5 → ℕ) a} := by
    funext a
    fin_cases a <;> simp [nodeChans, cyc, k5Spins, channel_00jj, channel_jj00,
      channel_0jj0]
  rw [hch, Fintype.piFinset_singleton, sum_singleton]
  simp only [cyc, Matrix.cons_val]
  rw [Lightlike.Spin4.VertexTests.fifteenJSimplex_cycle_spin]
  push_cast
  field_simp

lemma channel_j00j (j : ℕ) : channel j 0 0 j = {j} := by
  ext z; simp only [channel, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨-, h1, h2⟩
    unfold Tri at h1 h2; omega
  · rintro rfl; refine ⟨by omega, ?_⟩; unfold Tri; omega

/-- The doubled spins of the triangle: spin `j/2` on the edges `01, 02, 12` of `K₅`. -/
def triangle (j : ℕ) : Fin 10 → ℕ := ![j, j, 0, 0, j, 0, 0, 0, 0, 0]

/-- **Value check (the triangle).** The vertex of the triangle is `1/(j + 1)`, the square of the
15j value `1/√(j + 1)` (`fifteenJSimplex_triangle`), for every `j`. -/
theorem bcVertex_triangle (j : ℕ) :
    bcVertex (triangle j) = (((1 : ℝ) / ((j : ℝ) + 1) : ℝ) : ℂ) := by
  rw [bcVertex_eq_sum]
  have hch : nodeChans (triangle j) = fun a => {(![0, j, 0, 0, 0] : Fin 5 → ℕ) a} := by
    funext a
    fin_cases a <;> simp [nodeChans, triangle, k5Spins, channel_00jj, channel_jj00,
      channel_j00j]
  rw [hch, Fintype.piFinset_singleton, sum_singleton]
  simp only [triangle, Matrix.cons_val]
  rw [Lightlike.Spin4.VertexTests.fifteenJSimplex_triangle]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity)
  rw [← Complex.ofReal_pow]
  congr 1
  rw [div_pow, hs]; simp

/-- The edge spins of the triangle sum to `3j` in doubled units. -/
theorem sum_triangle (j : ℕ) : ∑ e, triangle j e = 3 * j := by
  simp [triangle, Fin.sum_univ_succ]; ring

/-- The edge spins of the closed loop sum to `4j` in doubled units. -/
theorem sum_cyc (j : ℕ) : ∑ e, cyc j e = 4 * j := by
  simp [cyc, Fin.sum_univ_succ]; ring

/-- **The sign bridge on the loop.** Four spins `j/2`: the sum is an integer, so the two
conventions agree: `1/(j + 1)²`. -/
theorem bcVertexBC_cyc (j : ℕ) : bcVertexBC (cyc j) = 1 / ((j : ℝ) + 1) ^ 2 := by
  rw [bcVertexBC_of_even (by rw [sum_cyc]; exact ⟨2 * j, by ring⟩), bcVertex_cyc, Complex.ofReal_re]

/-- **The sign bridge on the triangle, spin `1/2`.** The ten spins sum to `3/2`, a half-integer, so
the Baez–Christensen vertex is `-1/2`, while ours is `+1/2`. -/
theorem bcVertexBC_triangle_one : bcVertexBC (triangle 1) = -(1 / 2) := by
  rw [bcVertexBC_of_odd (by rw [sum_triangle]; exact ⟨1, by norm_num⟩), bcVertex_triangle]
  norm_num

/-- **Non-vacuity of the sign difference.** On the spin-`1/2` triangle the two conventions
disagree. -/
theorem bcVertexBC_triangle_ne : bcVertexBC (triangle 1) ≠ (bcVertex (triangle 1)).re := by
  refine bcVertexBC_ne_of_odd (by rw [sum_triangle]; exact ⟨1, by norm_num⟩) ?_
  rw [bcVertex_triangle]; norm_num

/-- **Value check.** Spin `1/2` on the loop: `1/4`. -/
theorem bcVertex_cyc_half : bcVertex (cyc 1) = (((1 / 4 : ℝ)) : ℂ) := by
  rw [bcVertex_cyc]; norm_num

/-- **Value check.** At spin `0` the vertex is `1`. -/
theorem bcVertex_zero : bcVertex 0 = 1 := by
  have := bcVertex_cyc 0
  have h : cyc 0 = 0 := by funext e; fin_cases e <;> rfl
  rw [h] at this
  rw [this]; norm_num

/-- **Wrong input.** The representation `(1/2, 0)` is not simple: weak simplicity fails. -/
theorem not_simple_half_zero :
    ¬ ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 →
        (eprlMap 1 0)ᴴ * simplicityOp 0 1 0 X * eprlMap 1 0 = 0 := by
  rw [simple_iff (by norm_num)]; norm_num

/-- **Non-vacuity.** The representation `(1/2, 1/2)` is simple. -/
theorem simple_half_half :
    ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 →
        (eprlMap 1 1)ᴴ * simplicityOp 0 1 1 X * eprlMap 1 1 = 0 :=
  (simple_iff (by norm_num)).mpr rfl

end Lightlike.SpinFoam.BC.Tests
