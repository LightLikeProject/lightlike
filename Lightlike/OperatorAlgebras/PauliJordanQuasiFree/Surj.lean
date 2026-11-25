import Mathlib

/-!
# G2-077: a linear-algebra lemma behind surjectivity of the one-particle map

For a real antisymmetric `T` and a real symmetric `U` on a finite-dimensional real inner
product space with `U T = T U` and `U² = -T²` (the situation `T = Δ`, `U = |Δ|`), every
equation `S y = -T b`, `T y = U b` is solvable.  This is the real-solvability statement
`∃ y, (U + iT)(ib - y) = 0` needed to show that the real-linear one-particle map
`f ↦ √P f` has dense (indeed full) range.
-/

namespace Lightlike.OperatorAlgebras.PauliJordanQuasiFree

open Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- If `⟪T x, y⟫ = c ⟪x, T y⟫` with `c ≠ 0`, then `(range T)ᗮ = ker T`. -/
lemma orth_range_eq_ker (T : E →ₗ[ℝ] E) {c : ℝ} (hc : c ≠ 0)
    (hT : ∀ x y, inner ℝ (T x) y = c * inner ℝ x (T y)) :
    (LinearMap.range T)ᗮ = LinearMap.ker T := by
  ext x
  rw [mem_orthogonal, LinearMap.mem_ker]
  constructor
  · intro h
    have h1 := h (T (T x)) ⟨T x, rfl⟩
    rw [hT] at h1
    have : inner ℝ (T x) (T x) = 0 := by
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hc
      · simpa using h2
    exact inner_self_eq_zero.mp this
  · rintro h _ ⟨w, rfl⟩
    rw [hT, h]; simp

/-- Under `⟪T x, y⟫ = c ⟪x, T y⟫`, `range T = (ker T)ᗮ`. -/
lemma range_eq_orth_ker (T : E →ₗ[ℝ] E) {c : ℝ} (hc : c ≠ 0)
    (hT : ∀ x y, inner ℝ (T x) y = c * inner ℝ x (T y)) :
    LinearMap.range T = (LinearMap.ker T)ᗮ := by
  rw [← orth_range_eq_ker T hc hT, orthogonal_orthogonal]

/-- **Solvability lemma.** `T` antisymmetric, `U` symmetric, commuting, `U² = -T²`:
for every `b` there is `y` with `U y = -T b` and `T y = U b`. -/
theorem exists_solve (T U : E →ₗ[ℝ] E)
    (hT : ∀ x y, inner ℝ (T x) y = -1 * inner ℝ x (T y))
    (hU : ∀ x y, inner ℝ (U x) y = 1 * inner ℝ x (U y))
    (hcomm : ∀ x, U (T x) = T (U x)) (hsq : ∀ x, U (U x) = -T (T x)) (b : E) :
    ∃ y, U y = -T b ∧ T y = U b := by
  have hkerT : LinearMap.ker U = LinearMap.ker T := by
    ext x
    simp only [LinearMap.mem_ker]
    constructor
    · intro h
      have h1 : inner ℝ (T x) (T x) = 0 := by
        rw [hT, ← neg_eq_neg_one_mul, neg_eq_zero]
        have : T (T x) = 0 := by
          have := hsq x
          rw [h, map_zero] at this
          simpa using this.symm
        rw [this]; simp
      exact inner_self_eq_zero.mp h1
    · intro h
      have h1 : inner ℝ (U x) (U x) = 0 := by
        rw [hU, one_mul]
        have : U (U x) = 0 := by rw [hsq x, h, map_zero, neg_zero]
        rw [this]; simp
      exact inner_self_eq_zero.mp h1
  have hrU : LinearMap.range U = LinearMap.range T := by
    rw [range_eq_orth_ker U one_ne_zero hU, range_eq_orth_ker T (by norm_num) hT, hkerT]
  have hmem : U b ∈ LinearMap.range T := hrU ▸ ⟨b, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_, hy⟩
  set z := U y + T b with hz
  have hzr : z ∈ LinearMap.range T := by
    refine add_mem (hrU ▸ ⟨y, rfl⟩) ⟨b, rfl⟩
  have hzk : z ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, hz, map_add, ← hcomm y, hy, hsq b]
    simp
  have hzo : z ∈ (LinearMap.range T)ᗮ := by
    rw [orth_range_eq_ker T (by norm_num) hT]; exact hzk
  have : z = 0 := by
    have := inner_self_eq_zero (𝕜 := ℝ) (x := z)
    exact this.mp (hzo z hzr)
  rw [eq_neg_iff_add_eq_zero, hz] at *
  exact this

end Lightlike.OperatorAlgebras.PauliJordanQuasiFree

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.exists_solve := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.exists_solve
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.orth_range_eq_ker := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.orth_range_eq_ker
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G2_077.range_eq_orth_ker := _root_.Lightlike.OperatorAlgebras.PauliJordanQuasiFree.range_eq_orth_ker
