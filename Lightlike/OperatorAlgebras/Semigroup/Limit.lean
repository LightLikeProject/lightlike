import Lightlike.OperatorAlgebras.Semigroup.CauchyEstimate
import Lightlike.OperatorAlgebras.Semigroup.ExpMVT

/-!
# The limit of the approximating semigroups

For `A` satisfying `HYHyp` let `T n t = exp (t Yos (n + 1))`. The Cauchy estimate and density show
that for every `x` and `T₀` the sequence `T n t x` is uniformly Cauchy in `t ∈ [0, T₀]`
(`HYHyp.exists_uniform_cauchy`); its limit `HYHyp.lim t x` is therefore uniform on compact intervals
(`HYHyp.exists_uniform_tendsto`).

## References

* Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
  <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, proof of Theorem 1.9.
-/

open NormedSpace Filter Topology Set
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {A : X →ₗ.[𝕜] X} (h : HYHyp A)

/-- The approximating contractions `T n t = exp (t Yos (n + 1))`. -/
def HYHyp.T (n : ℕ) (t : ℝ) : X →L[𝕜] X := exp (((t : ℝ) : 𝕜) • h.yos ((n : ℝ) + 1))

lemma HYHyp.T_norm_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖h.T n t‖ ≤ 1 :=
  h.norm_exp_yos_le (by positivity) ht

lemma HYHyp.T_apply_norm_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : X) : ‖h.T n t x‖ ≤ ‖x‖ :=
  ((h.T n t).le_opNorm x).trans (by simpa using mul_le_mul_of_nonneg_right (h.T_norm_le n ht) (norm_nonneg x))

/-- **Uniform Cauchy property on the domain of `A`.** -/
lemma HYHyp.exists_uniform_cauchy_dom (x : A.domain) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ t : ℝ, 0 ≤ t → t ≤ T₀ →
      ‖h.T m t (x : X) - h.T n t (x : X)‖ ≤ ε := by
  have hc : CauchySeq fun n : ℕ => h.yos ((n : ℝ) + 1) (x : X) := (h.tendsto_yos x).cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hc (ε / (2 * (T₀ + 1))) (by positivity)
  refine ⟨N, fun m hm n hn t ht0 htT => ?_⟩
  have h1 := hN m hm
  have h2 := hN n hn
  have h3 : ‖h.yos ((m : ℝ) + 1) (x : X) - h.yos ((n : ℝ) + 1) (x : X)‖ < ε / (T₀ + 1) := by
    have := dist_triangle_right (h.yos ((m : ℝ) + 1) (x : X)) (h.yos ((n : ℝ) + 1) (x : X))
      (h.yos ((N : ℝ) + 1) (x : X))
    simp only [dist_eq_norm] at this h1 h2
    have e : ε / (T₀ + 1) = ε / (2 * (T₀ + 1)) + ε / (2 * (T₀ + 1)) := by field_simp; ring
    linarith
  calc ‖h.T m t (x : X) - h.T n t (x : X)‖
      ≤ t * ‖h.yos ((m : ℝ) + 1) (x : X) - h.yos ((n : ℝ) + 1) (x : X)‖ :=
        h.norm_exp_yos_sub_le (by positivity) (by positivity) ht0 (x : X)
    _ ≤ T₀ * (ε / (T₀ + 1)) := by
        apply mul_le_mul htT h3.le (norm_nonneg _) hT₀
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith

/-- **Uniform Cauchy property on compact time intervals, for every `x`** (density of the domain and
the contraction property). -/
lemma HYHyp.exists_uniform_cauchy (x : X) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ t : ℝ, 0 ≤ t → t ≤ T₀ → ‖h.T m t x - h.T n t x‖ ≤ ε := by
  obtain ⟨y, hyD, hy⟩ := h.dense.exists_dist_lt x (show 0 < ε / 4 by positivity)
  obtain ⟨N, hN⟩ := h.exists_uniform_cauchy_dom ⟨y, hyD⟩ hT₀ (show 0 < ε / 2 by positivity)
  refine ⟨N, fun m hm n hn t ht0 htT => ?_⟩
  have hxy : ‖x - y‖ < ε / 4 := by rwa [← dist_eq_norm]
  have e : h.T m t x - h.T n t x =
      h.T m t (x - y) + (h.T m t y - h.T n t y) + h.T n t (y - x) := by
    simp only [map_sub]; abel
  rw [e]
  calc ‖h.T m t (x - y) + (h.T m t y - h.T n t y) + h.T n t (y - x)‖
      ≤ ‖h.T m t (x - y)‖ + ‖h.T m t y - h.T n t y‖ + ‖h.T n t (y - x)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _ |>.trans_eq' rfl |> fun h' => by
          linarith [norm_add_le (h.T m t (x - y) + (h.T m t y - h.T n t y)) (h.T n t (y - x)),
            norm_add_le (h.T m t (x - y)) (h.T m t y - h.T n t y)])
    _ ≤ ‖x - y‖ + ε / 2 + ‖y - x‖ := by
        gcongr
        · exact h.T_apply_norm_le m ht0 _
        · exact hN m hm n hn t ht0 htT
        · exact h.T_apply_norm_le n ht0 _
    _ ≤ ε := by
        rw [norm_sub_rev y x]
        linarith

lemma HYHyp.cauchySeq_T (x : X) {t : ℝ} (ht : 0 ≤ t) : CauchySeq fun n : ℕ => h.T n t x := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h.exists_uniform_cauchy x ht (show 0 < ε / 2 by positivity)
  exact ⟨N, fun m hm n hn => by
    rw [dist_eq_norm]
    exact (hN m hm n hn t ht le_rfl).trans_lt (by linarith)⟩

open Classical in
/-- The limit `lim_{n→∞} T n t x`. -/
def HYHyp.lim (t : ℝ) (x : X) : X := limUnder atTop fun n : ℕ => h.T n t x

lemma HYHyp.tendsto_lim (x : X) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => h.T n t x) atTop (𝓝 (h.lim t x)) :=
  (h.cauchySeq_T x ht).tendsto_limUnder

/-- **Uniform convergence on compact time intervals.** -/
lemma HYHyp.exists_uniform_tendsto (x : X) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, 0 ≤ t → t ≤ T₀ → ‖h.T n t x - h.lim t x‖ ≤ ε := by
  obtain ⟨N, hN⟩ := h.exists_uniform_cauchy x hT₀ hε
  refine ⟨N, fun n hn t ht0 htT => ?_⟩
  have hlim := (tendsto_const_nhds (x := h.T n t x)).sub (h.tendsto_lim x ht0)
  refine le_of_tendsto hlim.norm ?_
  filter_upwards [eventually_ge_atTop N] with m hm
  exact hN n hn m hm t ht0 htT

end Lightlike.OperatorAlgebras
