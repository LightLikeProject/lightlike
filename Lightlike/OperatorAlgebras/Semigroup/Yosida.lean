import Lightlike.OperatorAlgebras.Semigroup.Resolvent

/-!
# The Yosida approximants of a Hille–Yosida operator

For `A` satisfying `HYHyp` let `R l = (l - A)⁻¹` for `l > 0` (`HYHyp.res`). Then:

* `R l (A x) = l R l x - x` for `x ∈ dom A`;
* `l R l x → x` as `l → ∞`, for every `x` (a bounded family converging on the dense set `dom A`);
* the resolvents commute (resolvent identity);
* the **Yosida approximant** `Yos l = l² R l - l ∈ B(X)` satisfies `Yos l x = l R l (A x) → A x` for
  `x ∈ dom A`.

## References

* Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
  <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, Section 1: the resolvent
  of a contraction-generator and the Yosida approximation.
-/

open Filter Topology
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **A bounded family of operators converging on a dense set converges everywhere.** If `‖u i‖ ≤ 1`
and `u i x → x` for `x` in a dense set, then `u i x → x` for all `x`. -/
theorem tendsto_apply_of_dense {ι : Type*} {F : Filter ι} {D : Set X} (hD : Dense D)
    (u : ι → X →L[𝕜] X) (hu : ∀ i, ‖u i‖ ≤ 1) (hconv : ∀ x ∈ D, Tendsto (fun i => u i x) F (𝓝 x))
    (x : X) : Tendsto (fun i => u i x) F (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hyD, hy⟩ := hD.exists_dist_lt x (show 0 < ε / 3 by positivity)
  have h1 := Metric.tendsto_nhds.1 (hconv y hyD) (ε / 3) (by positivity)
  filter_upwards [h1] with i hi
  have hxy : dist x y < ε / 3 := hy
  have h2 : dist (u i x) (u i y) ≤ dist x y := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    calc ‖u i (x - y)‖ ≤ ‖u i‖ * ‖x - y‖ := (u i).le_opNorm _
      _ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right (hu i) (norm_nonneg _)
      _ = ‖x - y‖ := one_mul _
  calc dist (u i x) x ≤ dist (u i x) (u i y) + dist (u i y) y + dist y x := dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have := dist_comm y x
        linarith
    _ = ε := by ring

variable [CompleteSpace X] {A : X →ₗ.[𝕜] X}

open Classical in
/-- The resolvent `R l = (l - A)⁻¹` for `l > 0` (and `0` for `l ≤ 0`). -/
def HYHyp.res (h : HYHyp A) (l : ℝ) : X →L[𝕜] X :=
  if hl : 0 < l then Classical.choose (h.exists_resolvent hl) else 0

variable (h : HYHyp A)

lemma HYHyp.res_norm_le {l : ℝ} (hl : 0 < l) : ‖h.res l‖ ≤ l⁻¹ := by
  have := (Classical.choose_spec (h.exists_resolvent hl)).1
  simpa [HYHyp.res, hl] using this

lemma HYHyp.res_mem {l : ℝ} (hl : 0 < l) (y : X) :
    ∃ x : A.domain, (x : X) = h.res l y ∧ (l : 𝕜) • (x : X) - A x = y := by
  have := (Classical.choose_spec (h.exists_resolvent hl)).2.1 y
  simpa [HYHyp.res, hl] using this

lemma HYHyp.res_apply {l : ℝ} (hl : 0 < l) (x : A.domain) :
    h.res l ((l : 𝕜) • (x : X) - A x) = x := by
  have := (Classical.choose_spec (h.exists_resolvent hl)).2.2 x
  simpa [HYHyp.res, hl] using this

/-- `R l (A x) = l R l x - x` for `x ∈ dom A`. -/
lemma HYHyp.res_A {l : ℝ} (hl : 0 < l) (x : A.domain) :
    h.res l (A x) = (l : 𝕜) • h.res l (x : X) - x := by
  have := h.res_apply hl x
  rw [map_sub, map_smul] at this
  exact eq_sub_of_add_eq (sub_eq_iff_eq_add'.1 this).symm

/-- `l R l x → x` as `l → ∞`, for every `x`. -/
theorem HYHyp.tendsto_res (x : X) :
    Tendsto (fun n : ℕ => ((n + 1 : ℝ) : 𝕜) • h.res (n + 1) x) atTop (𝓝 x) := by
  refine tendsto_apply_of_dense (F := atTop) (D := (A.domain : Set X)) h.dense
    (fun n : ℕ => (((n + 1 : ℝ) : 𝕜)) • h.res ((n : ℝ) + 1)) ?_ ?_ x
  · intro n
    have hl : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have := h.res_norm_le hl
    calc ‖(((n : ℝ) + 1 : ℝ) : 𝕜) • h.res ((n : ℝ) + 1)‖
        ≤ ‖(((n : ℝ) + 1 : ℝ) : 𝕜)‖ * ‖h.res ((n : ℝ) + 1)‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = ((n : ℝ) + 1) * ‖h.res ((n : ℝ) + 1)‖ := by rw [RCLike.norm_ofReal, abs_of_pos hl]
      _ ≤ ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := mul_le_mul_of_nonneg_left this hl.le
      _ = 1 := mul_inv_cancel₀ hl.ne'
  · intro x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => ‖A ⟨x, hx⟩‖ * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ‖A ⟨x, hx⟩‖
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have hl : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have e : (((n : ℝ) + 1 : ℝ) : 𝕜) • h.res ((n : ℝ) + 1) x - x =
        h.res ((n : ℝ) + 1) (A ⟨x, hx⟩) := by
      rw [h.res_A hl ⟨x, hx⟩]
    simp only [ContinuousLinearMap.smul_apply]
    rw [e]
    calc ‖h.res ((n : ℝ) + 1) (A ⟨x, hx⟩)‖ ≤ ‖h.res ((n : ℝ) + 1)‖ * ‖A ⟨x, hx⟩‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((n : ℝ) + 1)⁻¹ * ‖A ⟨x, hx⟩‖ :=
          mul_le_mul_of_nonneg_right (h.res_norm_le hl) (norm_nonneg _)
      _ = ‖A ⟨x, hx⟩‖ * (1 / ((n : ℝ) + 1)) := by rw [one_div, mul_comm]

/-- The **resolvent identity**: `R l y - R μ y = (μ - l) R μ (R l y)`. -/
lemma HYHyp.res_sub {l μ : ℝ} (hl : 0 < l) (hμ : 0 < μ) (y : X) :
    h.res l y - h.res μ y = ((μ - l : ℝ) : 𝕜) • h.res μ (h.res l y) := by
  obtain ⟨x, hx1, hx2⟩ := h.res_mem hl y
  have h3 : (μ : 𝕜) • (x : X) - A x = ((μ - l : ℝ) : 𝕜) • (x : X) + y := by
    rw [← hx2]
    push_cast
    rw [sub_smul]
    abel
  have h4 := h.res_apply hμ x
  rw [h3, map_add, map_smul, hx1] at h4
  have h5 : h.res l y = h.res μ y + ((μ - l : ℝ) : 𝕜) • h.res μ (h.res l y) := by
    rw [add_comm]; exact h4.symm
  exact sub_eq_iff_eq_add'.2 h5

/-- The resolvents commute. -/
lemma HYHyp.res_comm {l μ : ℝ} (hl : 0 < l) (hμ : 0 < μ) :
    (h.res l).comp (h.res μ) = (h.res μ).comp (h.res l) := by
  ext y
  simp only [ContinuousLinearMap.comp_apply]
  by_cases hlμ : l = μ
  · rw [hlμ]
  · have e1 := h.res_sub hl hμ y
    have e2 := h.res_sub hμ hl y
    have hne : ((μ - l : ℝ) : 𝕜) ≠ 0 := by
      rw [Ne, RCLike.ofReal_eq_zero, sub_eq_zero]; exact fun h' => hlμ h'.symm
    have e3 : ((μ - l : ℝ) : 𝕜) • h.res μ (h.res l y) = ((μ - l : ℝ) : 𝕜) • h.res l (h.res μ y) := by
      have hc : ((l - μ : ℝ) : 𝕜) = -((μ - l : ℝ) : 𝕜) := by push_cast; ring
      have e2' : h.res l y - h.res μ y = ((μ - l : ℝ) : 𝕜) • h.res l (h.res μ y) := by
        rw [← neg_sub, e2, hc, neg_smul, neg_neg]
      exact e1.symm.trans e2'
    exact (smul_right_injective X hne e3).symm

/-- The **Yosida approximant** `l² R l - l`. -/
def HYHyp.yos (l : ℝ) : X →L[𝕜] X := ((l ^ 2 : ℝ) : 𝕜) • h.res l - (l : 𝕜) • (1 : X →L[𝕜] X)

/-- `yos l x = l R l (A x)` for `x ∈ dom A`. -/
lemma HYHyp.yos_apply {l : ℝ} (hl : 0 < l) (x : A.domain) :
    h.yos l (x : X) = (l : 𝕜) • h.res l (A x) := by
  rw [h.res_A hl x]
  simp only [HYHyp.yos, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_sub, smul_smul]
  push_cast
  rw [pow_two]

/-- `yos (n+1) x → A x` for `x ∈ dom A`. -/
theorem HYHyp.tendsto_yos (x : A.domain) :
    Tendsto (fun n : ℕ => h.yos ((n : ℝ) + 1) (x : X)) atTop (𝓝 (A x)) := by
  have := h.tendsto_res (A x)
  refine this.congr fun n => ?_
  rw [h.yos_apply (by positivity)]

end Lightlike.OperatorAlgebras
