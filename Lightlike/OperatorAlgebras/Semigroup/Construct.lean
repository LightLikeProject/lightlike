import Lightlike.OperatorAlgebras.Semigroup.Limit

/-!
# The limit semigroup

For `A` satisfying `HYHyp`, the limit `S t = lim_{n→∞} exp (t Yos (n + 1))` defines a contraction
semigroup `HYHyp.semigroup` (the semigroup law is the limit of `exp ((s + t) Y) = exp (s Y) exp (t Y)`;
strong continuity at `0` follows on the domain of `A` from `‖S t x - x‖ ≤ t ‖A x‖` and on `X` from
the density of the domain).

## References

* Math 7334 lecture notes, Georgia Tech (Spring 2017), Section 4,
  <https://loss.math.gatech.edu/17SPRINGTEA/7334/NOTES/section4hilleyosida.pdf>, proof of Theorem 1.9.
-/

open NormedSpace Filter Topology Set NNReal
open scoped LinearPMap

noncomputable section

namespace Lightlike.OperatorAlgebras

/-- The algebra of bounded operators is a normed `ℚ`-algebra (needed for the exponential). -/
local instance instNormedAlgebraRatCLM3 {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 _

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {A : X →ₗ.[𝕜] X} (h : HYHyp A)

lemma HYHyp.lim_add (x y : X) {t : ℝ} (ht : 0 ≤ t) :
    h.lim t (x + y) = h.lim t x + h.lim t y :=
  tendsto_nhds_unique (h.tendsto_lim (x + y) ht)
    (((h.tendsto_lim x ht).add (h.tendsto_lim y ht)).congr fun n => by simp)

lemma HYHyp.lim_smul (c : 𝕜) (x : X) {t : ℝ} (ht : 0 ≤ t) : h.lim t (c • x) = c • h.lim t x :=
  tendsto_nhds_unique (h.tendsto_lim (c • x) ht)
    ((h.tendsto_lim x ht).const_smul c |>.congr fun n => by simp)

lemma HYHyp.norm_lim_le (x : X) {t : ℝ} (ht : 0 ≤ t) : ‖h.lim t x‖ ≤ ‖x‖ :=
  le_of_tendsto (h.tendsto_lim x ht).norm
    (Eventually.of_forall fun n => h.T_apply_norm_le n ht x)

/-- The limit operator `S t`, `t ≥ 0`, as a bounded operator. -/
def HYHyp.S (t : ℝ≥0) : X →L[𝕜] X :=
  LinearMap.mkContinuous
    { toFun := fun x => h.lim (t : ℝ) x
      map_add' := fun x y => h.lim_add x y t.2
      map_smul' := fun c x => h.lim_smul c x t.2 } 1
    (fun x => by simpa using h.norm_lim_le x t.2)

lemma HYHyp.S_apply (t : ℝ≥0) (x : X) : h.S t x = h.lim (t : ℝ) x := rfl

lemma HYHyp.S_norm_le (t : ℝ≥0) : ‖h.S t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma HYHyp.S_zero : h.S 0 = 1 := by
  ext x
  rw [h.S_apply]
  have : ∀ n : ℕ, h.T n 0 x = x := fun n => by simp [HYHyp.T]
  exact tendsto_nhds_unique (h.tendsto_lim x (le_refl _) |>.congr (fun n => this n)) tendsto_const_nhds
    |> fun h' => by simpa using h'

lemma HYHyp.T_add (n : ℕ) (s t : ℝ) : h.T n (s + t) = h.T n s * h.T n t := by
  unfold HYHyp.T
  rw [show (((s + t : ℝ)) : 𝕜) • h.yos ((n : ℝ) + 1) =
      ((s : ℝ) : 𝕜) • h.yos ((n : ℝ) + 1) + ((t : ℝ) : 𝕜) • h.yos ((n : ℝ) + 1) by
        push_cast; rw [add_smul]]
  exact exp_add_of_commute ((Commute.refl _).smul_left _ |>.smul_right _)

lemma HYHyp.S_add (s t : ℝ≥0) : h.S (s + t) = (h.S s).comp (h.S t) := by
  ext x
  rw [ContinuousLinearMap.comp_apply, h.S_apply, h.S_apply, h.S_apply]
  set y := h.lim (t : ℝ) x with hy
  refine tendsto_nhds_unique (h.tendsto_lim x (by positivity)) ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => ‖h.T n (t : ℝ) x - y‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (h.tendsto_lim x t.2)
  have h2 : Tendsto (fun n : ℕ => ‖h.T n (s : ℝ) y - h.lim (s : ℝ) y‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (h.tendsto_lim y s.2)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.add h2)
  have e : h.T n ((s : ℝ) + (t : ℝ)) x - h.lim (s : ℝ) y =
      h.T n (s : ℝ) (h.T n (t : ℝ) x - y) + (h.T n (s : ℝ) y - h.lim (s : ℝ) y) := by
    rw [h.T_add]
    simp only [ContinuousLinearMap.mul_apply, map_sub]
    abel
  show ‖h.T n ((s : ℝ) + (t : ℝ)) x - h.lim (s : ℝ) y‖ ≤ _
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (h.T_apply_norm_le n s.2 _) le_rfl)

/-- On the domain of `A`: `‖S t x - x‖ ≤ t ‖A x‖`. -/
lemma HYHyp.norm_S_sub_le (x : A.domain) (t : ℝ≥0) : ‖h.S t (x : X) - x‖ ≤ (t : ℝ) * ‖A x‖ := by
  have hb : ∀ n : ℕ, ‖h.T n (t : ℝ) (x : X) - x‖ ≤ ‖h.yos ((n : ℝ) + 1) (x : X)‖ * (t : ℝ) := by
    intro n
    have := norm_exp_sub_smul_le (h.yos ((n : ℝ) + 1)) (x : X) 0 t.2
      (C := ‖h.yos ((n : ℝ) + 1) (x : X)‖) (fun r hr _ => by
        have := h.T_apply_norm_le n hr (h.yos ((n : ℝ) + 1) (x : X))
        simp only [HYHyp.T] at this
        simpa using this)
    simpa [HYHyp.T] using this
  have hl1 : Tendsto (fun n : ℕ => ‖h.T n (t : ℝ) (x : X) - x‖) atTop (𝓝 ‖h.lim (t : ℝ) (x : X) - x‖) :=
    ((h.tendsto_lim (x : X) t.2).sub_const _).norm
  have hl2 : Tendsto (fun n : ℕ => ‖h.yos ((n : ℝ) + 1) (x : X)‖ * (t : ℝ)) atTop
      (𝓝 (‖A x‖ * (t : ℝ))) := (h.tendsto_yos x).norm.mul_const _
  have := le_of_tendsto_of_tendsto' hl1 hl2 hb
  rw [h.S_apply]
  linarith [mul_comm ‖A x‖ (t : ℝ)]

/-- **Strong continuity at `0`.** -/
lemma HYHyp.tendsto_S (x : X) : Tendsto (fun t : ℝ≥0 => h.S t x) (𝓝 0) (𝓝 x) := by
  refine tendsto_apply_of_dense (F := 𝓝 (0 : ℝ≥0)) (D := (A.domain : Set X)) h.dense
    (fun t : ℝ≥0 => h.S t) (fun t => h.S_norm_le t) ?_ x
  intro y hy
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have : Tendsto (fun t : ℝ≥0 => (t : ℝ) * ‖A ⟨y, hy⟩‖) (𝓝 0) (𝓝 0) := by
    simpa using ((NNReal.continuous_coe.tendsto 0).mul_const ‖A ⟨y, hy⟩‖)
  exact squeeze_zero (fun t => norm_nonneg _) (fun t => h.norm_S_sub_le ⟨y, hy⟩ t) this

/-- **The limit semigroup** of a Hille–Yosida operator. -/
def HYHyp.semigroup : ContractionSemigroup 𝕜 X where
  S := h.S
  zero := h.S_zero
  add := h.S_add
  norm_le := h.S_norm_le
  tendsto_zero := h.tendsto_S

end Lightlike.OperatorAlgebras
