import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Bounds for curves on a half-open interval

Real-analysis lemmas for curves defined on `[0, b)`, used for the geodesics of the Kruskal manifold:

* `eq_zero_of_hasDerivAt_zero_Ico`: a function with vanishing derivative on `[0, b)` is constant;
* `abs_sub_le_of_hasDerivAt_Ico`: a bounded derivative bounds the function;
* `abs_le_of_linear_system_Ico`: Grönwall's bound for a linear system `u' = α p`, `p' = β u` with bounded
  coefficients;
* `exists_tendsto_of_bounded_deriv_Ico`: a curve in `ℝⁿ` with bounded velocity has a limit at `b`.
-/

open Set Filter Topology
open scoped NNReal

namespace Lightlike

/-- A function with vanishing derivative on `[0, b)` is constant there. -/
lemma eq_zero_of_hasDerivAt_zero_Ico {f : ℝ → ℝ} {b : ℝ} (hf : ∀ t ∈ Ico 0 b, HasDerivAt f 0 t)
    {t : ℝ} (ht : t ∈ Ico 0 b) : f t = f 0 := by
  have hsub : Icc 0 t ⊆ Ico 0 b := fun x hx => ⟨hx.1, hx.2.trans_lt ht.2⟩
  exact constant_of_has_deriv_right_zero
    (fun x hx => (hf x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hf x (hsub ⟨hx.1, hx.2.le⟩)).hasDerivWithinAt) t ⟨ht.1, le_rfl⟩

/-- A bounded derivative on `[0, b)` bounds the function. -/
lemma abs_sub_le_of_hasDerivAt_Ico {f f' : ℝ → ℝ} {b C : ℝ} (hf : ∀ t ∈ Ico 0 b, HasDerivAt f (f' t) t)
    (hC : ∀ t ∈ Ico 0 b, |f' t| ≤ C) {t : ℝ} (ht : t ∈ Ico 0 b) : |f t - f 0| ≤ C * b := by
  have hb : 0 < b := ht.1.trans_lt ht.2
  have h := (convex_Ico 0 b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivWithinAt) (fun x hx => by simpa using hC x hx)
    (⟨le_rfl, hb⟩ : (0 : ℝ) ∈ Ico 0 b) ht
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 ⟨le_rfl, hb⟩)
  calc |f t - f 0| ≤ C * ‖t - 0‖ := by simpa using h
    _ ≤ C * b := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        rw [sub_zero, Real.norm_of_nonneg ht.1]
        exact ht.2.le

/-- **Grönwall's bound for a linear system** `u' = α p`, `p' = β u` with `|α|, |β| ≤ K` on `[0, b)`. -/
lemma abs_le_of_linear_system_Ico {u p α β : ℝ → ℝ} {b K : ℝ}
    (hu : ∀ t ∈ Ico 0 b, HasDerivAt u (α t * p t) t) (hp : ∀ t ∈ Ico 0 b, HasDerivAt p (β t * u t) t)
    (hα : ∀ t ∈ Ico 0 b, |α t| ≤ K) (hβ : ∀ t ∈ Ico 0 b, |β t| ≤ K) {t : ℝ} (ht : t ∈ Ico 0 b) :
    |u t| ≤ (|u 0| + |p 0|) * Real.exp (K * b) ∧ |p t| ≤ (|u 0| + |p 0|) * Real.exp (K * b) := by
  have hb : 0 < b := ht.1.trans_lt ht.2
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hα 0 ⟨le_rfl, hb⟩)
  have hsub : Icc 0 t ⊆ Ico 0 b := fun x hx => ⟨hx.1, hx.2.trans_lt ht.2⟩
  have hd : ∀ x ∈ Ico 0 b, HasDerivAt (fun s => (u s, p s)) (α x * p x, β x * u x) x := fun x hx =>
    (hu x hx).prodMk (hp x hx)
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => (u s, p s))
    (f' := fun x => (α x * p x, β x * u x)) (δ := |u 0| + |p 0|) (K := K) (ε := 0) (a := 0) (b := t)
    (fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (hsub ⟨hx.1, hx.2.le⟩)).hasDerivWithinAt)
    (by
      rw [Prod.norm_def]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
    (fun x hx => by
      have hx' := hsub ⟨hx.1, hx.2.le⟩
      rw [Prod.norm_def, Prod.norm_def, add_zero]
      refine max_le ?_ ?_
      · rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul_of_nonneg_right (hα x hx') (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hK0)
      · rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul_of_nonneg_right (hβ x hx') (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hK0)) t ⟨ht.1, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hg
  have hmono : (|u 0| + |p 0|) * Real.exp (K * t) ≤ (|u 0| + |p 0|) * Real.exp (K * b) :=
    mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2.le hK0)) (by positivity)
  rw [Prod.norm_def] at hg
  exact ⟨(le_max_left _ _).trans (hg.trans hmono), (le_max_right _ _).trans (hg.trans hmono)⟩

/-- **A curve with bounded velocity on `[0, b)` has a limit at `b`.** -/
lemma exists_tendsto_of_bounded_deriv_Ico {n : ℕ} {c w : ℝ → Fin n → ℝ} {b : ℝ} (hb : 0 < b) {C : ℝ≥0}
    (hc : ∀ t ∈ Ico 0 b, HasDerivAt c (w t) t) (hw : ∀ t ∈ Ico 0 b, ‖w t‖₊ ≤ C) :
    ∃ z, Tendsto c (𝓝[<] b) (𝓝 z) := by
  have hlip : LipschitzOnWith C c (Ico 0 b) :=
    (convex_Ico 0 b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hc x hx).hasDerivWithinAt) hw
  obtain ⟨g, hg, heq⟩ := hlip.extend_pi
  refine ⟨g b, ?_⟩
  have h1 : Tendsto g (𝓝[<] b) (𝓝 (g b)) := (hg.continuous.tendsto b).mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [Ico_mem_nhdsLT hb] with t ht
  exact (heq ht).symm

end Lightlike
