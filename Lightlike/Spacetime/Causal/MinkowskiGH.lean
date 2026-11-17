import Lightlike.Spacetime.Causal.MinkowskiFuture
import Lightlike.CausalSets.ConeOrder

/-!
# Minkowski space is globally hyperbolic

By `minkowski_causalFuture_eq` the causal futures and pasts of Minkowski space `ℝ^{d+1}` are closed
light cones. A causal diamond `J⁺(x) ∩ J⁻(y)` is then closed and bounded, hence compact, and the
open diamonds `{w | p ≪ w ≪ q}`, `p = x - ε ∂₀`, `q = x + ε ∂₀`, are arbitrarily small causally
convex neighbourhoods of `x`, so Minkowski space is strongly causal.

## References

* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1.
* E. Minguzzi and M. Sánchez, *The causal hierarchy of spacetimes*, in *Recent developments in
  pseudo-Riemannian geometry*, EMS (2008), Sections 3 and 4.

The comparison with these sources at a location is pending.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

open Lightlike.CausalSets

variable {d : ℕ}

/-- The **timelike relation** of Minkowski space: `y - x` is future-directed timelike, in terms of the
spatial length. -/
def tl (x y : Fin (d + 1) → ℝ) : Prop :=
  0 < (y - x) 0 ∧ spatialSq (y - x) < ((y - x) 0) ^ 2

lemma tl_trans_left {x y z : Fin (d + 1) → ℝ} (h1 : tl x y) (h2 : coneLE y z) : tl x z := by
  rw [coneLE_iff_spatial] at h2
  obtain ⟨a0, a1⟩ := h1
  obtain ⟨b0, b1⟩ := h2
  have e : z - x = (y - x) + (z - y) := by abel
  have sa : √(spatialSq (y - x)) < (y - x) 0 := (Real.sqrt_lt' a0).2 a1
  have sb : √(spatialSq (z - y)) ≤ (z - y) 0 := Real.sqrt_le_iff.2 ⟨b0, b1⟩
  unfold tl
  rw [e]
  have hpos : 0 < ((y - x) + (z - y)) 0 := by simpa using add_pos_of_pos_of_nonneg a0 b0
  refine ⟨hpos, ?_⟩
  calc spatialSq ((y - x) + (z - y)) ≤ _ := spatialSq_add_le _ _
    _ < ((y - x) 0 + (z - y) 0) ^ 2 := by
        apply pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
    _ = _ := by simp

lemma tl_trans_right {x y z : Fin (d + 1) → ℝ} (h1 : coneLE x y) (h2 : tl y z) : tl x z := by
  rw [coneLE_iff_spatial] at h1
  obtain ⟨a0, a1⟩ := h1
  obtain ⟨b0, b1⟩ := h2
  have e : z - x = (y - x) + (z - y) := by abel
  have sa : √(spatialSq (y - x)) ≤ (y - x) 0 := Real.sqrt_le_iff.2 ⟨a0, a1⟩
  have sb : √(spatialSq (z - y)) < (z - y) 0 := (Real.sqrt_lt' b0).2 b1
  unfold tl
  rw [e]
  have hpos : 0 < ((y - x) + (z - y)) 0 := by simpa using add_pos_of_nonneg_of_pos a0 b0
  refine ⟨hpos, ?_⟩
  calc spatialSq ((y - x) + (z - y)) ≤ _ := spatialSq_add_le _ _
    _ < ((y - x) 0 + (z - y) 0) ^ 2 := by
        apply pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
    _ = _ := by simp

lemma coneLE_of_tl {x y : Fin (d + 1) → ℝ} (h : tl x y) : coneLE x y := by
  rw [coneLE_iff_spatial]
  exact ⟨h.1.le, h.2.le⟩

/-- A vector of the closed future cone has every coordinate at most its time component. -/
lemma norm_le_of_coneLE {x y : Fin (d + 1) → ℝ} (h : coneLE x y) : ‖y - x‖ ≤ (y - x) 0 := by
  rw [coneLE_iff_spatial] at h
  obtain ⟨h0, h1⟩ := h
  refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  rw [Real.norm_eq_abs]
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [abs_of_nonneg h0]
  · have : (y - x) i.succ ^ 2 ≤ spatialSq (y - x) :=
      Finset.single_le_sum (f := fun i : Fin d => (y - x) i.succ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ i)
    exact abs_le_of_sq_le_sq' (by nlinarith) h0 |> fun h => abs_le.2 h

lemma continuous_sub_time (a : Fin (d + 1) → ℝ) : Continuous fun z : Fin (d + 1) → ℝ => (z - a) 0 := by
  fun_prop

lemma continuous_sub_time' (a : Fin (d + 1) → ℝ) : Continuous fun z : Fin (d + 1) → ℝ => (a - z) 0 := by
  fun_prop

lemma continuous_sub_space (a : Fin (d + 1) → ℝ) :
    Continuous fun z : Fin (d + 1) → ℝ => spatialSq (z - a) := by
  unfold spatialSq
  exact continuous_finsetSum _ fun i _ => ((continuous_apply i.succ).sub continuous_const).pow 2

lemma continuous_sub_space' (a : Fin (d + 1) → ℝ) :
    Continuous fun z : Fin (d + 1) → ℝ => spatialSq (a - z) := by
  unfold spatialSq
  exact continuous_finsetSum _ fun i _ => (continuous_const.sub (continuous_apply i.succ)).pow 2

lemma continuous_sub_form (a : Fin (d + 1) → ℝ) :
    Continuous fun z : Fin (d + 1) → ℝ => minkowskiForm (d + 1) (z - a) (z - a) := by
  fun_prop

lemma continuous_sub_form' (a : Fin (d + 1) → ℝ) :
    Continuous fun z : Fin (d + 1) → ℝ => minkowskiForm (d + 1) (a - z) (a - z) := by
  fun_prop

lemma isClosed_coneLE_future (x : Fin (d + 1) → ℝ) : IsClosed {y | coneLE x y} :=
  (isClosed_le continuous_const (continuous_sub_time x)).inter
    (isClosed_le (continuous_sub_form x) continuous_const)

lemma isClosed_coneLE_past (y : Fin (d + 1) → ℝ) : IsClosed {x | coneLE x y} :=
  (isClosed_le continuous_const (continuous_sub_time' y)).inter
    (isClosed_le (continuous_sub_form' y) continuous_const)

lemma isOpen_tl_future (x : Fin (d + 1) → ℝ) : IsOpen {y | tl x y} :=
  (isOpen_lt continuous_const (continuous_sub_time x)).inter
    (isOpen_lt (continuous_sub_space x) ((continuous_sub_time x).pow 2))

lemma isOpen_tl_past (y : Fin (d + 1) → ℝ) : IsOpen {x | tl x y} :=
  (isOpen_lt continuous_const (continuous_sub_time' y)).inter
    (isOpen_lt (continuous_sub_space' y) ((continuous_sub_time' y).pow 2))

/-- The causal future of a point of Minkowski space, in terms of the cone order. -/
lemma mem_causalFuture_iff (x y : Fin (d + 1) → ℝ) :
    y ∈ causalFuture (minkowskiOrientation d) x ↔ coneLE x y := by
  rw [minkowski_causalFuture_eq]
  rfl

/-- The causal diamonds of Minkowski space are compact. -/
theorem minkowski_isCompact_diamond (x y : Fin (d + 1) → ℝ) :
    IsCompact (causalFuture (minkowskiOrientation d) x ∩ causalPast (minkowskiOrientation d) y) := by
  have e : causalFuture (minkowskiOrientation d) x ∩ causalPast (minkowskiOrientation d) y =
      {z | coneLE x z} ∩ {z | coneLE z y} := by
    ext z
    simp only [causalPast, mem_inter_iff, mem_ofPred_eq, mem_causalFuture_iff]
  rw [e]
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_coneLE_future x).inter (isClosed_coneLE_past y)) ?_
  refine (Metric.isBounded_closedBall (x := x) (r := (y - x) 0)).subset ?_
  rintro z ⟨h1, h2⟩
  rw [mem_closedBall_iff_norm]
  have := norm_le_of_coneLE h1
  have h3 : 0 ≤ (y - z) 0 := h2.1
  have : (z - x) 0 ≤ (y - x) 0 := by simp at h3 ⊢; linarith
  linarith [norm_le_of_coneLE h1]

/-- **Minkowski space is strongly causal**: the open diamonds around a point are arbitrarily small
causally convex neighbourhoods. -/
theorem minkowski_isStronglyCausal : IsStronglyCausal (minkowskiOrientation d) := by
  intro x U hU
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  set ε : ℝ := r / 4 with hε
  have hε0 : 0 < ε := by positivity
  set p : Fin (d + 1) → ℝ := x - ε • Pi.single 0 1 with hp
  set q : Fin (d + 1) → ℝ := x + ε • Pi.single 0 1 with hq
  have hs : spatialSq (ε • (Pi.single 0 1 : Fin (d + 1) → ℝ)) = 0 := by
    simp [spatialSq, Fin.succ_ne_zero]
  have ht : (ε • (Pi.single 0 1 : Fin (d + 1) → ℝ)) 0 = ε := by simp
  have hxp : tl p x := by
    have : x - p = ε • (Pi.single 0 1 : Fin (d + 1) → ℝ) := by rw [hp]; abel
    refine ⟨?_, ?_⟩ <;> rw [this] <;> simp only [ht, hs] <;> positivity
  have hxq : tl x q := by
    have : q - x = ε • (Pi.single 0 1 : Fin (d + 1) → ℝ) := by rw [hq]; abel
    refine ⟨?_, ?_⟩ <;> rw [this] <;> simp only [ht, hs] <;> positivity
  set V : Set (Fin (d + 1) → ℝ) := {w | tl p w} ∩ {w | tl w q} with hV
  have hVo : IsOpen V := (isOpen_tl_future p).inter (isOpen_tl_past q)
  have hxV : x ∈ V := ⟨hxp, hxq⟩
  have hn1 : ‖(Pi.single 0 1 : Fin (d + 1) → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  have hdist : dist p x ≤ ε := by
    rw [dist_eq_norm, hp, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
    nlinarith
  refine ⟨V, hVo.mem_nhds hxV, ?_, ?_⟩
  · intro w hw
    apply hrU
    rw [Metric.mem_ball]
    have h1 := norm_le_of_coneLE (coneLE_of_tl hw.1)
    have h2 : (w - p) 0 ≤ (q - p) 0 := by
      have := (coneLE_iff_spatial _ _).1 (coneLE_of_tl hw.2)
      simp at this ⊢
      linarith [this.1]
    have h3 : (q - p) 0 = 2 * ε := by
      rw [hp, hq]; simp; ring
    have hwp : dist w p ≤ 2 * ε := by rw [dist_eq_norm]; linarith
    have := dist_triangle w p x
    linarith
  · intro y hy z hz w hyw hwz
    rw [mem_causalFuture_iff] at hyw hwz
    exact ⟨tl_trans_left hy.1 hyw, tl_trans_right hwz hz.2⟩

/-- **Minkowski space is globally hyperbolic**: strongly causal with compact causal diamonds.
(The comparison with the sources at a location is pending.) -/
theorem minkowski_globallyHyperbolic : IsGloballyHyperbolic (minkowskiOrientation d) :=
  ⟨minkowski_isStronglyCausal, minkowski_isCompact_diamond⟩

end Lightlike.Causal
