import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Lightlike.Spacetime.Curvature

/-!
# The divergence theorem on a half-space, for compactly supported fields

`integral_divergence_halfSpace`: for a `C¹` vector field `F` on `ℝⁿ⁺¹` with compact support,

`∫_{x_i ≥ 0} ∑_j ∂_j F_j = -∫_{ℝⁿ} F_i (x_i = 0)`.

This is case (iii) in the proof of the divergence theorem of Loomis–Sternberg (a chart in which the domain
is a half-space), in coordinates: the only boundary term comes from the hyperplane `x_i = 0`, with the
outward normal `-e_i`. It follows from Mathlib's divergence theorem for boxes.

## References

* L. H. Loomis, S. Sternberg, *Advanced Calculus* (revised edition), chapter 10, section 6, Theorem 6.1,
  p. 421, and Case III of its proof, p. 423.
-/

open MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- A point with a coordinate of absolute value larger than `R` lies outside the closed ball of radius
`R` (sup norm). -/
lemma notMem_closedBall_of_abs_coord_gt {m : ℕ} {R : ℝ} {x : Fin m → ℝ} (j : Fin m) (hj : R < |x j|) :
    x ∉ closedBall (0 : Fin m → ℝ) R := by
  intro hx
  rw [mem_closedBall_zero_iff] at hx
  have h1 : ‖x j‖ ≤ ‖x‖ := norm_le_pi_norm x j
  rw [Real.norm_eq_abs] at h1
  linarith

/-- **The divergence theorem on a half-space**, for a compactly supported `C¹` vector field. -/
theorem integral_divergence_halfSpace (i : Fin (n + 1))
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (hc : ∀ j, HasCompactSupport (F j)) :
    ∫ x in {x : Fin (n + 1) → ℝ | 0 ≤ x i}, ∑ j, pd j (F j) x =
      -∫ y : Fin n → ℝ, F i (Fin.insertNth i 0 y) := by
  -- a radius beyond which all components vanish
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ j x, x ∉ closedBall (0 : Fin (n + 1) → ℝ) R → F j x = 0 := by
    have hb : ∀ j, ∃ r : ℝ, tsupport (F j) ⊆ closedBall 0 r := fun j =>
      (hc j).isCompact.isBounded.subset_closedBall 0
    choose r hr using hb
    refine ⟨(∑ j, |r j|) + 1, by positivity, fun j x hx => ?_⟩
    by_contra hne
    have hmem : x ∈ closedBall (0 : Fin (n + 1) → ℝ) (r j) := hr j (subset_tsupport _ hne)
    refine hx (closedBall_subset_closedBall ?_ hmem)
    have h1 : |r j| ≤ ∑ k, |r k| :=
      Finset.single_le_sum (f := fun k => |r k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    linarith [le_abs_self (r j)]
  obtain ⟨a, ha⟩ : ∃ a : Fin (n + 1) → ℝ, a = Function.update (fun _ => -(R + 1)) i 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (n + 1) → ℝ, b = fun _ => R + 1 := ⟨_, rfl⟩
  have hai : a i = 0 := by rw [ha, Function.update_self]
  have haj : ∀ j, j ≠ i → a j = -(R + 1) := fun j hj => by rw [ha, Function.update_of_ne hj]
  have hbj : ∀ j, b j = R + 1 := fun j => by rw [hb]
  have hle : a ≤ b := by
    intro j
    by_cases hj : j = i
    · rw [hj, hai, hbj]
      linarith
    · rw [haj j hj, hbj]
      linarith
  -- the divergence vanishes outside the ball
  have hdiv0 : ∀ x, x ∉ closedBall (0 : Fin (n + 1) → ℝ) R → ∑ j, pd j (F j) x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun j _ => ?_
    have hev : F j =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with z hz
      exact hR j z hz
    unfold pd
    rw [hev.fderiv_eq]
    simp
  -- the half-space integral is the integral over the box
  have hsub : Icc a b ⊆ {x : Fin (n + 1) → ℝ | 0 ≤ x i} := by
    intro x hx
    have := hx.1 i
    rw [hai] at this
    exact this
  have hbox : ∫ x in {x : Fin (n + 1) → ℝ | 0 ≤ x i}, ∑ j, pd j (F j) x =
      ∫ x in Icc a b, ∑ j, pd j (F j) x := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero
      (measurableSet_le measurable_const (measurable_pi_apply i)) hsub fun x hx => ?_
    refine hdiv0 x fun hball => hx.2 ⟨fun j => ?_, fun j => ?_⟩
    · rw [mem_closedBall_zero_iff] at hball
      have h1 : |x j| ≤ R := (Real.norm_eq_abs (x j) ▸ norm_le_pi_norm x j).trans hball
      by_cases hj : j = i
      · rw [hj, hai]
        exact hx.1
      · rw [haj j hj]
        linarith [neg_abs_le (x j)]
    · rw [mem_closedBall_zero_iff] at hball
      have h1 : |x j| ≤ R := (Real.norm_eq_abs (x j) ▸ norm_le_pi_norm x j).trans hball
      rw [hbj]
      linarith [le_abs_self (x j)]
  -- the divergence theorem on the box
  have hcont : Continuous (fun x => ∑ j, pd j (F j) x) :=
    continuous_finsetSum _ fun j _ => by
      unfold pd
      exact ((hF j).continuous_fderiv (by simp)).clm_apply continuous_const
  have key := integral_divergence_of_hasFDerivAt_off_countable' a b hle F
    (fun j x => fderiv ℝ (F j) x) ∅ countable_empty (fun j => (hF j).continuous.continuousOn)
    (fun x _ j => ((hF j).differentiable (by simp)).differentiableAt.hasFDerivAt)
    (hcont.continuousOn.integrableOn_compact isCompact_Icc : IntegrableOn _ (Icc a b) volume)
  have key' : ∫ x in Icc a b, ∑ j, pd j (F j) x =
      ∑ j : Fin (n + 1), ((∫ y in Icc (a ∘ Fin.succAbove j) (b ∘ Fin.succAbove j),
          F j (Fin.insertNth j (b j) y)) -
        ∫ y in Icc (a ∘ Fin.succAbove j) (b ∘ Fin.succAbove j), F j (Fin.insertNth j (a j) y)) := key
  -- the front faces do not contribute
  have hfront : ∀ j, ∫ y in Icc (a ∘ Fin.succAbove j) (b ∘ Fin.succAbove j),
      F j (Fin.insertNth j (b j) y) = 0 := by
    intro j
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => hR j _ ?_
    refine notMem_closedBall_of_abs_coord_gt j ?_
    rw [Fin.insertNth_apply_same, hbj, abs_of_pos (by linarith)]
    linarith
  -- the back faces other than `i` do not contribute
  have hback : ∀ j, j ≠ i → ∫ y in Icc (a ∘ Fin.succAbove j) (b ∘ Fin.succAbove j),
      F j (Fin.insertNth j (a j) y) = 0 := by
    intro j hj
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => hR j _ ?_
    refine notMem_closedBall_of_abs_coord_gt j ?_
    rw [Fin.insertNth_apply_same, haj j hj, abs_neg, abs_of_pos (by linarith)]
    linarith
  -- the back face `i` is the integral over the whole hyperplane
  have hface : ∫ y in Icc (a ∘ Fin.succAbove i) (b ∘ Fin.succAbove i), F i (Fin.insertNth i (a i) y) =
      ∫ y : Fin n → ℝ, F i (Fin.insertNth i 0 y) := by
    rw [hai]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hR i _ ?_
    have hex : ∃ k, R < |y k| := by
      by_contra hno
      push_neg at hno
      refine hy ⟨fun k => ?_, fun k => ?_⟩
      · show a (i.succAbove k) ≤ y k
        rw [haj _ (Fin.succAbove_ne i k)]
        linarith [neg_abs_le (y k), hno k]
      · show y k ≤ b (i.succAbove k)
        rw [hbj]
        linarith [le_abs_self (y k), hno k]
    obtain ⟨k, hk⟩ := hex
    refine notMem_closedBall_of_abs_coord_gt (i.succAbove k) ?_
    rw [Fin.insertNth_apply_succAbove]
    exact hk
  rw [hbox, key', Finset.sum_eq_single i]
  · rw [hfront i, hface, zero_sub]
  · intro j _ hj
    rw [hfront j, hback j hj, sub_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end Lightlike
