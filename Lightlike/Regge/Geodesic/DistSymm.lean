import Lightlike.Regge.Geodesic.Metric

/-!
# Symmetry and translation invariance of the distance of a metric on all of space

For a metric `g` on `ℝⁿ` and `U = univ`, the distance `Lightlike.Geodesic.dist g univ` is symmetric
(`dist_comm_univ`: reverse the curve, `length_reverse`) and invariant under a translation `e` for which
the metric is invariant, `g (p + e) = g p` (`dist_translate_univ`: translate the curve). The second is
what makes the distance of a periodic metric a function on the torus.

## Main results

* `length_reverse`: reversing a curve preserves its length.
* `dist_comm_univ`: the distance is symmetric.
* `dist_translate_univ`: the distance of a translation-invariant metric is invariant.
-/

open Real Set MeasureTheory
namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}

theorem normSq_neg (x v : Fin n → ℝ) : normSq g x (-v) = normSq g x v := by
  unfold normSq; simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct]

/-- Reversing a curve preserves its length. -/
theorem length_reverse (c : ℝ → Fin n → ℝ) :
    length g (fun t => c (1 - t)) 0 1 = length g c 0 1 := by
  unfold length
  have h : ∀ t, deriv (fun t => c (1 - t)) t = -deriv c (1 - t) := fun t => by
    have := deriv_comp_const_sub (a := (1 : ℝ)) (f := c) (x := t)
    simpa using this
  simp only [h, normSq_neg]
  exact intervalIntegral.integral_comp_sub_left (fun t => √(normSq g (c t) (deriv c t))) 1 |>.trans (by simp)

/-- **The distance is symmetric** (for `U` all of space). -/
theorem dist_comm_univ (x y : Fin n → ℝ) : dist g univ x y = dist g univ y x := by
  have key : ∀ x y : Fin n → ℝ, {L | ∃ c, IsAdmissible univ c x y ∧ length g c 0 1 = L} ⊆
      {L | ∃ c, IsAdmissible univ c y x ∧ length g c 0 1 = L} := by
    rintro x y L ⟨c, hc, rfl⟩
    refine ⟨fun t => c (1 - t), ⟨?_, fun _ _ => mem_univ _, by simpa using hc.finish, by simpa using hc.start⟩,
      length_reverse c⟩
    exact hc.smooth.comp (contDiff_const.sub contDiff_id)
  unfold dist
  exact congrArg sInf (Set.Subset.antisymm (key x y) (key y x))


/-- **Translation invariance of the distance.** If the metric is invariant under the translation `e`,
so is the distance (`U` all of space). -/
theorem dist_translate_univ (e : Fin n → ℝ) (hg : ∀ p, g (p + e) = g p) (x y : Fin n → ℝ) :
    dist g univ (x + e) (y + e) = dist g univ x y := by
  have key : ∀ (e : Fin n → ℝ), (∀ p, g (p + e) = g p) → ∀ x y : Fin n → ℝ,
      {L | ∃ c, IsAdmissible univ c x y ∧ length g c 0 1 = L} ⊆
      {L | ∃ c, IsAdmissible univ c (x + e) (y + e) ∧ length g c 0 1 = L} := by
    intro e hg x y L ⟨c, hc, hL⟩
    refine ⟨fun t => c t + e, ⟨hc.smooth.add contDiff_const, fun _ _ => mem_univ _, by simp [hc.start], by simp [hc.finish]⟩, ?_⟩
    rw [← hL]
    unfold length
    congr 1
    funext t
    have : deriv (fun t => c t + e) t = deriv c t := by simp
    simp only [this, normSq, hg (c t)]
  have key' : ∀ x y : Fin n → ℝ, {L | ∃ c, IsAdmissible univ c (x + e) (y + e) ∧ length g c 0 1 = L} ⊆
      {L | ∃ c, IsAdmissible univ c x y ∧ length g c 0 1 = L} := by
    have hg' : ∀ p, g (p + -e) = g p := fun p => by
      have := hg (p + -e); simpa using this.symm
    intro x y L hL
    have := key (-e) hg' (x + e) (y + e) hL
    simpa using this
  unfold dist
  exact congrArg sInf (Set.Subset.antisymm (key e hg x y) (key' x y)).symm

end Lightlike.Geodesic
