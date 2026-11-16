import Lightlike.PL.WeakJordan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The weak Jordan theorem for a circle in the plane

The image of a continuous injective map from the circle into the plane has a disconnected
complement.

## Main results

* `weak_jordan`: the weak Jordan theorem (Klazar, arXiv:2604.04296, Section 2, Claim 4, after
  Thomassen; Klazar's numbering).
-/

open Set Real

namespace Lightlike.PL

/-- The image of a short arc of the circle under an embedding is an arc. -/
lemma isArc_circle_arc {g : Circle → ℝ × ℝ} (hc : Continuous g) (hi : Function.Injective g)
    {s t : ℝ} (hst : s < t) (hlen : t - s < 2 * π) :
    IsArc (g '' (Circle.exp '' Icc s t)) (g (Circle.exp s)) (g (Circle.exp t)) := by
  have hm : ∀ l : ℝ, l ∈ Icc (0 : ℝ) 1 → s + l * (t - s) ∈ Icc s t := fun l hl =>
    ⟨by nlinarith [hl.1], by nlinarith [hl.2]⟩
  refine ⟨fun l => g (Circle.exp (s + l * (t - s))), ?_, ?_, by simp, by simp, ?_⟩
  · exact (hc.comp (Circle.exp.continuous.comp (by fun_prop))).continuousOn
  · intro a ha b hb hab
    have h1 := hi hab
    have h2 := Circle.exp_injOn_Icc hlen (hm a ha) (hm b hb) h1
    have : a * (t - s) = b * (t - s) := by linarith
    exact mul_right_cancel₀ (by linarith) this
  · ext y
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨_, ⟨_, hm l hl, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨(u - s) / (t - s), ⟨div_nonneg (by linarith [hu.1]) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]; linarith [hu.2]
      · show g (Circle.exp (s + (u - s) / (t - s) * (t - s))) = g (Circle.exp u)
        rw [div_mul_cancel₀ _ (by linarith : (t - s) ≠ 0)]; simp

/-- The circle is the union of two arcs from `1` to `w` that meet only at their ends, as a map. -/
lemma exists_two_arcs (g : Circle → ℝ × ℝ) (hc : Continuous g) (hi : Function.Injective g)
    {w : Circle} (hw : w ≠ 1) :
    ∃ A₀ A₁ : Set (ℝ × ℝ), IsArc A₀ (g 1) (g w) ∧ IsArc A₁ (g 1) (g w) ∧
      A₀ ∩ A₁ = {g 1, g w} ∧ A₀ ∪ A₁ = range g := by
  set θ : ℝ := Circle.angleDiff 1 w with hθ
  set φ : ℝ := Circle.angleDiff w 1 with hφ
  have hθ0 : 0 < θ := Circle.angleDiff_pos (Ne.symm hw)
  have hφ0 : 0 < φ := Circle.angleDiff_pos hw
  have hsum : θ + φ = 2 * π := Circle.angleDiff_add_angleDiff (Ne.symm hw)
  have hexp : Circle.exp θ = w := by
    have := Circle.exp_angleDiff_mul (x := 1) (y := w)
    simpa [hθ] using this
  have hexp' : Circle.exp (-φ) = w := by
    rw [← hexp, Circle.exp_eq_exp]
    exact ⟨-1, by push_cast; linarith⟩
  have h0 := isArc_circle_arc hc hi (s := 0) (t := θ) hθ0 (by linarith)
  have h1 := isArc_circle_arc hc hi (s := -φ) (t := 0) (by linarith) (by linarith)
  rw [Circle.exp_zero, hexp] at h0
  rw [Circle.exp_zero, hexp'] at h1
  have hE : Circle.exp '' Icc 0 θ ∩ Circle.exp '' Icc (-φ) 0 = {1, w} := by
    ext z
    simp only [mem_inter_iff, mem_image, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, ⟨r, hr, hrs⟩⟩
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 hrs.symm
      have hm1 : (m : ℝ) < 2 := by nlinarith [hs.1, hs.2, hr.1, hr.2, Real.pi_pos]
      have hm0 : (-1 : ℝ) < m := by nlinarith [hs.1, hs.2, hr.1, hr.2, Real.pi_pos]
      have hm0' : (0 : ℤ) ≤ m := by
        have : (-1 : ℤ) < m := by exact_mod_cast hm0
        omega
      have hm1' : m ≤ 1 := by
        have : m < 2 := by exact_mod_cast hm1
        omega
      interval_cases m
      · have : s = 0 := by simp at hm; linarith [hs.1, hr.2]
        subst this; left; simp
      · right
        have hsθ : s = θ := by push_cast at hm; linarith [hs.2, hr.1]
        rw [hsθ, hexp]
    · rintro (rfl | rfl)
      · exact ⟨⟨0, ⟨le_rfl, hθ0.le⟩, by simp⟩, ⟨0, ⟨by linarith, le_rfl⟩, by simp⟩⟩
      · exact ⟨⟨θ, ⟨hθ0.le, le_rfl⟩, hexp⟩, ⟨-φ, ⟨le_rfl, by linarith⟩, hexp'⟩⟩
  have hU : Circle.exp '' Icc 0 θ ∪ Circle.exp '' Icc (-φ) 0 = univ := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨x, rfl⟩ := Circle.exp_surjective z
    set n : ℤ := ⌊(x + φ) / (2 * π)⌋ with hn
    have h2π : 0 < 2 * π := by positivity
    have hn1 : (n : ℝ) ≤ (x + φ) / (2 * π) := Int.floor_le _
    have hn2 : (x + φ) / (2 * π) < n + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ h2π] at hn1
    rw [div_lt_iff₀ h2π] at hn2
    have hx : Circle.exp x = Circle.exp (x - n * (2 * π)) :=
      Circle.exp_eq_exp.2 ⟨n, by ring⟩
    rcases le_or_gt (x - n * (2 * π)) 0 with h | h
    · exact Or.inr ⟨x - n * (2 * π), ⟨by nlinarith, h⟩, hx.symm⟩
    · exact Or.inl ⟨x - n * (2 * π), ⟨h.le, by nlinarith⟩, hx.symm⟩
  refine ⟨_, _, h0, h1.symm, ?_, ?_⟩
  · rw [← Set.image_inter hi, hE, Set.image_pair]
  · rw [← Set.image_union, hU, Set.image_univ]

end Lightlike.PL
