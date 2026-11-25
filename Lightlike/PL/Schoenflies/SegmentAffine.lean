import Mathlib
import Lightlike.PL.Schoenflies.ChainHit

/-!
# An affine homeomorphism between two segments

Row G3-188 (PL5), ring cells.  `exists_segment_affine`: for non-degenerate segments `[a, b]` and `[a', b']` there is a
continuous map, bijective from `[a, b]` onto `[a', b']`, sending `a ↦ a'` and `b ↦ b'`.
-/

open Set

namespace Lightlike.PL.Schoenflies

/-- The parameter of the orthogonal projection onto the line through `a` and `b`. -/
noncomputable def segParam (a b z : ℝ × ℝ) : ℝ :=
  ((z.1 - a.1) * (b.1 - a.1) + (z.2 - a.2) * (b.2 - a.2)) / ((b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2)

lemma segParam_line {a b : ℝ × ℝ} (hab : a ≠ b) (θ : ℝ) : segParam a b (a + θ • (b - a)) = θ := by
  have hd : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
    intro h
    have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    exact hab (Prod.ext (by linarith) (by linarith))
  unfold segParam
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  field_simp
  ring

theorem exists_segment_affine {a b a' b' : ℝ × ℝ} (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ A : ℝ × ℝ → ℝ × ℝ, ContinuousOn A (segment ℝ a b) ∧ BijOn A (segment ℝ a b) (segment ℝ a' b') ∧
      A a = a' ∧ A b = b' := by
  have hd : (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 ≠ 0 := by
    intro h
    have h1 : b.1 - a.1 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    have h2 : b.2 - a.2 = 0 := by nlinarith [sq_nonneg (b.1 - a.1), sq_nonneg (b.2 - a.2)]
    exact hab (Prod.ext (by linarith) (by linarith))
  refine ⟨fun z => a' + segParam a b z • (b' - a'), ?_, ?_, ?_, ?_⟩
  · have : Continuous (segParam a b) := by
      unfold segParam
      refine Continuous.div (by fun_prop) (by fun_prop) fun _ => hd
    exact (by fun_prop : Continuous fun z => a' + segParam a b z • (b' - a')).continuousOn
  · rw [segment_eq_image', segment_eq_image']
    have hinj : InjOn (fun θ : ℝ => a + θ • (b - a)) univ := by
      intro x _ y _ hxy
      have := congrArg (segParam a b) hxy
      simpa [segParam_line hab] using this
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨θ, hθ, rfl⟩
      refine ⟨θ, hθ, ?_⟩
      simp only [segParam_line hab]
    · rintro _ ⟨θ, hθ, rfl⟩ _ ⟨θ', hθ', rfl⟩ h
      simp only [segParam_line hab] at h
      have : θ • (b' - a') = θ' • (b' - a') := add_left_cancel h
      have hne : b' - a' ≠ 0 := sub_ne_zero.2 hab'.symm
      have := smul_left_injective ℝ hne this
      rw [this]
    · rintro _ ⟨θ, hθ, rfl⟩
      refine ⟨a + θ • (b - a), ⟨θ, hθ, rfl⟩, ?_⟩
      simp only [segParam_line hab]
  · have := segParam_line hab 0
    simp only [zero_smul, add_zero] at this
    simp [this]
  · have := segParam_line hab 1
    simp only [one_smul, add_sub_cancel] at this
    simp [this]

end Lightlike.PL.Schoenflies
