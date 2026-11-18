import Mathlib

/-!
# Reparametrisation by a monotone functional

If a continuous curve `c` on `[a, b]` satisfies `ℓ (c s) ≤ ℓ (c t)` and
`‖c t - c s‖ ≤ C (ℓ (c t) - ℓ (c s))` for `s ≤ t`, then `c` factors through the functional `ℓ`:
`c = ĉ ∘ (ℓ ∘ c)` for a `C`-Lipschitz map `ĉ : ℝ → E` (constant outside the range of `ℓ ∘ c`).
This is the reparametrisation used to apply Arzelà–Ascoli to causal curves, whose own parameter
carries no bound.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Set

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve with `ℓ`-controlled displacement factors through `ℓ` as a Lipschitz map. -/
theorem exists_lipschitz_factor {c : ℝ → E} {ℓ : E →L[ℝ] ℝ} {C : ℝ} (hC : 0 < C) {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn c (Icc a b))
    (hmono : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      ℓ (c s) ≤ ℓ (c t) ∧ ‖c t - c s‖ ≤ C * (ℓ (c t) - ℓ (c s))) :
    ∃ ĉ : ℝ → E, (∀ x y, ‖ĉ x - ĉ y‖ ≤ C * |x - y|) ∧ (∀ t ∈ Icc a b, ĉ (ℓ (c t)) = c t) ∧
      (∀ x, ∃ t ∈ Icc a b, ĉ x = c t) := by
  have hcont : ContinuousOn (fun t => ℓ (c t)) (Icc a b) := ℓ.continuous.comp_continuousOn hc
  set lo : ℝ := ℓ (c a) with hlo
  set hi : ℝ := ℓ (c b) with hhi
  have hlohi : lo ≤ hi := (hmono a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab).1
  -- clamp into `[lo, hi]`
  let cl : ℝ → ℝ := fun x => max lo (min hi x)
  have hcl_mem : ∀ x, cl x ∈ Icc lo hi := fun x => ⟨le_max_left _ _, max_le hlohi (min_le_left _ _)⟩
  have hcl_lip : ∀ x y, |cl x - cl y| ≤ |x - y| := by
    intro x y
    have h1 : |min hi x - min hi y| ≤ |x - y| := by
      rw [abs_le]; constructor <;> cases le_total hi x <;> cases le_total hi y <;>
        simp_all <;> linarith [abs_nonneg (x - y), le_abs_self (x - y), neg_abs_le (x - y)]
    have h2 : ∀ u v : ℝ, |max lo u - max lo v| ≤ |u - v| := by
      intro u v
      rw [abs_le]; constructor <;> cases le_total lo u <;> cases le_total lo v <;>
        simp_all <;> linarith [abs_nonneg (u - v), le_abs_self (u - v), neg_abs_le (u - v)]
    exact (h2 _ _).trans h1
  have hex : ∀ y ∈ Icc lo hi, ∃ t ∈ Icc a b, ℓ (c t) = y := fun y hy =>
    intermediate_value_Icc hab hcont hy
  choose! τ hτ hτl using hex
  have hτ' : ∀ x, τ (cl x) ∈ Icc a b := fun x => hτ _ (hcl_mem x)
  have hτl' : ∀ x, ℓ (c (τ (cl x))) = cl x := fun x => hτl _ (hcl_mem x)
  -- two parameters with the same value of `ℓ ∘ c` give the same point
  have hdisp : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖c t - c s‖ ≤ C * |ℓ (c t) - ℓ (c s)| := by
    intro s hs t ht
    rcases le_total s t with h | h
    · obtain ⟨h1, h2⟩ := hmono s hs t ht h
      rwa [abs_of_nonneg (by linarith)]
    · obtain ⟨h1, h2⟩ := hmono t ht s hs h
      rw [norm_sub_rev, abs_of_nonpos (by linarith)]
      linarith
  refine ⟨fun x => c (τ (cl x)), ?_, ?_, fun x => ⟨_, hτ' x, rfl⟩⟩
  · intro x y
    have := hdisp _ (hτ' y) _ (hτ' x)
    rw [hτl' x, hτl' y] at this
    calc ‖c (τ (cl x)) - c (τ (cl y))‖ ≤ C * |cl x - cl y| := this
      _ ≤ C * |x - y| := mul_le_mul_of_nonneg_left (hcl_lip x y) hC.le
  · intro t ht
    have hmem : ℓ (c t) ∈ Icc lo hi :=
      ⟨(hmono a ⟨le_rfl, hab⟩ t ht ht.1).1, (hmono t ht b ⟨hab, le_rfl⟩ ht.2).1⟩
    have hcl : cl (ℓ (c t)) = ℓ (c t) := by
      simp only [cl]
      rw [min_eq_right hmem.2, max_eq_right hmem.1]
    have := hdisp t ht _ (hτ' (ℓ (c t)))
    have hv : ℓ (c (τ (cl (ℓ (c t))))) = ℓ (c t) := by rw [hτl', hcl]
    rw [hv, sub_self, abs_zero, mul_zero] at this
    show c (τ (cl (ℓ (c t)))) = c t
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end Lightlike.Causal
