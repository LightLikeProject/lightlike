import Lightlike.Spacetime.RiccatiFocusing

/-!
# Twist destroys focusing (GE3, Tier 1)

With vorticity `ω` the Raychaudhuri inequality reads `Θ' ≤ -Θ²/m + ω²` (the twist term enters with the opposite
sign). Take `ω` constant (rigidly rotating congruence). The focusing lemma `focusing` then fails: the constant
`Θ ≡ -√m · ω < 0` satisfies the inequality on every `[0, L)`. So no bound `L ≤ B` can hold, and the hypothesis
"vanishing twist" in the Raychaudhuri focusing theorem is necessary.
-/

open Set

namespace Lightlike

/-- The constant expansion `-√m ω` satisfies the twisted Riccati inequality `Θ' ≤ -Θ²/m + ω²` (with equality). -/
theorem twisted_riccati_const {m ω : ℝ} (hm : 0 < m) :
    (0 : ℝ) ≤ -(-(Real.sqrt m * ω)) ^ 2 / m + ω ^ 2 := by
  have h : (Real.sqrt m) ^ 2 = m := Real.sq_sqrt hm.le
  have : -(-(Real.sqrt m * ω)) ^ 2 / m + ω ^ 2 = 0 := by
    field_simp
    rw [h]
    ring
  rw [this]

/-- **Twist counterexample**: for every `ω > 0`, `m > 0` and every `L`, there is a negative expansion profile on
`[0, L)` obeying `Θ' ≤ -Θ²/m + ω²` and `Θ 0 < 0`, so the focusing bound `L ≤ m/|Θ 0|` fails for large `L`.
Hence there is no uniform bound on the lifetime. -/
theorem twisted_no_focusing {m ω : ℝ} (hm : 0 < m) (hω : 0 < ω) :
    ¬ ∃ B : ℝ, ∀ (Θ Θ' : ℝ → ℝ) (L : ℝ),
      (∀ s ∈ Ico (0 : ℝ) L, HasDerivAt Θ (Θ' s) s) →
      (∀ s ∈ Ico (0 : ℝ) L, Θ' s ≤ -(Θ s) ^ 2 / m + ω ^ 2) → Θ 0 < 0 → L ≤ B := by
  rintro ⟨B, hB⟩
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have h := hB (fun _ => -(Real.sqrt m * ω)) (fun _ => 0) (|B| + 1)
    (fun s _ => hasDerivAt_const s _)
    (fun s _ => twisted_riccati_const hm)
    (show -(Real.sqrt m * ω) < 0 by linarith [mul_pos hs hω])
  linarith [le_abs_self B]

/-- A constant profile `Θ ≡ -c` obeys `Θ' = 0 ≤ -Θ²/m + ω²` iff `c² ≤ m ω²`. For `ω = 0` this forces `c = 0`,
consistent with `focusing`; for `ω > 0` it allows `c = √m ω > 0`, i.e. a negative non-focusing profile. -/
theorem twisted_riccati_const_iff {m ω c : ℝ} (hm : 0 < m) :
    (0 : ℝ) ≤ -(c) ^ 2 / m + ω ^ 2 ↔ c ^ 2 ≤ m * ω ^ 2 := by
  have e : -(c) ^ 2 / m + ω ^ 2 = (m * ω ^ 2 - c ^ 2) / m := by field_simp; ring
  rw [e, div_nonneg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨by linarith, hm.le⟩

end Lightlike
