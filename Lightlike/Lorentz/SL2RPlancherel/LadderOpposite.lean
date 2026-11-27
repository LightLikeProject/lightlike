import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.LadderClosed

/-!
# The ladder images of the opposite-sign blocks in closed form

For the `K`-types `(l, -s)` with `l, s` natural (the blocks of opposite sign, where the discrete
series live), the raising operator `ladUp l (-s)` acts on `sinh^{l+s} ξ · u(cosh ξ)` by
`u ↦ u' + s u / (v - 1)` (`hLRN_eq`), with the singular point `v = 1` at the identity, in contrast to
`u ↦ u' + s u / (v + 1)` for the same-sign blocks (`hLR_eq`).  Layer 2c-v of the Plancherel formula
on `SL(2,ℝ)`, milestone HA3.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The recursion `u₀ = G^{(s)}`, `u_{l+1} = u_l' + s u_l/(v-1)` of the opposite-sign blocks. -/
def uRecN (s : ℕ) (G : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => iteratedDeriv s G
  | l + 1 => fun v => deriv (uRecN s G l) v + ((s / (v - 1) : ℝ) : ℂ) * uRecN s G l v

/-- The `l`-fold ladder image `ladUp (l-1) (-s) ∘ ⋯ ∘ ladUp 0 (-s)` of the profile `profile s G`. -/
def hLRN (s : ℕ) (G : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => profile s G
  | l + 1 => ladUp (l : ℝ) (-(s : ℝ)) (hLRN s G l)

/-- `uRecN` is smooth on `v > 1`. -/
theorem uRecN_contDiffOn (s : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ContDiffOn ℝ ∞ (uRecN s G l) (Ioi 1) := by
  induction l with
  | zero => exact (contDiff_iteratedDeriv_infty hG s).contDiffOn
  | succ l ih =>
    have h1 : ContDiffOn ℝ ∞ (deriv (uRecN s G l)) (Ioi 1) :=
      ih.deriv_of_isOpen isOpen_Ioi (by simp)
    have hr : ContDiffOn ℝ ∞ (fun v : ℝ => (s : ℝ) / (v - 1)) (Ioi 1) :=
      contDiffOn_const.div (contDiffOn_id.sub contDiffOn_const) fun v hv => by
        have : (1 : ℝ) < v := hv
        show v - 1 ≠ 0
        exact ne_of_gt (by linarith)
    have h2 : ContDiffOn ℝ ∞ (fun v : ℝ => ((s / (v - 1) : ℝ) : ℂ)) (Ioi 1) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hr
    exact h1.add (h2.mul ih)

/-- **Closed form of the opposite-sign ladder images**: on `ξ > 0`,
`hLRN s G l ξ = sinh^{l+s} ξ · u_l(cosh ξ)` with `u_{l+1} = u_l' + s u_l/(v - 1)`. -/
theorem hLRN_eq (s : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ∀ ξ : ℝ, 0 < ξ →
      hLRN s G l ξ = ((Real.sinh ξ ^ (l + s) : ℝ) : ℂ) * uRecN s G l (Real.cosh ξ) := by
  induction l with
  | zero => intro ξ _; simp [hLRN, uRecN, profile]
  | succ l ih =>
    intro ξ hξ
    have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
    have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hc1 : (1 : ℝ) < Real.cosh ξ := Real.one_lt_cosh.2 hξ.ne'
    have hc1' : ((Real.cosh ξ : ℂ) - 1) ≠ 0 := by
      have : ((Real.cosh ξ - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 hc1).ne'
      simpa using this
    have hrel : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 - ((Real.sinh ξ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cosh_sq_sub_sinh_sq ξ
    have hu : DifferentiableAt ℝ (uRecN s G l) (Real.cosh ξ) :=
      ((uRecN_contDiffOn s hG l).differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hc1)
    have hdu := hu.hasDerivAt.scomp ξ (Real.hasDerivAt_cosh ξ)
    have hp : HasDerivAt (fun y : ℝ => ((Real.sinh y ^ (l + s) : ℝ) : ℂ))
        (((((l + s : ℕ) : ℝ) * Real.sinh ξ ^ (l + s - 1) * Real.cosh ξ : ℝ)) : ℂ) ξ :=
      (((Real.hasDerivAt_sinh ξ).pow (l + s))).ofReal_comp
    have h := hp.mul hdu
    have h' : HasDerivAt (hLRN s G l) _ ξ := h.congr_of_eventuallyEq (f₁ := hLRN s G l)
      (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun y hy => ih y hy))
    show ladUp (l : ℝ) (-(s : ℝ)) (hLRN s G l) ξ = _
    unfold ladUp
    rw [h'.deriv, ih ξ hξ]
    simp only [ladCoeff, uRecN, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_pow, Complex.ofReal_one]
    rcases Nat.eq_zero_or_pos (l + s) with h0 | hpos
    · have hl : l = 0 := by omega
      have hs0 : s = 0 := by omega
      subst hl; subst hs0
      simp
    · obtain ⟨m, hm⟩ : ∃ m, l + s = m + 1 := ⟨l + s - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel, Nat.cast_succ]
      have e : l + 1 + s = m + 1 + 1 := by omega
      rw [e]
      have hm' : ((l : ℂ) + s) = m + 1 := by exact_mod_cast hm
      have hl : (l : ℂ) = m + 1 - s := by linear_combination hm'
      rw [hl]
      simp only [Function.comp_apply]
      field_simp
      linear_combination ((s : ℂ) * uRecN s G l (Real.cosh ξ) * (Real.sinh ξ : ℂ) ^ (m + 1)) * hrel

/-- Trust check: for `s = 0` the opposite-sign chain is the same-sign chain with `r = 0`. -/
theorem hLRN_zero_eq_hLR (G : ℝ → ℂ) (l : ℕ) : hLRN 0 G l = hLR 0 G l := by
  induction l with
  | zero => rfl
  | succ l ih => simp [hLRN, hLR, ih]

end Lightlike.Lorentz.SL2RPlancherel
