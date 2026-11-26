import Lightlike.Lorentz.SL2RPlancherel.LadderProfile

/-!
# Closed form of the ladder images of a radial function

For `G` smooth and `r : ℕ`, `hLR r G l` is the `l`-fold left ladder image `ladUp (l-1) r ∘ … ∘ ladUp 0 r` of the profile
`sinh^r ξ · G^{(r)}(cosh ξ)` (the type `(0, r)`), and `uRec r G l` is the recursion `u₀ = G^{(r)}`,
`u_{l+1} = u_l' + r u_l/(v+1)` in the variable `v`. `hLR_eq`: on `ξ > 0`,
`hLR r G l ξ = sinh^{l+r} ξ · u_l(cosh ξ)`, since
`ladUp l r (sinh^{l+r} · u∘cosh) = sinh^{l+r+1} · (u' + r u/(v+1))∘cosh`. In particular the ladder images vanish to order
`l + r` at `ξ = 0` with a factor that is smooth in `v`.
-/

open Set Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- The recursion `u₀ = G^{(r)}`, `u_{l+1} = u_l' + r u_l/(v+1)`. -/
def uRec (r : ℕ) (G : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => iteratedDeriv r G
  | l + 1 => fun v => deriv (uRec r G l) v + ((r / (v + 1) : ℝ) : ℂ) * uRec r G l v

/-- The `l`-fold left ladder image of the profile `profile r G`. -/
def hLR (r : ℕ) (G : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => profile r G
  | l + 1 => ladUp (l : ℝ) (r : ℝ) (hLR r G l)

/-- `uRec` is smooth on `v > -1`. -/
theorem uRec_contDiffOn (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ContDiffOn ℝ ∞ (uRec r G l) (Ioi (-1)) := by
  induction l with
  | zero => exact (contDiff_iteratedDeriv_infty hG r).contDiffOn
  | succ l ih =>
    have h1 : ContDiffOn ℝ ∞ (deriv (uRec r G l)) (Ioi (-1)) :=
      ih.deriv_of_isOpen isOpen_Ioi (by simp)
    have hr : ContDiffOn ℝ ∞ (fun v : ℝ => (r : ℝ) / (v + 1)) (Ioi (-1)) :=
      contDiffOn_const.div (contDiffOn_id.add contDiffOn_const) fun v hv => by
        have : (-1 : ℝ) < v := hv
        show v + 1 ≠ 0
        exact ne_of_gt (by linarith)
    have h2 : ContDiffOn ℝ ∞ (fun v : ℝ => ((r / (v + 1) : ℝ) : ℂ)) (Ioi (-1)) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn hr
    exact h1.add (h2.mul ih)

/-- **Closed form of the ladder images**: on `ξ > 0`, `hLR r G l ξ = sinh^{l+r} ξ · u_l(cosh ξ)`. -/
theorem hLR_eq (r : ℕ) {G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (l : ℕ) :
    ∀ ξ : ℝ, 0 < ξ → hLR r G l ξ = ((Real.sinh ξ ^ (l + r) : ℝ) : ℂ) * uRec r G l (Real.cosh ξ) := by
  induction l with
  | zero => intro ξ _; simp [hLR, uRec, profile]
  | succ l ih =>
    intro ξ hξ
    have hs : Real.sinh ξ ≠ 0 := (Real.sinh_pos_iff.2 hξ).ne'
    have hs' : ((Real.sinh ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
    have hc1 : (0 : ℝ) < Real.cosh ξ + 1 := by linarith [Real.one_le_cosh ξ]
    have hc1' : ((Real.cosh ξ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc1.ne'
    have hrel : ((Real.cosh ξ : ℝ) : ℂ) ^ 2 - ((Real.sinh ξ : ℝ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.cosh_sq_sub_sinh_sq ξ
    have hu : DifferentiableAt ℝ (uRec r G l) (Real.cosh ξ) :=
      ((uRec_contDiffOn r hG l).differentiableOn (by simp)).differentiableAt
        (Ioi_mem_nhds (by linarith [Real.one_le_cosh ξ]))
    have hdu := hu.hasDerivAt.scomp ξ (Real.hasDerivAt_cosh ξ)
    have hp : HasDerivAt (fun y : ℝ => ((Real.sinh y ^ (l + r) : ℝ) : ℂ))
        (((((l + r : ℕ) : ℝ) * Real.sinh ξ ^ (l + r - 1) * Real.cosh ξ : ℝ)) : ℂ) ξ :=
      (((Real.hasDerivAt_sinh ξ).pow (l + r))).ofReal_comp
    have h := hp.mul hdu
    have h' : HasDerivAt (hLR r G l) _ ξ := h.congr_of_eventuallyEq (f₁ := hLR r G l)
      (Filter.eventuallyEq_of_mem (Ioi_mem_nhds hξ) (fun y hy => ih y hy))
    show ladUp (l : ℝ) (r : ℝ) (hLR r G l) ξ = _
    unfold ladUp
    rw [h'.deriv, ih ξ hξ]
    simp only [ladCoeff, uRec, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_pow, Complex.ofReal_one]
    rcases Nat.eq_zero_or_pos (l + r) with h0 | hpos
    · have hl : l = 0 := by omega
      have hr0 : r = 0 := by omega
      subst hl; subst hr0
      simp
    · obtain ⟨m, hm⟩ : ∃ m, l + r = m + 1 := ⟨l + r - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel, Nat.cast_succ]
      have e : l + 1 + r = m + 1 + 1 := by omega
      rw [e]
      have hm' : ((l : ℂ) + r) = m + 1 := by exact_mod_cast hm
      have hl : (l : ℂ) = m + 1 - r := by linear_combination hm'
      have hc1'' : (1 + (Real.cosh ξ : ℂ)) ≠ 0 := by
        have : ((Real.cosh ξ + 1 : ℝ) : ℂ) = 1 + (Real.cosh ξ : ℂ) := by push_cast; ring
        rw [← this]; exact hc1'
      rw [hl]
      simp only [Function.comp_apply]
      field_simp
      have key : ((Real.sinh ξ : ℝ) : ℂ) ^ 2 * (1 + (Real.cosh ξ : ℂ))⁻¹ = (Real.cosh ξ : ℂ) - 1 := by
        field_simp
        linear_combination -hrel
      linear_combination (-((r : ℂ) * uRec r G l (Real.cosh ξ) * (Real.sinh ξ : ℂ) ^ (m + 1))) * key

end Lightlike.Lorentz.SL2RPlancherel
