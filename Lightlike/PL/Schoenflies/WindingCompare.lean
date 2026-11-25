import Mathlib
import Lightlike.PL.IndexCurve
import Lightlike.PL.IndexTriangle
import Lightlike.PL.IndexConstancy

/-!
# Winding numbers of two close loops, and of a loop with a path to infinity

Row G3-188 (PL5), step 3 of the pass-4 plan.

* `period_inc_eq_of_close` (dog-walking): if `‖ψ - f‖ < ‖f - z‖` along two loops of the circle, the period
  increments of global logarithms of `ψ - z` and `f - z` agree.
* `period_inc_zero_of_joined`: a loop `ψ` with a path in the complement of its range from `z` to a point far
  from the loop has period increment `0` about `z`.
-/

open Complex Set unitInterval Real

namespace Lightlike.PL.Schoenflies

theorem period_inc_eq_of_close {f ψ : Circle → ℂ} (hf : Continuous f) (hψ : Continuous ψ) {z : ℂ}
    (hclose : ∀ t, ‖ψ t - f t‖ < ‖f t - z‖) {Ff Fψ : ℝ → ℂ} (hFf : Continuous Ff) (hFψ : Continuous Fψ)
    (hf' : ∀ s, exp (Ff s) = f (Circle.exp s) - z) (hψ' : ∀ s, exp (Fψ s) = ψ (Circle.exp s) - z) :
    Fψ (2 * π) - Fψ 0 = Ff (2 * π) - Ff 0 := by
  have hne : ∀ s, f (Circle.exp s) - z ≠ 0 := fun s h => by
    have := hf' s; rw [h] at this; exact exp_ne_zero _ this
  set r : ℝ → ℂ := fun s => (ψ (Circle.exp s) - z) / (f (Circle.exp s) - z) with hr
  have hrslit : ∀ s, r s ∈ Complex.slitPlane := by
    intro s
    have h1 := hclose (Circle.exp s)
    have hpos : 0 < ‖f (Circle.exp s) - z‖ := norm_pos_iff.2 (hne s)
    have h2 : ‖r s - 1‖ < 1 := by
      have : r s - 1 = (ψ (Circle.exp s) - f (Circle.exp s)) / (f (Circle.exp s) - z) := by
        rw [hr]; simp only []; field_simp [hne s]; ring
      rw [this, norm_div, div_lt_one hpos]; exact h1
    have h3 : 0 < (r s).re := by
      have := Complex.abs_re_le_norm (r s - 1)
      have h4 : |(r s - 1).re| < 1 := lt_of_le_of_lt this h2
      rw [Complex.sub_re, Complex.one_re] at h4
      have := (abs_lt.1 h4).1
      linarith
    exact Or.inl h3
  have hrc : Continuous r := by
    rw [hr]
    refine Continuous.div ((hψ.comp Circle.exp.continuous).sub continuous_const)
      ((hf.comp Circle.exp.continuous).sub continuous_const) hne
  set G : ℝ → ℂ := fun s => Fψ s - Ff s with hG
  have hGexp : ∀ s, exp (G s) = r s := by
    intro s; rw [hG, hr]; simp only []; rw [Complex.exp_sub, hψ', hf']
  set L : ℝ → ℂ := fun s => Complex.log (r s) with hL
  have hLc : Continuous L := by
    rw [hL]; exact continuous_iff_continuousAt.2 fun s => (continuousAt_clog (hrslit s)).comp hrc.continuousAt
  have hLexp : ∀ s, exp (L s) = r s := fun s => by
    rw [hL]; simp only []; exact exp_log (Complex.slitPlane_ne_zero (hrslit s))
  have hGc : Continuous G := hFψ.sub hFf
  set c : ℂ := G 0 - L 0 with hc
  have hexpc : exp c = 1 := by rw [hc, Complex.exp_sub, hGexp, hLexp, div_self]; exact Complex.slitPlane_ne_zero (hrslit 0)
  have hEq : ∀ s, G s - c = L s := by
    have hcov := Complex.isCoveringMap_exp
    have hmain : (fun s => G s - c) = L := by
      refine hcov.eq_of_comp_eq (A := ℝ) (f := fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {w : ℂ // w ≠ 0}))
        (hGc.sub continuous_const) hLc ?_ 0 (by simp [hc])
      funext s
      apply Subtype.ext
      simp only [Function.comp_apply]
      rw [Complex.exp_sub, hGexp, hexpc, div_one, hLexp]
    exact fun s => congrFun hmain s
  have hper : r (2 * π) = r 0 := by
    rw [hr]; simp only []; rw [Circle.exp_two_pi, Circle.exp_zero]
  have h1 := hEq (2 * π)
  have h2 := hEq 0
  have h3 : L (2 * π) = L 0 := by rw [hL]; simp only []; rw [hper]
  have : G (2 * π) - G 0 = 0 := by linear_combination h1 - h2 + h3
  rw [hG] at this
  simp only [] at this
  linear_combination this

/-- The loop `t ↦ ψ (exp (2π t))` as a path. -/
noncomputable def circleLoop (ψ : Circle → ℂ) (hψ : Continuous ψ) : Path (ψ (Circle.exp 0)) (ψ (Circle.exp 0)) where
  toFun t := ψ (Circle.exp (2 * π * (t : ℝ)))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp [Circle.exp_two_pi]

theorem period_inc_zero_of_joined {ψ : Circle → ℂ} (hψ : Continuous ψ) {z w : ℂ}
    (hj : JoinedIn (range ψ)ᶜ z w) {ρ : ℝ} (hρ : ∀ t, ‖ψ t‖ ≤ ρ) (hw : ρ < ‖w‖) {F : ℝ → ℂ}
    (hFc : Continuous F) (hF : ∀ s, exp (F s) = ψ (Circle.exp s) - z) : F (2 * π) = F 0 := by
  set α := circleLoop ψ hψ with hα
  have hrange : range α ⊆ range ψ := by
    rintro _ ⟨t, rfl⟩; exact ⟨_, rfl⟩
  have hj' : JoinedIn (range α)ᶜ z w := hj.mono (fun x hx hx' => hx (hrange hx'))
  have hidx : loopIndex α z = loopIndex α w := loopIndex_eq_of_joinedIn α hj'
  have hα0 : ∀ t, ‖α t‖ ≤ ρ := fun t => hρ _
  have hw0 : loopIndex α w = 0 := loopIndex_eq_zero_of_far α hα0 hw
  have hav : ∀ t, α t ≠ z := fun t h => by
    have := hF (2 * π * (t : ℝ))
    have h' : ψ (Circle.exp (2 * π * (t : ℝ))) = z := h
    rw [h', sub_self] at this
    exact exp_ne_zero _ this
  have hinc : logInc α z = F (2 * π) - F 0 := by
    have := logInc_arc hFc hF (a := 0) (b := 2 * π) α (fun t => by
      show ψ (Circle.exp (2 * π * (t : ℝ))) = _
      simp [mul_comm])
    exact this
  have h1 := loopIndex_spec α hav
  rw [hidx, hw0, hinc] at h1
  simpa [sub_eq_zero] using h1

end Lightlike.PL.Schoenflies
