import Lightlike.Cosmology.BianchiIXWainwrightHsu.WainwrightHsu

/-!
# Preservation of the constraint and of the signs of `Nᵢ` (row G1-040, milestone CO14)

Along a solution `γ` of the Wainwright–Hsu system, `G' = 2 q G` and `Nᵢ' = fᵢ Nᵢ`; a linear
scalar equation `f' = a f` with continuous `a` gives `f t = f 0 · exp (∫₀ᵗ a)`
(`linear_ode_exp`). Hence the constraint `G = 0` holds at all times as soon as it holds at one
time (`IsSol.Gc_eq_zero`), and `N₁N₂N₃ > 0` (type IX) is preserved (`IsSol.prod_pos`).
-/

namespace Lightlike.Rows.G1_040

open Real

noncomputable section

/-- A linear scalar ODE `f' = a f` with continuous coefficient has the solution
`f t = f 0 · exp (∫₀ᵗ a)`. -/
lemma linear_ode_exp {f a : ℝ → ℝ} (ha : Continuous a)
    (hf : ∀ t, HasDerivAt f (a t * f t) t) (t : ℝ) :
    f t = f 0 * Real.exp (∫ s in (0 : ℝ)..t, a s) := by
  have hI : ∀ s, HasDerivAt (fun u => ∫ r in (0 : ℝ)..u, a r) (a s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
      (ha.stronglyMeasurableAtFilter _ _) ha.continuousAt
  have hg : ∀ s, HasDerivAt (fun u => f u * Real.exp (-∫ r in (0 : ℝ)..u, a r)) 0 s := by
    intro s
    have h1 := (hI s).neg.exp
    have h2 := (hf s).mul h1
    refine h2.congr_deriv ?_
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at hc
  have := congrArg (· * Real.exp (∫ s in (0 : ℝ)..t, a s)) hc
  simp only at this
  rw [mul_assoc, ← Real.exp_add] at this
  simpa using this

/-- Continuity of the components of a solution. -/
lemma IsSol.continuous {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) : Continuous γ :=
  continuous_iff_continuousAt.2 fun t => (h t).continuousAt

lemma qd_continuous : Continuous qd := by
  unfold qd sp sm
  fun_prop

/-- The derivative of the constraint function along a solution is `2 q G`. -/
lemma IsSol.Gc_deriv {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (t : ℝ) :
    HasDerivAt (fun s => Gc (γ s)) ((2 * qd (γ t)) * Gc (γ t)) t := by
  have h0 := h.comp 0 t
  have h1 := h.comp 1 t
  have h2 := h.comp 2 t
  have h3 := h.comp 3 t
  have h4 := h.comp 4 t
  have hs : HasDerivAt (fun s => Gc (γ s)) (dG (γ t)) t := by
    have e := ((((h0.pow 2).add (h1.pow 2)).add
      ((((((h2.pow 2).add (h3.pow 2)).add (h4.pow 2)).sub
        ((((h2.mul h3).add (h3.mul h4)).add (h4.mul h2)).const_mul 2))).const_mul (3 / 4))).sub_const 1)
    refine e.congr_deriv ?_
    simp only [dG, sp, sm, n1, n2, n3]
    ring
  rw [constraint_deriv] at hs
  exact hs

/-- **The constraint is preserved**: if `G = 0` at one time it holds at all times. -/
lemma IsSol.Gc_eq_zero {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (t₀ : ℝ) (h0 : Gc (γ t₀) = 0) (t : ℝ) :
    Gc (γ t) = 0 := by
  have hc : Continuous fun s => 2 * qd (γ s) := continuous_const.mul (qd_continuous.comp h.continuous)
  have key := linear_ode_exp hc (f := fun s => Gc (γ s)) (h.Gc_deriv)
  have hz : Gc (γ 0) = 0 := by
    have k0 := key t₀
    rw [h0] at k0
    rcases mul_eq_zero.1 k0.symm with h' | h'
    · exact h'
    · exact absurd h' (Real.exp_pos _).ne'
  simp [key t, hz]

/-- A component with `vf x i = a x * x i`, `a` continuous, keeps its sign along a solution:
`γ t i = γ 0 i · exp(∫ a)`. -/
lemma IsSol.comp_exp {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (i : Fin 5) (a : (Fin 5 → ℝ) → ℝ)
    (ha : Continuous a) (hv : ∀ x, vf x i = a x * x i) (t : ℝ) :
    γ t i = γ 0 i * Real.exp (∫ s in (0 : ℝ)..t, a (γ s)) := by
  refine linear_ode_exp (f := fun s => γ s i) (a := fun s => a (γ s)) (ha.comp h.continuous)
    (fun s => ?_) t
  have := h.comp i s
  rwa [hv] at this

/-- `N₁` keeps its sign along a solution. -/
lemma IsSol.n1_pos {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (h0 : 0 < n1 (γ 0)) (t : ℝ) :
    0 < n1 (γ t) := by
  have := h.comp_exp 2 (fun x => qd x - 4 * sp x) (by unfold qd sp sm; fun_prop)
    (fun x => by simp [vf, n1]) t
  simp only [n1] at h0 ⊢
  rw [this]
  exact mul_pos h0 (Real.exp_pos _)

/-- `N₂` keeps its sign along a solution. -/
lemma IsSol.n2_pos {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (h0 : 0 < n2 (γ 0)) (t : ℝ) :
    0 < n2 (γ t) := by
  have := h.comp_exp 3 (fun x => qd x + 2 * sp x + 2 * √3 * sm x)
    (by unfold qd sp sm; fun_prop) (fun x => by simp [vf, n2]) t
  simp only [n2] at h0 ⊢
  rw [this]
  exact mul_pos h0 (Real.exp_pos _)

/-- `N₃` keeps its sign along a solution. -/
lemma IsSol.n3_pos {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ) (h0 : 0 < n3 (γ 0)) (t : ℝ) :
    0 < n3 (γ t) := by
  have := h.comp_exp 4 (fun x => qd x + 2 * sp x - 2 * √3 * sm x)
    (by unfold qd sp sm; fun_prop) (fun x => by simp [vf, n3]) t
  simp only [n3] at h0 ⊢
  rw [this]
  exact mul_pos h0 (Real.exp_pos _)

/-- **Type IX is preserved**: if all `Nᵢ > 0` at time `0`, then at all times, and `N₁N₂N₃` is
non-decreasing. -/
lemma IsSol.prod_monotone_of_pos {γ : ℝ → Fin 5 → ℝ} (h : IsSol γ)
    (h1 : 0 < n1 (γ 0)) (h2 : 0 < n2 (γ 0)) (h3 : 0 < n3 (γ 0)) :
    Monotone (fun s => n1 (γ s) * n2 (γ s) * n3 (γ s)) :=
  h.prod_monotone fun t =>
    (mul_pos (mul_pos (h.n1_pos h1 t) (h.n2_pos h2 t)) (h.n3_pos h3 t)).le

end

end Lightlike.Rows.G1_040
