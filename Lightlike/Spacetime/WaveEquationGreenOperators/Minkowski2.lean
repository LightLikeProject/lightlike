module

public import Mathlib

/-!
# The retarded Green operator of the 1+1 wave operator, in light-cone coordinates (row G1-059)

On `ℝ × ℝ` with light-cone coordinates `(u, v) = (t - x, t + x)` the wave operator
`∂ₜ² - ∂ₓ²` is `4 ∂ᵤ ∂ᵥ`.  We define it as `box` and the retarded operator
`Gret f (u, v) = 1/4 ∫_{b ≤ v} ∫_{a ≤ u} f (a, b)`, and prove `box (Gret f) = f` for continuous
compactly supported `f` (the `P ∘ G = id` half of the Green operator property, BGP key `bgp-2007`,
Section 3.4).  The remaining halves are in the later files of this folder.

* `box`, `Gret`: the operators;
* `hasDerivAt_integral_Iic`: the fundamental theorem of calculus for `x ↦ ∫_{t ≤ x} g t`;
* `box_Gret`: `box (Gret f) = f`.
-/

@[expose] public section

open MeasureTheory Set

namespace Lightlike.GreenOps.Mink2

/-- The wave operator `∂ₜ² - ∂ₓ² = 4 ∂ᵤ ∂ᵥ` in light-cone coordinates `(u, v)`,
`box f (u, v) = 4 ∂ᵤ (∂ᵥ f)`. -/
noncomputable def box (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  4 * deriv (fun u => deriv (fun v => f (u, v)) p.2) p.1

/-- The retarded Green operator in light-cone coordinates:
`Gret f (u, v) = 1/4 ∫_{b ≤ v} ∫_{a ≤ u} f (a, b) da db`. -/
noncomputable def Gret (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / 4) * ∫ b in Iic p.2, ∫ a in Iic p.1, f (a, b)

/-- Fundamental theorem of calculus for the primitive `x ↦ ∫_{t ≤ x} g t` of an integrable
continuous function. -/
lemma hasDerivAt_integral_Iic {g : ℝ → ℝ} (hg : Continuous g) (hi : Integrable g) (x : ℝ) :
    HasDerivAt (fun y => ∫ t in Iic y, g t) (g x) x := by
  have h : ∀ y, ∫ t in Iic y, g t = (∫ t in Iic 0, g t) + ∫ t in (0 : ℝ)..y, g t := by
    intro y
    have := intervalIntegral.integral_Iic_sub_Iic (μ := volume) hi.integrableOn hi.integrableOn
      (a := 0) (b := y)
    linarith
  have h' : (fun y => ∫ t in Iic y, g t) =
      fun y => (∫ t in Iic 0, g t) + ∫ t in (0 : ℝ)..y, g t := funext h
  rw [h']
  exact ((hg.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

/-- A compactly supported function on `ℝ × ℝ` vanishes outside a square. -/
lemma exists_bound {f : ℝ × ℝ → ℝ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, ∀ p, f p ≠ 0 → |p.1| < R ∧ |p.2| < R := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.exists_norm_le
  refine ⟨R + 1, fun p hp => ?_⟩
  have h := hR p (subset_tsupport _ hp)
  have h1 : ‖p.1‖ ≤ R := (norm_fst_le p).trans h
  have h2 : ‖p.2‖ ≤ R := (norm_snd_le p).trans h
  rw [Real.norm_eq_abs] at h1 h2
  exact ⟨by linarith, by linarith⟩

variable {f : ℝ × ℝ → ℝ} {R : ℝ}

/-- Slices `a ↦ f (a, b)` of a continuous function vanishing outside a square are integrable. -/
lemma integrable_slice1 (hc : Continuous f) (hR : ∀ p, f p ≠ 0 → |p.1| < R ∧ |p.2| < R)
    (b : ℝ) : Integrable (fun a => f (a, b)) := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) ?_)
  intro a ha
  by_contra h
  have h1 : |a| < R := (hR _ h).1
  exact ha ⟨(abs_lt.mp h1).1.le, (abs_lt.mp h1).2.le⟩

/-- The inner primitive is the interval integral from `-R`. -/
lemma phi_eq (hc : Continuous f) (hR : ∀ p, f p ≠ 0 → |p.1| < R ∧ |p.2| < R) (u b : ℝ) :
    ∫ a in Iic u, f (a, b) = ∫ a in (-R)..u, f (a, b) := by
  have h := intervalIntegral.integral_Iic_sub_Iic (μ := volume)
    (integrable_slice1 hc hR b).integrableOn (integrable_slice1 hc hR b).integrableOn
    (a := -R) (b := u)
  have h0 : ∫ a in Iic (-R), f (a, b) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro a ha
    by_contra h'
    have h1 : |a| < R := (hR _ h').1
    have h2 : a ≤ -R := ha
    linarith [(abs_lt.mp h1).1]
  linarith

/-- The inner primitive depends continuously on the outer variable. -/
lemma continuous_phi (hc : Continuous f) (hR : ∀ p, f p ≠ 0 → |p.1| < R ∧ |p.2| < R) (u : ℝ) :
    Continuous fun b => ∫ a in Iic u, f (a, b) := by
  have : (fun b => ∫ a in Iic u, f (a, b)) = fun b => ∫ a in (-R)..u, f (a, b) :=
    funext fun b => phi_eq hc hR u b
  rw [this]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun b a => f (a, b)) (hc.comp continuous_swap) _ _

/-- The inner primitive is integrable in the outer variable. -/
lemma integrable_phi (hc : Continuous f) (hR : ∀ p, f p ≠ 0 → |p.1| < R ∧ |p.2| < R) (u : ℝ) :
    Integrable fun b => ∫ a in Iic u, f (a, b) := by
  refine Continuous.integrable_of_hasCompactSupport (continuous_phi hc hR u)
    (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) ?_)
  intro b hb
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro a _
  by_contra h
  have h1 : |b| < R := (hR _ h).2
  exact hb ⟨(abs_lt.mp h1).1.le, (abs_lt.mp h1).2.le⟩

/-- `box ∘ Gret = id` on continuous compactly supported functions. -/
theorem box_Gret (hc : Continuous f) (hcs : HasCompactSupport f) : box (Gret f) = f := by
  obtain ⟨R, hR⟩ := exists_bound hcs
  funext ⟨u, v⟩
  have step : ∀ u' : ℝ, deriv (fun v' => Gret f (u', v')) v = 1 / 4 * ∫ a in Iic u', f (a, v) := by
    intro u'
    have h := (hasDerivAt_integral_Iic (continuous_phi hc hR u') (integrable_phi hc hR u') v)
    exact (h.const_mul (1 / 4)).deriv
  have h2 : (fun u' => deriv (fun v' => Gret f (u', v')) v) =
      fun u' => 1 / 4 * ∫ a in Iic u', f (a, v) := funext step
  have h3 := (hasDerivAt_integral_Iic (g := fun a => f (a, v)) (by fun_prop)
    (integrable_slice1 hc hR v) u).const_mul (1 / 4)
  unfold box
  dsimp only
  rw [h2, h3.deriv]
  ring

end Lightlike.GreenOps.Mink2
