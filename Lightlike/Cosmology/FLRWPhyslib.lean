module

public import Lightlike.Cosmology.FLRW
public import Physlib.Cosmology.FLRW.Basic

/-!
# The Friedmann equations: ours and Physlib's

`FirstFriedmann` and `SecondFriedmann` (in `Lightlike.Cosmology.FLRW`) take the scale factor, the
density and the pressure as functions `ℝ → ℝ`, in units `c = 1`. Physlib's
`Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann` and `SecondOrderFriedmann` take functions on
Physlib's `Time` and keep `c` explicit. This file reads a function of the real time coordinate as a
function on `Time` (`onTime`), proves that the two forms of each equation agree at `c = 1`, and
restates `flrw_einstein_iff_friedmann` with Physlib's equations on the right.

* `timeDeriv_onTime` : Physlib's time derivative `∂ₜ (onTime f)` is `deriv f`, with no
  differentiability hypothesis.
* `firstOrderFriedmann_onTime_iff`, `secondOrderFriedmann_onTime_iff` : the two equations agree.
* `flrw_einstein_iff_physlib_friedmann` : Einstein's equations for the FLRW metric with a perfect
  fluid hold iff Physlib's two Friedmann equations hold at `c = 1`.
-/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace Lightlike.Cosmology

open Time

/-- A function of the real time coordinate, read as a function on Physlib's `Time`. -/
def onTime (f : ℝ → ℝ) : Time → ℝ := fun s => f s.val

/-- Physlib's time derivative of `onTime f` is the ordinary derivative of `f`. No
differentiability is needed: both sides are `0` where `f` is not differentiable. -/
theorem timeDeriv_onTime (f : ℝ → ℝ) (t : Time) : ∂ₜ (onTime f) t = deriv f t.val := by
  have h : onTime f = f ∘ toRealCLE := rfl
  rw [Time.deriv_eq, h, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, show toRealCLE (1 : Time) = 1 from Time.one_val]
  rfl

/-- `timeDeriv_onTime` as an equality of functions on `Time`. -/
theorem timeDeriv_onTime_eq (f : ℝ → ℝ) : ∂ₜ (onTime f) = onTime (deriv f) :=
  funext (timeDeriv_onTime f)

/-- Our first Friedmann equation is Physlib's `FirstOrderFriedmann` at `c = 1`. -/
theorem firstOrderFriedmann_onTime_iff (a ρ : ℝ → ℝ) (k Λ Gn : ℝ) (t : Time) :
    _root_.Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann (onTime a) (onTime ρ) k Λ Gn 1 t ↔
      FirstFriedmann a ρ k Λ Gn t.val := by
  unfold _root_.Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann FirstFriedmann
  rw [timeDeriv_onTime]
  simp only [onTime, one_pow, mul_one]

/-- Our second Friedmann equation is Physlib's `SecondOrderFriedmann` at `c = 1`. -/
theorem secondOrderFriedmann_onTime_iff (a ρ p : ℝ → ℝ) (Λ Gn : ℝ) (t : Time) :
    _root_.Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann (onTime a) (onTime ρ) (onTime p)
        Λ Gn 1 t ↔
      SecondFriedmann a ρ p Λ Gn t.val := by
  unfold _root_.Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann SecondFriedmann
  rw [timeDeriv_onTime_eq, timeDeriv_onTime]
  simp only [onTime, one_pow, mul_one, div_one]

/-- **CO1, with Physlib's Friedmann equations.** For `a > 0` smooth on an open interval `I`,
Einstein's equations for the FLRW metric with a perfect fluid hold on the chart iff Physlib's
`FirstOrderFriedmann` and `SecondOrderFriedmann` hold, at `c = 1`, at every time in `I`. -/
theorem flrw_einstein_iff_physlib_friedmann {I : Set ℝ} (hI : IsOpen I) {a ρ p : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) (k Λ Gn : ℝ) :
    IsEinsteinSolution Λ Gn (flrwMetric a k) (perfectFluid ρ p (flrwMetric a k))
        (flrwDomain I k) ↔
      ∀ t : Time, t.val ∈ I →
        _root_.Cosmology.FLRW.FriedmannEquation.FirstOrderFriedmann (onTime a) (onTime ρ) k Λ Gn
            1 t ∧
          _root_.Cosmology.FLRW.FriedmannEquation.SecondOrderFriedmann (onTime a) (onTime ρ)
            (onTime p) Λ Gn 1 t := by
  rw [flrw_einstein_iff_friedmann hI ha hpos]
  simp only [firstOrderFriedmann_onTime_iff, secondOrderFriedmann_onTime_iff]
  exact ⟨fun h t ht => h t.val ht, fun h t ht => h ⟨t⟩ ht⟩

end Lightlike.Cosmology
