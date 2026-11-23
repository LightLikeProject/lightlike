module

public import Lightlike.Rows.G1_028.SlowRoll

/-!
# The slow-roll number of e-folds from the dynamics

Units `8πG = 1`.  In slow roll the Friedmann equation `3H² = φ̇²/2 + V` reduces to `3H² = V` and
the Klein–Gordon equation `φ̈ + 3Hφ̇ + V′ = 0` reduces to `3Hφ̇ = −V′`.  Dividing,
`H/φ̇ = −V/V′`, so `dN = H dt = −(V/V′) dφ` and the number of e-folds
`N = ∫_{t_i}^{t_e} H dt` equals `∫_{φ_e}^{φ_i} V/V′ dφ` (`eFolds`).

* `slowRoll_hubble_eq` : pointwise, `H = −(V/V′)(φ) · φ̇`.
* `eFolds_eq_integral_hubble` : `N = ∫_{t_i}^{t_e} H dt = eFolds V (φ t_i) (φ t_e)`.

**References.** Baumann, *TASI Lectures on Inflation* (`baumann-2009`), Section 6.2.
-/

@[expose] public section

open intervalIntegral Set

noncomputable section

namespace Lightlike

namespace Cosmology

namespace SlowRoll

/-- Pointwise slow-roll identity: from `3H² = V` and `3Hφ̇ = −V′` with `V′ ≠ 0` one gets
`H = −(V/V′) · φ̇`. -/
lemma slowRoll_hubble_eq {V' Vv H φd : ℝ} (hV' : V' ≠ 0)
    (hF : 3 * H ^ 2 = Vv) (hKG : 3 * H * φd = -V') :
    H = -(Vv / V') * φd := by
  have hH : H ≠ 0 := by
    rintro rfl
    apply hV'
    linarith
  have hφd : φd ≠ 0 := by
    rintro rfl
    apply hV'
    linarith
  have hV : V' = -(3 * H * φd) := by linarith
  rw [← hF, hV]
  field_simp

/-- **Number of e-folds from the dynamics.** Along a `C¹` field path `φ(t)` on `[a, b]` obeying the
slow-roll equations `3H² = V(φ)` and `3Hφ̇ = −V′(φ)` with `V′(φ) ≠ 0`, and with `V/V′` continuous
on the range of `φ`, the number of e-folds `∫_a^b H dt` equals `∫_{φ(b)}^{φ(a)} V/V′ dφ`. -/
theorem eFolds_eq_integral_hubble {V φ φd H : ℝ → ℝ} {a b : ℝ}
    (hφ : ∀ t ∈ uIcc a b, HasDerivAt φ (φd t) t) (hφd : ContinuousOn φd (uIcc a b))
    (hg : ContinuousOn (fun x => V x / deriv V x) (φ '' uIcc a b))
    (hV' : ∀ t ∈ uIcc a b, deriv V (φ t) ≠ 0)
    (hF : ∀ t ∈ uIcc a b, 3 * H t ^ 2 = V (φ t))
    (hKG : ∀ t ∈ uIcc a b, 3 * H t * φd t = -deriv V (φ t)) :
    ∫ t in a..b, H t = eFolds V (φ a) (φ b) := by
  have h1 : ∫ t in a..b, H t
      = ∫ t in a..b, -(((fun x => V x / deriv V x) ∘ φ) t * φd t) := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have := slowRoll_hubble_eq (hV' t ht) (hF t ht) (hKG t ht)
    simp only [Function.comp]
    rw [this]
    ring
  rw [h1, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_mul_deriv' hφ hφd hg, eFolds,
    intervalIntegral.integral_symm (φ a) (φ b)]

end SlowRoll

end Cosmology

end Lightlike
