import Mathlib
import Lightlike.Lorentz.SL2RPlancherel.PrincipalPairing

/-!
# The radial Casimir equation of the principal-series matrix coefficients

The matrix coefficients `Φ^ν_{m,n}` are smooth (`contDiff_mcoefP`), since their derivative is a
combination of the neighbouring coefficients, and they solve the radial Casimir equation of the
`K`-type `(n, -m)` with the eigenvalue `-w(w + 1) = 1/4 + ν²/4`:
`radialCasimir_{n,-m} Φ^ν_{m,n} = -w(w + 1) Φ^ν_{m,n}` on `ξ > 0` (`radialCasimir_mcoefP`), from the
factorisation `ladDown_{n+1} ∘ ladUp_n = radialCasimir_n + n(n + 1)` and the ladder identities.
Layer 2c-v of the Plancherel formula on `SL(2,ℝ)` (opposite-sign blocks), milestone HA3.
-/

open MeasureTheory Set Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma ladDown_congr (l r : ℝ) {F F' : ℝ → ℂ} {ξ : ℝ} (h : F =ᶠ[nhds ξ] F') :
    ladDown l r F ξ = ladDown l r F' ξ := by
  unfold ladDown
  rw [h.deriv_eq, h.self_of_nhds]

/-- **The matrix coefficients are smooth.** -/
theorem contDiff_mcoefP (ν : ℝ) (m n : ℤ) : ContDiff ℝ ∞ (mcoefP ν m n) := by
  suffices h : ∀ k : ℕ, ∀ n : ℤ, ContDiff ℝ k (mcoefP ν m n) from
    contDiff_infty.2 fun k => h k n
  intro k
  induction k with
  | zero => intro n; exact contDiff_zero.2 (continuous_mcoefP ν m n)
  | succ k ih =>
    intro n
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun ξ => (hasDerivAt_mcoefP ν m n ξ).differentiableAt, by simp, ?_⟩
    have e : deriv (mcoefP ν m n) = fun ξ => (wP ν - n) / 2 * mcoefP ν m (n + 1) ξ +
        (wP ν + n) / 2 * mcoefP ν m (n - 1) ξ :=
      funext fun ξ => (hasDerivAt_mcoefP ν m n ξ).deriv
    rw [e]
    exact (contDiff_const.mul (ih (n + 1))).add (contDiff_const.mul (ih (n - 1)))

/-- **The radial Casimir equation**: on `ξ > 0`,
`radialCasimir_{n,-m} Φ^ν_{m,n} = -w(w + 1) Φ^ν_{m,n}`. -/
theorem radialCasimir_mcoefP (ν : ℝ) (m n : ℤ) {ξ : ℝ} (hξ : 0 < ξ) :
    radialCasimir n (-m) (mcoefP ν m n) ξ = -(wP ν * (wP ν + 1)) * mcoefP ν m n ξ := by
  have h2 : ContDiff ℝ 2 (mcoefP ν m n) := (contDiff_mcoefP ν m n).of_le (by norm_cast)
  have hdl := ladDown_ladUp (n : ℝ) (-(m : ℝ)) h2 hξ
  have hup : ladUp (n : ℝ) (-(m : ℝ)) (mcoefP ν m n) =ᶠ[nhds ξ]
      fun t => (wP ν - n) * mcoefP ν m (n + 1) t := by
    filter_upwards [Ioi_mem_nhds hξ] with t ht
    exact ladUp_mcoefP ν m n (ne_of_gt ht)
  rw [ladDown_congr _ _ hup] at hdl
  have hlin : ladDown ((n : ℝ) + 1) (-(m : ℝ)) (fun t => (wP ν - n) * mcoefP ν m (n + 1) t) ξ =
      (wP ν - n) * ladDown ((n : ℝ) + 1) (-(m : ℝ)) (mcoefP ν m (n + 1)) ξ := by
    simp only [ladDown]
    rw [deriv_const_mul _ (hasDerivAt_mcoefP ν m (n + 1) ξ).differentiableAt]
    ring
  have hd := ladDown_mcoefP ν m (n + 1) (ne_of_gt hξ)
  push_cast at hd
  simp only [add_sub_cancel_right] at hd
  rw [hlin, hd] at hdl
  push_cast at hdl
  linear_combination (-1 : ℂ) * hdl

end Lightlike.Lorentz.SL2RPlancherel
