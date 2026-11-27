module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileBdry
public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileLadderForm
public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileDecay

/-!
# Orthogonality of the ladder chain images to the profiles of `D_n⁻`, for every `n`

For `n = 2 (a + ν)` with `a ∈ {0, 1/2}` the radial profiles `ψ_{jk}`, `k ∈ ℕ`, of the antiholomorphic series `D_n⁻`
(of `K`-type `((n + 2k)/2, -(n + 2j)/2)`) satisfy the kernel equation `ladDown (a+ν) r ψ_{j0} = 0`, `r = -(n+2j)/2`,
and `ladDown (a+ν+k+1) r ψ_{j,k+1} = -(k+1) ψ_{jk}`. Hence every chain `H_{i+1} = ladUp (a+i) r H_i` of functions
continuous on `[0, ∞)` and vanishing for large `ξ` is orthogonal to `ψ_{jk}` in `L²(sinh ξ dξ)` at the index `i = ν + k`.
For `a = 0` (`n` even) this is the case of integral `K`-types, for `a = 1/2` (`n` odd) that of half-integral ones.
-/

@[expose] public section

open MeasureTheory Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **Orthogonality of ladder chain images to the radial profiles of `D_n⁻`, for every `n`**: with
`n = 2 (a + ν)`, `ν ≥ 1`, `r = -(n + 2j)/2`, and `H_{i+1} = ladUp (a+i) r H_i` for functions `H_i` continuous on `[0, ∞)`,
`C¹` on `(0, ∞)` and vanishing for large `ξ`: `∫_0^∞ H_{ν+k} conj(ψ_{jk}) sinh ξ dξ = 0` for all `k`. -/
theorem integral_chain_mul_profile_eq_zero (n j ν : ℕ) (a r : ℝ) (hν : 1 ≤ ν) (hn : 1 ≤ n)
    (hna : (n : ℝ) = 2 * (a + ν)) (hr : r = -((n + 2 * j : ℕ) : ℝ) / 2) (κ : ℂ) {H : ℕ → ℝ → ℂ}
    (hH1 : ∀ i, ContDiffOn ℝ 1 (H i) (Ioi 0)) (hHc : ∀ i, ContinuousOn (H i) (Ici 0))
    (hHR : ∀ i, ∃ R : ℝ, 0 < R ∧ ∀ ξ, R ≤ ξ → H i ξ = 0)
    (hstep : ∀ (i : ℕ) (ξ : ℝ), 0 < ξ → H (i + 1) ξ = ladUp (a + (i : ℝ)) r (H i) ξ) (k : ℕ) :
    ∫ ξ in Ioi (0 : ℝ), H (ν + k) ξ * (starRingEnd ℂ) (profileFun n k j κ ξ) * (Real.sinh ξ : ℂ) = 0 := by
  subst hr
  exact integral_chain_mul_conj_eq_zero_off a (-((n + 2 * j : ℕ) : ℝ) / 2) ν hν (G := fun k ξ => profileFun n k j κ ξ)
    (fun k => -((k + 1 : ℕ) : ℝ))
    (fun k => contDiffOn_profileFun n k j hn κ)
    (fun k => (continuous_profileFun n k j hn κ).continuousOn)
    (fun ξ hξ => by
      have h := ladDown_profileFun_zero_minus n j hn κ hξ
      have e1 : (((n + 2 * 0 : ℕ) : ℝ) / 2) = a + (ν : ℝ) := by push_cast; linarith
      rw [e1] at h
      exact h)
    (fun k ξ hξ => by
      have h := ladDown_profileFun_succ_minus n k j hn κ hξ
      have e1 : (((n + 2 * (k + 1) : ℕ) : ℝ) / 2) = a + ((ν + k + 1 : ℕ) : ℝ) := by push_cast; linarith
      rw [e1] at h
      rw [h]
      push_cast
      ring)
    hH1 hHc hHR hstep k

end Lightlike.Lorentz.SL2RPlancherel
