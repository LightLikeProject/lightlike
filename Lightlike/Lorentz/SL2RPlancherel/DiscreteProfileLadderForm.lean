module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProfileODE
public import Lightlike.Lorentz.SL2RPlancherel.Ladder

/-!
# The radial profiles of the discrete series in the ladder operators of the `K`-type equations

The radial profile `ψ_{jl}(ξ) = ⟨e_j, D_n(a(ξ)) e_l⟩ / ‖e_j‖²` (`profileFun`, with `κ = ‖e_j‖²` it is the matrix
coefficient, `profile_eq_mcoef`) has `K × K`-weights `-(n + 2j), -(n + 2l)`, i.e. `K`-type
`(l', r') = (-(n + 2l)/2, (n + 2j)/2)` in the notation of `Ladder.lean`. For `ξ > 0`:
* `ladUp l' r' ψ_{j,k+1} = (k + 1) ψ_{jk}` and `ladUp l' r' ψ_{j0} = 0` (`ladUp_profileFun_succ`,
  `ladUp_profileFun_zero`): the lowest weight vector `e_0` is killed by the raising operator;
* `ladDown l' r' ψ_{jl} = (n + l) ψ_{j,l+1}` (`ladDown_profileFun`).

The complex conjugate profile (the coefficient of the antiholomorphic series `D_n⁻`, of `K`-type
`((n + 2l)/2, -(n + 2j)/2)`) satisfies the mirror equations; in particular `ladDown ((n)/2) (-(n + 2j)/2) ψ_{j0} = 0`
(`ladDown_profileFun_zero_minus`), the kernel equation of the lowering operator adjoint to the raising operator.
-/

@[expose] public section

open Set Real

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

lemma ladCoeff_eq_neg_ladB (n j l : ℕ) (ξ : ℝ) :
    ladCoeff (-((n + 2 * l : ℕ) : ℝ) / 2) (((n + 2 * j : ℕ) : ℝ) / 2) ξ = -ladB n j l ξ := by
  unfold ladCoeff ladB
  ring

lemma ladCoeff_eq_ladB (n j l : ℕ) (ξ : ℝ) :
    ladCoeff (((n + 2 * l : ℕ) : ℝ) / 2) (-((n + 2 * j : ℕ) : ℝ) / 2) ξ = ladB n j l ξ := by
  unfold ladCoeff ladB
  ring

/-- **The raising equation of the profile**: `ladUp (-(n+2(k+1))/2) ((n+2j)/2) ψ_{j,k+1} = (k+1) ψ_{jk}`. -/
theorem ladUp_profileFun_succ (n k j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladUp (-((n + 2 * (k + 1) : ℕ) : ℝ) / 2) (((n + 2 * j : ℕ) : ℝ) / 2) (profileFun n (k + 1) j κ) ξ =
      ((k + 1 : ℕ) : ℂ) * profileFun n k j κ ξ := by
  unfold ladUp
  rw [ladCoeff_eq_neg_ladB]
  have := profileFun_up n k j hn κ hξ
  push_cast at this ⊢
  linear_combination this

/-- **The lowest weight vector is killed by the raising operator**: `ladUp (-n/2) ((n+2j)/2) ψ_{j0} = 0`. -/
theorem ladUp_profileFun_zero (n j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladUp (-((n + 2 * 0 : ℕ) : ℝ) / 2) (((n + 2 * j : ℕ) : ℝ) / 2) (profileFun n 0 j κ) ξ = 0 := by
  unfold ladUp
  rw [ladCoeff_eq_neg_ladB]
  have := profileFun_up_zero n j hn κ hξ
  push_cast at this ⊢
  linear_combination this

/-- **The lowering equation of the profile**: `ladDown (-(n+2l)/2) ((n+2j)/2) ψ_{jl} = (n + l) ψ_{j,l+1}`. -/
theorem ladDown_profileFun (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladDown (-((n + 2 * l : ℕ) : ℝ) / 2) (((n + 2 * j : ℕ) : ℝ) / 2) (profileFun n l j κ) ξ =
      ((n + l : ℕ) : ℂ) * profileFun n (l + 1) j κ ξ := by
  unfold ladDown
  rw [ladCoeff_eq_neg_ladB]
  have := profileFun_down n l j hn κ hξ
  push_cast at this ⊢
  linear_combination (-1 : ℂ) * this

/-- **The kernel equation of the lowering operator for the antiholomorphic series**:
`ladDown (n/2) (-(n+2j)/2) ψ_{j0} = 0`. -/
theorem ladDown_profileFun_zero_minus (n j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladDown (((n + 2 * 0 : ℕ) : ℝ) / 2) (-((n + 2 * j : ℕ) : ℝ) / 2) (profileFun n 0 j κ) ξ = 0 := by
  unfold ladDown
  rw [ladCoeff_eq_ladB]
  have := profileFun_up_zero n j hn κ hξ
  push_cast at this ⊢
  linear_combination (-1 : ℂ) * this

/-- **The raising operator on the profile of `D_n⁻`**: `ladUp ((n+2l)/2) (-(n+2j)/2) ψ_{jl} = -(n + l) ψ_{j,l+1}`. -/
theorem ladUp_profileFun_minus (n l j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladUp (((n + 2 * l : ℕ) : ℝ) / 2) (-((n + 2 * j : ℕ) : ℝ) / 2) (profileFun n l j κ) ξ =
      -((n + l : ℕ) : ℂ) * profileFun n (l + 1) j κ ξ := by
  unfold ladUp
  rw [ladCoeff_eq_ladB]
  have := profileFun_down n l j hn κ hξ
  push_cast at this ⊢
  linear_combination this

/-- **The lowering operator on the profile of `D_n⁻`**: `ladDown ((n+2(k+1))/2) (-(n+2j)/2) ψ_{j,k+1} = -(k+1) ψ_{jk}`;
for `k = 0` and `l = 0` see `ladDown_profileFun_zero_minus`. -/
theorem ladDown_profileFun_succ_minus (n k j : ℕ) (hn : 1 ≤ n) (κ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    ladDown (((n + 2 * (k + 1) : ℕ) : ℝ) / 2) (-((n + 2 * j : ℕ) : ℝ) / 2) (profileFun n (k + 1) j κ) ξ =
      -((k + 1 : ℕ) : ℂ) * profileFun n k j κ ξ := by
  unfold ladDown
  rw [ladCoeff_eq_ladB]
  have := profileFun_up n k j hn κ hξ
  push_cast at this ⊢
  linear_combination (-1 : ℂ) * this

end Lightlike.Lorentz.SL2RPlancherel
