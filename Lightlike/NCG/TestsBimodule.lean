import Lightlike.NCG.Bimodule
import Lightlike.NCG.TestsTwoPoint

/-!
# Tests for the bimodule decomposition: the two-point space

On `ℂ ⊕ ℂ` acting diagonally on `ℂ²` with `J` the complex conjugation, `J π(b) J = π(b̄)`, so
`Hᵢⱼ = π(Pᵢ) π(Pⱼ) H` vanishes for `i ≠ j`: the Krajewski diagram has only the diagonal vertices `H₀₀`, `H₁₁`.

* `isSelfAdjoint_zero_H2`, `twoPointReal`: the real structure of `(ℂ², ℂ², 0)` with `J` the complex conjugation;
* `twoPointPartition`: the units `(1, 0)`, `(0, 1)` of `ℂ ⊕ ℂ`;
* `Hsub_zero_one`: `H₀₁ = 0`.
-/

open scoped InnerProductSpace

namespace Lightlike.NCG.TwoPoint

lemma isSelfAdjoint_zero_H2 : IsSelfAdjoint (0 : H2 →L[ℂ] H2) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, map_zero]

/-- **The real structure** of `(ℂ², ℂ², 0)`: `J` the complex conjugation. -/
noncomputable def twoPointReal : RealStructure (twoPoint 0 isSelfAdjoint_zero_H2) where
  J := conjJ
  inner_J x y := by
    simp only [PiLp.inner_apply, conjJ_apply, RCLike.inner_apply, starRingEnd_apply, star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  J_J x := by
    ext i
    simp [conjJ_apply]
  order_zero a b x := by
    show pi2 a (conjJ (pi2 b (conjJ x))) = conjJ (pi2 b (conjJ (pi2 a x)))
    rw [conjJ_pi2_conjJ, conjJ_pi2_conjJ, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply,
      ← map_mul, ← map_mul, mul_comm]
  first_order a b x := by
    have hD : (twoPoint 0 isSelfAdjoint_zero_H2).D = 0 := rfl
    simp [FiniteSpectralTriple.comm, hD]
  D_J x := by
    show (0 : H2 →L[ℂ] H2) (conjJ x) = conjJ ((0 : H2 →L[ℂ] H2) x)
    simp

/-- The units `(1, 0)` and `(0, 1)` of `ℂ ⊕ ℂ`, a central partition. -/
def twoPointPartition : CentralPartition (Fin 2 → ℂ) (Fin 2) where
  P i := Pi.single i 1
  star_P i := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  mul_P i j := by
    ext k
    by_cases hij : i = j
    · subst hij; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hij]
      by_cases hk : k = i
      · subst hk; simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne hk]
  sum_P := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  central i a := mul_comm _ _

/-- **`H₀₁ = 0`** on the two-point space: the off-diagonal vertex of its Krajewski diagram is empty. -/
theorem Hsub_zero_one : Hsub twoPointReal twoPointPartition 0 1 = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, rfl⟩
  rw [Submodule.mem_bot, proj_apply, leftP_apply, rightP_apply]
  show pi2 (Pi.single 0 1) (conjJ (pi2 (Pi.single 1 1) (conjJ y))) = 0
  rw [conjJ_pi2_conjJ, ← ContinuousLinearMap.mul_apply, ← map_mul]
  have : (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) * star (Pi.single (1 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) = 0 := by
    ext k
    fin_cases k <;> simp
  rw [this, map_zero, ContinuousLinearMap.zero_apply]

end Lightlike.NCG.TwoPoint
