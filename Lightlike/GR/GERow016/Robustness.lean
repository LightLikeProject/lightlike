import Lightlike.GR.GERow016.Dilation
import Lightlike.GR.GERow016.Rotation

/-!
# Stress tests for the null-infinity results of gap row GE7

Tier-3 robustness checks for `ScriPlus.lean`, `Dilation.lean` and `Rotation.lean`:

* finite points never reach `I⁺` (`compactify_not_mem_scriPlus`) and the conformal factor is positive there
  (`scriFactor_compactify_pos`), so `I⁺` is a genuine boundary of the image of `compactify`;
* `scriPoint` is injective (`scriPoint_injective`), so the parametrisation by `(u, θ, φ)` is faithful;
* the hypothesis `c ≠ 0` of `scriDilate_inv` cannot be dropped: the dilation by `0` collapses `I⁺` onto the
  slice `u = 0` (`scriDilate_zero_not_injOn`, `scriDilate_zero_no_inverse`).
-/

open Real

noncomputable section

namespace Lightlike

/-- **Finite points are not on `I⁺`**: the image of `compactify` is disjoint from `scriPlus`, because
`T + R = arctan (t + r) < π/2`. -/
theorem compactify_not_mem_scriPlus (y : Fin 4 → ℝ) : compactify y ∉ scriPlus := by
  intro h
  have hp : compactify y 0 + compactify y 1 = arctan (y 0 + y 1) := by simp [compactify]; ring
  have := h.1
  rw [hp] at this
  exact (Real.arctan_lt_pi_div_two _).ne this

/-- The conformal factor is strictly positive away from null infinity, in the compactified form. -/
theorem scriFactor_compactify_pos (y : Fin 4 → ℝ) : 0 < scriFactor (compactify y) := by
  rw [scriFactor_compactify, conformalFactor]
  positivity

/-- **The parametrisation of `I⁺` by `(u, θ, φ)` is injective.** -/
theorem scriPoint_injective {u θ φ u' θ' φ' : ℝ} (h : scriPoint u θ φ = scriPoint u' θ' φ') :
    u = u' ∧ θ = θ' ∧ φ = φ' := by
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [scriPoint, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at h0 h2 h3
  refine ⟨?_, h2, h3⟩
  have : arctan u = arctan u' := by linarith
  exact Real.arctan_injective this

/-- **The hypothesis `c ≠ 0` is necessary**: the dilation by `0` is not injective on `I⁺`; it collapses the two
points of retarded times `0` and `1` (same angles) to one. -/
theorem scriDilate_zero_not_injOn :
    ¬ Set.InjOn (scriDilate 0) scriPlus := by
  intro h
  have h1 := scriPoint_mem 0 0 0
  have h2 := scriPoint_mem 1 0 0
  have e : scriDilate 0 (scriPoint 0 0 0) = scriDilate 0 (scriPoint 1 0 0) := by
    rw [scriDilate_scriPoint, scriDilate_scriPoint]; simp
  have := scriPoint_injective (h h1 h2 e)
  norm_num at this

/-- Consequently no map is a left inverse of `scriDilate 0` on `I⁺`, so `scriDilate_inv` fails for `c = 0`
whatever the inverse dilation is. -/
theorem scriDilate_zero_no_inverse (d : ℝ) :
    ¬ ∀ p ∈ scriPlus, scriDilate d (scriDilate 0 p) = p := by
  intro h
  apply scriDilate_zero_not_injOn
  intro p hp q hq e
  rw [← h p hp, ← h q hq, e]

end Lightlike
