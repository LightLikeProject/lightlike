import Lightlike.GR.Kerr

/-!
# Partial derivatives of functions of `(r, θ)`

For `f z = G (z 1) (z 2)` with `G` differentiable at `(y 1, y 2)`: `∂_r f = ∂₁G`, `∂_θ f = ∂₂G`
and `∂_t f = ∂_φ f = 0` (`pd_rθ`). This is the form of every entry of the Kerr metric
(`Lightlike/GR/Kerr.lean`) and of its derivatives.

Gap row GE6, supporting file.
-/

open Matrix Real

noncomputable section

namespace Lightlike

/-- **Partial derivatives of a function of `(r, θ)`.** If `z ↦ G (z 1) (z 2)` is differentiable at `y`
and `G` has partial derivatives `A` (in the first variable) and `B` (in the second) at `(y 1, y 2)`, then
`∂_r`, `∂_θ` of `z ↦ G (z 1) (z 2)` at `y` are `A`, `B`, and `∂_t`, `∂_φ` vanish. -/
theorem pd_rθ (G : ℝ → ℝ → ℝ) {y : Fin 4 → ℝ} {A B : ℝ}
    (hG : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => G (z 1) (z 2)) y)
    (h1 : HasDerivAt (fun r => G r (y 2)) A (y 1)) (h2 : HasDerivAt (fun t => G (y 1) t) B (y 2))
    (k : Fin 4) :
    pd k (fun z => G (z 1) (z 2)) y = if k = 1 then A else if k = 2 then B else 0 := by
  set f : (Fin 4 → ℝ) → ℝ := fun z => G (z 1) (z 2) with hf
  have hL : HasFDerivAt f (fderiv ℝ f y) y := hG.hasFDerivAt
  have line : ∀ k : Fin 4, HasDerivAt (fun t : ℝ => f (y + t • Pi.single k 1))
      (fderiv ℝ f y (Pi.single k 1)) 0 := by
    intro k
    have hl : HasDerivAt (fun t : ℝ => y + t • (Pi.single k 1 : Fin 4 → ℝ)) (Pi.single k 1) 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const (Pi.single k 1 : Fin 4 → ℝ)).const_add y
    have := hL.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    exact this
  unfold pd
  have e1 : (fun t : ℝ => f (y + t • Pi.single 1 1)) = fun t => G (y 1 + t) (y 2) := by
    funext t; simp [hf, Pi.single_apply]
  have e2 : (fun t : ℝ => f (y + t • Pi.single 2 1)) = fun t => G (y 1) (y 2 + t) := by
    funext t; simp [hf, Pi.single_apply]
  have e0 : (fun t : ℝ => f (y + t • Pi.single 0 1)) = fun _ => G (y 1) (y 2) := by
    funext t; simp [hf, Pi.single_apply]
  have e3 : (fun t : ℝ => f (y + t • Pi.single 3 1)) = fun _ => G (y 1) (y 2) := by
    funext t; simp [hf, Pi.single_apply]
  have d1 : HasDerivAt (fun t : ℝ => G (y 1 + t) (y 2)) A 0 :=
    HasDerivAt.comp_const_add (f := fun r => G r (y 2)) (y 1) 0 (by simpa using h1)
  have d2 : HasDerivAt (fun t : ℝ => G (y 1) (y 2 + t)) B 0 :=
    HasDerivAt.comp_const_add (f := fun t => G (y 1) t) (y 2) 0 (by simpa using h2)
  fin_cases k
  · have := line 0; rw [e0] at this
    simpa using ((hasDerivAt_const (0 : ℝ) (G (y 1) (y 2))).unique this).symm
  · have := line 1; rw [e1] at this
    simpa using this.unique d1
  · have := line 2; rw [e2] at this
    simpa using this.unique d2
  · have := line 3; rw [e3] at this
    simpa using ((hasDerivAt_const (0 : ℝ) (G (y 1) (y 2))).unique this).symm

end Lightlike
