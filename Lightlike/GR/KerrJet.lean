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

/-- **Partial derivatives of a function of `(r, θ)`.** If `G` is differentiable at `(y 1, y 2)` with
partial derivatives `A` (in the first variable) and `B` (in the second), then `∂_r`, `∂_θ` of
`z ↦ G (z 1) (z 2)` at `y` are `A`, `B`, and `∂_t`, `∂_φ` vanish. -/
theorem pd_rθ (G : ℝ → ℝ → ℝ) {y : Fin 4 → ℝ} {A B : ℝ}
    (hG : DifferentiableAt ℝ (fun p : ℝ × ℝ => G p.1 p.2) (y 1, y 2))
    (h1 : HasDerivAt (fun r => G r (y 2)) A (y 1)) (h2 : HasDerivAt (fun t => G (y 1) t) B (y 2))
    (k : Fin 4) :
    pd k (fun z => G (z 1) (z 2)) y = if k = 1 then A else if k = 2 then B else 0 := by
  set P : ℝ × ℝ → ℝ := fun p => G p.1 p.2 with hP
  set L := fderiv ℝ P (y 1, y 2) with hL
  have hPd : HasFDerivAt P L (y 1, y 2) := hG.hasFDerivAt
  have hLA : L (1, 0) = A := by
    have hl : HasDerivAt (fun r : ℝ => (r, y 2)) ((1 : ℝ), (0 : ℝ)) (y 1) :=
      (hasDerivAt_id' (y 1)).prodMk (hasDerivAt_const _ _)
    have := hPd.comp_hasDerivAt (y 1) hl
    exact this.unique h1
  have hLB : L (0, 1) = B := by
    have hl : HasDerivAt (fun t : ℝ => (y 1, t)) ((0 : ℝ), (1 : ℝ)) (y 2) :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id' (y 2))
    have := hPd.comp_hasDerivAt (y 2) hl
    exact this.unique h2
  let pr : (Fin 4 → ℝ) →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1).prod
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2)
  have hpr : HasFDerivAt (fun z : Fin 4 → ℝ => ((z 1, z 2) : ℝ × ℝ)) pr y := pr.hasFDerivAt
  have hf0 : HasFDerivAt (P ∘ fun z : Fin 4 → ℝ => ((z 1, z 2) : ℝ × ℝ)) (L.comp pr) y := hPd.comp y hpr
  have hf : HasFDerivAt (fun z : Fin 4 → ℝ => G (z 1) (z 2)) (L.comp pr) y := hf0
  unfold pd
  rw [hf.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have e : ∀ k : Fin 4, pr (Pi.single k 1) = if k = 1 then ((1 : ℝ), (0 : ℝ))
      else if k = 2 then ((0 : ℝ), (1 : ℝ)) else (0, 0) := by
    intro k
    have hprv : ∀ v : Fin 4 → ℝ, pr v = (v 1, v 2) := fun v => rfl
    fin_cases k <;> simp [hprv, Pi.single_apply, Fin.ext_iff]
  rw [e k]
  split_ifs <;> first | exact hLA | exact hLB | exact (congrArg L Prod.mk_zero_zero).trans L.map_zero

end Lightlike
