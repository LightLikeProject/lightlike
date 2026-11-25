module

public import Lightlike.GR.CosmicStringCone.ConeMetric

/-!
# The conical metric is flat away from the axis

Row G1-048 (milestone CO26). For `a ≠ 0` the Riemann tensor of `coneMetric a`
(`−dt² + dz² + dr² + a² r² dθ²`) vanishes at every point with `r > 0`, so the metric is flat on
`coneRegion`: the string only produces a conical singularity on the axis `r = 0`.

* `pd_coneGamma`: the partial derivatives of the Christoffel table.
* `riemann_cone`: all components of the Riemann tensor vanish off the axis.
* `isFlatOn_cone`: `IsFlatOn (coneMetric a) coneRegion`.
-/

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

namespace StringCone

/-- The partial derivatives of the Christoffel table off the axis: `∂_r Γ^r_{θθ} = −a²` and
`∂_r Γ^θ_{rθ} = ∂_r Γ^θ_{θr} = −1/r²`, all others vanish. -/
lemma pd_coneGamma (a : ℝ) (i j k μ : Fin 4) {x : Fin 4 → ℝ} (hx : x 2 ≠ 0) :
    pd μ (coneGamma a i j k) x =
      if i = 2 ∧ j = 3 ∧ k = 3 then (if μ = 2 then -(a ^ 2) else 0)
      else if i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) then
        (if μ = 2 then -((x 2) ^ 2)⁻¹ else 0)
      else 0 := by
  by_cases h1 : i = 2 ∧ j = 3 ∧ k = 3
  · have hf : coneGamma a i j k = fun y => -(a ^ 2 * y 2) := by
      funext y; simp [coneGamma, h1]
    have h2 : HasFDerivAt (fun y : Fin 4 → ℝ => -(a ^ 2 * y 2))
        (-(a ^ 2 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2)) x :=
      ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x).const_mul (a ^ 2)).neg
    unfold pd
    rw [hf, h2.fderiv]
    simp only [eq_true h1, ite_true]
    by_cases hm : μ = 2
    · subst hm; simp
    · simp [hm, Ne.symm hm]
  · by_cases h2 : i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2))
    · have hf : coneGamma a i j k = fun y => (y 2)⁻¹ := by
        funext y
        simp only [coneGamma, eq_false h1, eq_true h2, ite_false, ite_true, one_div]
      have h3 : HasFDerivAt (fun y : Fin 4 → ℝ => (y 2)⁻¹)
          (-(x 2 ^ 2)⁻¹ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2) x :=
        (hasDerivAt_inv hx).comp_hasFDerivAt x (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x)
      unfold pd
      rw [hf, h3.fderiv]
      simp only [eq_false h1, eq_true h2, ite_false, ite_true]
      by_cases hm : μ = 2
      · subst hm; simp
      · simp [hm, Ne.symm hm]
    · have hf : coneGamma a i j k = fun _ => 0 := by
        funext y; simp only [coneGamma, eq_false h1, eq_false h2, ite_false]
      rw [hf]
      simp only [eq_false h1, eq_false h2, ite_false]
      exact pd_const _ _ _

/-- `pd` of the library's Christoffel symbols of the conical metric equals `pd` of the table. -/
lemma pd_christoffel_cone {a : ℝ} (ha : a ≠ 0) (i j k μ : Fin 4) {x : Fin 4 → ℝ}
    (hx : x ∈ coneRegion) :
    pd μ (christoffel (coneMetric a) i j k) x = pd μ (coneGamma a i j k) x := by
  unfold pd
  congr 1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [isOpen_coneRegion.mem_nhds hx] with y hy
  exact christoffel_cone ha i j k (show y 2 ≠ 0 from (show (0:ℝ) < y 2 from hy).ne')

/-- **The Riemann tensor of the conical metric vanishes off the axis.** -/
theorem riemann_cone {a : ℝ} (ha : a ≠ 0) (ρ σ μ ν : Fin 4) {x : Fin 4 → ℝ}
    (hx : x ∈ coneRegion) : riemann (coneMetric a) ρ σ μ ν x = 0 := by
  have hx' : x 2 ≠ 0 := (show (0:ℝ) < x 2 from hx).ne'
  unfold riemann
  rw [pd_christoffel_cone ha _ _ _ _ hx, pd_christoffel_cone ha _ _ _ _ hx, Fin.sum_univ_four]
  simp only [christoffel_cone ha _ _ _ hx', pd_coneGamma a _ _ _ _ hx']
  fin_cases ρ <;> fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    simp [coneGamma] <;> field_simp <;> ring

/-- **The conical metric is flat away from the axis**: `IsFlatOn (coneMetric a) coneRegion`
for `a ≠ 0` (i.e. `4Gμ ≠ 1`). -/
theorem isFlatOn_cone {a : ℝ} (ha : a ≠ 0) : IsFlatOn (coneMetric a) coneRegion :=
  ⟨isCoordMetric_cone ha, fun _ hx ρ σ μ ν => riemann_cone ha ρ σ μ ν hx⟩

end StringCone

end Lightlike
