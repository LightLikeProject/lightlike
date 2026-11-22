module

public import Lightlike.Spacetime.Curvature

/-!
# The conical metric of a straight string: coordinate metric and Christoffel symbols

Row G1-048 (milestone CO26; source `hindmarsh-kibble-1995`, eq. (6.1)). In the coordinates
`(t, z, r, θ)` (indices `0, 1, 2, 3` of `Fin 4 → ℝ`) the metric of a straight cosmic string is
`−dt² + dz² + dr² + a² r² dθ²` with `a = 1 − 4Gμ`. Here `coneMetric a` is this matrix-valued
function; the identification of `μ` with the energy per unit length of a vortex is *not* proved, it
is only the parameter `a`.

* `coneMetric a`: the components `g_{μν}(y)`; `coneRegion`: the region `r > 0` (away from the axis).
* `isCoordMetric_cone`: for `a ≠ 0` it is a coordinate metric on `coneRegion`.
* `christoffel_cone`: the Christoffel symbols of the library are `Γ^r_{θθ} = −a² r`,
  `Γ^θ_{rθ} = Γ^θ_{θr} = 1/r`, all others zero (at every point with `r ≠ 0`, for `a ≠ 0`).
-/

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Lightlike

namespace StringCone

/-- The components of the conical metric `−dt² + dz² + dr² + a² r² dθ²` in the coordinates
`(t, z, r, θ) = (y 0, y 1, y 2, y 3)`; `a = 1 − 4Gμ`. -/
def coneMetric (a : ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
  fun y => Matrix.diagonal ![-1, 1, 1, a ^ 2 * (y 2) ^ 2]

/-- The region away from the axis, `r > 0`. -/
def coneRegion : Set (Fin 4 → ℝ) := {y | 0 < y 2}

lemma isOpen_coneRegion : IsOpen coneRegion :=
  isOpen_lt continuous_const (continuous_apply 2)

/-- For `a ≠ 0` the conical metric is a coordinate metric on the region `r > 0`. -/
theorem isCoordMetric_cone {a : ℝ} (ha : a ≠ 0) : IsCoordMetric (coneMetric a) coneRegion := by
  refine isCoordMetric_diagonal (fun y => ![-1, 1, 1, a ^ 2 * (y 2) ^ 2]) isOpen_coneRegion ?_ ?_
  · intro i
    fin_cases i
    · simpa using (contDiffOn_const : ContDiffOn ℝ _ (fun _ : Fin 4 → ℝ => (-1 : ℝ)) coneRegion)
    · simpa using (contDiffOn_const : ContDiffOn ℝ _ (fun _ : Fin 4 → ℝ => (1 : ℝ)) coneRegion)
    · simpa using (contDiffOn_const : ContDiffOn ℝ _ (fun _ : Fin 4 → ℝ => (1 : ℝ)) coneRegion)
    · simp only [Fin.isValue, Fin.reduceFinMk, Matrix.cons_val]
      have hc : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 2) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2).contDiff
      exact contDiffOn_const.mul (hc.pow 2).contDiffOn
  · intro x hx i
    have hx' : 0 < x 2 := hx
    fin_cases i <;> simp [ha, hx'.ne']

/-- The partial derivatives of the components of the conical metric: only `∂_r g_{θθ} = 2 a² r`
is nonzero. -/
lemma pd_cone (a : ℝ) (j l k : Fin 4) (x : Fin 4 → ℝ) :
    pd j (fun y => coneMetric a y l k) x =
      if l = 3 ∧ k = 3 ∧ j = 2 then 2 * a ^ 2 * x 2 else 0 := by
  by_cases hlk : l = 3 ∧ k = 3
  · obtain ⟨rfl, rfl⟩ := hlk
    have hf : (fun y : Fin 4 → ℝ => coneMetric a y 3 3) = fun y => a ^ 2 * (y 2) ^ 2 := by
      funext y; simp [coneMetric]
    have h2 := ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x).pow 2).const_mul (a ^ 2)
    unfold pd
    rw [hf, h2.fderiv]
    by_cases hj : j = 2
    · subst hj; simp; ring
    · simp [hj, Ne.symm hj]
  · have hf : (fun y : Fin 4 → ℝ => coneMetric a y l k) = fun _ => coneMetric a 0 l k := by
      funext y
      fin_cases l <;> fin_cases k <;> simp_all [coneMetric]
    rw [hf, pd_const]
    exact (ite_eq_right_iff.mpr fun h => absurd ⟨h.1, h.2.1⟩ hlk).symm

/-- The inverse of the conical metric off the axis: the diagonal matrix of the inverses of the
entries. -/
lemma coneMetric_inv {a : ℝ} (ha : a ≠ 0) {x : Fin 4 → ℝ} (hx : x 2 ≠ 0) :
    (coneMetric a x)⁻¹ = Matrix.diagonal ![-1, 1, 1, (a ^ 2 * (x 2) ^ 2)⁻¹] := by
  apply Matrix.inv_eq_right_inv
  unfold coneMetric
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp; field_simp

/-- The nonzero Christoffel symbols of the conical metric, as a table:
`Γ^r_{θθ} = −a² r`, `Γ^θ_{rθ} = Γ^θ_{θr} = 1/r`. -/
def coneGamma (a : ℝ) (i j k : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if i = 2 ∧ j = 3 ∧ k = 3 then -(a ^ 2 * x 2)
  else if i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) then 1 / x 2 else 0

/-- **The Christoffel symbols of the conical metric** (for `a ≠ 0`, at every point): the library's
`christoffel` is the table `coneGamma`, i.e. `Γ^r_{θθ} = −a² r`, `Γ^θ_{rθ} = Γ^θ_{θr} = 1/r`, and
all other symbols vanish (at every point off the axis, `r ≠ 0`). -/
theorem christoffel_cone {a : ℝ} (ha : a ≠ 0) (i j k : Fin 4) {x : Fin 4 → ℝ} (hx : x 2 ≠ 0) :
    christoffel (coneMetric a) i j k x = coneGamma a i j k x := by
  unfold christoffel
  simp only [pd_cone, coneMetric_inv ha hx]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [Matrix.diagonal_apply, coneGamma] <;> field_simp

end StringCone

end Lightlike
