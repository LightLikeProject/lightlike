import Mathlib
import Lightlike.Dirac.StereoCurved

/-!
# Killing spinors of the round sphere in the stereographic chart

For a vector `v` in a Clifford module `V` (a real representation of `Cl(ℝⁿ, -‖·‖²)`) and `ε = ±1`
the spinor `f(y) = h(y)^{-1/2} (v + ε y·v)`, with `h = (1+‖y‖²)/2` and `y·` Clifford multiplication by the
position vector, satisfies `D f = -(n/2) ε f` for the Dirac operator of the unit `n`-sphere in the
stereographic orthonormal frame (`diracF_stereo_killing`).  On `S²` this gives the eigenvalues
`∓1`, so the Friedrich bound `|λ| ≥ n/2` of `StereoFriedrich` is sharp
(`diracF_stereo_killing_two`).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `Yop ρ x` is Clifford multiplication by the vector `x`. -/
lemma Yop_eq_rho (ρ : CliffordRep n V) (x : E n) :
    Yop ρ x = ρ (ι (Qneg n) x) := by
  have hx : x = ∑ l, x l • e l := by
    ext j
    simp [e, Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [Yop, gam, map_sum, map_smul]

/-- `(y·)² = -‖y‖²`. -/
lemma Yop_sq (ρ : CliffordRep n V) (x : E n) (v : V) :
    Yop ρ x (Yop ρ x v) = (-‖x‖ ^ 2) • v := by
  have h := congrArg ρ (ι_sq_scalar (Qneg n) x)
  have h2 : Yop ρ x * Yop ρ x = (-‖x‖ ^ 2) • (1 : V →L[ℝ] V) := by
    rw [Yop_eq_rho, ← map_mul, h]
    simp [Qneg_apply, Algebra.algebraMap_eq_smul_one]
  have := congrArg (fun L => L v) h2
  simpa using this

/-- The continuous linear map `x ↦ x·v`. -/
noncomputable def Lmul (ρ : CliffordRep n V) (v : V) : E n →L[ℝ] V :=
  ∑ l, (EuclideanSpace.proj l : E n →L[ℝ] ℝ).smulRight (gam ρ l v)

lemma Lmul_apply (ρ : CliffordRep n V) (v : V) (x : E n) : Lmul ρ v x = Yop ρ x v := by
  simp [Lmul, Yop]

lemma Yop_e (ρ : CliffordRep n V) (v : V) (i : Fin n) : Yop ρ (e i) v = gam ρ i v := by
  simp [Yop, e]

/-- The Killing spinor `f(y) = h(y)^{-1/2} (v + ε y·v)` in the stereographic chart. -/
noncomputable def killingSpinor (ρ : CliffordRep n V) (v : V) (ε : ℝ) : E n → V :=
  fun x => stereoH x ^ (-(1 / 2 : ℝ)) • (v + ε • Yop ρ x v)

lemma fderiv_killingSpinor_e (ρ : CliffordRep n V) (v : V) (ε : ℝ) (x : E n) (i : Fin n) :
    fderiv ℝ (killingSpinor ρ v ε) x (e i) =
      (-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1) * x i) • (v + ε • Yop ρ x v) +
        (stereoH x ^ (-(1 / 2 : ℝ)) * ε) • gam ρ i v := by
  have hg : HasFDerivAt (fun y => stereoH y ^ (-(1 / 2 : ℝ)))
      ((-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) • fderiv ℝ stereoH x) x := by
    have := (hasFDerivAt_stereoH x).rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (stereoH_pos x).ne')
    rwa [(hasFDerivAt_stereoH x).fderiv]
  have hw : HasFDerivAt (fun y : E n => v + ε • Yop ρ y v) (ε • Lmul ρ v) x := by
    have h1 : (fun y : E n => v + ε • Yop ρ y v) = fun y => v + ε • Lmul ρ v y := by
      funext y; rw [Lmul_apply]
    rw [h1]
    exact ((ε • Lmul ρ v).hasFDerivAt).const_add v
  have h2 := (hg.smul hw).fderiv
  have h3 : fderiv ℝ (killingSpinor ρ v ε) x = _ := h2
  rw [h3]
  simp [fderiv_stereoH_apply, e, Lmul_apply, Yop, EuclideanSpace.inner_single_right]
  module

/-- Pure algebra behind the Killing spinor equation. -/
lemma killing_algebra (g h c s ε N : ℝ) (P v : V) (hε : ε * ε = 1) (hc : h * c = -g / 2)
    (hh : h = (1 + s) / 2) :
    h • (c • (P + ε • ((-s) • v)) + (-(N * (g * ε))) • v) +
        (-(N - 1) / 2) • (g • (P + ε • ((-s) • v))) =
      (-(N / 2) * ε) • (g • (v + ε • P)) := by
  have e1 : h * c + (-(N - 1) / 2) * g = (-(N / 2) * ε) * g * ε := by
    linear_combination hc + (N / 2) * g * hε
  have e2 : h * c * ε * (-s) + h * (-(N * g * ε)) + (-(N - 1) / 2) * g * ε * (-s) =
      (-(N / 2) * ε) * g := by
    linear_combination (-ε * s) * hc + (-N * g * ε) * hh
  calc _ = (h * c + (-(N - 1) / 2) * g) • P +
        (h * c * ε * (-s) + h * (-(N * g * ε)) + (-(N - 1) / 2) * g * ε * (-s)) • v := by module
    _ = ((-(N / 2) * ε) * g * ε) • P + ((-(N / 2) * ε) * g) • v := by rw [e1, e2]
    _ = _ := by module

/-- The Dirac operator of `Sⁿ` in the stereographic chart on a Killing spinor. -/
theorem dirac_flat_killingSpinor (ρ : CliffordRep n V) (v : V) (ε : ℝ) (x : E n) :
    dirac ρ (killingSpinor ρ v ε) x =
      (-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) •
          (Yop ρ x v + ε • ((-‖x‖ ^ 2) • v)) +
        (-((n : ℝ) * (stereoH x ^ (-(1 / 2 : ℝ)) * ε))) • v := by
  have h1 : ∀ i, gam ρ i (fderiv ℝ (killingSpinor ρ v ε) x (e i)) =
      ((-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) * x i) •
          gam ρ i (v + ε • Yop ρ x v) +
        (-(stereoH x ^ (-(1 / 2 : ℝ)) * ε)) • v := by
    intro i
    rw [fderiv_killingSpinor_e, map_add, map_smul, map_smul, gam_sq]
    module
  have h2 : ∑ i, ((-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) * x i) •
      gam ρ i (v + ε • Yop ρ x v) = (-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) •
        Yop ρ x (v + ε • Yop ρ x v) := by
    simp only [Yop, sum_apply, smul_apply, Finset.smul_sum,
      mul_smul]
  have h3 : Yop ρ x (v + ε • Yop ρ x v) = Yop ρ x v + ε • ((-‖x‖ ^ 2) • v) := by
    rw [map_add, map_smul, Yop_sq]
  simp only [dirac, h1, Finset.sum_add_distrib, h2, h3, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  module

/-- **Killing spinors of the round sphere.**  For `ε = ±1` and any `v` in the Clifford module, the
spinor `f(y) = h(y)^{-1/2}(v + ε y·v)` satisfies `D f = -(n/2) ε f` for the Dirac operator of the
unit `n`-sphere in the stereographic chart (`diracF`). -/
theorem diracF_stereo_killing (ρ : CliffordRep n V) (v : V) {ε : ℝ} (hε : ε * ε = 1) (x : E n) :
    diracF ρ stereoF stereoOmega (killingSpinor ρ v ε) x =
      (-((n : ℝ) / 2) * ε) • killingSpinor ρ v ε x := by
  have hne : stereoH x ≠ 0 := (stereoH_pos x).ne'
  have hf : killingSpinor ρ v ε x = stereoH x ^ (-(1 / 2 : ℝ)) • (v + ε • Yop ρ x v) := rfl
  have h3 : Yop ρ x (v + ε • Yop ρ x v) = Yop ρ x v + ε • ((-‖x‖ ^ 2) • v) := by
    rw [map_add, map_smul, Yop_sq]
  rw [diracF_stereo, dirac_flat_killingSpinor, hf, map_smul, h3]
  have hc : stereoH x * (-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) =
      -(stereoH x ^ (-(1 / 2 : ℝ))) / 2 := by
    rw [Real.rpow_sub_one hne]
    field_simp
  have hh : stereoH x = (1 + ‖x‖ ^ 2) / 2 := rfl
  exact killing_algebra _ _ _ _ _ _ _ _ hε hc hh

/-- A Killing spinor with `v ≠ 0` is not identically zero (its value at the origin is `√2 · v`
up to the positive factor `h(0)^{-1/2}`). -/
lemma killingSpinor_ne_zero (ρ : CliffordRep n V) {v : V} (hv : v ≠ 0) (ε : ℝ) :
    killingSpinor ρ v ε ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hY : Yop ρ (0 : E n) v = 0 := by simp [Yop]
  have hpos : 0 < stereoH (0 : E n) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (stereoH_pos _) _
  simp only [killingSpinor, hY, smul_zero, add_zero, Pi.zero_apply] at h0
  exact hv ((smul_eq_zero.mp h0).resolve_left hpos.ne')

/-- On the round `2`-sphere the Killing spinors have Dirac eigenvalues `∓1`; together with the
Friedrich bound `|λ| ≥ 1` (`eigen_sq_ge_friedrich_stereo`) this shows the bound is sharp. -/
theorem diracF_stereo_killing_two (ρ : CliffordRep 2 V) (v : V) {ε : ℝ} (hε : ε * ε = 1) (x : E 2) :
    diracF ρ stereoF stereoOmega (killingSpinor ρ v ε) x = (-ε) • killingSpinor ρ v ε x := by
  rw [diracF_stereo_killing ρ v hε]
  congr 1
  push_cast
  ring

end Lightlike.Dirac
