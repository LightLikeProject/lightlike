import Mathlib
import Lightlike.Dirac.KillingSpinor

/-!
# Dirac eigenspinors of the round `2`-sphere with eigenvalue `±2` (the case `k = 1`)

In the stereographic chart (`h = (1+‖y‖²)/2`, `y·` Clifford multiplication by the position vector,
`s = ‖y‖² = 2h-1`) put
`f(y) = h^{-3/2} ((1 - 2s) v + ε (s - 2) y·v)`, `ε = ±1`.
Then `D f = 2ε f` for the Dirac operator of the unit `2`-sphere (`diracF_stereo_eigen_two`).
Together with the Killing spinors (`diracF_stereo_killing_two`, eigenvalues `∓1`) this exhibits the
eigenvalues `±(k+1)` of the Dirac operator of `S²` for `k = 0, 1`.  These eigenspinors are regular at
the pole `h → ∞` in the sense that `‖f‖` stays bounded (decay `h^{-1/2}`); no claim on completeness
(multiplicities) is made here.

The computation is done for the family `α(h(y)) v + β(h(y)) y·v` with `α, β` functions of the
radial variable `h` (`dirac_radial_h`).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma hasFDerivAt_comp_stereoH {α : ℝ → ℝ} {α' : ℝ} (x : E n) (hα : HasDerivAt α α' (stereoH x)) :
    HasFDerivAt (fun y => α (stereoH y)) (α' • innerSL ℝ x) x := by
  have := hα.comp_hasFDerivAt x (hasFDerivAt_stereoH x)
  refine HasFDerivAt.congr_fderiv this ?_
  ext w
  simp

/-- Flat Dirac operator on a radial combination `α(h) v + β(h) y·v`. -/
lemma dirac_radial_h (ρ : CliffordRep n V) (v : V) {α β : ℝ → ℝ} {α' β' : ℝ} (x : E n)
    (hα : HasDerivAt α α' (stereoH x)) (hβ : HasDerivAt β β' (stereoH x)) :
    dirac ρ (fun y => α (stereoH y) • v + β (stereoH y) • Yop ρ y v) x =
      α' • Yop ρ x v + (-(β' * ‖x‖ ^ 2) - (n : ℝ) * β (stereoH x)) • v := by
  have hw : HasFDerivAt (fun y : E n => Yop ρ y v) (Lmul ρ v) x := by
    have h1 : (fun y : E n => Yop ρ y v) = fun y => Lmul ρ v y := by
      funext y; rw [Lmul_apply]
    rw [h1]
    exact (Lmul ρ v).hasFDerivAt
  have hf := ((hasFDerivAt_comp_stereoH x hα).smul_const v).add
    ((hasFDerivAt_comp_stereoH x hβ).smul hw)
  have hf' : HasFDerivAt (fun y => α (stereoH y) • v + β (stereoH y) • Yop ρ y v) _ x := hf
  have hd : ∀ i, gam ρ i (fderiv ℝ (fun y => α (stereoH y) • v + β (stereoH y) • Yop ρ y v) x (e i)) =
      (α' * x i) • gam ρ i v + (β' * x i) • gam ρ i (Yop ρ x v) + (-β (stereoH x)) • v := by
    intro i
    rw [hf'.fderiv]
    have hY : Yop ρ (EuclideanSpace.single i 1) v = gam ρ i v := Yop_e ρ v i
    simp [e, Lmul_apply, EuclideanSpace.inner_single_right, hY, gam_sq]
    module
  have h2 : ∀ w : V, ∑ i, (x i) • gam ρ i w = Yop ρ x w := by
    intro w; simp [Yop, sum_apply]
  have h3 : ∑ i, (α' * x i) • gam ρ i v = α' • Yop ρ x v := by
    calc _ = α' • ∑ i, (x i) • gam ρ i v := by
          rw [Finset.smul_sum]; simp only [mul_smul]
      _ = _ := by rw [h2]
  have h4 : ∑ i, (β' * x i) • gam ρ i (Yop ρ x v) = β' • ((-‖x‖ ^ 2) • v) := by
    calc _ = β' • ∑ i, (x i) • gam ρ i (Yop ρ x v) := by
          rw [Finset.smul_sum]; simp only [mul_smul]
      _ = _ := by rw [h2, Yop_sq]
  simp only [dirac, hd, Finset.sum_add_distrib, h3, h4, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  module

/-- The `k = 1` eigenspinor `h^{-3/2}((1-2s) v + ε (s-2) y·v)`, `s = ‖y‖²`, written in the variable
`h = (1+s)/2` as `(3h^{-3/2} - 4h^{-1/2}) v + ε (2h^{-1/2} - 3h^{-3/2}) y·v`. -/
noncomputable def eigSpinorOne (ρ : CliffordRep n V) (v : V) (ε : ℝ) : E n → V :=
  fun y => (3 * stereoH y ^ (-(1 / 2 : ℝ) - 1) - 4 * stereoH y ^ (-(1 / 2 : ℝ))) • v +
    (ε * (2 * stereoH y ^ (-(1 / 2 : ℝ)) - 3 * stereoH y ^ (-(1 / 2 : ℝ) - 1))) • Yop ρ y v

/-- **Dirac eigenspinors of `S²` with eigenvalue `2ε`** (`ε = ±1`), the case `k = 1` of the spectrum
`±(k+1)`: `D f = 2ε f` in the stereographic chart. -/
theorem diracF_stereo_eigen_two (ρ : CliffordRep 2 V) (v : V) {ε : ℝ} (hε : ε * ε = 1) (x : E 2) :
    diracF ρ stereoF stereoOmega (eigSpinorOne ρ v ε) x = (2 * ε) • eigSpinorOne ρ v ε x := by
  have hne : stereoH x ≠ 0 := (stereoH_pos x).ne'
  have hs : ‖x‖ ^ 2 = 2 * stereoH x - 1 := by unfold stereoH; ring
  have hq : HasDerivAt (fun u : ℝ => u ^ (-(1 / 2 : ℝ)))
      (-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) (stereoH x) :=
    Real.hasDerivAt_rpow_const (Or.inl hne)
  have hr : HasDerivAt (fun u : ℝ => u ^ (-(1 / 2 : ℝ) - 1))
      ((-(1 / 2 : ℝ) - 1) * stereoH x ^ (-(1 / 2 : ℝ) - 1 - 1)) (stereoH x) :=
    Real.hasDerivAt_rpow_const (Or.inl hne)
  have hα : HasDerivAt (fun u : ℝ => 3 * u ^ (-(1 / 2 : ℝ) - 1) - 4 * u ^ (-(1 / 2 : ℝ)))
      (3 * ((-(1 / 2 : ℝ) - 1) * stereoH x ^ (-(1 / 2 : ℝ) - 1 - 1)) -
        4 * (-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1))) (stereoH x) :=
    (hr.const_mul 3).sub (hq.const_mul 4)
  have hβ : HasDerivAt (fun u : ℝ => ε * (2 * u ^ (-(1 / 2 : ℝ)) - 3 * u ^ (-(1 / 2 : ℝ) - 1)))
      (ε * (2 * (-(1 / 2 : ℝ) * stereoH x ^ (-(1 / 2 : ℝ) - 1)) -
        3 * ((-(1 / 2 : ℝ) - 1) * stereoH x ^ (-(1 / 2 : ℝ) - 1 - 1)))) (stereoH x) :=
    ((hq.const_mul 2).sub (hr.const_mul 3)).const_mul ε
  have hD := dirac_radial_h ρ v x hα hβ
  have hf : eigSpinorOne ρ v ε = fun y => (3 * stereoH y ^ (-(1 / 2 : ℝ) - 1) -
      4 * stereoH y ^ (-(1 / 2 : ℝ))) • v + (ε * (2 * stereoH y ^ (-(1 / 2 : ℝ)) -
      3 * stereoH y ^ (-(1 / 2 : ℝ) - 1))) • Yop ρ y v := rfl
  have hY : Yop ρ x (Yop ρ x v) = (-‖x‖ ^ 2) • v := Yop_sq ρ x v
  have e1 : stereoH x ^ (-(1 / 2 : ℝ) - 1) = stereoH x ^ (-(1 / 2 : ℝ)) / stereoH x :=
    Real.rpow_sub_one hne _
  have e2 : stereoH x ^ (-(1 / 2 : ℝ) - 1 - 1) =
      stereoH x ^ (-(1 / 2 : ℝ)) / stereoH x / stereoH x := by
    rw [Real.rpow_sub_one hne, e1]
  rw [diracF_stereo, hf]
  simp only [] at hD ⊢
  rw [hD, map_add, map_smul, map_smul, hY, e1, e2, hs]
  generalize stereoH x ^ (-(1 / 2 : ℝ)) = q
  generalize stereoH x = h at hne ⊢
  match_scalars
  · field_simp
    linear_combination (-4 * q * (2 * h - 3)) * hε
  · field_simp
    ring

/-- The `k = 1` eigenspinor with `v ≠ 0` is not identically zero (value at the origin
`2 h(0)^{-1/2} v`). -/
lemma eigSpinorOne_ne_zero (ρ : CliffordRep n V) {v : V} (hv : v ≠ 0) (ε : ℝ) :
    eigSpinorOne ρ v ε ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hY : Yop ρ (0 : E n) v = 0 := by simp [Yop]
  have hH : stereoH (0 : E n) = 1 / 2 := by simp [stereoH]
  have hpos : 0 < ((1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have e1 : ((1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ) - 1) = ((1 / 2 : ℝ)) ^ (-(1 / 2 : ℝ)) / (1 / 2) :=
    Real.rpow_sub_one (by norm_num) _
  simp only [eigSpinorOne, hY, smul_zero, add_zero, Pi.zero_apply, hH, e1] at h0
  have : (3 * ((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) - 4 * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ))) =
      2 * (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
  rw [this] at h0
  exact hv ((smul_eq_zero.mp h0).resolve_left (by positivity))

/-- On `S²` the Dirac operator has the eigenvalues `±2` (`k = 1`), with the nonzero eigenspinors
`eigSpinorOne`; compare `diracF_stereo_killing_two` (eigenvalues `±1`, `k = 0`). -/
theorem exists_eigenspinor_two (ρ : CliffordRep 2 V) {v : V} (hv : v ≠ 0) {ε : ℝ} (hε : ε * ε = 1) :
    eigSpinorOne ρ v ε ≠ 0 ∧
      ∀ x, diracF ρ stereoF stereoOmega (eigSpinorOne ρ v ε) x = (2 * ε) • eigSpinorOne ρ v ε x :=
  ⟨eigSpinorOne_ne_zero ρ hv ε, diracF_stereo_eigen_two ρ v hε⟩

end Lightlike.Dirac
