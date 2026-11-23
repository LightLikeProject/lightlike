import Mathlib
import Lightlike.Dirac.EigenspinorK1

/-!
# Conformal covariance of the Dirac operator of the round sphere in the stereographic chart

With `h = (1+‖y‖²)/2` the stereographic conformal factor, the Dirac operator `D` of the unit `n`-sphere
(`diracF_stereo`: `D f = h D₀ f − ((n−1)/2) y·f`, `D₀` the flat Dirac operator) satisfies, for every real
exponent `s`,

`D (h^s g) = h^{s+1} D₀ g + (s − (n−1)/2) h^s y·g`   (`diracF_stereo_rpow_smul`).

For `s = (n−1)/2` the last term vanishes (`diracF_stereo_conformal`): `D (h^{(n-1)/2} g) = h^{(n+1)/2} D₀ g`.
Consequently `h^{(n-1)/2} g` is an eigenspinor of the sphere with eigenvalue `λ` iff `h · D₀ g = λ g`
(`diracF_stereo_conformal_eigen_iff`); this turns the sphere eigenvalue problem into a flat one.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open CliffordAlgebra

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The flat Dirac operator of a spinor weighted by `h^s`:
`D₀ (h^s g) = h^s D₀ g + s h^{s-1} y·g`. -/
lemma dirac_rpow_smul (ρ : CliffordRep n V) (s : ℝ) {g : E n → V} (x : E n)
    (hg : DifferentiableAt ℝ g x) :
    dirac ρ (fun y => stereoH y ^ s • g y) x =
      stereoH x ^ s • dirac ρ g x + (s * stereoH x ^ (s - 1)) • Yop ρ x (g x) := by
  have hne : stereoH x ≠ 0 := (stereoH_pos x).ne'
  have hq : HasDerivAt (fun u : ℝ => u ^ s) (s * stereoH x ^ (s - 1)) (stereoH x) :=
    Real.hasDerivAt_rpow_const (Or.inl hne)
  have hf := (hasFDerivAt_comp_stereoH x hq).smul hg.hasFDerivAt
  have hf' : HasFDerivAt (fun y => stereoH y ^ s • g y) _ x := hf
  have hd : ∀ i, gam ρ i (fderiv ℝ (fun y => stereoH y ^ s • g y) x (e i)) =
      stereoH x ^ s • gam ρ i (fderiv ℝ g x (e i)) + (s * stereoH x ^ (s - 1) * x i) • gam ρ i (g x) := by
    intro i
    rw [hf'.fderiv]
    simp [e, EuclideanSpace.inner_single_right]
  have h2 : ∀ w : V, ∑ i, (x i) • gam ρ i w = Yop ρ x w := by
    intro w; simp [Yop, sum_apply]
  have h3 : ∑ i, (s * stereoH x ^ (s - 1) * x i) • gam ρ i (g x) =
      (s * stereoH x ^ (s - 1)) • Yop ρ x (g x) := by
    calc _ = (s * stereoH x ^ (s - 1)) • ∑ i, (x i) • gam ρ i (g x) := by
          rw [Finset.smul_sum]; simp only [mul_smul]
      _ = _ := by rw [h2]
  simp only [dirac, hd, Finset.sum_add_distrib, ← Finset.smul_sum, h3]

/-- **Weighted covariance of the sphere Dirac operator.** For every real `s`,
`D (h^s g) = h^{s+1} D₀ g + (s − (n−1)/2) h^s y·g`. -/
theorem diracF_stereo_rpow_smul (ρ : CliffordRep n V) (s : ℝ) {g : E n → V} (x : E n)
    (hg : DifferentiableAt ℝ g x) :
    diracF ρ stereoF stereoOmega (fun y => stereoH y ^ s • g y) x =
      stereoH x ^ (s + 1) • dirac ρ g x + (s - ((n : ℝ) - 1) / 2) • (stereoH x ^ s • Yop ρ x (g x)) := by
  have hne : stereoH x ≠ 0 := (stereoH_pos x).ne'
  have e1 : stereoH x ^ (s - 1) = stereoH x ^ s / stereoH x := Real.rpow_sub_one hne s
  have e2 : stereoH x ^ (s + 1) = stereoH x ^ s * stereoH x := Real.rpow_add_one hne s
  rw [diracF_stereo, dirac_rpow_smul ρ s x hg, e1, e2, map_smul]
  simp only [smul_add, smul_smul]
  generalize stereoH x ^ s = q
  generalize stereoH x = h at hne ⊢
  match_scalars
  · ring
  · field_simp
    ring

/-- **Conformal covariance**: `D (h^{(n-1)/2} g) = h^{(n+1)/2} D₀ g`. -/
theorem diracF_stereo_conformal (ρ : CliffordRep n V) {g : E n → V} (x : E n)
    (hg : DifferentiableAt ℝ g x) :
    diracF ρ stereoF stereoOmega (fun y => stereoH y ^ (((n : ℝ) - 1) / 2) • g y) x =
      stereoH x ^ (((n : ℝ) - 1) / 2 + 1) • dirac ρ g x := by
  rw [diracF_stereo_rpow_smul ρ _ x hg]
  simp

/-- `h^{(n-1)/2} g` is an eigenspinor of the round sphere with eigenvalue `λ` iff `h · D₀ g = λ g`. -/
theorem diracF_stereo_conformal_eigen_iff (ρ : CliffordRep n V) {g : E n → V} (x : E n)
    (hg : DifferentiableAt ℝ g x) (lam : ℝ) :
    diracF ρ stereoF stereoOmega (fun y => stereoH y ^ (((n : ℝ) - 1) / 2) • g y) x =
        lam • (stereoH x ^ (((n : ℝ) - 1) / 2) • g x) ↔
      stereoH x • dirac ρ g x = lam • g x := by
  have hpos : 0 < stereoH x ^ (((n : ℝ) - 1) / 2) := Real.rpow_pos_of_pos (stereoH_pos x) _
  rw [diracF_stereo_conformal ρ x hg, Real.rpow_add_one (stereoH_pos x).ne', mul_smul,
    smul_comm lam]
  exact (smul_right_injective V hpos.ne').eq_iff

end Lightlike.Dirac
