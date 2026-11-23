import Mathlib
import Lightlike.Dirac.LichnerowiczFrame

/-!
# The round sphere in a stereographic chart: frame, spin connection, curvature

On `ℝⁿ` take the conformally flat orthonormal frame `Fₐ(y) = h(y) eₐ` with `h(y) = (1 + ‖y‖²)/2`
(the inverse conformal factor of the stereographic chart of the unit sphere `Sⁿ`, metric
`4 |dy|²/(1+|y|²)²`).  Its structure functions are `cₐbc = yₐ δ_bc − y_b δₐc`, the torsion-free skew
frame connection is `ωₐbc = y_c δₐb − y_b δₐc`, and the structure-equation curvature is
`Rₐb,kl = δₐl δ_bk − δₐk δ_bl`, the curvature of the unit sphere (`stereo_curvF`).  Consequently
`lichnerowicz_frame_general` applies with `s = n(n-1)`, e.g. `s = 2` on the 2-sphere
(`stereo_scalar`).

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The inverse conformal factor `h(y) = (1 + ‖y‖²)/2` of the stereographic chart. -/
noncomputable def stereoH (y : E n) : ℝ := (1 + ‖y‖ ^ 2) / 2

/-- The conformally flat orthonormal frame `Fₐ(y) = h(y) eₐ` of the round sphere. -/
noncomputable def stereoF (y : E n) (a : Fin n) : E n := stereoH y • EuclideanSpace.single a 1

/-- Structure functions `cₐbc = yₐ δ_bc − y_b δₐc` of the stereographic frame. -/
noncomputable def stereoCs (y : E n) (a b c : Fin n) : ℝ :=
  (if b = c then y a else 0) - (if a = c then y b else 0)

/-- The skew frame connection `ωₐbc = y_c δₐb − y_b δₐc` of the stereographic frame. -/
noncomputable def stereoOmega (y : E n) (a : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun b c => (if a = b then y c else 0) - (if a = c then y b else 0)

lemma hasFDerivAt_stereoH (x : E n) : HasFDerivAt stereoH ((1 / 2 : ℝ) • (2 • innerSL ℝ x)) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 := (h.const_add (1 : ℝ)).const_smul (1 / 2 : ℝ)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [stereoH, Pi.smul_apply, smul_eq_mul]
  ring

lemma fderiv_stereoH_apply (x v : E n) : fderiv ℝ stereoH x v = ⟪x, v⟫ := by
  rw [(hasFDerivAt_stereoH x).fderiv]
  simp

lemma hasFDerivAt_stereoF (x : E n) (b : Fin n) :
    HasFDerivAt (fun y => stereoF y b)
      ((fderiv ℝ stereoH x).smulRight (EuclideanSpace.single b (1 : ℝ))) x :=
  (((hasFDerivAt_stereoH x).differentiableAt.hasFDerivAt).smul_const
    (EuclideanSpace.single b (1 : ℝ)))

lemma fderiv_stereoF_apply (x v : E n) (b : Fin n) :
    fderiv ℝ (fun y => stereoF y b) x v = ⟪x, v⟫ • EuclideanSpace.single b (1 : ℝ) := by
  rw [(hasFDerivAt_stereoF x b).fderiv]
  simp [fderiv_stereoH_apply]

lemma contDiff_stereoH : ContDiff ℝ 2 (stereoH : E n → ℝ) := by
  unfold stereoH
  exact (contDiff_const.add (contDiff_norm_sq ℝ)).div_const 2

lemma contDiff_stereoF (b : Fin n) : ContDiff ℝ 2 (fun y : E n => stereoF y b) := by
  unfold stereoF
  exact contDiff_stereoH.smul contDiff_const

lemma stereoH_pos (x : E n) : 0 < stereoH x := by
  unfold stereoH
  positivity

lemma inner_stereoF (x : E n) (a : Fin n) : ⟪x, stereoF x a⟫ = stereoH x * x a := by
  simp [stereoF, inner_smul_right, EuclideanSpace.inner_single_right]

/-- The structure functions of the stereographic frame: `[F_a, F_b] = ∑ c cₐbc F_c`. -/
lemma stereo_bracket (x : E n) (a b : Fin n) :
    fderiv ℝ (fun y => stereoF y b) x (stereoF x a) - fderiv ℝ (fun y => stereoF y a) x (stereoF x b)
      = ∑ c, stereoCs x a b c • stereoF x c := by
  rw [fderiv_stereoF_apply, fderiv_stereoF_apply, inner_stereoF, inner_stereoF]
  unfold stereoCs
  simp only [sub_smul, Finset.sum_sub_distrib]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [stereoF, smul_smul]
  rw [mul_comm (stereoH x), mul_comm (stereoH x)]

/-- The stereographic frame connection is skew. -/
lemma stereoOmega_skew (x : E n) (a k l : Fin n) :
    stereoOmega x a k l = - stereoOmega x a l k := by
  simp only [stereoOmega]
  ring

/-- The stereographic frame connection is torsion-free. -/
lemma stereo_torsion (x : E n) (a b c : Fin n) :
    stereoOmega x a b c - stereoOmega x b a c = stereoCs x a b c := by
  simp only [stereoOmega, stereoCs]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]
    ring

lemma hasFDerivAt_coord (x : E n) (l : Fin n) :
    HasFDerivAt (fun y : E n => y l) (EuclideanSpace.proj l : E n →L[ℝ] ℝ) x :=
  (EuclideanSpace.proj l : E n →L[ℝ] ℝ).hasFDerivAt

lemma stereoOmega_eq (a k l : Fin n) :
    (fun y : E n => stereoOmega y a k l) =
      fun y => (if a = k then (1 : ℝ) else 0) * y l - (if a = l then (1 : ℝ) else 0) * y k := by
  funext y
  simp only [stereoOmega]
  split_ifs <;> simp

lemma contDiff_stereoOmega (a k l : Fin n) :
    ContDiff ℝ 2 (fun y : E n => stereoOmega y a k l) := by
  have hp : ∀ l : Fin n, ContDiff ℝ 2 (fun y : E n => y l) := fun l =>
    (EuclideanSpace.proj l : E n →L[ℝ] ℝ).contDiff
  rw [stereoOmega_eq]
  exact (contDiff_const.mul (hp l)).sub (contDiff_const.mul (hp k))

lemma fderiv_stereoOmega_apply (x v : E n) (b k l : Fin n) :
    fderiv ℝ (fun y => stereoOmega y b k l) x v =
      (if b = k then v l else 0) - (if b = l then v k else 0) := by
  have h : HasFDerivAt (fun y : E n => (if b = k then (1 : ℝ) else 0) * y l -
      (if b = l then (1 : ℝ) else 0) * y k) _ x :=
    ((hasFDerivAt_coord x l).const_mul (if b = k then (1 : ℝ) else 0)).sub
      ((hasFDerivAt_coord x k).const_mul (if b = l then (1 : ℝ) else 0))
  rw [stereoOmega_eq, h.fderiv]
  split_ifs <;> simp

/-- Curvature of the unit sphere in a frame: `Rₐb,kl = δₐl δ_bk − δₐk δ_bl`. -/
noncomputable def unitR (a b k l : Fin n) : ℝ :=
  (if a = l then 1 else 0) * (if b = k then 1 else 0) -
    (if a = k then 1 else 0) * (if b = l then 1 else 0)

lemma sum_coord_mul_self (x : E n) : ∑ m, x m * x m = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [sq]

lemma stereo_curvF (x : E n) (a b k l : Fin n) :
    curvF stereoF stereoOmega (stereoCs x) x a b k l = unitR a b k l := by
  have hn := sum_coord_mul_self x
  have h2 : (1 + ‖x‖ ^ 2) / 2 = stereoH x := rfl
  have hD : ∀ a b : Fin n, omegaD stereoF stereoOmega x a b k l =
      (if l = a then if b = k then stereoH x else 0 else 0) -
        (if k = a then if b = l then stereoH x else 0 else 0) := by
    intro a b
    simp only [omegaD, fderiv_stereoOmega_apply, stereoF, PiLp.smul_apply, PiLp.single_apply,
      smul_eq_mul]
    split_ifs <;> simp
  simp only [curvF, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.sum_apply,
    Matrix.smul_apply, hD, stereoOmega, stereoCs, unitR, smul_eq_mul]
  simp [sub_mul, mul_sub, ite_mul, mul_ite, Finset.sum_sub_distrib]
  rw [hn]
  simp only [stereoH]
  clear hD h2 hn
  simp only [@eq_comm _ l a, @eq_comm _ k a, @eq_comm _ l b, @eq_comm _ k b, @eq_comm _ b a]
  by_cases h1 : b = k <;> by_cases h2 : a = l <;> by_cases h3 : a = k <;> by_cases h4 : b = l <;>
    by_cases h5 : a = b <;> by_cases h6 : k = l <;> subst_vars <;> simp_all <;> ring

/-- The scalar curvature `∑ᵢⱼ Rᵢⱼ,ⱼᵢ` of the unit `n`-sphere is `n (n - 1)`; for `n = 2` it is `2`. -/
lemma unitR_scalar (n : ℕ) : ∑ i : Fin n, ∑ j : Fin n, unitR i j j i = (n : ℝ) * (n - 1) := by
  simp only [unitR]
  simp [Finset.sum_sub_distrib]
  ring

/-- The scalar curvature of the stereographic frame of the unit `n`-sphere is `n (n - 1)`. -/
lemma stereo_scalar (x : E n) :
    ∑ i, ∑ j, curvF stereoF stereoOmega (stereoCs x) x i j j i = (n : ℝ) * (n - 1) := by
  simp only [stereo_curvF]
  exact unitR_scalar n

lemma stereoF_linearIndependent (x : E n) : LinearIndependent ℝ (stereoF x) := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.units_smul
    (fun _ => Units.mk0 (stereoH x) (stereoH_pos x).ne')
  convert h using 1
  funext a
  simp [stereoF]

/-- **Lichnerowicz formula on the unit sphere in the stereographic chart.**  For a `C²` spinor field
`f` (values in a Clifford module `ρ` of `ℝⁿ`) near `x`, with the Dirac operator and the Hessian taken
in the stereographic orthonormal frame of the round `n`-sphere (`stereoF`, `stereoOmega`):
`D² f = -∑ᵢ ∇²f(Fᵢ,Fᵢ) + (n(n-1)/4) f`.  For `n = 2` the curvature term is `f/2 = (s/4) f`, `s = 2`. -/
theorem stereo_lichnerowicz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep n V) {f : E n → V} {x : E n} (hf : ContDiffAt ℝ 2 f x) :
    diracF ρ stereoF stereoOmega (diracF ρ stereoF stereoOmega f) x =
      -∑ i, hessF ρ stereoF stereoOmega f x i i +
        (((n : ℝ) * (n - 1) / 4) : ℝ) • f x := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hω : ∀ a k l, DifferentiableAt ℝ (fun y => stereoOmega y a k l) x := fun a k l =>
    ((contDiff_stereoOmega a k l).differentiable (by norm_num)) x
  have hnf : ∀ j, DifferentiableAt ℝ (fun y => nablaF ρ stereoF stereoOmega j f y) x := by
    intro j
    have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (stereoF y j)) x :=
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
        (((contDiff_stereoF j).differentiable (by norm_num)) x)
    have h2 := (hasFDerivAt_spinForm ρ (M := fun y => stereoOmega y j) (g := f) (hω j) hfd
      ).differentiableAt
    exact h1.add h2
  have key := lichnerowicz_frame_general ρ stereoF stereoOmega hf
    (fun a => (contDiff_stereoF a).contDiffAt) (stereoF_linearIndependent x) hω hnf
    (Filter.Eventually.of_forall fun y a k l => stereoOmega_skew y a k l) stereoCs
    (Filter.Eventually.of_forall fun y a b => stereo_bracket y a b)
    (Filter.Eventually.of_forall fun y a b c => stereo_torsion y a b c)
  rw [key, stereo_scalar]
  have e : (1 / 4 * ((n : ℝ) * (n - 1))) = (n : ℝ) * (n - 1) / 4 := by ring
  rw [e]

/-- **Lichnerowicz formula on the unit 2-sphere** (stereographic chart): `D² = -∑ ∇²(Fᵢ,Fᵢ) + 1/2`,
i.e. `R/4` with `R = 2`.  The `R/2` version would give the constant `1`, which differs from `1/2`
(`stereo_two_half_fails`). -/
theorem stereo_lichnerowicz_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep 2 V) {f : E 2 → V} {x : E 2} (hf : ContDiffAt ℝ 2 f x) :
    diracF ρ stereoF stereoOmega (diracF ρ stereoF stereoOmega f) x =
      -∑ i, hessF ρ stereoF stereoOmega f x i i + (1 / 2 : ℝ) • f x := by
  rw [stereo_lichnerowicz ρ hf]
  norm_num

/-- The "`R/2`" curvature constant on the unit 2-sphere is `1`, not the `1/2` of the true formula. -/
lemma stereo_two_half_fails :
    (1 / 2 : ℝ) * ∑ i : Fin 2, ∑ j : Fin 2, unitR i j j i ≠
      (1 / 4 : ℝ) * ∑ i : Fin 2, ∑ j : Fin 2, unitR i j j i := by
  rw [unitR_scalar]
  norm_num

end Lightlike.Dirac
