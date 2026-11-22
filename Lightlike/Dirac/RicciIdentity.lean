import Mathlib
import Lightlike.Dirac.SpinDeriv
import Lightlike.Dirac.Lichnerowicz

/-!
# The Ricci identity for the spin connection in a general frame

Let `F x a ∈ ℝⁿ` (`a : Fin n`) be a frame field (not necessarily constant), `ω x a` the skew
connection matrices, and `∇ₐ f = ∂_{Fₐ} f + spinForm (ωₐ) f`. For `f` of class `C²` the second
derivative is symmetric, so the commutator `[∇ₐ, ∇_b] f` has no second-order part:

`[∇ₐ, ∇_b] f = ∑_c cₐbc ∂_{F_c} f + spinForm (∂ₐω_b - ∂_bωₐ + ω_b ωₐ - ωₐ ω_b) f`

where `cₐbc` are the structure functions `[Fₐ, F_b] = ∑ c cₐbc F_c`. If the connection is torsion-free
(`ωₐbc - ω_baс = cₐbc`, with `∇ₐ F_b = ∑_c ωₐbc F_c`), the Hessian
`∇²f(Fₐ,F_b) = ∇ₐ∇_b f - ∑_k ωₐbk ∇ₖ f` has antisymmetric part `spinorCurvature` of the structure
equation curvature `Rₐb = ∂ₐω_b - ∂_bωₐ + ω_b ωₐ - ωₐ ω_b - ∑_c cₐbc ω_c`
(`ricci_identity`). This replaces the hypothesis `hRicci` of `lichnerowicz_frame`.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The spinor covariant derivative along the frame vector `F x a`:
`∇ₐ f = ∂_{F x a} f + spinForm (ω x a) (f x)`. -/
noncomputable def nablaF (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (a : Fin n) (f : E n → V) (x : E n) : V :=
  fderiv ℝ f x (F x a) + spinForm ρ (ω x a) (f x)

/-- The second covariant derivative `∇ₐ ∇_b f` in a general frame (product rule). -/
theorem nablaF_nablaF (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) (hF : ∀ a, DifferentiableAt ℝ (fun y => F y a) x)
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x) (a b : Fin n) :
    nablaF ρ F ω a (fun y => nablaF ρ F ω b f y) x =
      fderiv ℝ (fderiv ℝ f) x (F x a) (F x b) +
      fderiv ℝ f x (fderiv ℝ (fun y => F y b) x (F x a)) +
      spinForm ρ (fun k l => fderiv ℝ (fun y => ω y b k l) x (F x a)) (f x) +
      spinForm ρ (ω x b) (fderiv ℝ f x (F x a)) +
      spinForm ρ (ω x a) (nablaF ρ F ω b f x) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hf2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 := hf2.hasFDerivAt.clm_apply (hF b).hasFDerivAt
  have h2 := hasFDerivAt_spinForm ρ (M := fun y => ω y b) (g := f) (hω b) hfd
  have key : fderiv ℝ (fun y => nablaF ρ F ω b f y) x =
      fderiv ℝ (fun y => fderiv ℝ f y (F y b)) x +
        fderiv ℝ (fun y => spinForm ρ (ω y b) (f y)) x :=
    (h1.differentiableAt.hasFDerivAt.add h2.differentiableAt.hasFDerivAt).fderiv
  have e : nablaF ρ F ω a (fun y => nablaF ρ F ω b f y) x =
      fderiv ℝ (fun y => nablaF ρ F ω b f y) x (F x a) +
        spinForm ρ (ω x a) (nablaF ρ F ω b f x) := rfl
  rw [e, key, add_apply, fderiv_clm_apply hf2 (hF b), fderiv_spinForm_apply ρ (hω b) hfd]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  abel

/-- The derivative matrix `(∂ₐ ω_b)ₖₗ = ∂_{F x a} (ω y b k l)` at `x`. -/
noncomputable def omegaD (F : E n → Fin n → E n) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : E n) (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun k l => fderiv ℝ (fun y => ω y b k l) x (F x a)

/-- **Commutator of the spinor covariant derivatives.**  For `f` of class `C²` at `x`, a frame `F`
with structure functions `cs` (`[F_b, F_a] = ∑ cs a b c F_c` in the form `hbr`), and skew `ω x a`:
`∇ₐ∇_b f - ∇_b∇ₐ f = ∑_c cₐbc ∂_{F_c} f + spinForm (∂ₐω_b - ∂_bωₐ + ω_b ωₐ - ωₐ ω_b) f`. -/
theorem nablaF_comm (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) (hF : ∀ a, DifferentiableAt ℝ (fun y => F y a) x)
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (hskew : ∀ a k l, ω x a k l = - ω x a l k) (cs : Fin n → Fin n → Fin n → ℝ)
    (hbr : ∀ a b, fderiv ℝ (fun y => F y b) x (F x a) - fderiv ℝ (fun y => F y a) x (F x b) =
      ∑ c, cs a b c • F x c) (a b : Fin n) :
    nablaF ρ F ω a (fun y => nablaF ρ F ω b f y) x -
        nablaF ρ F ω b (fun y => nablaF ρ F ω a f y) x =
      ∑ c, cs a b c • fderiv ℝ f x (F x c) +
      spinForm ρ (omegaD F ω x a b - omegaD F ω x b a + (ω x b * ω x a - ω x a * ω x b))
        (f x) := by
  have hsym : fderiv ℝ (fderiv ℝ f) x (F x a) (F x b) = fderiv ℝ (fderiv ℝ f) x (F x b) (F x a) :=
    (hf.isSymmSndFDerivAt (by simp)) _ _
  have hbr' : fderiv ℝ f x (fderiv ℝ (fun y => F y b) x (F x a)) -
      fderiv ℝ f x (fderiv ℝ (fun y => F y a) x (F x b)) =
      ∑ c, cs a b c • fderiv ℝ f x (F x c) := by
    rw [← map_sub, hbr a b, map_sum]
    simp only [map_smul]
  have hbk := congrArg (fun L => L (f x))
    (spinForm_bracket ρ (A := ω x a) (B := ω x b) (hskew a))
  simp only [spinForm_sub, sub_apply, mul_apply_eq_comp] at hbk
  rw [nablaF_nablaF ρ F ω hf hF hω a b, nablaF_nablaF ρ F ω hf hF hω b a]
  simp only [spinForm_add, spinForm_sub, add_apply, sub_apply]
  simp only [nablaF, map_add]
  have hd : ∀ u v : Fin n, spinForm ρ (fun k l => fderiv ℝ (fun y => ω y u k l) x (F x v))
      (f x) = spinForm ρ (omegaD F ω x v u) (f x) := fun u v => rfl
  rw [hd, hd]
  linear_combination (norm := module) hsym + hbr' + hbk

/-- `spinorCurvature` of the frame data `R` is `spinForm` of the matrices `R i j`. -/
lemma spinorCurvature_eq_spinForm (ρ : CliffordRep n V)
    (R : Fin n → Fin n → Fin n → Fin n → ℝ) (i j : Fin n) :
    spinorCurvature (gam ρ) R i j = spinForm ρ (fun k l => R i j k l) := by
  simp only [spinorCurvature, spinForm, Finset.smul_sum, smul_smul]

/-- The frame Hessian `∇²f(Fₐ,F_b) = ∇ₐ∇_b f - ∑ₖ ωₐbk ∇ₖ f` at `x`. -/
noncomputable def hessF (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) (f : E n → V) (x : E n) (a b : Fin n) : V :=
  nablaF ρ F ω a (fun y => nablaF ρ F ω b f y) x - ∑ k, (ω x a b k) • nablaF ρ F ω k f x

/-- The curvature matrices of the structure equation,
`Rₐb = ∂ₐω_b - ∂_bωₐ + ω_b ωₐ - ωₐ ω_b - ∑_c cₐbc ω_c`, at `x`. -/
noncomputable def curvF (F : E n → Fin n → E n) (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (cs : Fin n → Fin n → Fin n → ℝ) (x : E n) (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  omegaD F ω x a b - omegaD F ω x b a + (ω x b * ω x a - ω x a * ω x b) -
    ∑ c, cs a b c • ω x c

/-- **Ricci identity for the spin connection.**  For a torsion-free frame connection
(`ωₐbc - ω_bac = cₐbc`), the antisymmetric part of the frame Hessian of a `C²` spinor field is the
action of the spinor curvature of the structure-equation curvature `curvF`:
`∇²f(Fₐ,F_b) - ∇²f(F_b,Fₐ) = ¼ ∑ₖₗ (Rₐb)ₖₗ γₖγₗ f`. -/
theorem ricci_identity (ρ : CliffordRep n V) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) (hF : ∀ a, DifferentiableAt ℝ (fun y => F y a) x)
    (hω : ∀ a k l, DifferentiableAt ℝ (fun y => ω y a k l) x)
    (hskew : ∀ a k l, ω x a k l = - ω x a l k) (cs : Fin n → Fin n → Fin n → ℝ)
    (hbr : ∀ a b, fderiv ℝ (fun y => F y b) x (F x a) - fderiv ℝ (fun y => F y a) x (F x b) =
      ∑ c, cs a b c • F x c)
    (htors : ∀ a b c, ω x a b c - ω x b a c = cs a b c) (a b : Fin n) :
    hessF ρ F ω f x a b - hessF ρ F ω f x b a =
      spinorCurvature (gam ρ) (fun a b k l => curvF F ω cs x a b k l) a b (f x) := by
  rw [spinorCurvature_eq_spinForm]
  have hc := nablaF_comm ρ F ω hf hF hω hskew cs hbr a b
  have hsum : ∑ k, (ω x a b k) • nablaF ρ F ω k f x - ∑ k, (ω x b a k) • nablaF ρ F ω k f x =
      ∑ c, cs a b c • fderiv ℝ f x (F x c) + spinForm ρ (∑ c, cs a b c • ω x c) (f x) := by
    rw [← Finset.sum_sub_distrib, spinForm_sum]
    simp only [sum_apply, nablaF, smul_add, spinForm_smul, smul_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← htors a b c]
    module
  have e : (fun k l => curvF F ω cs x a b k l) = curvF F ω cs x a b := rfl
  rw [e, curvF, spinForm_sub]
  simp only [hessF, sub_apply]
  rw [sub_sub_sub_comm, hc, hsum]
  abel

end Lightlike.Dirac
