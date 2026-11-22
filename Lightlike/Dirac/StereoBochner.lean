import Mathlib
import Lightlike.Dirac.StereoCurved
import Lightlike.Dirac.RicciIdentity
import Lightlike.Dirac.SpinDeriv

/-!
# Integrated Bochner identity on the round sphere in the stereographic chart

Pointwise (any frame with skew connection matrices, skew Clifford module):
`⟪∇ₐ∇ₐ f, f⟫ = ∂_{Fₐ}⟪∇ₐ f, f⟫ − ‖∇ₐ f‖²` (`inner_nablaF_nablaF`).  On the round sphere the divergence
term is compensated by the connection term of the frame Hessian after integration against the
Riemannian density `h^{-n}`, which gives `∫ ⟪−∑ ∇²f(Fᵢ,Fᵢ), f⟫ = ∫ ∑ ‖∇ᵢ f‖²`
(`integral_inner_neg_hess_stereo`) and the integrated Lichnerowicz formula.

## References

* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators* (1992), chapter
  "Clifford Modules and Dirac Operators" (source key `bgv-1992`); no equation number is claimed.
-/

namespace Lightlike.Dirac

open scoped RealInnerProductSpace
open MeasureTheory

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `⟪γᵢγⱼ u, v⟫ = ⟪u, γⱼγᵢ v⟫` for a skew Clifford module. -/
lemma inner_gam_mul_gam {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (i j : Fin n) (u v : V) :
    inner ℝ ((gam ρ i * gam ρ j) u) v = inner ℝ u ((gam ρ j * gam ρ i) v) := by
  have hρ' : ∀ (i : Fin n) (w u : V), inner ℝ (gam ρ i w) u = -inner ℝ w (gam ρ i u) := hρ
  simp only [mul_apply_eq_comp, hρ', neg_neg]

/-- The spinorial connection form of a skew matrix is skew-adjoint on a skew Clifford module. -/
lemma spinForm_inner_skew {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : ∀ i j, M i j = -M j i) (u v : V) :
    inner ℝ (spinForm ρ M u) v = -inner ℝ u (spinForm ρ M v) := by
  have h1 : inner ℝ (spinForm ρ M u) v =
      (1 / 4 : ℝ) * ∑ i, ∑ j, M i j * inner ℝ u ((gam ρ j * gam ρ i) v) := by
    simp only [spinForm, smul_apply, sum_apply,
      real_inner_smul_left, sum_inner, inner_gam_mul_gam hρ]
  have h2 : inner ℝ u (spinForm ρ M v) =
      (1 / 4 : ℝ) * ∑ i, ∑ j, M i j * inner ℝ u ((gam ρ i * gam ρ j) v) := by
    simp only [spinForm, smul_apply, sum_apply,
      real_inner_smul_right, inner_sum]
  rw [h1, h2, Finset.sum_comm (f := fun i j => M i j * inner ℝ u ((gam ρ j * gam ρ i) v))]
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hM j i]
  ring

/-- **Pointwise Bochner identity.** For a skew Clifford module and a skew connection matrix `ω x a`,
`⟪∇ₐ∇ₐ f, f⟫ = ∂_{Fₐ}⟪∇ₐ f, f⟫ − ‖∇ₐ f‖²` at `x`. -/
lemma inner_nablaF_nablaF {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) (F : E n → Fin n → E n)
    (ω : E n → Fin n → Matrix (Fin n) (Fin n) ℝ) {f : E n → V} {x : E n} (a : Fin n)
    (hskew : ∀ k l, ω x a k l = -ω x a l k)
    (hfd : DifferentiableAt ℝ f x)
    (hu : DifferentiableAt ℝ (fun y => nablaF ρ F ω a f y) x) :
    inner ℝ (nablaF ρ F ω a (fun y => nablaF ρ F ω a f y) x) (f x) =
      fderiv ℝ (fun y => inner ℝ (nablaF ρ F ω a f y) (f y)) x (F x a) -
        ‖nablaF ρ F ω a f x‖ ^ 2 := by
  have hG := hu.hasFDerivAt.inner ℝ hfd.hasFDerivAt
  rw [hG.fderiv]
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply]
  have e1 : nablaF ρ F ω a (fun y => nablaF ρ F ω a f y) x =
      fderiv ℝ (fun y => nablaF ρ F ω a f y) x (F x a) +
        spinForm ρ (ω x a) (nablaF ρ F ω a f x) := rfl
  have hu0 : nablaF ρ F ω a f x = fderiv ℝ f x (F x a) + spinForm ρ (ω x a) (f x) := rfl
  have hn : ‖nablaF ρ F ω a f x‖ ^ 2 = inner ℝ (nablaF ρ F ω a f x) (fderiv ℝ f x (F x a)) +
      inner ℝ (nablaF ρ F ω a f x) (spinForm ρ (ω x a) (f x)) := by
    rw [← real_inner_self_eq_norm_sq, ← inner_add_right, ← hu0]
  rw [e1, inner_add_left, spinForm_inner_skew hρ hskew, hn]
  ring

lemma sum_stereoOmega_diag (x : E n) (k : Fin n) :
    ∑ i, stereoOmega x i i k = ((n : ℝ) - 1) * x k := by
  simp only [stereoOmega, ite_true, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  have : ∑ i : Fin n, (if i = k then x i else 0) = x k := by simp
  rw [this, nsmul_eq_mul]
  ring

/-- Integrability of `φ ∂ᵢ G` for a continuous `φ` and compactly supported `C¹` function `G`. -/
lemma integrable_mul_fderiv_scalar {φ G : E n → ℝ} (hφ : Continuous φ) (hG : ContDiff ℝ 1 G)
    (hGc : HasCompactSupport G) (i : Fin n) :
    Integrable (fun x => φ x * fderiv ℝ G x (e i)) := by
  have hGd : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  refine Continuous.integrable_of_hasCompactSupport
    (hφ.mul (hGd.clm_apply continuous_const)) ?_
  refine HasCompactSupport.intro hGc.isCompact fun x hx => ?_
  simp [fderiv_of_notMem_tsupport ℝ hx]

/-- The stereographic covariant derivative of a compactly supported field vanishes off `tsupport f`. -/
lemma nablaF_stereo_eq_zero {ρ : CliffordRep n V} {f : E n → V} {x : E n} (hx : x ∉ tsupport f)
    (i : Fin n) : nablaF ρ stereoF stereoOmega i f x = 0 := by
  simp [nablaF, fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]

/-- The stereographic covariant derivative of a `C²` field is `C¹`. -/
lemma contDiff_nablaF_stereo {ρ : CliffordRep n V} {f : E n → V} (hf : ContDiff ℝ 2 f)
    (i : Fin n) : ContDiff ℝ 1 (fun y => nablaF ρ stereoF stereoOmega i f y) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  refine ContDiff.add ?_ ?_
  · exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      ((contDiff_stereoF i).of_le (by norm_num))
  · have h : ∀ y, spinForm ρ (stereoOmega y i) (f y) =
        (1 / 4 : ℝ) • ∑ k, ∑ l, stereoOmega y i k l • (gam ρ k * gam ρ l) (f y) := by
      intro y
      simp only [spinForm, smul_apply, sum_apply]
    simp only [h]
    refine ContDiff.const_smul _ (ContDiff.sum fun k _ => ContDiff.sum fun l _ => ?_)
    exact ((contDiff_stereoOmega i k l).of_le (by norm_num)).smul
      ((gam ρ k * gam ρ l).contDiff.comp hf1)

/-- The stereographic covariant derivative of a `C¹` field is continuous. -/
lemma continuous_nablaF_stereo {ρ : CliffordRep n V} {g : E n → V} (hg : ContDiff ℝ 1 g)
    (i : Fin n) : Continuous (fun y => nablaF ρ stereoF stereoOmega i g y) := by
  refine Continuous.add ?_ ?_
  · exact (hg.continuous_fderiv (by norm_num)).clm_apply (contDiff_stereoF i).continuous
  · have h : ∀ y, spinForm ρ (stereoOmega y i) (g y) =
        (1 / 4 : ℝ) • ∑ k, ∑ l, stereoOmega y i k l • (gam ρ k * gam ρ l) (g y) := by
      intro y
      simp only [spinForm, smul_apply, sum_apply]
    simp only [h]
    refine Continuous.const_smul (continuous_finsetSum _ fun k _ =>
      continuous_finsetSum _ fun l _ => ?_) _
    exact ((contDiff_stereoOmega i k l).continuous).smul
      ((gam ρ k * gam ρ l).continuous.comp hg.continuous)

/-- `D f` is `C¹` for a `C²` field `f` in the stereographic frame. -/
lemma contDiff_diracF_stereo {ρ : CliffordRep n V} {f : E n → V} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (diracF ρ stereoF stereoOmega f) :=
  ContDiff.sum fun i _ => (gam ρ i).contDiff.comp (contDiff_nablaF_stereo hf i)

/-- `D g` is continuous for a `C¹` field `g` in the stereographic frame. -/
lemma continuous_diracF_stereo {ρ : CliffordRep n V} {g : E n → V} (hg : ContDiff ℝ 1 g) :
    Continuous (diracF ρ stereoF stereoOmega g) :=
  continuous_finsetSum _ fun i _ => (gam ρ i).continuous.comp (continuous_nablaF_stereo hg i)

/-- `D f` vanishes off `tsupport f`. -/
lemma diracF_stereo_eq_zero {ρ : CliffordRep n V} {f : E n → V} {x : E n}
    (hx : x ∉ tsupport f) : diracF ρ stereoF stereoOmega f x = 0 := by
  simp [diracF, nablaF_stereo_eq_zero hx]

/-- Scalar integration by parts against a `C¹` weight, with a compactly supported `C¹` factor. -/
lemma integral_mul_fderiv_scalar {φ G : E n → ℝ} (hφ : ContDiff ℝ 1 φ) (hG : ContDiff ℝ 1 G)
    (hGc : HasCompactSupport G) (i : Fin n) :
    ∫ x, φ x * fderiv ℝ G x (e i) = -∫ x, fderiv ℝ φ x (e i) * G x := by
  have hφd : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hGd : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  have h1 : Integrable (fun x => (ContinuousLinearMap.mul ℝ ℝ) (fderiv ℝ φ x (e i)) (G x)) :=
    integrable_of_cont_supp (k := G)
      ((hφd.clm_apply continuous_const).mul hG.continuous) hGc (fun x hx => by simp [hx])
  have h2 : Integrable (fun x => (ContinuousLinearMap.mul ℝ ℝ) (φ x) (fderiv ℝ G x (e i))) := by
    refine Continuous.integrable_of_hasCompactSupport
      (hφ.continuous.mul (hGd.clm_apply continuous_const)) ?_
    refine HasCompactSupport.intro hGc.isCompact fun x hx => ?_
    have : fderiv ℝ G x = 0 := by
      have := notMem_tsupport_iff_eventuallyEq.mp hx
      exact (Filter.EventuallyEq.fderiv_eq this).trans (by simp)
    simp [this]
  have h3 : Integrable (fun x => (ContinuousLinearMap.mul ℝ ℝ) (φ x) (G x)) :=
    integrable_of_cont_supp (k := G) (hφ.continuous.mul hG.continuous) hGc
      (fun x hx => by simp [hx])
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := MeasureTheory.volume)
    (B := ContinuousLinearMap.mul ℝ ℝ) (v := e i) h1 h2 h3
    (fun x _ => (hφ.differentiable (by norm_num)) x) (fun x _ => (hG.differentiable (by norm_num)) x)

/-- **Pointwise Bochner identity on the round sphere** (stereographic frame): with
`Gᵢ(y) = ⟪∇ᵢ f(y), f(y)⟫`,
`∑ᵢ ⟪∇²f(Fᵢ,Fᵢ), f⟫ = ∑ᵢ ∂_{Fᵢ} Gᵢ − ∑ᵢ ‖∇ᵢ f‖² − (n-1) ∑ₖ xₖ Gₖ`. -/
lemma sum_inner_hess_stereo {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {f : E n → V} {x : E n}
    (hf : ContDiffAt ℝ 2 f x) :
    ∑ i, inner ℝ (hessF ρ stereoF stereoOmega f x i i) (f x) =
      ∑ i, fderiv ℝ (fun y => inner ℝ (nablaF ρ stereoF stereoOmega i f y) (f y)) x (stereoF x i) -
        ∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2 -
        ((n : ℝ) - 1) * ∑ k, x k * inner ℝ (nablaF ρ stereoF stereoOmega k f x) (f x) := by
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
  have h1 : ∀ i, inner ℝ (hessF ρ stereoF stereoOmega f x i i) (f x) =
      (fderiv ℝ (fun y => inner ℝ (nablaF ρ stereoF stereoOmega i f y) (f y)) x (stereoF x i) -
        ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) -
      ∑ k, stereoOmega x i i k * inner ℝ (nablaF ρ stereoF stereoOmega k f x) (f x) := by
    intro i
    rw [hessF, inner_sub_left, inner_nablaF_nablaF hρ stereoF stereoOmega i
      (fun k l => stereoOmega_skew x i k l) hfd (hnf i), sum_inner]
    simp only [real_inner_smul_left]
  simp only [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_stereoOmega_diag, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Integrated Bochner identity on the round sphere** (stereographic chart, Riemannian density
`h^{-n}`): for a compactly supported `C²` spinor field `f`,
`∫ ⟪−∑ᵢ ∇²f(Fᵢ,Fᵢ), f⟫ h^{-n} = ∫ (∑ᵢ ‖∇ᵢ f‖²) h^{-n}`, i.e. `∇*∇` is nonnegative. -/
theorem integral_inner_neg_hess_stereo {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {f : E n → V}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, inner ℝ (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x) * stereoW n x =
      ∫ x, (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) * stereoW n x := by
  set G : Fin n → E n → ℝ :=
    fun i y => inner ℝ (nablaF ρ stereoF stereoOmega i f y) (f y) with hGdef
  have hGc1 : ∀ i, ContDiff ℝ 1 (G i) := fun i =>
    (contDiff_nablaF_stereo hf i).inner ℝ (hf.of_le (by norm_num))
  have hGcs : ∀ i, HasCompactSupport (G i) := fun i =>
    HasCompactSupport.intro hfc.isCompact fun x hx => by
      simp [G, image_eq_zero_of_notMem_tsupport hx]
  have hφd : Continuous (fderiv ℝ (stereoPhi n)) := contDiff_stereoPhi.continuous_fderiv (by norm_num)
  have hI1 : ∀ i, Integrable (fun x => stereoPhi n x * fderiv ℝ (G i) x (e i)) := fun i =>
    integrable_mul_fderiv_scalar contDiff_stereoPhi.continuous (hGc1 i) (hGcs i) i
  have hI2 : ∀ i, Integrable (fun x => fderiv ℝ (stereoPhi n) x (e i) * G i x) := fun i =>
    integrable_of_cont_supp (k := G i)
      ((hφd.clm_apply continuous_const).mul (hGc1 i).continuous) (hGcs i)
      (fun x hx => by simp [hx])
  set T : E n → ℝ := fun x => ∑ i, (stereoPhi n x * fderiv ℝ (G i) x (e i) +
    fderiv ℝ (stereoPhi n) x (e i) * G i x) with hTdef
  have hT0 : ∫ x, T x = 0 := by
    simp only [T]
    have hsum := integral_finsetSum (μ := volume) Finset.univ
      (f := fun i x => stereoPhi n x * fderiv ℝ (G i) x (e i) +
        fderiv ℝ (stereoPhi n) x (e i) * G i x) (fun i _ => (hI1 i).add (hI2 i))
    rw [hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_add (hI1 i) (hI2 i),
      integral_mul_fderiv_scalar contDiff_stereoPhi (hGc1 i) (hGcs i) i]
    ring
  have hTint : Integrable T := integrable_finsetSum _ fun i _ => (hI1 i).add (hI2 i)
  have hBint : Integrable (fun x => (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) *
      stereoW n x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · refine (continuous_finsetSum _ fun i _ => ?_).mul continuous_stereoW
      exact ((contDiff_nablaF_stereo hf i).continuous).norm.pow 2
    · refine HasCompactSupport.intro hfc.isCompact fun x hx => ?_
      simp [nablaF_stereo_eq_zero hx]
  have hpt : ∀ x, inner ℝ (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x) * stereoW n x =
      (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) * stereoW n x - T x := by
    intro x
    rw [inner_neg_left, sum_inner, sum_inner_hess_stereo hρ hf.contDiffAt]
    have hF : ∀ i, fderiv ℝ (G i) x (stereoF x i) = stereoH x * fderiv ℝ (G i) x (e i) := by
      intro i
      show fderiv ℝ (G i) x (stereoH x • e i) = _
      rw [map_smul, smul_eq_mul]
    have hT : T x = stereoW n x * (stereoH x * ∑ i, fderiv ℝ (G i) x (e i)) -
        ((n : ℝ) - 1) * stereoW n x * ∑ i, x i * G i x := by
      simp only [T, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fderiv_stereoPhi_apply, inner_e, stereoPhi_eq]
      ring
    have hF' : ∑ i, fderiv ℝ (G i) x (stereoF x i) =
        stereoH x * ∑ i, fderiv ℝ (G i) x (e i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hF i
    simp only [hGdef] at hT hF'
    rw [hT, hF']
    ring
  calc ∫ x, inner ℝ (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x) * stereoW n x
      = ∫ x, ((∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) * stereoW n x - T x) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x, (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) * stereoW n x) - ∫ x, T x :=
        integral_sub hBint hTint
    _ = _ := by rw [hT0, sub_zero]

/-- **Integrated Lichnerowicz formula on the round sphere** (stereographic chart, Riemannian density
`h^{-n}`): for a compactly supported `C²` spinor field `f` (values in a skew Clifford module),
`∫ ‖D f‖² h^{-n} = ∫ (∑ᵢ ‖∇ᵢ f‖²) h^{-n} + (n(n-1)/4) ∫ ‖f‖² h^{-n}`.
The constant `n(n-1)/4 = s/4` with scalar curvature `s = n(n-1)` of the unit sphere. -/
theorem integral_norm_diracF_stereo_sq {ρ : CliffordRep n V} (hρ : IsSkewRep ρ) {f : E n → V}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW n x =
      (∫ x, (∑ i, ‖nablaF ρ stereoF stereoOmega i f x‖ ^ 2) * stereoW n x) +
        ((n : ℝ) * (n - 1) / 4) * ∫ x, ‖f x‖ ^ 2 * stereoW n x := by
  have hDc1 := contDiff_diracF_stereo (ρ := ρ) hf
  have hDcs : HasCompactSupport (diracF ρ stereoF stereoOmega f) :=
    HasCompactSupport.intro hfc.isCompact fun x hx => diracF_stereo_eq_zero hx
  have h1 := integral_diracF_stereo_inner hρ (hf.of_le (by norm_num)) hDc1 hfc hDcs
  have hM : Integrable (fun x => inner ℝ (f x)
      (diracF ρ stereoF stereoOmega (diracF ρ stereoF stereoOmega f) x) * stereoW n x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hf.continuous.inner (continuous_diracF_stereo hDc1)).mul continuous_stereoW
    · exact HasCompactSupport.intro hfc.isCompact fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx]
  have hQ : Integrable (fun x => ((n : ℝ) * (n - 1) / 4) * (‖f x‖ ^ 2 * stereoW n x)) :=
    integrable_of_cont_supp (k := f)
      (continuous_const.mul ((hf.continuous.norm.pow 2).mul continuous_stereoW)) hfc
      (fun x hx => by simp [hx])
  have hP : ∀ x, inner ℝ (f x)
        (diracF ρ stereoF stereoOmega (diracF ρ stereoF stereoOmega f) x) * stereoW n x =
      inner ℝ (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x) * stereoW n x +
        ((n : ℝ) * (n - 1) / 4) * (‖f x‖ ^ 2 * stereoW n x) := by
    intro x
    rw [stereo_lichnerowicz ρ hf.contDiffAt, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, real_inner_comm (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x)]
    ring
  have hPint : Integrable (fun x => inner ℝ (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x) *
      stereoW n x) := by
    refine (hM.sub hQ).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hP x]
    ring
  calc ∫ x, ‖diracF ρ stereoF stereoOmega f x‖ ^ 2 * stereoW n x
      = ∫ x, inner ℝ (diracF ρ stereoF stereoOmega f x) (diracF ρ stereoF stereoOmega f x) *
          stereoW n x := by
        simp only [real_inner_self_eq_norm_sq]
    _ = ∫ x, inner ℝ (f x)
          (diracF ρ stereoF stereoOmega (diracF ρ stereoF stereoOmega f) x) * stereoW n x := h1
    _ = ∫ x, (inner ℝ (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x) * stereoW n x +
          ((n : ℝ) * (n - 1) / 4) * (‖f x‖ ^ 2 * stereoW n x)) :=
        integral_congr_ae (Filter.Eventually.of_forall hP)
    _ = (∫ x, inner ℝ (-∑ i, hessF ρ stereoF stereoOmega f x i i) (f x) * stereoW n x) +
          ∫ x, ((n : ℝ) * (n - 1) / 4) * (‖f x‖ ^ 2 * stereoW n x) := integral_add hPint hQ
    _ = _ := by
        rw [integral_inner_neg_hess_stereo hρ hf hfc, integral_const_mul]

end Lightlike.Dirac
