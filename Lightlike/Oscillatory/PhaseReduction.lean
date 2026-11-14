module

public import Lightlike.Oscillatory.Hadamard
public import Lightlike.Oscillatory.Vanishing

/-!
# Local stationary phase at a nondegenerate critical point

The reduction of a general phase to its quadratic part, following the proof of Hörmander,
*The Analysis of Linear Partial Differential Operators I*, Theorem 7.7.5.

Let `φ : ℝⁿ → ℂ` be smooth with `φ(0) = 0`, `dφ(0) = 0`, `Im φ ≥ 0` on a ball around `0`, and a
nondegenerate Hessian `A` at `0`. Write `φ = ⟨A x, x⟩/2 + g`, where `g` vanishes to third order
(`phaseRem_eq_cubic`, by Hadamard's lemma), and `F_s = ⟨A x, x⟩/2 + s g` for `s ∈ [0, 1]`
(`phaseFamily`). Then `Im ⟨A x, x⟩ ≥ 0` (`im_qform_hessMat_nonneg`), so `Im F_s ≥ 0` near `0`,
and `∂ₗ F_s = (B s x · x)ₗ` with `B s 0 = A` invertible, which supplies the coefficients of the
integration by parts (`exists_phase_coeff`). Taylor's formula for `e^{iτ s g}` (`cexp_taylor`,
`expansion`) splits `∫ u e^{iτφ}` into terms `(iτ)ʲ ∫ gʲ u e^{iτ⟨A x, x⟩/2}`, each handled by the
quadratic-phase lemma and integration by parts (`exists_bound_quad`), and a remainder controlled
uniformly in `s` (`exists_bound_phaseFamily`, Hörmander's (7.7.12)).

* `stationary_phase_local`: for `u` smooth and supported in a small ball around `0`,
  `∫ u e^{iτφ} = (2π/τ)^{n/2} (det(-iA))^{-1/2} u(0) + O(τ^{-n/2-1})` as `τ → ∞`.
-/

@[expose] public section

namespace Lightlike.Oscillatory

open MeasureTheory Complex Matrix Finset Set Filter
open scoped Real ContDiff Topology

variable {n : ℕ}

/-! ### Coordinate derivatives -/

/-- The partial derivative of a sum. -/
theorem coordDeriv_add {f h : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (l : Fin n) :
    coordDeriv (fun y => f y + h y) l x = coordDeriv f l x + coordDeriv h l x := by
  simp only [coordDeriv]
  rw [show (fun y => f y + h y) = f + h from rfl, (hf.hasFDerivAt.add hh.hasFDerivAt).fderiv]
  rfl

/-- The partial derivative of a difference. -/
theorem coordDeriv_sub {f h : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hh : DifferentiableAt ℝ h x) (l : Fin n) :
    coordDeriv (fun y => f y - h y) l x = coordDeriv f l x - coordDeriv h l x := by
  simp only [coordDeriv]
  rw [show (fun y => f y - h y) = f - h from rfl, (hf.hasFDerivAt.sub hh.hasFDerivAt).fderiv]
  rfl

/-- The partial derivative of a constant multiple. -/
theorem coordDeriv_const_mul {f : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (c : ℂ) (l : Fin n) :
    coordDeriv (fun y => c * f y) l x = c * coordDeriv f l x := by
  simp only [coordDeriv, fderiv_const_mul hf c, _root_.smul_apply, smul_eq_mul]

/-- The linear form `x ↦ ∑ₖ aₖ xₖ`. -/
noncomputable def linCLM (a : Fin n → ℂ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  ∑ k, a k • (ofRealCLM.comp (ContinuousLinearMap.proj k))

/-- `linCLM a x = ∑ₖ aₖ xₖ`. -/
theorem linCLM_apply (a : Fin n → ℂ) (x : Fin n → ℝ) : linCLM a x = ∑ k, a k * (x k : ℂ) := by
  simp [linCLM]

/-- `linCLM a` sends the `j`-th basis vector to `aⱼ`. -/
theorem linCLM_single (a : Fin n → ℂ) (j : Fin n) : linCLM a (Pi.single j 1) = a j := by
  rw [linCLM_apply, Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The `l`-th entry of `A x` is the linear form `linCLM (A l)` at `x`. -/
theorem mulVec_cvec_eq_linCLM (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n) (x : Fin n → ℝ) :
    (A *ᵥ cvec x) l = linCLM (A l) x := by
  rw [linCLM_apply]
  rfl

/-! ### The Hessian -/

/-- The Hessian matrix `∂ⱼ∂ᵢφ(x)` of `φ : ℝⁿ → ℂ`. -/
noncomputable def hessMat (φ : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => coordDeriv (fun y => coordDeriv φ i y) j x

/-- The Hessian entries are the entries of the second Fréchet derivative. -/
theorem hessMat_eq {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (x : Fin n → ℝ) (i j : Fin n) :
    hessMat φ x i j = fderiv ℝ (fderiv ℝ φ) x (Pi.single j 1) (Pi.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  simp only [hessMat, coordDeriv]
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The Hessian of a smooth function is symmetric (Schwarz). -/
theorem hessMat_isSymm {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (x : Fin n → ℝ) :
    (hessMat φ x).IsSymm := by
  have hs := hφ.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [hessMat_eq hφ, hessMat_eq hφ, hs]

/-- Partial derivatives of a smooth function are smooth. -/
theorem contDiff_coordDeriv {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f) (l : Fin n) :
    ContDiff ℝ ∞ (coordDeriv f l) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The partial derivative of a continuous linear map is its value on a basis vector. -/
theorem coordDeriv_clm (L : (Fin n → ℝ) →L[ℝ] ℂ) (l : Fin n) (x : Fin n → ℝ) :
    coordDeriv L l x = L (Pi.single l 1) := by
  simp [coordDeriv, ContinuousLinearMap.fderiv]

/-! ### The phase as quadratic part plus a cubic remainder -/

section Phase

variable {φ : (Fin n → ℝ) → ℂ}

/-- The remainder `g = φ - ⟨A x, x⟩/2` after the quadratic part, `A` the Hessian at `0`. -/
noncomputable def phaseRem (φ : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  φ x - qform (hessMat φ 0) x / 2

/-- The Hadamard coefficients `Mₗⱼ` of `∂ₗ g`: `∂ₗ g = ∑ⱼ xⱼ Mₗⱼ`. -/
noncomputable def phaseM (φ : (Fin n → ℝ) → ℂ) (l j : Fin n) : (Fin n → ℝ) → ℂ :=
  hadamardCoeff (coordDeriv (phaseRem φ) l) j

/-- `Nᵢⱼ(x) = ∫₀¹ t Mᵢⱼ(t x) dt`, so that the Hadamard coefficients of `g` are `∑ⱼ xⱼ Nᵢⱼ`. -/
noncomputable def phaseN (φ : (Fin n → ℝ) → ℂ) (i j : Fin n) (x : Fin n → ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..1, (t : ℂ) * phaseM φ i j (t • x)

/-- The cubic coefficients `gᵢⱼₖ`: `g = ∑ xᵢ xⱼ xₖ gᵢⱼₖ`. -/
noncomputable def phaseCubic (φ : (Fin n → ℝ) → ℂ) (i j k : Fin n) : (Fin n → ℝ) → ℂ :=
  hadamardCoeff (phaseN φ i j) k

/-- The remainder `g = φ - ⟨A x, x⟩/2` is smooth. -/
theorem contDiff_phaseRem (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (phaseRem φ) :=
  hφ.sub ((contDiff_qform _).div_const 2)

/-- `∂ₗ g = ∂ₗ φ - (A x)ₗ`. -/
theorem coordDeriv_phaseRem (hφ : ContDiff ℝ ∞ φ) (l : Fin n) (x : Fin n → ℝ) :
    coordDeriv (phaseRem φ) l x = coordDeriv φ l x - linCLM (hessMat φ 0 l) x := by
  have h1 : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ (fun y => qform (hessMat φ 0) y / 2) x :=
    (((contDiff_qform _).div_const 2).differentiable (by simp)) x
  rw [show phaseRem φ = fun y => φ y - qform (hessMat φ 0) y / 2 from rfl, coordDeriv_sub h1 h2,
    coordDeriv_qform_half (hessMat_isSymm hφ 0), mulVec_cvec_eq_linCLM]

/-- The coefficients `Mₗⱼ` are smooth. -/
theorem contDiff_phaseM (hφ : ContDiff ℝ ∞ φ) (l j : Fin n) : ContDiff ℝ ∞ (phaseM φ l j) :=
  contDiff_hadamardCoeff (contDiff_coordDeriv (contDiff_phaseRem hφ) l) j

/-- `Mₗⱼ(0) = ∂ⱼ∂ₗ g(0) = 0`: the remainder has no quadratic part. -/
theorem phaseM_zero (hφ : ContDiff ℝ ∞ φ) (l j : Fin n) : phaseM φ l j 0 = 0 := by
  have hG : coordDeriv (phaseRem φ) l = fun y => coordDeriv φ l y - linCLM (hessMat φ 0 l) y :=
    funext (coordDeriv_phaseRem hφ l)
  have h1 : DifferentiableAt ℝ (fun y => coordDeriv φ l y) 0 :=
    ((contDiff_coordDeriv hφ l).differentiable (by simp)) 0
  rw [phaseM, hadamardCoeff_zero, hG, ← coordDeriv,
    coordDeriv_sub h1 (linCLM _).differentiableAt, coordDeriv_clm, linCLM_single]
  exact sub_eq_zero.mpr rfl

/-- Hadamard's lemma for `∂ₗ g`, which vanishes at `0`: `∂ₗ g = ∑ⱼ xⱼ Mₗⱼ`. -/
theorem coordDeriv_phaseRem_eq_sum (hφ : ContDiff ℝ ∞ φ) (hφ1 : fderiv ℝ φ 0 = 0) (l : Fin n)
    (x : Fin n → ℝ) : coordDeriv (phaseRem φ) l x = ∑ j, (x j : ℂ) * phaseM φ l j x := by
  have h0 : coordDeriv (phaseRem φ) l 0 = 0 := by
    rw [coordDeriv_phaseRem hφ, coordDeriv, hφ1, map_zero]
    simp
  rw [hadamard (contDiff_coordDeriv (contDiff_phaseRem hφ) l) x, h0, zero_add]
  rfl

/-- The coefficients `Nᵢⱼ` are smooth. -/
theorem contDiff_phaseN (hφ : ContDiff ℝ ∞ φ) (i j : Fin n) : ContDiff ℝ ∞ (phaseN φ i j) := by
  unfold phaseN
  apply contDiff_intervalIntegral_param
  have h2 : ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × ℝ => p.2 • p.1) := contDiff_snd.smul contDiff_fst
  exact (ofRealCLM.contDiff.comp contDiff_snd).mul ((contDiff_phaseM hφ i j).comp h2)

/-- `Nᵢⱼ(0) = Mᵢⱼ(0)/2 = 0`. -/
theorem phaseN_zero (hφ : ContDiff ℝ ∞ φ) (i j : Fin n) : phaseN φ i j 0 = 0 := by
  simp [phaseN, phaseM_zero hφ]

/-- The Hadamard coefficients of `g` are `∑ⱼ xⱼ Nᵢⱼ`. -/
theorem hadamardCoeff_phaseRem (hφ : ContDiff ℝ ∞ φ) (hφ1 : fderiv ℝ φ 0 = 0) (i : Fin n)
    (x : Fin n → ℝ) : hadamardCoeff (phaseRem φ) i x = ∑ j, (x j : ℂ) * phaseN φ i j x := by
  have hc : ∀ j, Continuous (fun t : ℝ => (t : ℂ) * phaseM φ i j (t • x)) := fun j =>
    continuous_ofReal.mul ((contDiff_phaseM hφ i j).continuous.comp
      (continuous_id.smul continuous_const))
  have hpt : ∀ t : ℝ, fderiv ℝ (phaseRem φ) (t • x) (Pi.single i 1) =
      ∑ j, (x j : ℂ) * ((t : ℂ) * phaseM φ i j (t • x)) := by
    intro t
    rw [← coordDeriv, coordDeriv_phaseRem_eq_sum hφ hφ1]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ofReal_mul]
    ring
  unfold hadamardCoeff phaseN
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun j _ => ((hc j).const_mul _).intervalIntegrable 0 1]
  simp_rw [intervalIntegral.integral_const_mul]

/-- `g(0) = 0` when `φ(0) = 0`. -/
theorem phaseRem_zero (hφ0 : φ 0 = 0) : phaseRem φ 0 = 0 := by
  simp [phaseRem, hφ0, qform_zero]

/-- The remainder is cubic: `g(x) = ∑ᵢⱼₖ xᵢ xⱼ xₖ gᵢⱼₖ(x)` with smooth `gᵢⱼₖ`. -/
theorem phaseRem_eq_cubic (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ 0 = 0) (hφ1 : fderiv ℝ φ 0 = 0)
    (x : Fin n → ℝ) : phaseRem φ x =
      ∑ i, (x i : ℂ) * ∑ j, (x j : ℂ) * ∑ k, (x k : ℂ) * phaseCubic φ i j k x := by
  rw [hadamard (contDiff_phaseRem hφ) x, phaseRem_zero hφ0, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hadamardCoeff_phaseRem hφ hφ1]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [hadamard (contDiff_phaseN hφ i j) x, phaseN_zero hφ, zero_add]
  rfl

/-- The cubic coefficients `gᵢⱼₖ` are smooth. -/
theorem contDiff_phaseCubic (hφ : ContDiff ℝ ∞ φ) (i j k : Fin n) :
    ContDiff ℝ ∞ (phaseCubic φ i j k) :=
  contDiff_hadamardCoeff (contDiff_phaseN hφ i j) k

/-! ### The quadratic part has `Im ⟨A x, x⟩ ≥ 0` -/

/-- If `Im φ ≥ 0` near a critical point `0` with `φ(0) = 0`, then the Hessian `A` there has
`Im ⟨A x, x⟩ ≥ 0` for every `x`: `⟨A x, x⟩/2` is the limit of `φ(t x)/t²` as `t → 0⁺`. -/
theorem im_qform_hessMat_nonneg (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ 0 = 0) (hφ1 : fderiv ℝ φ 0 = 0)
    {r : ℝ} (hr : 0 < r) (hIm : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) r, 0 ≤ (φ x).im)
    (x : Fin n → ℝ) : 0 ≤ (qform (hessMat φ 0) x).im := by
  set S : ℝ → ℂ := fun t => ∑ i, (x i : ℂ) * ∑ j, (x j : ℂ) * ∑ k, (x k : ℂ) *
    phaseCubic φ i j k (t • x) with hS
  have hSc : Continuous S :=
    continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_finsetSum _ fun j _ => continuous_const.mul
        (continuous_finsetSum _ fun k _ => continuous_const.mul
          ((contDiff_phaseCubic hφ i j k).continuous.comp (continuous_id.smul continuous_const))))
  set h : ℝ → ℂ := fun t => qform (hessMat φ 0) x / 2 + (t : ℂ) * S t with hh
  have hhc : Continuous h := continuous_const.add (continuous_ofReal.mul hSc)
  have hφt : ∀ t : ℝ, φ (t • x) = (t : ℂ) ^ 2 * h t := by
    intro t
    have h1 : φ (t • x) = qform (hessMat φ 0) (t • x) / 2 + phaseRem φ (t • x) := by
      simp [phaseRem]
    have h2 : ∑ i, ((t • x) i : ℂ) * ∑ j, ((t • x) j : ℂ) * ∑ k, ((t • x) k : ℂ) *
        phaseCubic φ i j k (t • x) = (t : ℂ) ^ 3 * S t := by
      simp only [hS, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, ofReal_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h1, phaseRem_eq_cubic hφ hφ0 hφ1, h2, qform_smul]
    simp only [hh]
    ring
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ (h t).im := by
    have ht : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) := by
      exact Continuous.tendsto' (f := fun t : ℝ => t • x) (by fun_prop) 0 0 (by simp)
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t • x ∈ Metric.ball (0 : Fin n → ℝ) r :=
      ht (Metric.ball_mem_nhds 0 hr)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hev, self_mem_nhdsWithin]
      with t ht1 ht2
    have h3 := hIm _ ht1
    rw [hφt, ← ofReal_pow, im_ofReal_mul] at h3
    have ht2' : (0 : ℝ) < t := ht2
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
  have hlim : Tendsto (fun t => (h t).im) (𝓝[>] 0) (𝓝 (h 0).im) :=
    ((continuous_im.comp hhc).tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : 0 ≤ (h 0).im := ge_of_tendsto hlim hpos
  simp only [hh, ofReal_zero, zero_mul, add_zero, div_ofNat_im] at h0
  linarith

/-! ### The phase family `F s = ⟨A x, x⟩/2 + s g` -/

/-- The phase family `F s x = ⟨A x, x⟩/2 + s g(x)`, from the quadratic part (`s = 0`) to `φ`
(`s = 1`). -/
noncomputable def phaseFamily (φ : (Fin n → ℝ) → ℂ) (s : ℝ) (x : Fin n → ℝ) : ℂ :=
  qform (hessMat φ 0) x / 2 + (s : ℂ) * phaseRem φ x

/-- At `s = 1` the phase family is `φ`. -/
theorem phaseFamily_one (x : Fin n → ℝ) : phaseFamily φ 1 x = φ x := by
  simp [phaseFamily, phaseRem]

/-- At `s = 0` the phase family is the quadratic part `⟨A x, x⟩/2`. -/
theorem phaseFamily_zero (x : Fin n → ℝ) :
    phaseFamily φ 0 x = qform (hessMat φ 0) x / 2 := by
  simp [phaseFamily]

/-- Each phase of the family is smooth. -/
theorem contDiff_phaseFamily (hφ : ContDiff ℝ ∞ φ) (s : ℝ) : ContDiff ℝ ∞ (phaseFamily φ s) :=
  ((contDiff_qform _).div_const 2).add (contDiff_const.mul (contDiff_phaseRem hφ))

/-- For `s ∈ [0, 1]`, `Im F_s ≥ 0` on the ball where `Im φ ≥ 0`: `F_s` is a convex combination
of `⟨A x, x⟩/2` and `φ`. -/
theorem im_phaseFamily_nonneg (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ 0 = 0) (hφ1 : fderiv ℝ φ 0 = 0)
    {r : ℝ} (hr : 0 < r) (hIm : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) r, 0 ≤ (φ x).im)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {x : Fin n → ℝ} (hx : x ∈ Metric.ball (0 : Fin n → ℝ) r) :
    0 ≤ (phaseFamily φ s x).im := by
  have hF : phaseFamily φ s x =
      ((1 - s : ℝ) : ℂ) * (qform (hessMat φ 0) x / 2) + (s : ℂ) * φ x := by
    simp only [phaseFamily, phaseRem]; push_cast; ring
  have hQ := im_qform_hessMat_nonneg hφ hφ0 hφ1 hr hIm x
  have hQ2 : 0 ≤ (qform (hessMat φ 0) x / 2).im := by rw [div_ofNat_im]; positivity
  rw [hF, add_im, im_ofReal_mul, im_ofReal_mul]
  exact add_nonneg (mul_nonneg (by linarith [hs.2]) hQ2) (mul_nonneg hs.1 (hIm x hx))

/-! ### The gradient of the phase family, `∂ₗ F s = (B s x · x)ₗ` -/

/-- The matrix `B s x = A + s M(x)`, so that `∂ₗ (F s) x = (B s x · x)ₗ`. -/
noncomputable def phaseB (φ : (Fin n → ℝ) → ℂ) (s : ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  hessMat φ 0 + (s : ℂ) • Matrix.of (fun l j => phaseM φ l j x)

/-- `B s 0 = A`, since `M(0) = 0`. -/
theorem phaseB_zero (hφ : ContDiff ℝ ∞ φ) (s : ℝ) : phaseB φ s 0 = hessMat φ 0 := by
  ext l j
  simp [phaseB, phaseM_zero hφ]

/-- `∂ₗ F_s(x) = (B s x · x)ₗ`. -/
theorem coordDeriv_phaseFamily (hφ : ContDiff ℝ ∞ φ) (hφ1 : fderiv ℝ φ 0 = 0) (s : ℝ) (l : Fin n)
    (x : Fin n → ℝ) : coordDeriv (phaseFamily φ s) l x = (phaseB φ s x *ᵥ cvec x) l := by
  have h1 : DifferentiableAt ℝ (fun y => qform (hessMat φ 0) y / 2) x :=
    (((contDiff_qform _).div_const 2).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ (phaseRem φ) x := ((contDiff_phaseRem hφ).differentiable (by simp)) x
  have h3 : DifferentiableAt ℝ (fun y => (s : ℂ) * phaseRem φ y) x := h2.const_mul _
  rw [show phaseFamily φ s = fun y => qform (hessMat φ 0) y / 2 + (s : ℂ) * phaseRem φ y from rfl,
    coordDeriv_add h1 h3, coordDeriv_qform_half (hessMat_isSymm hφ 0),
    coordDeriv_const_mul h2, coordDeriv_phaseRem_eq_sum hφ hφ1, phaseB, add_mulVec, smul_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, of_apply, cvec]
  congr 1
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  ring

/-! ### The coefficients of the integration by parts -/

/-- A smooth function times a function smooth on an open neighbourhood of its support is
smooth. -/
theorem contDiff_mul_of_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h f : E → ℂ} {U : Set E} (hh : ContDiff ℝ ∞ h) (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (hsub : tsupport h ⊆ U) : ContDiff ℝ ∞ (fun p => h p * f p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ U
  · exact hh.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hp))
  · have h0 : h =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h' => hp (hsub h')
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with q hq
    simp [hq]

/-- The determinant of a matrix with smooth entries is smooth. -/
theorem contDiff_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : E → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, ContDiff ℝ ∞ (fun p => M p i j)) :
    ContDiff ℝ ∞ (fun p => (M p).det) := by
  simp_rw [det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)

/-- The entries of the adjugate of a matrix with smooth entries are smooth. -/
theorem contDiff_adjugate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : E → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, ContDiff ℝ ∞ (fun p => M p i j)) (i j : Fin n) :
    ContDiff ℝ ∞ (fun p => adjugate (M p) i j) := by
  simp_rw [adjugate_apply]
  refine contDiff_det fun k l => ?_
  by_cases hk : k = j
  · simp only [updateRow_apply, hk, ↓reduceIte]
    exact contDiff_const
  · simp only [updateRow_apply, hk, ↓reduceIte]
    exact hM k l

/-- Entries of the inverse matrix: `B⁻¹ⱼₗ = (det B)⁻¹ adj(B)ⱼₗ`. -/
theorem inv_apply_eq_det_inv_mul (B : Matrix (Fin n) (Fin n) ℂ) (j l : Fin n) :
    B⁻¹ j l = B.det⁻¹ * adjugate B j l := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]

/-- The entries of `B s x` are smooth in `(s, x)`. -/
theorem contDiff_phaseB_apply (hφ : ContDiff ℝ ∞ φ) (l j : Fin n) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => phaseB φ p.1 p.2 l j) := by
  simp only [phaseB, Matrix.add_apply, Matrix.smul_apply, of_apply, smul_eq_mul]
  exact contDiff_const.add ((ofRealCLM.contDiff.comp contDiff_fst).mul
    ((contDiff_phaseM hφ l j).comp contDiff_snd))

/-- The cutoff in the homotopy parameter: `1` on `[0, 1]`, supported in `[-1/2, 3/2]`. -/
noncomputable def sBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The cutoff `sBump` is `1` on `[0, 1]`. -/
theorem sBump_eq_one {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : sBump s = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [show sBump.rIn = 1 / 2 from rfl, Real.closedBall_eq_Icc]
  constructor <;> linarith [hs.1, hs.2]

/-- The coefficients of the integration by parts. Near the nondegenerate critical point `0`
there are smooth `cⱼₗ(s, x)` with `∑ₗ cⱼₗ ∂ₗ F_s = xⱼ` for `s ∈ [0, 1]` and `|x| ≤ δ`: they
are the entries of `(B s x)⁻¹`, which exists near `x = 0` since `B s 0 = A` is invertible
(Hörmander, ALPDO I, proof of Theorem 7.7.5). -/
theorem exists_phase_coeff (hφ : ContDiff ℝ ∞ φ) (hφ1 : fderiv ℝ φ 0 = 0)
    (hdet : (hessMat φ 0).det ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ, 0 < δ ∧ δ < r ∧ ∃ c : Fin n → Fin n → ℝ → (Fin n → ℝ) → ℂ,
      (∀ j l, ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => c j l p.1 p.2)) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) δ, ∀ j,
        ∑ l, c j l s x * coordDeriv (phaseFamily φ s) l x = x j := by
  have hdetc : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => (phaseB φ p.1 p.2).det) :=
    contDiff_det (contDiff_phaseB_apply hφ)
  have hev : ∀ᶠ x in 𝓝 (0 : Fin n → ℝ), ∀ s ∈ Metric.closedBall (1 / 2 : ℝ) 1,
      (phaseB φ s x).det ≠ 0 := by
    refine (isCompact_closedBall (1 / 2 : ℝ) 1).eventually_forall_of_forall_eventually
      fun s _ => ?_
    have hc : ContinuousAt (fun z : (Fin n → ℝ) × ℝ => (phaseB φ z.2 z.1).det) (0, s) :=
      (hdetc.continuous.comp continuous_swap).continuousAt
    have h0 : (phaseB φ s 0).det ≠ 0 := by rw [phaseB_zero hφ]; exact hdet
    exact hc.eventually_ne h0
  obtain ⟨ε, hε, hεB⟩ := Metric.eventually_nhds_iff.mp hev
  set δ := min (ε / 3) (r / 2) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : 2 * δ < ε := by
    have := min_le_left (ε / 3) (r / 2); linarith
  have hδr : δ < r := by
    have := min_le_right (ε / 3) (r / 2); linarith
  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ, 2 * δ, hδ, by linarith⟩
  let U : Set (ℝ × (Fin n → ℝ)) := {p | (phaseB φ p.1 p.2).det ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun hdetc.continuous continuous_const
  let h : ℝ × (Fin n → ℝ) → ℂ := fun p => (sBump p.1 : ℂ) * (χ p.2 : ℂ)
  have hh : ContDiff ℝ ∞ h :=
    (ofRealCLM.contDiff.comp (sBump.contDiff.comp contDiff_fst)).mul
      (ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd))
  have hsupp : tsupport h ⊆ U := by
    have hsub : tsupport h ⊆
        Metric.closedBall (1 / 2 : ℝ) 1 ×ˢ Metric.closedBall (0 : Fin n → ℝ) (2 * δ) := by
      refine closure_minimal ?_ (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
      intro p hp
      have hp' : (sBump p.1 : ℂ) * (χ p.2 : ℂ) ≠ 0 := hp
      have h1 : sBump p.1 ≠ 0 := fun h0 => hp' (by simp [h0])
      have h2 : χ p.2 ≠ 0 := fun h0 => hp' (by simp [h0])
      refine ⟨?_, ?_⟩
      · have := subset_tsupport _ h1
        rw [ContDiffBump.tsupport_eq] at this
        exact this
      · have := subset_tsupport _ h2
        rw [ContDiffBump.tsupport_eq] at this
        exact this
    intro p hp
    obtain ⟨h1, h2⟩ := hsub hp
    exact hεB (lt_of_le_of_lt (Metric.mem_closedBall.mp h2) hδε) p.1 h1
  refine ⟨δ, hδ, hδr, fun j l s x => (sBump s : ℂ) * (χ x : ℂ) *
    ((phaseB φ s x).det⁻¹ * adjugate (phaseB φ s x) j l), fun j l => ?_, ?_⟩
  · have hf : ContDiffOn ℝ ∞ (fun p : ℝ × (Fin n → ℝ) =>
        (phaseB φ p.1 p.2).det⁻¹ * adjugate (phaseB φ p.1 p.2) j l) U :=
      (hdetc.contDiffOn.inv fun p hp => hp).mul
        (contDiff_adjugate (contDiff_phaseB_apply hφ) j l).contDiffOn
    exact contDiff_mul_of_tsupport hh hf hU hsupp
  · intro s hs x hx j
    have h1 : sBump s = 1 := sBump_eq_one hs
    have h2 : χ x = 1 := χ.one_of_mem_closedBall hx
    have hs' : s ∈ Metric.closedBall (1 / 2 : ℝ) 1 := by
      rw [Real.closedBall_eq_Icc]; constructor <;> linarith [hs.1, hs.2]
    have hB : (phaseB φ s x).det ≠ 0 :=
      hεB (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)) s hs'
    have hv : ((phaseB φ s x)⁻¹ *ᵥ (phaseB φ s x *ᵥ cvec x)) j = (x j : ℂ) := by
      rw [mulVec_mulVec, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB), one_mulVec]; rfl
    rw [← hv]
    simp only [h1, h2, ofReal_one, one_mul, coordDeriv_phaseFamily hφ hφ1,
      ← inv_apply_eq_det_inv_mul]
    rfl

/-- The estimate behind Hörmander's (7.7.12): near the critical point, an amplitude family
vanishing to order `p` at `0` gives `|∫ v e^{iτF_s}| ≤ C τ^{-⌊p/2⌋}` for `τ ≥ 1`, uniformly in
`s ∈ [0, 1]` (Hörmander, ALPDO I, proof of Theorem 7.7.5). -/
theorem exists_bound_phaseFamily (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ 0 = 0)
    (hφ1 : fderiv ℝ φ 0 = 0) (hdet : (hessMat φ 0).det ≠ 0) {r : ℝ} (hr : 0 < r)
    (hIm : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) r, 0 ≤ (φ x).im) :
    ∃ δ, 0 < δ ∧ δ < r ∧ ∀ (p : ℕ) {v : ℝ → (Fin n → ℝ) → ℂ},
      Vanish (Metric.closedBall (0 : Fin n → ℝ) δ) p v →
        ∃ C, ∀ s ∈ Icc (0 : ℝ) 1, ∀ τ : ℝ, 1 ≤ τ →
          ‖∫ x, v s x * cexp (I * τ * phaseFamily φ s x)‖ ≤ C * (τ ^ (p / 2))⁻¹ := by
  obtain ⟨δ, hδ, hδr, c, hc, hid⟩ := exists_phase_coeff hφ hφ1 hdet hr
  refine ⟨δ, hδ, hδr, ?_⟩
  exact exists_bound_vanish (isCompact_closedBall 0 δ) (contDiff_phaseFamily hφ)
    (fun s hs x hx => im_phaseFamily_nonneg hφ hφ0 hφ1 hr hIm hs
      (Metric.closedBall_subset_ball hδr hx)) hc hid

/-! ### Taylor's formula for `exp` with integral remainder -/

/-- The derivative of `s ↦ e^{z₀ + s z}`. -/
theorem hasDerivAt_cexp_affine (z₀ z : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => cexp (z₀ + s * z)) (cexp (z₀ + s * z) * z) s := by
  have h1 : HasDerivAt (fun w : ℂ => cexp (z₀ + w * z)) (cexp (z₀ + s * z) * z) (s : ℂ) := by
    simpa using (((hasDerivAt_id (s : ℂ)).mul_const z).const_add z₀).cexp
  exact h1.comp_ofReal

/-- Taylor's formula for `exp` with integral remainder:
`e^(z₀ + z) = e^z₀ ∑_{j ≤ T} z^j/j! + z^(T+1)/T! ∫₀¹ (1 - s)^T e^(z₀ + s z) ds`. -/
theorem cexp_taylor (z₀ z : ℂ) (T : ℕ) :
    cexp (z₀ + z) = cexp z₀ * ∑ j ∈ range (T + 1), z ^ j / (j.factorial : ℂ) +
      z ^ (T + 1) / (T.factorial : ℂ) *
        ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ T * cexp (z₀ + s * z) := by
  induction T with
  | zero =>
    have hc : Continuous (fun s : ℝ => cexp (z₀ + s * z) * z) := by fun_prop
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_cexp_affine z₀ z s) (hc.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_mul_const] at h
    simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero] at h
    simp only [zero_add, range_one, sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, mul_one, pow_one, one_mul]
    linear_combination (-1 : ℂ) * h
  | succ T ih =>
    have hP : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) ^ (T + 1))
        (-((T + 1 : ℂ) * (1 - (s : ℂ)) ^ T)) s := by
      intro s
      have h1 : HasDerivAt (fun w : ℂ => (1 - w) ^ (T + 1))
          (-((T + 1 : ℂ) * (1 - (s : ℂ)) ^ T)) (s : ℂ) := by
        have := ((hasDerivAt_id (s : ℂ)).const_sub 1).pow (T + 1)
        simp only [id, Nat.add_sub_cancel] at this
        convert this using 1
        push_cast
        ring
      exact h1.comp_ofReal
    have hA : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) ^ (T + 1) * cexp (z₀ + s * z))
          ((-(T + 1 : ℂ)) * ((1 - (s : ℂ)) ^ T * cexp (z₀ + s * z)) +
            ((1 - (s : ℂ)) ^ (T + 1) * cexp (z₀ + s * z)) * z) s := by
      intro s _
      convert (hP s).mul (hasDerivAt_cexp_affine z₀ z s) using 1
      ring
    have hc1 : Continuous (fun s : ℝ => (1 - (s : ℂ)) ^ T * cexp (z₀ + s * z)) := by fun_prop
    have hc2 : Continuous (fun s : ℝ => (1 - (s : ℂ)) ^ (T + 1) * cexp (z₀ + s * z)) := by
      fun_prop
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hA
      (((hc1.const_mul _).add (hc2.mul_const _)).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable 0 1)
      ((hc2.mul_const _).intervalIntegrable 0 1), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const] at h
    simp only [ofReal_one, sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, zero_mul, ofReal_zero, sub_zero, one_pow, one_mul,
      add_zero] at h
    set IT := ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ T * cexp (z₀ + s * z) with hIT
    set IT1 := ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ (T + 1) * cexp (z₀ + s * z) with hIT1
    have hT : ((T : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero T
    have hF : (T.factorial : ℂ) ≠ 0 := by exact_mod_cast T.factorial_ne_zero
    have hI : IT = (cexp z₀ + z * IT1) / (T + 1) := by
      field_simp
      linear_combination (-1 : ℂ) * h
    rw [ih, sum_range_succ _ (T + 1), Nat.factorial_succ, hI]
    push_cast
    field_simp
    ring

/-! ### Assembly: local stationary phase -/

/-- `gʲ u` vanishes to order `3 j` at `0`, since `g` is cubic. -/
theorem vanish_phaseRem_pow (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ 0 = 0) (hφ1 : fderiv ℝ φ 0 = 0)
    {K : Set (Fin n → ℝ)} {u : (Fin n → ℝ) → ℂ} (hu : ContDiff ℝ ∞ u)
    (huK : ∀ x ∉ K, u x = 0) (j : ℕ) :
    Vanish K (3 * j) (fun _ x => phaseRem φ x ^ j * u x) := by
  induction j with
  | zero =>
    simp only [mul_zero, pow_zero, one_mul]
    exact vanish_zero_iff.mpr ⟨hu.comp contDiff_snd, fun _ x hx => huK x hx⟩
  | succ j ih =>
    have h := vanish_mul_cubic (fun i j k => contDiff_phaseCubic hφ i j k)
      (phaseRem_eq_cubic hφ hφ0 hφ1) ih
    rw [show 3 * (j + 1) = 3 * j + 3 by ring]
    exact vanish_congr (fun s x => by ring) h

/-- The pointwise expansion behind the proof: Taylor's formula for `e^{iτ g}` around the quadratic
phase, `u e^{iτφ} = ∑_{j ≤ T} (iτ)ʲ/j! gʲ u e^{iτ⟨A x, x⟩/2} + (iτ)^{T+1}/T! g^{T+1} u ∫₀¹ (1-s)^T
e^{iτF_s} ds`. -/
theorem expansion (τ : ℝ) (T : ℕ) (u : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    u x * cexp (I * τ * φ x) =
      ∑ j ∈ range (T + 1), (I * τ) ^ j / (j.factorial : ℂ) *
        (phaseRem φ x ^ j * u x * cexp (I * τ * (qform (hessMat φ 0) x / 2))) +
      (I * τ) ^ (T + 1) / (T.factorial : ℂ) *
        (phaseRem φ x ^ (T + 1) * u x *
          ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ T * cexp (I * τ * phaseFamily φ s x)) := by
  have hφx : I * τ * φ x = I * τ * (qform (hessMat φ 0) x / 2) + I * τ * phaseRem φ x := by
    simp only [phaseRem]; ring
  have hF : ∀ s : ℝ, I * τ * (qform (hessMat φ 0) x / 2) + s * (I * τ * phaseRem φ x) =
      I * τ * phaseFamily φ s x := fun s => by simp only [phaseFamily]; ring
  rw [hφx, cexp_taylor _ _ T, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp_rw [hF]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]
    ring
  · rw [mul_pow]
    ring

/-- **Local stationary phase** at a nondegenerate critical point (Hörmander, *The Analysis of
Linear Partial Differential Operators I*, Theorem 7.7.5, leading term, near one critical point).
Let `φ` be smooth with `φ(0) = 0`, `dφ(0) = 0`, `Im φ ≥ 0` on `ball 0 r` and `det A ≠ 0` for the
Hessian `A = φ''(0)`. Then for some `0 < δ < r` and every smooth `u` supported in `closedBall 0 δ`,
`∫ u e^{iτφ} = (2π/τ)^{n/2} invSqrtDet(-iA) u(0) + O(τ^{-n/2-1})` as `τ → ∞`, where
`invSqrtDet(-iA)` is Hörmander's `(det(φ''(0)/i))^{-1/2}`. -/
theorem stationary_phase_local (hφ : ContDiff ℝ ∞ φ) (hφ0 : φ 0 = 0) (hφ1 : fderiv ℝ φ 0 = 0)
    {r : ℝ} (hr : 0 < r) (hIm : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) r, 0 ≤ (φ x).im)
    (hdet : (hessMat φ 0).det ≠ 0) :
    ∃ δ, 0 < δ ∧ δ < r ∧ ∀ u : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ u →
      tsupport u ⊆ Metric.closedBall 0 δ →
      (fun τ : ℝ => (∫ x, u x * cexp (I * τ * φ x)) -
        ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • hessMat φ 0) * u 0) =O[atTop]
        fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
  obtain ⟨δ, hδ, hδr, hB⟩ := exists_bound_phaseFamily hφ hφ0 hφ1 hdet hr hIm
  refine ⟨δ, hδ, hδr, fun u hu hsupp => ?_⟩
  have hK : IsCompact (Metric.closedBall (0 : Fin n → ℝ) δ) := isCompact_closedBall 0 δ
  have hA : (hessMat φ 0).IsSymm := hessMat_isSymm hφ 0
  have hQIm : ∀ x, 0 ≤ (qform (hessMat φ 0) x).im := im_qform_hessMat_nonneg hφ hφ0 hφ1 hr hIm
  have hus : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hsupp
  have huK : ∀ x ∉ Metric.closedBall (0 : Fin n → ℝ) δ, u x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h)
  have hv := vanish_phaseRem_pow hφ hφ0 hφ1 hu huK
  set T := 2 * n + 1 with hT
  have hg : Continuous (phaseRem φ) := (contDiff_phaseRem hφ).continuous
  have hQc : Continuous (fun x => qform (hessMat φ 0) x / 2) :=
    ((contDiff_qform _).div_const 2).continuous
  have hFc : Continuous (fun p : (Fin n → ℝ) × ℝ => phaseFamily φ p.2 p.1) :=
    (hQc.comp continuous_fst).add ((continuous_ofReal.comp continuous_snd).mul
      (hg.comp continuous_fst))
  have hint_j : ∀ (τ : ℝ) (j : ℕ), Integrable (fun x => phaseRem φ x ^ j * u x *
      cexp (I * τ * (qform (hessMat φ 0) x / 2))) := by
    intro τ j
    refine Continuous.integrable_of_hasCompactSupport
      (((hg.pow j).mul hu.continuous).mul ((continuous_const.mul hQc).cexp)) ?_
    exact HasCompactSupport.intro hK fun x hx => by simp [huK x hx]
  have hRc : ∀ τ : ℝ, Continuous (fun x => ∫ s in (0 : ℝ)..1,
      (1 - (s : ℂ)) ^ T * cexp (I * τ * phaseFamily φ s x)) := fun τ =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (((continuous_const.sub (continuous_ofReal.comp continuous_snd)).pow T).mul
        ((continuous_const.mul hFc).cexp)) 0 1
  have hint_R : ∀ τ : ℝ, Integrable (fun x => phaseRem φ x ^ (T + 1) * u x *
      ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ T * cexp (I * τ * phaseFamily φ s x)) := by
    intro τ
    refine Continuous.integrable_of_hasCompactSupport
      (((hg.pow _).mul hu.continuous).mul (hRc τ)) ?_
    exact HasCompactSupport.intro hK fun x hx => by simp [huK x hx]
  set Q2 : ℝ → ℂ := fun τ => ∫ x, u x * cexp (I * τ * qform (hessMat φ 0) x / 2) with hQ2
  set J : ℕ → ℝ → ℂ := fun m τ => ∫ x, phaseRem φ x ^ m * u x *
    cexp (I * τ * (qform (hessMat φ 0) x / 2)) with hJ
  set R : ℝ → ℂ := fun τ => ∫ x, phaseRem φ x ^ (T + 1) * u x *
    ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ T * cexp (I * τ * phaseFamily φ s x) with hR
  have hdecomp : ∀ τ : ℝ, (∫ x, u x * cexp (I * τ * φ x)) -
      ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • hessMat φ 0) * u 0 =
      (Q2 τ - ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • hessMat φ 0) * u 0) +
        ∑ j ∈ range T, (I * τ) ^ (j + 1) / ((j + 1).factorial : ℂ) * J (j + 1) τ +
        (I * τ) ^ (T + 1) / (T.factorial : ℂ) * R τ := by
    intro τ
    have h1 : (∫ x, u x * cexp (I * τ * φ x)) =
        ∑ j ∈ range (T + 1), (I * τ) ^ j / (j.factorial : ℂ) * J j τ +
          (I * τ) ^ (T + 1) / (T.factorial : ℂ) * R τ := by
      simp_rw [expansion τ T u]
      rw [integral_add, integral_finsetSum]
      · simp_rw [integral_const_mul]
        rfl
      · exact fun j _ => (hint_j τ j).const_mul _
      · exact integrable_finsetSum _ fun j _ => (hint_j τ j).const_mul _
      · exact (hint_R τ).const_mul _
    have h0 : J 0 τ = Q2 τ := by
      simp only [hJ, hQ2, pow_zero, one_mul, mul_div_assoc]
    rw [h1, sum_range_succ', h0]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    ring
  rw [show (fun τ : ℝ => (∫ x, u x * cexp (I * τ * φ x)) -
      ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • hessMat φ 0) * u 0) = _
    from funext hdecomp]
  have h₁ : (fun τ : ℝ => Q2 τ - ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) *
      invSqrtDet (-I • hessMat φ 0) * u 0) =O[atTop] fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
    obtain ⟨C, τ₀, hτ₀, hC⟩ := quadratic_phase hA hQIm hdet hu hus
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop τ₀] with τ hτ
    have hτp : 0 < τ := lt_of_lt_of_le hτ₀ hτ
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hτp.le _)]
    exact hC τ hτ
  have h₂ : (fun τ : ℝ => ∑ j ∈ range T, (I * τ) ^ (j + 1) / ((j + 1).factorial : ℂ) *
      J (j + 1) τ) =O[atTop] fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
    refine Asymptotics.IsBigO.fun_sum fun j _ => ?_
    have hvj : Vanish (Metric.closedBall (0 : Fin n → ℝ) δ) (2 * (j + 1) + 1)
        (fun _ x => phaseRem φ x ^ (j + 1) * u x) := vanish_of_le (by omega) (hv (j + 1))
    obtain ⟨C, hC⟩ := exists_bound_quad hA hQIm hdet hK (j + 1) hvj 0
    refine Asymptotics.IsBigO.of_bound (C / ((j + 1).factorial : ℝ)) ?_
    filter_upwards [hC, eventually_ge_atTop 1] with τ hτ h1
    have hτp : 0 < τ := by linarith
    have hJb : ‖J (j + 1) τ‖ ≤ C * τ ^ (-((n : ℝ) / 2) - 1 - ((j + 1 : ℕ) : ℝ)) := hτ
    have hpow : τ ^ (j + 1) * τ ^ (-((n : ℝ) / 2) - 1 - ((j + 1 : ℕ) : ℝ)) =
        τ ^ (-((n : ℝ) / 2) - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hτp]
      congr 1
      ring
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hτp.le _)]
    simp only [norm_mul, norm_div, norm_pow, norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hτp.le, Complex.norm_natCast]
    calc τ ^ (j + 1) / ((j + 1).factorial : ℝ) * ‖J (j + 1) τ‖
        ≤ τ ^ (j + 1) / ((j + 1).factorial : ℝ) *
          (C * τ ^ (-((n : ℝ) / 2) - 1 - ((j + 1 : ℕ) : ℝ))) := by gcongr
      _ = C / ((j + 1).factorial : ℝ) * τ ^ (-((n : ℝ) / 2) - 1) := by rw [← hpow]; ring
  have hR_fubini : ∀ τ : ℝ, R τ = ∫ s in (0 : ℝ)..1, (1 - (s : ℂ)) ^ T *
      ∫ x, phaseRem φ x ^ (T + 1) * u x * cexp (I * τ * phaseFamily φ s x) := by
    intro τ
    set G : (Fin n → ℝ) → ℝ → ℂ := fun x s => (sBump s : ℂ) * ((1 - (s : ℂ)) ^ T *
      (phaseRem φ x ^ (T + 1) * u x * cexp (I * τ * phaseFamily φ s x))) with hG
    have hGc : Continuous (Function.uncurry G) :=
      (continuous_ofReal.comp (sBump.continuous.comp continuous_snd)).mul
        (((continuous_const.sub (continuous_ofReal.comp continuous_snd)).pow T).mul
          ((((hg.comp continuous_fst).pow _).mul (hu.continuous.comp continuous_fst)).mul
            ((continuous_const.mul hFc).cexp)))
    have hGs : HasCompactSupport (Function.uncurry G) := by
      refine HasCompactSupport.intro (hK.prod (isCompact_closedBall (1 / 2 : ℝ) 1))
        fun p hp => ?_
      show G p.1 p.2 = 0
      by_cases h1 : p.1 ∈ Metric.closedBall (0 : Fin n → ℝ) δ
      · have h2 : p.2 ∉ Metric.closedBall (1 / 2 : ℝ) 1 := fun h2 => hp ⟨h1, h2⟩
        have h3 : sBump p.2 = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          rw [ContDiffBump.tsupport_eq]
          exact h2
        simp [hG, h3]
      · simp [hG, huK _ h1]
    have hsw := integral_integral_swap_of_hasCompactSupport hGc hGs (μ := volume)
      (ν := volume.restrict (Ioc (0 : ℝ) 1))
    have hL : R τ = ∫ x, ∫ s in Ioc (0 : ℝ) 1, G x s := by
      simp only [hR]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      simp only [hG, sBump_eq_one (Ioc_subset_Icc_self hs), ofReal_one, one_mul]
      ring
    rw [hL, hsw, intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    simp only [hG, sBump_eq_one (Ioc_subset_Icc_self hs), ofReal_one, one_mul]
    rw [integral_const_mul]
  have h₃ : (fun τ : ℝ => (I * τ) ^ (T + 1) / (T.factorial : ℂ) * R τ) =O[atTop]
      fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
    obtain ⟨C, hC⟩ := hB (3 * (T + 1)) (hv (T + 1))
    have hp : 3 * (T + 1) / 2 = 3 * n + 3 := by omega
    have hRb : ∀ τ : ℝ, 1 ≤ τ → ‖R τ‖ ≤ max C 0 * (τ ^ (3 * n + 3))⁻¹ := by
      intro τ hτ
      rw [hR_fubini τ]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := max C 0 * (τ ^ (3 * n + 3))⁻¹) (f := fun s : ℝ => (1 - (s : ℂ)) ^ T *
          ∫ x, phaseRem φ x ^ (T + 1) * u x * cexp (I * τ * phaseFamily φ s x)) ?_
      · rw [sub_zero, abs_one, mul_one] at hb
        exact hb
      intro s hs
      rw [uIoc_of_le zero_le_one] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
      have h1 : ‖(1 - (s : ℂ)) ^ T‖ ≤ 1 := by
        rw [norm_pow]
        apply pow_le_one₀ (norm_nonneg _)
        rw [← ofReal_one, ← ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [hs'.2])]
        linarith [hs'.1]
      have h2 := hC s hs' τ hτ
      rw [hp] at h2
      have hτ0 : 0 ≤ (τ ^ (3 * n + 3))⁻¹ := by positivity
      rw [norm_mul]
      calc ‖(1 - (s : ℂ)) ^ T‖ *
            ‖∫ x, phaseRem φ x ^ (T + 1) * u x * cexp (I * τ * phaseFamily φ s x)‖
          ≤ 1 * (max C 0 * (τ ^ (3 * n + 3))⁻¹) := by
            gcongr
            exact h2.trans (by gcongr; exact le_max_left _ _)
        _ = max C 0 * (τ ^ (3 * n + 3))⁻¹ := one_mul _
    refine Asymptotics.IsBigO.of_bound (max C 0 / (T.factorial : ℝ)) ?_
    filter_upwards [eventually_ge_atTop 1] with τ hτ
    have hτp : 0 < τ := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hτp.le _)]
    simp only [norm_mul, norm_div, norm_pow, norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hτp.le, Complex.norm_natCast]
    have hpow : τ ^ (T + 1) * (τ ^ (3 * n + 3))⁻¹ ≤ τ ^ (-((n : ℝ) / 2) - 1) := by
      rw [show T + 1 = 2 * n + 2 by omega, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_neg hτp.le, ← Real.rpow_add hτp]
      apply Real.rpow_le_rpow_of_exponent_le hτ
      push_cast
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hC0 : 0 ≤ max C 0 / (T.factorial : ℝ) := by positivity
    calc τ ^ (T + 1) / (T.factorial : ℝ) * ‖R τ‖
        ≤ τ ^ (T + 1) / (T.factorial : ℝ) * (max C 0 * (τ ^ (3 * n + 3))⁻¹) := by
          gcongr
          exact hRb τ hτ
      _ = max C 0 / (T.factorial : ℝ) * (τ ^ (T + 1) * (τ ^ (3 * n + 3))⁻¹) := by ring
      _ ≤ max C 0 / (T.factorial : ℝ) * τ ^ (-((n : ℝ) / 2) - 1) := by gcongr
  exact (h₁.add h₂).add h₃

end Phase

end Lightlike.Oscillatory
