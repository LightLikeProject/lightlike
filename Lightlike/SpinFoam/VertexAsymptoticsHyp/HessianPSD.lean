import Lightlike.Oscillatory.StationaryPhase
import Lightlike.SpinFoam.VertexAsymptoticsHyp.HessianKernel

/-!
# The real part of the Hessian at a maximum of `Re S` (route 1 of task T-SF10-P2)

If `S` is smooth on an open set `U`, `Re S ≤ 0` near `x₀ ∈ U` and `Re S x₀ = 0`, `dS x₀ = 0`, then
`Re ⟨H(x₀) v, v⟩ ≤ 0` for every real `v` (`H = hessMat S x₀`), i.e. `Re(-H)` is positive
semidefinite. The proof localises `S` with a bump function and applies `im_qform_hessMat_nonneg`
to the phase `-i (S(x₀ + ·) - S x₀)`.
-/

open Filter Lightlike.Oscillatory Matrix
open scoped Topology ContDiff

namespace Lightlike.Asymptotics.Lorentzian

variable {n : ℕ}

/-- The Hessian matrix only depends on the germ of the function. -/
theorem hessMat_congr {f g : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ} (h : f =ᶠ[𝓝 x] g) :
    hessMat f x = hessMat g x := by
  ext i j
  have h1 : (fun y => coordDeriv f i y) =ᶠ[𝓝 x] fun y => coordDeriv g i y := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [coordDeriv, hy]
  show fderiv ℝ (fun y => coordDeriv f i y) x (Pi.single j 1) =
    fderiv ℝ (fun y => coordDeriv g i y) x (Pi.single j 1)
  rw [h1.fderiv_eq]

/-- The Hessian of a constant multiple of a function smooth on an open set. -/
theorem hessMat_const_mul_open {f : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {x : Fin n → ℝ} (hx : x ∈ U) (c : ℂ) :
    hessMat (fun y => c * f y) x = c • hessMat f x := by
  ext i j
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ f y := fun y hy =>
    (hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have h1 : (fun y => coordDeriv (fun y => c * f y) i y) =ᶠ[𝓝 x] fun y => c * coordDeriv f i y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact coordDeriv_const_mul (hdiff y hy) c i
  have h2 : DifferentiableAt ℝ (fun y => coordDeriv f i y) x := by
    have hc : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y) x :=
      (hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp)
    have : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y (Pi.single i 1)) x :=
      hc.clm_apply contDiffAt_const
    exact this.differentiableAt (by simp)
  show fderiv ℝ (fun y => coordDeriv (fun y => c * f y) i y) x (Pi.single j 1) =
    c * fderiv ℝ (fun y => coordDeriv f i y) x (Pi.single j 1)
  rw [h1.fderiv_eq]
  exact coordDeriv_const_mul h2 c j

/-- **`Re(-H)` is positive semidefinite at a point where `Re S` attains its maximum `0`.** For `S`
smooth on an open `U ∋ x₀` with `Re S ≤ 0` near `x₀`, `Re S x₀ = 0` and `dS x₀ = 0`, the quadratic
form of the Hessian has nonpositive real part. -/
theorem re_qform_hessMat_nonpos {S : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ S U) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ U) (hre : (S x₀).re = 0)
    (hd : fderiv ℝ S x₀ = 0) (hle : ∀ᶠ y in 𝓝 x₀, (S y).re ≤ 0) (v : Fin n → ℝ) :
    (qform (hessMat S x₀) v).re ≤ 0 := by
  obtain ⟨ε, hε, hεB⟩ := Metric.eventually_nhds_iff.mp hle
  obtain ⟨ε₂, hε₂, hε₂B⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  set δ := min ε ε₂ / 3 with hδdef
  have hm : 0 < min ε ε₂ := lt_min hε hε₂
  have hδ : 0 < δ := by positivity
  have hδ1 : 3 * δ = min ε ε₂ := by rw [hδdef]; ring
  have hδε : 2 * δ < ε := by have := min_le_left ε ε₂; linarith
  have hδε₂ : 2 * δ < ε₂ := by have := min_le_right ε ε₂; linarith
  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ, 2 * δ, hδ, by linarith⟩
  set Ψ : (Fin n → ℝ) → ℂ := fun y => -Complex.I * recentre S x₀ y with hΨ
  set U' : Set (Fin n → ℝ) := {y | x₀ + y ∈ U} with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hrec : ContDiffOn ℝ ∞ (recentre S x₀) U' := by
    have h1 : ContDiffOn ℝ ∞ (fun y => S (x₀ + y)) U' :=
      hS.comp (contDiff_const.add contDiff_id).contDiffOn (fun y hy => hy)
    exact h1.sub contDiffOn_const
  have hΨc : ContDiffOn ℝ ∞ Ψ U' := contDiffOn_const.mul hrec
  have hsub : tsupport (fun y => (χ y : ℂ)) ⊆ U' := by
    have h1 : tsupport (fun y => (χ y : ℂ)) ⊆ tsupport χ := by
      refine closure_mono fun y hy => ?_
      intro h0
      exact hy (by simp [h0])
    refine h1.trans ?_
    rw [ContDiffBump.tsupport_eq]
    intro y hy
    apply hε₂B
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    have := Metric.mem_closedBall.mp hy
    rw [dist_zero_right] at this
    simpa using lt_of_le_of_lt this hδε₂
  have hχ : ContDiff ℝ ∞ (fun y => (χ y : ℂ)) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hΦ : ContDiff ℝ ∞ (fun y => (χ y : ℂ) * Ψ y) := contDiff_mul_of_tsupport hχ hΨc hU'o hsub
  have hEq : (fun y => (χ y : ℂ) * Ψ y) =ᶠ[𝓝 0] Ψ := by
    filter_upwards [χ.eventuallyEq_one] with y hy
    simp [hy]
  have hΦ0 : (fun y => (χ y : ℂ) * Ψ y) 0 = 0 := by simp [hΨ, recentre]
  have hΨ0U : (0 : Fin n → ℝ) ∈ U' := by simpa [hU'] using hx₀
  have hrec0 : fderiv ℝ (recentre S x₀) 0 = 0 := by
    rw [fderiv_recentre]; simpa using hd
  have hΦ1 : fderiv ℝ (fun y => (χ y : ℂ) * Ψ y) 0 = 0 := by
    rw [hEq.fderiv_eq, hΨ]
    have hdr : DifferentiableAt ℝ (recentre S x₀) 0 :=
      ((hrec.contDiffAt (hU'o.mem_nhds hΨ0U)).differentiableAt (by simp))
    rw [fderiv_const_mul hdr, hrec0]
    ext w
    simp
  have hIm : ∀ y ∈ Metric.ball (0 : Fin n → ℝ) (2 * δ), 0 ≤ ((fun y => (χ y : ℂ) * Ψ y) y).im := by
    intro y hy
    have hy' : ‖y‖ < 2 * δ := by simpa using hy
    have hS1 : (S (x₀ + y)).re ≤ 0 := by
      apply hεB
      rw [dist_eq_norm, add_sub_cancel_left]
      exact lt_trans hy' hδε
    have : (Ψ y).im = -(S (x₀ + y)).re := by
      simp [hΨ, recentre, hre]
    simp only [Complex.im_ofReal_mul]
    rw [this]
    exact mul_nonneg χ.nonneg (by linarith)
  have key := im_qform_hessMat_nonneg hΦ hΦ0 hΦ1 (by positivity : 0 < 2 * δ) hIm v
  have hH : hessMat (fun y => (χ y : ℂ) * Ψ y) 0 = -Complex.I • hessMat S x₀ := by
    rw [hessMat_congr hEq, hΨ, hessMat_const_mul_open hU'o hrec hΨ0U, hessMat_recentre]
  rw [hH] at key
  have hq : qform (-Complex.I • hessMat S x₀) v = -Complex.I * qform (hessMat S x₀) v := by
    simp [qform, Finset.mul_sum, mul_assoc]
  rw [hq] at key
  simpa using key

/-- The Hessian of a function smooth on an open set is symmetric. -/
theorem hessMat_isSymm_of_contDiffOn {S : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ S U) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ U) : (hessMat S x₀).IsSymm := by
  obtain ⟨ε₂, hε₂, hε₂B⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  let χ : ContDiffBump x₀ := ⟨ε₂ / 3, ε₂ / 2, by positivity, by linarith⟩
  have hsub : tsupport (fun y => (χ y : ℂ)) ⊆ U := by
    have h1 : tsupport (fun y => (χ y : ℂ)) ⊆ tsupport χ := by
      refine closure_mono fun y hy => ?_
      intro h0
      exact hy (by simp [h0])
    refine h1.trans ?_
    rw [ContDiffBump.tsupport_eq]
    intro y hy
    apply hε₂B
    rw [Metric.mem_ball]
    have := Metric.mem_closedBall.mp hy
    exact lt_of_le_of_lt this (by show ε₂ / 2 < ε₂; linarith)
  have hχ : ContDiff ℝ ∞ (fun y => (χ y : ℂ)) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hΦ : ContDiff ℝ ∞ (fun y => (χ y : ℂ) * S y) := contDiff_mul_of_tsupport hχ hS hU hsub
  have hEq : (fun y => (χ y : ℂ) * S y) =ᶠ[𝓝 x₀] S := by
    filter_upwards [χ.eventuallyEq_one] with y hy
    simp [hy]
  rw [← hessMat_congr hEq]
  exact hessMat_isSymm hΦ x₀

/-- `Re ⟨A v, v⟩` is the quadratic form of the real part. -/
theorem re_qform_eq_dotProduct {A : Matrix (Fin n) (Fin n) ℂ} (v : Fin n → ℝ) :
    (qform A v).re = v ⬝ᵥ ((A.map Complex.re) *ᵥ v) := by
  simp only [qform, Complex.re_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- **Invertibility of `-H` from `Im(-H)` injective on `ker Re(-H)`** (route 1 of T-SF10-P2). If `S`
is smooth on an open `U ∋ x₀`, `Re S ≤ 0` near `x₀`, `Re S x₀ = 0`, `dS x₀ = 0`, and no nonzero real
vector lies in the kernels of both `Re(-H)` and `Im(-H)`, then `det(-H) ≠ 0`. -/
theorem det_neg_hessMat_ne_zero {S : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hS : ContDiffOn ℝ ∞ S U) {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ U) (hre : (S x₀).re = 0)
    (hd : fderiv ℝ S x₀ = 0) (hle : ∀ᶠ y in 𝓝 x₀, (S y).re ≤ 0)
    (hker : ∀ v : Fin n → ℝ, ((-hessMat S x₀).map Complex.re) *ᵥ v = 0 →
      ((-hessMat S x₀).map Complex.im) *ᵥ v = 0 → v = 0) :
    (-hessMat S x₀).det ≠ 0 := by
  refine det_ne_zero_of_re_psd_ker ?_ ?_ hker
  · have := hessMat_isSymm_of_contDiffOn hU hS hx₀
    rw [Matrix.transpose_neg]
    exact congrArg Neg.neg this
  · intro u
    rw [← re_qform_eq_dotProduct]
    have h := re_qform_hessMat_nonpos hU hS hx₀ hre hd hle u
    have : qform (-hessMat S x₀) u = -qform (hessMat S x₀) u := by
      simp [qform, Finset.sum_neg_distrib]
    rw [this, Complex.neg_re]
    linarith

end Lightlike.Asymptotics.Lorentzian
