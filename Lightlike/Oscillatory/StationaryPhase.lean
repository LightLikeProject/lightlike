module

public import Lightlike.Oscillatory.Flat
public import Lightlike.Oscillatory.Localisation

/-!
# Stationary phase

For a smooth phase `φ : ℝⁿ → ℂ` and a smooth, compactly supported amplitude `a`, the integral
`∫ a(x) e^{iτφ(x)} dx` is governed as `τ → ∞` by the critical points: the points of the support of
`a` with `Im φ = 0` and `dφ = 0`. At a nondegenerate one `x₀` with complex Hessian `H`, the
contribution is `e^{iτφ(x₀)} (2π/τ)^{n/2} det(−iH)^{−1/2} a(x₀)`, the square root taken on the
principal branch for each eigenvalue of `−iH` (`invSqrtDet`). Reference: Hörmander, *The Analysis
of Linear Partial Differential Operators I*, Theorem 7.7.5.

The hypothesis on the imaginary part is `Im φ ≥ 0` on the support of `a` only. Hörmander assumes
it on an open set containing the support; the two differ at a critical point on the boundary of
the support, where `Im φ` may be negative arbitrarily close by. Such a point contributes nothing
to the leading term: the amplitude is flat there, so it vanishes to every order in the sense of
`Vanish` (`vanish_of_flat`), and `exists_bound_vanish`, with the coefficients that
`exists_phase_coeff` gives for the phase itself, bounds its integral.

* `stationary_phase_local_boundary`: the bound `O(τ^{-n/2-1})` for an amplitude supported near a
  nondegenerate critical point that is not an interior point of its support, assuming
  `Im φ ≥ 0` only on that support.
* `stationary_phase_pi`: the theorem on `Fin n → ℝ`. The integral is localised to the critical
  points by `integral_localise`, with cutoffs inside the balls where `stationary_phase_local`
  (interior critical points) or `stationary_phase_local_boundary` (boundary critical points)
  holds for the recentred phase `φ(x₀ + y) − φ(x₀)` (`recentre`). The remainder is `O(τ^{-n-2})`.
* `stationary_phase`: the same on `EuclideanSpace ℝ (Fin n)`, with the Hessian `hess` taken along
  `EuclideanSpace.single`. It follows by the measure-preserving identification `WithLp.toLp 2`
  (`ofEuc`, `isBigO_euc_of_pi`).
* `stationary_phase_pi_of_isOpen`, `stationary_phase_of_isOpen`: the corollaries with Hörmander's
  hypothesis, `Im φ ≥ 0` on an open set containing the support.
-/

@[expose] public section

namespace Lightlike.Oscillatory

open MeasureTheory Complex Matrix Finset Set Filter Asymptotics
open scoped Real ContDiff Topology

variable {n : ℕ}

/-- The phase `φ` recentred at `x₀`: `y ↦ φ(x₀ + y) − φ(x₀)`. -/
noncomputable def recentre (φ : (Fin n → ℝ) → ℂ) (x₀ : Fin n → ℝ) : (Fin n → ℝ) → ℂ :=
  fun y => φ (x₀ + y) - φ x₀

/-- The recentred phase is smooth. -/
theorem contDiff_recentre {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ) (x₀ : Fin n → ℝ) :
    ContDiff ℝ ∞ (recentre φ x₀) :=
  (hφ.comp (contDiff_const.add contDiff_id)).sub contDiff_const

/-- The recentred phase vanishes at the origin. -/
theorem recentre_zero (φ : (Fin n → ℝ) → ℂ) (x₀ : Fin n → ℝ) : recentre φ x₀ 0 = 0 := by
  simp [recentre]

/-- The derivative of the recentred phase is the translated derivative. -/
theorem fderiv_recentre (φ : (Fin n → ℝ) → ℂ) (x₀ y : Fin n → ℝ) :
    fderiv ℝ (recentre φ x₀) y = fderiv ℝ φ (x₀ + y) := by
  show fderiv ℝ (fun y => φ (x₀ + y) - φ x₀) y = _
  rw [fderiv_sub_const, fderiv_comp_add_left]

/-- Partial derivatives of the recentred phase. -/
theorem coordDeriv_recentre (φ : (Fin n → ℝ) → ℂ) (x₀ : Fin n → ℝ) (i : Fin n)
    (y : Fin n → ℝ) : coordDeriv (recentre φ x₀) i y = coordDeriv φ i (x₀ + y) := by
  simp only [coordDeriv, fderiv_recentre]

/-- The Hessian of the recentred phase at the origin is the Hessian of `φ` at `x₀`. -/
theorem hessMat_recentre (φ : (Fin n → ℝ) → ℂ) (x₀ : Fin n → ℝ) :
    hessMat (recentre φ x₀) 0 = hessMat φ x₀ := by
  ext i j
  simp only [hessMat]
  rw [show (fun y => coordDeriv (recentre φ x₀) i y) = fun y => coordDeriv φ i (x₀ + y) from
    funext fun y => coordDeriv_recentre φ x₀ i y]
  simp only [coordDeriv]
  rw [fderiv_comp_add_left (f := fun y => fderiv ℝ φ y (Pi.single i 1)) x₀, add_zero]

/-- `(τ^k)⁻¹ ≤ τ^(-(n/2) - 1)` for `τ ≥ 1` and `k ≥ n/2 + 1`, here with `k = n + 2`. -/
theorem inv_pow_le_rpow {τ : ℝ} (hτ : 1 ≤ τ) :
    (τ ^ (n + 2))⁻¹ ≤ τ ^ (-((n : ℝ) / 2) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hτ ?_
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **Boundary critical points add no leading term.** Let `φ` be smooth with `dφ(0) = 0` and
`det φ''(0) ≠ 0`. There is `δ > 0` such that for every smooth `u` supported in the closed `δ`-ball,
with `0` not an interior point of its support and `Im φ ≥ 0` on its support,
`∫ u e^{iτφ} = O(τ^{-n/2-1})`. The amplitude is flat at `0`, so it lies in
`Vanish (tsupport u) (2n + 4)` (`vanish_of_flat`), and `exists_bound_vanish` for the constant
family `F s = φ` applies; that bound needs `Im φ ≥ 0` on the support only. -/
theorem stationary_phase_local_boundary {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : fderiv ℝ φ 0 = 0) (hdet : (hessMat φ 0).det ≠ 0) :
    ∃ δ, 0 < δ ∧ ∀ u : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ u →
      tsupport u ⊆ Metric.closedBall 0 δ → 0 ∉ interior (tsupport u) →
      (∀ x ∈ tsupport u, 0 ≤ (φ x).im) →
      (fun τ : ℝ => ∫ x, u x * cexp (I * τ * φ x)) =O[atTop]
        fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
  obtain ⟨δ, hδ, -, c, hc, hid⟩ := exists_phase_coeff hφ hφ1 hdet one_pos
  refine ⟨δ, hδ, fun u hu hsu h0 hIm => ?_⟩
  have hflat : ∀ k, iteratedFDeriv ℝ k u 0 = 0 := fun k =>
    iteratedFDeriv_eq_zero_of_mem_closure_compl hu
      (by rwa [closure_compl, mem_compl_iff]) k
  have hKc : IsCompact (tsupport u) :=
    (isCompact_closedBall 0 δ).of_isClosed_subset (isClosed_tsupport u) hsu
  have hv : Vanish (tsupport u) (2 * n + 4) (fun _ x => u x) :=
    vanish_of_flat _ hu hflat fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hF1 : phaseFamily φ 1 = φ := funext phaseFamily_one
  obtain ⟨C, hC⟩ := exists_bound_vanish hKc (F := fun _ => φ) (fun _ => hφ)
    (fun _ _ x hx => hIm x hx) (c := fun j l _ x => c j l 1 x)
    (fun j l => (hc j l).comp (contDiff_const (c := (1 : ℝ)) |>.prodMk contDiff_snd))
    (fun _ _ x hx j => by
      have := hid 1 ⟨zero_le_one, le_rfl⟩ x (hsu hx) j
      rwa [hF1] at this)
    (2 * n + 4) hv
  have hk : (2 * n + 4) / 2 = n + 2 := by omega
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩ 1 le_rfl)
    simpa using this
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with τ hτ
  have := hC 0 ⟨le_rfl, zero_le_one⟩ τ hτ
  rw [hk] at this
  refine this.trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
  exact mul_le_mul_of_nonneg_left (inv_pow_le_rpow hτ) hC0

/-- **Stationary phase** (`Fin n → ℝ` form). `φ` smooth with `Im φ ≥ 0` on the support of the
smooth, compactly supported amplitude `a`; the critical points in the support (`Im φ = 0`,
`dφ = 0`) form the finite set `K` and are nondegenerate (`det(−iH) ≠ 0`). Then
`∫ a e^{iτφ} = Σ_{x₀∈K} e^{iτφ(x₀)} (2π/τ)^{n/2} det(−iH(x₀))^{-1/2} a(x₀) + O(τ^{-n/2-1})`.
Critical points on the boundary of the support are allowed; `a` is flat there, so their terms
are `0`. Source: Hörmander, *ALPDO I*, Theorem 7.7.5 (leading term), with Theorem 7.7.1 away from
`K`. -/
theorem stationary_phase_pi {φ a : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (hIm : ∀ x ∈ tsupport a, 0 ≤ (φ x).im)
    (K : Finset (Fin n → ℝ))
    (hK : ∀ x ∈ tsupport a, ((φ x).im = 0 ∧ fderiv ℝ φ x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport a) (hnd : ∀ x ∈ K, (-I • hessMat φ x).det ≠ 0) :
    (fun τ : ℝ => (∫ x, a x * cexp (I * τ * φ x)) -
        ∑ x₀ ∈ K, cexp (I * τ * φ x₀) * ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-I • hessMat φ x₀) * a x₀)
      =O[atTop] fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
  have hcrit : ∀ x₀ ∈ K, (φ x₀).im = 0 ∧ fderiv ℝ φ x₀ = 0 := fun x₀ hx =>
    (hK x₀ (hKs x₀ hx)).2 hx
  have hloc : ∀ x₀ ∈ K, ∃ δ, 0 < δ ∧ ∀ u : (Fin n → ℝ) → ℂ, ContDiff ℝ ∞ u →
      tsupport u ⊆ Metric.closedBall 0 δ → (∀ y ∈ tsupport u, x₀ + y ∈ tsupport a) →
      (fun τ : ℝ => (∫ y, u y * cexp (I * τ * recentre φ x₀ y)) -
        ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • hessMat φ x₀) * u 0) =O[atTop]
        fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
    intro x₀ hx
    have hdet : (hessMat (recentre φ x₀) 0).det ≠ 0 := by
      rw [hessMat_recentre]
      intro h
      apply hnd x₀ hx
      rw [Matrix.det_smul, h, mul_zero]
    have hφ1 : fderiv ℝ (recentre φ x₀) 0 = 0 := by
      rw [fderiv_recentre, add_zero]
      exact (hcrit x₀ hx).2
    have hImr : ∀ y, x₀ + y ∈ tsupport a → 0 ≤ (recentre φ x₀ y).im := fun y hy => by
      simp only [recentre, sub_im, (hcrit x₀ hx).1, sub_zero]
      exact hIm _ hy
    by_cases hint : x₀ ∈ interior (tsupport a)
    · obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hint
      have hIm' : ∀ y ∈ Metric.ball (0 : Fin n → ℝ) r, 0 ≤ (recentre φ x₀ y).im :=
        fun y hy => hImr y (interior_subset (hrU (by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
          simpa using hy)))
      obtain ⟨δ, hδ, -, hδu⟩ := stationary_phase_local (contDiff_recentre hφ x₀)
        (recentre_zero φ x₀) hφ1 hr hIm' hdet
      exact ⟨δ, hδ, fun u hu hsu _ => by simpa only [hessMat_recentre] using hδu u hu hsu⟩
    · obtain ⟨δ, hδ, hδu⟩ := stationary_phase_local_boundary (contDiff_recentre hφ x₀) hφ1 hdet
      refine ⟨δ, hδ, fun u hu hsu hsa => ?_⟩
      have h0 : 0 ∉ interior (tsupport u) := fun h0 => hint (by
        have h1 := interior_mono
          (show tsupport u ⊆ (Homeomorph.addLeft x₀) ⁻¹' tsupport a from
            fun y hy => by simpa using hsa y hy) h0
        rw [← Homeomorph.preimage_interior] at h1
        simpa using h1)
      have hu0 : u 0 = 0 := apply_eq_zero_of_mem_closure_compl hu.continuous
        (by rwa [closure_compl, mem_compl_iff])
      refine (hδu u hu hsu h0 fun y hy => hImr y (hsa y hy)).congr_left fun τ => ?_
      rw [hu0, mul_zero, sub_zero]
  choose! δ hδ hδu using hloc
  obtain ⟨χ, hχs, hχt, hχ1, hrem⟩ := integral_localise hφ ha hc hIm K
    (fun x hx h1 h2 => (hK x hx).1 ⟨h1, h2⟩) hKs δ hδ
  obtain ⟨C, hC⟩ := hrem (n + 2)
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1 le_rfl)
    simpa using this
  have hR : (fun τ : ℝ => (∫ x, a x * cexp (I * τ * φ x)) -
      ∑ x₀ ∈ K, ∫ x, ((χ x₀ x : ℂ) * a x) * cexp (I * τ * φ x)) =O[atTop]
      fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with τ hτ
    refine (hC τ hτ).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
    exact mul_le_mul_of_nonneg_left (inv_pow_le_rpow hτ) hC0
  have hP : ∀ x₀ ∈ K, (fun τ : ℝ => (∫ x, ((χ x₀ x : ℂ) * a x) * cexp (I * τ * φ x)) -
      cexp (I * τ * φ x₀) * ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) *
        invSqrtDet (-I • hessMat φ x₀) * a x₀) =O[atTop]
      fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) := by
    intro x₀ hx
    set u : (Fin n → ℝ) → ℂ := fun y => (χ x₀ (x₀ + y) : ℂ) * a (x₀ + y) with hu_def
    have htr : ContDiff ℝ ∞ fun y : Fin n → ℝ => x₀ + y := contDiff_const.add contDiff_id
    have hu : ContDiff ℝ ∞ u :=
      (ofRealCLM.contDiff.comp ((hχs x₀ hx).comp htr)).mul (ha.comp htr)
    have hsu : tsupport u ⊆ Metric.closedBall 0 (δ x₀) := by
      refine closure_minimal ?_ Metric.isClosed_closedBall
      intro y hy
      have hy' : x₀ + y ∈ Function.support (χ x₀) := fun h => hy (by simp [u, h])
      have hb := hχt x₀ hx (subset_tsupport _ hy')
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] at hb
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hb.le
    have hsa : ∀ y ∈ tsupport u, x₀ + y ∈ tsupport a := by
      intro y hy
      refine closure_minimal (t := (fun y => x₀ + y) ⁻¹' tsupport a) ?_
        ((isClosed_tsupport a).preimage htr.continuous) hy
      intro z hz
      exact subset_tsupport a fun h => hz (by simp [u, h])
    have hu0 : u 0 = a x₀ := by simp [u, hχ1 x₀ hx]
    have hint : ∀ τ : ℝ, (∫ x, ((χ x₀ x : ℂ) * a x) * cexp (I * τ * φ x)) =
        cexp (I * τ * φ x₀) * ∫ y, u y * cexp (I * τ * recentre φ x₀ y) := by
      intro τ
      rw [← integral_const_mul, ← integral_add_left_eq_self _ x₀]
      congr 1
      funext y
      simp only [u, recentre]
      rw [show I * τ * φ (x₀ + y) = I * τ * φ x₀ + I * τ * (φ (x₀ + y) - φ x₀) by ring,
        Complex.exp_add]
      ring
    have hnorm : ∀ τ : ℝ, ‖cexp (I * τ * φ x₀)‖ = 1 := by
      intro τ
      rw [Complex.norm_exp]
      simp [(hcrit x₀ hx).1]
    have hg := (hδu x₀ hx u hu hsu hsa).norm_left
    refine isBigO_norm_left.mp (hg.congr_left fun τ => ?_)
    rw [hint τ, hu0]
    rw [show ∀ e P r L A : ℂ, e * P - e * r * L * A = e * (P - r * L * A) by intros; ring,
      norm_mul, hnorm, one_mul]
  refine (hR.add (IsBigO.fun_sum hP)).congr_left fun τ => ?_
  simp only [Finset.sum_sub_distrib]
  ring

/-- **Stationary phase, with Hörmander's hypothesis** (`Fin n → ℝ` form). `φ` smooth with
`Im φ ≥ 0` on an open set `U` containing the support of the smooth, compactly supported amplitude
`a`; the critical points in the support (`Im φ = 0`, `dφ = 0`) form the finite set `K` and are
nondegenerate (`det(−iH) ≠ 0`). Then
`∫ a e^{iτφ} = Σ_{x₀∈K} e^{iτφ(x₀)} (2π/τ)^{n/2} det(−iH(x₀))^{-1/2} a(x₀) + O(τ^{-n/2-1})`.
Source: Hörmander, *ALPDO I*, Theorem 7.7.5 (leading term), with Theorem 7.7.1 away from `K`. -/
theorem stationary_phase_pi_of_isOpen {φ a : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) {U : Set (Fin n → ℝ)} (_hU : IsOpen U)
    (haU : tsupport a ⊆ U) (hIm : ∀ x ∈ U, 0 ≤ (φ x).im) (K : Finset (Fin n → ℝ))
    (hK : ∀ x ∈ tsupport a, ((φ x).im = 0 ∧ fderiv ℝ φ x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport a) (hnd : ∀ x ∈ K, (-I • hessMat φ x).det ≠ 0) :
    (fun τ : ℝ => (∫ x, a x * cexp (I * τ * φ x)) -
        ∑ x₀ ∈ K, cexp (I * τ * φ x₀) * ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-I • hessMat φ x₀) * a x₀)
      =O[atTop] fun τ : ℝ => τ ^ (-((n : ℝ) / 2) - 1) :=
  stationary_phase_pi hφ ha hc (fun x hx => hIm x (haU hx)) K hK hKs hnd

/-- The complex Hessian matrix of `φ` at `x` in the standard basis of `ℝⁿ`. -/
noncomputable def hess (φ : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single j 1)

/-- A function on `EuclideanSpace ℝ (Fin n)` read on `ℝⁿ = Fin n → ℝ`, through `toLp 2`. -/
noncomputable def ofEuc (f : EuclideanSpace ℝ (Fin n) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun x => f (WithLp.toLp 2 x)

/-- `ofEuc f` is `f` composed with the continuous linear equivalence `toLp 2`. -/
theorem ofEuc_eq_comp (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    ofEuc f = f ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm := rfl

/-- `ofEuc` preserves smoothness. -/
theorem contDiff_ofEuc {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ofEuc f) :=
  hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff

/-- The support of `ofEuc f` is the preimage of the support of `f`. -/
theorem tsupport_ofEuc (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    tsupport (ofEuc f) = WithLp.toLp 2 ⁻¹' tsupport f := by
  rw [ofEuc_eq_comp]
  exact tsupport_comp_eq_preimage f
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toHomeomorph

/-- `ofEuc` preserves compact support. -/
theorem hasCompactSupport_ofEuc {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (ofEuc f) :=
  hf.comp_homeomorph (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toHomeomorph

/-- The derivative of `ofEuc f` (chain rule through the linear equivalence). -/
theorem fderiv_ofEuc (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : Fin n → ℝ) :
    fderiv ℝ (ofEuc f) x = (fderiv ℝ f (WithLp.toLp 2 x)).comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm :
        (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
  rw [ofEuc_eq_comp]
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.comp_right_fderiv

/-- `ofEuc f` is critical at `x` exactly when `f` is critical at `toLp 2 x`. -/
theorem fderiv_ofEuc_eq_zero_iff (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : Fin n → ℝ) :
    fderiv ℝ (ofEuc f) x = 0 ↔ fderiv ℝ f (WithLp.toLp 2 x) = 0 := by
  rw [fderiv_ofEuc]
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun v => ?_
    have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℂ => L (WithLp.ofLp v)) h
    simpa using this
  · intro h
    rw [h, ContinuousLinearMap.zero_comp]

/-- Partial derivatives of `ofEuc f` are derivatives of `f` along `EuclideanSpace.single`. -/
theorem coordDeriv_ofEuc (f : EuclideanSpace ℝ (Fin n) → ℂ) (i : Fin n) (x : Fin n → ℝ) :
    coordDeriv (ofEuc f) i x = fderiv ℝ f (WithLp.toLp 2 x) (EuclideanSpace.single i 1) := by
  simp only [coordDeriv, fderiv_ofEuc]
  rfl

/-- The Hessian of `ofEuc φ` is `hess φ`. -/
theorem hessMat_ofEuc (φ : EuclideanSpace ℝ (Fin n) → ℂ) (x : Fin n → ℝ) :
    hessMat (ofEuc φ) x = hess φ (WithLp.toLp 2 x) := by
  ext i j
  simp only [hessMat, hess]
  rw [show (fun y => coordDeriv (ofEuc φ) i y) =
      ofEuc (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) from
    funext fun y => coordDeriv_ofEuc φ i y]
  exact coordDeriv_ofEuc _ j x

/-- Integrals over `EuclideanSpace ℝ (Fin n)` and over `Fin n → ℝ` agree. -/
theorem integral_ofEuc (f : EuclideanSpace ℝ (Fin n) → ℂ) : ∫ x, f x = ∫ x, ofEuc f x :=
  ((PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding f).symm

/-- Membership in the image of a finite set under `ofLp`. -/
theorem mem_image_ofLp (K : Finset (EuclideanSpace ℝ (Fin n))) (x : Fin n → ℝ) :
    x ∈ K.image WithLp.ofLp ↔ WithLp.toLp 2 x ∈ K := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa using hk
  · intro h
    exact ⟨_, h, rfl⟩

/-- The stationary-phase expansion on `Fin n → ℝ` for `ofEuc φ`, `ofEuc a` and the image of `K`
gives the expansion on `EuclideanSpace ℝ (Fin n)`. -/
theorem isBigO_euc_of_pi {φ a : EuclideanSpace ℝ (Fin n) → ℂ}
    (K : Finset (EuclideanSpace ℝ (Fin n))) {g : ℝ → ℝ}
    (h : (fun τ : ℝ => (∫ x, ofEuc a x * cexp (I * τ * ofEuc φ x)) -
        ∑ x₀ ∈ K.image WithLp.ofLp, cexp (I * τ * ofEuc φ x₀) *
          ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) * invSqrtDet (-I • hessMat (ofEuc φ) x₀) *
          ofEuc a x₀) =O[atTop] g) :
    (fun τ : ℝ => (∫ x, a x * cexp (I * τ * φ x)) -
        ∑ x₀ ∈ K, cexp (I * τ * φ x₀) * ((2 * π / τ) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-I • hess φ x₀) * a x₀) =O[atTop] g := by
  refine h.congr_left fun τ => ?_
  rw [integral_ofEuc (fun x => a x * cexp (I * τ * φ x)),
    Finset.sum_image (fun x _ y _ hxy => WithLp.ofLp_injective 2 hxy)]
  simp only [hessMat_ofEuc]
  simp only [ofEuc, WithLp.toLp_ofLp]

/-- **Stationary phase.** `φ` smooth with `Im φ ≥ 0` on the support of the smooth, compactly
supported amplitude `a`; the critical points in the support (`Im φ = 0`, `dφ = 0`) form the
finite set `K` and are nondegenerate (`det(−iH) ≠ 0`). Then
`∫ a e^{iλφ} = Σ_{x₀∈K} e^{iλφ(x₀)} (2π/λ)^{n/2} det(−iH(x₀))^{-1/2} a(x₀) + O(λ^{-n/2-1})`.
Critical points on the boundary of the support are allowed. Source: Hörmander, *ALPDO I*,
Theorem 7.7.5 (leading term), with Theorem 7.7.1 away from `K`. -/
theorem stationary_phase {φ a : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hIm : ∀ x ∈ tsupport a, 0 ≤ (φ x).im) (K : Finset (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ x ∈ tsupport a, ((φ x).im = 0 ∧ fderiv ℝ φ x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport a) (hnd : ∀ x ∈ K, (-I • hess φ x).det ≠ 0) :
    (fun lam : ℝ => (∫ x, a x * cexp (I * lam * φ x)) -
        ∑ x₀ ∈ K, cexp (I * lam * φ x₀) * ((2 * π / lam) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-I • hess φ x₀) * a x₀)
      =O[atTop] fun lam : ℝ => lam ^ (-((n : ℝ) / 2) - 1) := by
  refine isBigO_euc_of_pi K (stationary_phase_pi (contDiff_ofEuc hφ)
    (contDiff_ofEuc ha) (hasCompactSupport_ofEuc hc) ?_ (K.image WithLp.ofLp) ?_ ?_ ?_)
  · intro x hx
    rw [tsupport_ofEuc] at hx
    exact hIm _ hx
  · intro x hx
    rw [tsupport_ofEuc] at hx
    rw [fderiv_ofEuc_eq_zero_iff, mem_image_ofLp]
    exact hK _ hx
  · intro x hx
    rw [mem_image_ofLp] at hx
    rw [tsupport_ofEuc]
    exact hKs _ hx
  · intro x hx
    rw [mem_image_ofLp] at hx
    rw [hessMat_ofEuc]
    exact hnd _ hx

/-- **Stationary phase, with Hörmander's hypothesis.** `φ` smooth with `Im φ ≥ 0` on an open set
`U` containing the support of the smooth, compactly supported amplitude `a`; the critical points
in the support (`Im φ = 0`, `dφ = 0`) form the finite set `K` and are nondegenerate
(`det(−iH) ≠ 0`). Then
`∫ a e^{iλφ} = Σ_{x₀∈K} e^{iλφ(x₀)} (2π/λ)^{n/2} det(−iH(x₀))^{-1/2} a(x₀) + O(λ^{-n/2-1})`.
Source: Hörmander, *ALPDO I*, Theorem 7.7.5 (leading term), with Theorem 7.7.1 away from `K`. -/
theorem stationary_phase_of_isOpen {φ a : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    {U : Set (EuclideanSpace ℝ (Fin n))} (_hU : IsOpen U) (haU : tsupport a ⊆ U)
    (hIm : ∀ x ∈ U, 0 ≤ (φ x).im) (K : Finset (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ x ∈ tsupport a, ((φ x).im = 0 ∧ fderiv ℝ φ x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport a) (hnd : ∀ x ∈ K, (-I • hess φ x).det ≠ 0) :
    (fun lam : ℝ => (∫ x, a x * cexp (I * lam * φ x)) -
        ∑ x₀ ∈ K, cexp (I * lam * φ x₀) * ((2 * π / lam) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-I • hess φ x₀) * a x₀)
      =O[atTop] fun lam : ℝ => lam ^ (-((n : ℝ) / 2) - 1) :=
  stationary_phase hφ ha hc (fun x hx => hIm x (haU hx)) K hK hKs hnd

end Lightlike.Oscillatory
