import Lightlike.Oscillatory.PhaseReduction

/-!
# Second-order condition at a maximum of `Re φ` (route 1 of task T-SF10-P2, step 2)

If `φ : ℝⁿ → ℂ` is `C²` at `x` and `Re φ ≤ Re φ x` near `x`, then the real part of the Hessian
`hessMat φ x` is negative semidefinite. Mathlib has no second-derivative test, so a one-variable
version (`deriv2_nonpos_of_isLocalMax`) is proved first by the mean value theorem.
-/

open Filter Topology Matrix

namespace Lightlike.Asymptotics.Lorentzian

open Lightlike.Oscillatory

/-- One-variable second-order necessary condition: if `h` has a local maximum at `0`, `h' t` is the
derivative of `h` near `0` and `h'` has derivative `c` at `0`, then `c ≤ 0`. -/
theorem deriv2_nonpos_of_isLocalMax {h h' : ℝ → ℝ} {c : ℝ}
    (hd : ∀ᶠ t in 𝓝 0, HasDerivAt h (h' t) t) (hd' : HasDerivAt h' c 0)
    (hmax : IsLocalMax h 0) : c ≤ 0 := by
  by_contra hc
  replace hc := not_le.1 hc
  have h0 : h' 0 = 0 := by
    have h1 : HasDerivAt h (h' 0) 0 := hd.self_of_nhds
    exact hmax.hasDerivAt_eq_zero h1
  have hslope : ∀ᶠ t in 𝓝[≠] (0 : ℝ), 0 < t⁻¹ * (h' t - h' 0) := by
    have := (hd'.tendsto_slope_zero).eventually_const_lt hc
    refine this.mono fun t ht => ?_
    simpa using ht
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt h (h' t) t ∧ h t ≤ h 0 ∧
      (t ∈ ({0} : Set ℝ)ᶜ → 0 < t⁻¹ * (h' t - h' 0)) :=
    hd.and (hmax.and (eventually_nhdsWithin_iff.1 hslope))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  have hb : 0 < ε / 2 := by positivity
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (ε / 2), HasDerivAt h (h' x) x := by
    intro x hx
    refine (hball ?_).1
    rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
    linarith [hx.2]
  have hcont : ContinuousOn h (Set.Icc 0 (ε / 2)) := by
    intro x hx
    refine (hball (y := x) ?_).1.continuousAt.continuousWithinAt
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    linarith [hx.2]
  obtain ⟨c0, hc0, hc0eq⟩ := exists_hasDerivAt_eq_slope h h' hb hcont hder
  have hcd : dist c0 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hc0.1]
    linarith [hc0.2]
  obtain ⟨-, -, hpos⟩ := hball hcd
  have hpos' := hpos (by simpa using hc0.1.ne')
  have hh'c : 0 < h' c0 := by
    rw [h0, sub_zero] at hpos'
    exact (mul_pos_iff_of_pos_left (inv_pos.2 hc0.1)).1 hpos'
  have hbd : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hb]
    linarith
  obtain ⟨-, hle, -⟩ := hball hbd
  rw [sub_zero] at hc0eq
  have : 0 < (h (ε / 2) - h 0) / (ε / 2) := by rw [← hc0eq]; exact hh'c
  have := (div_pos_iff_of_pos_right hb).1 this
  linarith

variable {n : ℕ}

/-- Hessian entries as entries of the second Fréchet derivative, for a function that is only `C²`
at the point. -/
theorem hessMat_eq_local {φ : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ} (hφ : ContDiffAt ℝ 2 φ x)
    (i j : Fin n) :
    hessMat φ x i j = fderiv ℝ (fderiv ℝ φ) x (Pi.single j 1) (Pi.single i 1) := by
  have hd1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x :=
    hφ.fderiv_right (m := 1) (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x := hd1.differentiableAt (by norm_num)
  simp only [hessMat, coordDeriv]
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The Hessian of a function that is `C²` at the point is symmetric (Schwarz). -/
theorem hessMat_isSymm_local {φ : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ} (hφ : ContDiffAt ℝ 2 φ x) :
    (hessMat φ x).IsSymm := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [hessMat_eq_local hφ, hessMat_eq_local hφ, hs]

theorem pi_eq_sum_single_smul (u : Fin n → ℝ) :
    u = ∑ i, u i • (Pi.single i 1 : Fin n → ℝ) := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- The real Hessian form `uᵀ (Re H) u` is the real part of the second derivative `D²φ(x)(u,u)`. -/
theorem dotProduct_re_hessMat_mulVec {φ : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (u : Fin n → ℝ) :
    u ⬝ᵥ ((hessMat φ x).map Complex.re *ᵥ u) = (fderiv ℝ (fderiv ℝ φ) x u u).re := by
  set D := fderiv ℝ (fderiv ℝ φ) x with hD
  have hu := pi_eq_sum_single_smul u
  have h1 : D u u = ∑ j, ∑ i, (u j * u i : ℝ) • D (Pi.single j 1) (Pi.single i 1) := by
    conv_lhs => rw [hu]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  rw [h1, Complex.re_sum]
  simp only [Complex.re_sum, Complex.smul_re, smul_eq_mul]
  simp only [dotProduct, mulVec, Matrix.map_apply, hessMat_eq_local hφ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Second-order condition.** If `φ` is `C²` at `x` and `Re φ ≤ Re φ x` near `x`, the real part of
the Hessian is negative semidefinite: `uᵀ (Re H) u ≤ 0`. -/
theorem dotProduct_re_hessMat_nonpos {φ : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ}
    (hφ : ContDiffAt ℝ 2 φ x) (hmax : ∀ᶠ y in 𝓝 x, (φ y).re ≤ (φ x).re) (u : Fin n → ℝ) :
    u ⬝ᵥ ((hessMat φ x).map Complex.re *ᵥ u) ≤ 0 := by
  rw [dotProduct_re_hessMat_mulVec hφ u]
  have hline : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hline0 : x + (0 : ℝ) • u = x := by simp
  have hcont : Continuous (fun t : ℝ => x + t • u) := by fun_prop
  have htend : Tendsto (fun t : ℝ => x + t • u) (𝓝 0) (𝓝 x) := by
    simpa [hline0] using hcont.tendsto 0
  -- C² near x
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 φ y := hφ.eventually (by simp)
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (fun s : ℝ => (φ (x + s • u)).re)
        ((fderiv ℝ φ (x + t • u) u).re) t := by
    refine (htend.eventually hev).mono fun t ht => ?_
    have hφd : HasFDerivAt φ (fderiv ℝ φ (x + t • u))  (x + t • u) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => x + s • u) u t := by
      simpa using ((hasDerivAt_id t).smul_const u).const_add x
    have := hφd.comp_hasDerivAt t hl
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t this)
  have hd1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := hφ.fderiv_right (m := 1) (by norm_num)
  have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (hd1.differentiableAt (by norm_num)).hasFDerivAt
  have hd' : HasDerivAt (fun t : ℝ => (fderiv ℝ φ (x + t • u) u).re)
      ((fderiv ℝ (fderiv ℝ φ) x u u).re) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => fderiv ℝ φ (x + t • u))
        (fderiv ℝ (fderiv ℝ φ) x u) 0 := by
      have : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) (x + (0 : ℝ) • u) := by
        rw [hline0]; exact hD
      exact this.comp_hasDerivAt (0 : ℝ) hline
    have h2 := (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  refine deriv2_nonpos_of_isLocalMax hd hd' ?_
  have : ∀ᶠ t in 𝓝 (0 : ℝ), (φ (x + t • u)).re ≤ (φ (x + (0 : ℝ) • u)).re := by
    rw [hline0]
    exact htend.eventually hmax
  exact this

end Lightlike.Asymptotics.Lorentzian
