module

public import Lightlike.Lorentz.SL2RPlancherel.DiscreteProjection

/-!
# The discrete series term of the Plancherel formula of `SL(2,ℝ)`

For `n ≥ 2` and `f ∈ L²(SL(2,ℝ), haarR)` the squared norm of the projection of `f` onto the isotypic subspace of
`D_n⁺` is `d_n Σ_{j,l} |∫ f(g) conj(⟨ê_j, D_n(g) ê_l⟩) dg|²` with the formal degree `d_n = (n-1)/(8π²)`
(`norm_sq_starProjection_discrete_eq`, `formalDegree`); the integrals are the matrix entries of `D_n` of the
unit vectors `ê_j = e_j/‖e_j‖` of the `K`-weight basis, so the sum is the Hilbert–Schmidt norm of `D_n(f)` in
this basis.
-/

@[expose] public section

open MeasureTheory Set Finset Complex Real UpperHalfPlane Lightlike.Lorentz.SL2R Lightlike.Lorentz
open scoped InnerProductSpace Manifold ENNReal

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

/-- **The formal degree of the holomorphic discrete series `D_n⁺`**, `d_n = (n - 1)/(8π²)`, for the Haar measure
`haarR` normalised by `∫ Φ(cosh d(g)) dg = 4π² ∫_{t>1} Φ(t) dt`. -/
def formalDegree (n : ℕ) : ℝ := ((n : ℝ) - 1) / (8 * π ^ 2)

lemma norm_evalConst_sq {n : ℕ} (hn : 2 ≤ n) :
    ‖evalConst n‖ ^ 2 = (4 * π / ((n : ℝ) - 1)) ^ 2 / (4 : ℝ) ^ n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  unfold evalConst
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_inv, norm_pow]
  have h2 : ‖(-2 * Complex.I : ℂ)‖ = 2 := by simp
  rw [h2, abs_of_pos (div_pos (by positivity) (by linarith)), mul_pow, inv_pow]
  have : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this]
  ring

/-- **The Schur ratio is the inverse of the formal degree**: `2π|c₀|²/‖e₀‖² = 8π²/(n - 1)`. -/
theorem schurRatio_eq {n : ℕ} (hn : 2 ≤ n) : schurRatio hn = 8 * π ^ 2 / ((n : ℝ) - 1) := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have h2 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  unfold schurRatio schurConst
  rw [kClass_zero hn, norm_sq_lowestClass hn, norm_evalConst_sq hn]
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have hpi : 0 < π := Real.pi_pos
  field_simp
  ring

theorem formalDegree_eq_inv {n : ℕ} (hn : 2 ≤ n) : formalDegree n = (schurRatio hn)⁻¹ := by
  rw [schurRatio_eq hn]
  have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  unfold formalDegree
  rw [inv_div]

lemma formalDegree_pos {n : ℕ} (hn : 2 ≤ n) : 0 < formalDegree n := by
  rw [formalDegree_eq_inv hn]; exact inv_pos.2 (schurRatio_pos hn)

/-- The matrix coefficient of the unit vectors `ê_j`, `ê_l`: `⟨e_j, D(g) e_l⟩ / (‖e_j‖ ‖e_l‖)`. -/
lemma mcoef_kUnit {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (g : SL2R) :
    mcoef n ((kUnit hn p.1 : holoSubmodule n) : Hn n) ((kUnit hn p.2 : holoSubmodule n) : Hn n) g =
      (((‖kClass hn p.1‖ * ‖kClass hn p.2‖)⁻¹ : ℝ) : ℂ) * mcoef n (kClass hn p.1) (kClass hn p.2) g := by
  show mcoef n (((‖kClass hn p.1‖⁻¹ : ℝ) : ℂ) • kClass hn p.1) (((‖kClass hn p.2‖⁻¹ : ℝ) : ℂ) • kClass hn p.2) g = _
  unfold mcoef
  rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  rw [mul_inv]
  ring

/-- `⟨u_p, f⟩ = d^{-1/2} ∫ conj(⟨ê_j, D(g) ê_l⟩) f(g) dg`. -/
lemma inner_uLp_eq {n : ℕ} (hn : 2 ≤ n) (p : ℕ × ℕ) (f : Lp ℂ 2 (haarR : Measure SL2R)) :
    ⟪uLp hn p, f⟫_ℂ = (((Real.sqrt (schurRatio hn))⁻¹ : ℝ) : ℂ) *
      ∫ g, (starRingEnd ℂ) (mcoef n ((kUnit hn p.1 : holoSubmodule n) : Hn n)
        ((kUnit hn p.2 : holoSubmodule n) : Hn n) g) * f g ∂haarR := by
  have hae : ∀ᵐ g ∂haarR, ⟪(uLp hn p : SL2R → ℂ) g, f g⟫_ℂ =
      (((Real.sqrt (schurRatio hn))⁻¹ : ℝ) : ℂ) * ((starRingEnd ℂ) (mcoef n
        ((kUnit hn p.1 : holoSubmodule n) : Hn n) ((kUnit hn p.2 : holoSubmodule n) : Hn n) g) * f g) := by
    filter_upwards [(memLp_uFun hn p).coeFn_toLp] with g h1
    simp only [uLp]
    rw [h1, mcoef_kUnit]
    simp only [uFun, uConst, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    have hs := Real.sqrt_pos.2 (schurRatio_pos hn)
    have h1' := norm_kClass_pos hn p.1
    have h2' := norm_kClass_pos hn p.2
    push_cast
    rw [mul_inv, mul_inv, mul_comm]
    ring
  rw [L2.inner_def, integral_congr_ae hae, integral_const_mul]

/-- **The discrete series term of the Plancherel formula**: for `f ∈ L²(SL(2,ℝ))`,
`‖P_n f‖² = d_n Σ_{j,l} |∫ f(g) conj(⟨ê_j, D_n(g) ê_l⟩) dg|²`, `d_n = (n - 1)/(8π²)`. -/
theorem norm_sq_starProjection_discrete_eq {n : ℕ} (hn : 2 ≤ n) (f : Lp ℂ 2 (haarR : Measure SL2R)) :
    ‖(discreteSpace hn).starProjection f‖ ^ 2 = formalDegree n * ∑' p : ℕ × ℕ,
      ‖∫ g, (starRingEnd ℂ) (mcoef n ((kUnit hn p.1 : holoSubmodule n) : Hn n)
        ((kUnit hn p.2 : holoSubmodule n) : Hn n) g) * f g ∂haarR‖ ^ 2 := by
  rw [norm_sq_starProjection_discrete hn f, ← tsum_mul_left]
  refine tsum_congr (fun p => ?_)
  rw [inner_uLp_eq hn p f, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, formalDegree_eq_inv hn,
    inv_pow, Real.sq_sqrt (schurRatio_pos hn).le]

end Lightlike.Lorentz.SL2RPlancherel
