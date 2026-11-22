import Mathlib
import Lightlike.Dirac.ConnesDistance3

/-!
# Connes' distance on the circle: smooth test functions

On the circle `ℝ / Lℤ` the Dirac operator is `D = γ d/dx` and `‖[D, f]‖ = ‖f'‖_∞`. The extremal
function for the distance is the triangle wave `x ↦ dist (x, Lℤ)`, which is not `C¹`; we approximate
it by the explicit smooth `L`-periodic functions
`circFn L k x = (L / 2π) · arcsin (cos (2π x / L) / k)` (`k > 1`), whose derivative is
`-sin u / √(k² - cos² u)` (`u = 2π x / L`), of absolute value `≤ 1`, and which tend to the triangle wave
as `k ↓ 1`.

## References

Connes' distance formula (definition only); Dirac operator: `bgv-1992`.
-/

open Real

namespace Lightlike.Dirac

/-- The smooth approximation `x ↦ ω⁻¹ arcsin (cos (ω x) / k)` of the triangle wave, `ω = 2π / L`. -/
noncomputable def circFn (ω k : ℝ) (x : ℝ) : ℝ := ω⁻¹ * arcsin (cos (ω * x) / k)

lemma circFn_periodic {ω : ℝ} (hω : ω ≠ 0) (k : ℝ) : Function.Periodic (circFn ω k) (2 * π / ω) := by
  intro x
  unfold circFn
  have : ω * (x + 2 * π / ω) = ω * x + 2 * π := by field_simp
  rw [this, cos_add_two_pi]

lemma cos_div_ne_one {k : ℝ} (hk : 1 < k) (t : ℝ) : cos t / k ≠ 1 := by
  intro h
  have hk0 : 0 < k := by linarith
  have : cos t = k := by field_simp at h; linarith
  have := cos_le_one t
  linarith

lemma cos_div_ne_neg_one {k : ℝ} (hk : 1 < k) (t : ℝ) : cos t / k ≠ -1 := by
  intro h
  have hk0 : 0 < k := by linarith
  have : cos t = -k := by field_simp at h; linarith
  have := neg_one_le_cos t
  linarith

lemma hasDerivAt_circFn {ω k : ℝ} (hk : 1 < k) (x : ℝ) :
    HasDerivAt (circFn ω k)
      (ω⁻¹ * (1 / √(1 - (cos (ω * x) / k) ^ 2) * (-sin (ω * x) * ω / k))) x := by
  have h1 : HasDerivAt (fun x : ℝ => cos (ω * x) / k) (-sin (ω * x) * ω / k) x := by
    have := (((hasDerivAt_id x).const_mul ω).cos).div_const k
    simpa [id] using this
  have h2 := (hasDerivAt_arcsin (cos_div_ne_neg_one hk (ω * x)) (cos_div_ne_one hk (ω * x))).comp
    x h1
  exact h2.const_mul ω⁻¹

lemma contDiff_circFn (ω : ℝ) {k : ℝ} (hk : 1 < k) : ContDiff ℝ 1 (circFn ω k) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h1 : ContDiffAt ℝ 1 (fun x : ℝ => cos (ω * x) / k) x :=
    ((contDiff_const.mul contDiff_id).cos.div_const k).contDiffAt
  have h2 : ContDiffAt ℝ 1 arcsin ((fun x : ℝ => cos (ω * x) / k) x) :=
    contDiffAt_arcsin (cos_div_ne_neg_one hk (ω * x)) (cos_div_ne_one hk (ω * x))
  have h3 : ContDiffAt ℝ 1 (arcsin ∘ fun x : ℝ => cos (ω * x) / k) x := ContDiffAt.comp x h2 h1
  exact contDiffAt_const.mul h3

lemma abs_deriv_circFn_le {ω k : ℝ} (hω : 0 < ω) (hk : 1 < k) (x : ℝ) :
    |deriv (circFn ω k) x| ≤ 1 := by
  rw [(hasDerivAt_circFn (ω := ω) hk x).deriv]
  set s := sin (ω * x)
  set c := cos (ω * x)
  have hk0 : 0 < k := by linarith
  have hsc : s ^ 2 + c ^ 2 = 1 := sin_sq_add_cos_sq _
  have hle : |s| / k ≤ √(1 - (c / k) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_pow, sq_abs]
    have : 1 - c ^ 2 / k ^ 2 = (k ^ 2 - c ^ 2) / k ^ 2 := by field_simp
    rw [this]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hpos : 0 < √(1 - (c / k) ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : (c / k) ^ 2 < 1 := by
      rw [div_pow]
      rw [div_lt_one (by positivity)]
      nlinarith [sq_nonneg s]
    linarith
  have heq : ω⁻¹ * (1 / √(1 - (c / k) ^ 2) * (-s * ω / k)) = -(s / k) / √(1 - (c / k) ^ 2) := by
    field_simp
  rw [heq, abs_div, abs_neg, abs_of_pos hpos, abs_div, abs_of_pos hk0]
  rw [div_le_one hpos]
  exact hle

end Lightlike.Dirac
