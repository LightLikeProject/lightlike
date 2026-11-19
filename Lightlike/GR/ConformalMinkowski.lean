import Lightlike.GR.Schwarzschild
import Lightlike.Spacetime.ChartChange
import Lightlike.Spacetime.RiemannSymmetry

/-!
# The conformal compactification of Minkowski space

Minkowski space `ds² = -dt² + dr² + r² dΩ²` (`minkSph`) in the coordinates
`T + R = arctan(t + r)`, `T - R = arctan(t - r)` (`compactify`) becomes the conformal rescaling of the metric
`-dT² + dR² + (sin 2R / 2)² dΩ²` (`compactMetric`, a region of the Einstein static universe) by the factor
`cos²(T + R) cos²(T - R) = 1/((1 + (t+r)²)(1 + (t-r)²))`: `pullback_compact` says the pullback of `compactMetric`
is `(1/((1+(t+r)²)(1+(t-r)²))) • minkSph`. The factor tends to `0` along `r → ∞` (`conformalFactor_tendsto`):
null infinity is at finite distance in the compactified metric. The image lies in `|T| + R < π/2`
(`compactify_mem`); `compactMetric` is a quarter of the Einstein static universe metric `-dT² + dR² + sin²R dΩ²` of `R × S³` in the
doubled coordinates (`pullback_esu_doubling`). A rescaling of the two variables separately, `(t, r) ↦ (arctan t, arctan r)`, is not
conformal (`arctan_not_conformal`).

Gap row GE7. Source read (pdftotext): D. Harlow, *Jerusalem Lectures on Black Holes and Quantum Information*,
arXiv:1409.1231, section 2.3 "Penrose diagrams", eqs. (2.11)-(2.13), p. 7: `T ± R = arctan(t ± r)` and
`ds² = (1/(cos²(T+R) cos²(T−R))) [−dT² + dR² + (sin 2R/2)² dΩ²]`. The same section states the theorem that
conformally related metrics have the same null geodesics (not formalized here). Second source: Aharony-Gubser-Maldacena-Ooguri-Oz,
arXiv:hep-th/9905111, section 2, eqs. (2.13)-(2.16), pp. 38-39: `u± = t ± r = tan ũ±`, `ũ± = (τ ± θ)/2`, `ds² = (1/(4 cos²ũ₊ cos²ũ₋))
(-dτ² + dθ² + sin²θ dΩ²)` (2.14), "the maximally extended space ... has the geometry of R × S^p (Einstein static universe)" (2.16): `pullback_esu_doubling`
with `(τ, θ) = (2T, 2R)`. Hawking–Ellis, ch. 5: not read.
-/

open Matrix Real

noncomputable section

namespace Lightlike

/-- Minkowski space in spherical coordinates `(t, r, θ, φ)`. -/
def minkSph (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal ![-1, 1, y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The compactified metric `-dT² + dR² + (sin 2R / 2)² dΩ²` in coordinates `(T, R, θ, φ)`. -/
def compactMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal ![-1, 1, (sin (2 * y 1) / 2) ^ 2, (sin (2 * y 1) / 2) ^ 2 * sin (y 2) ^ 2]

/-- `T = (arctan(t+r) + arctan(t-r))/2`, `R = (arctan(t+r) - arctan(t-r))/2`. -/
def compactify (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(arctan (y 0 + y 1) + arctan (y 0 - y 1)) / 2, (arctan (y 0 + y 1) - arctan (y 0 - y 1)) / 2, y 2, y 3]

/-- The conformal factor `cos²(T+R) cos²(T-R) = 1/((1 + (t+r)²)(1 + (t-r)²))`. -/
def conformalFactor (y : Fin 4 → ℝ) : ℝ := 1 / ((1 + (y 0 + y 1) ^ 2) * (1 + (y 0 - y 1) ^ 2))

lemma diff_arctan_add (y : Fin 4 → ℝ) :
    DifferentiableAt ℝ (fun z : Fin 4 → ℝ => arctan (z 0 + z 1)) y :=
  Real.differentiable_arctan.differentiableAt.comp y (by fun_prop)

lemma diff_arctan_sub (y : Fin 4 → ℝ) :
    DifferentiableAt ℝ (fun z : Fin 4 → ℝ => arctan (z 0 - z 1)) y :=
  Real.differentiable_arctan.differentiableAt.comp y (by fun_prop)

private lemma proj_hasFDerivAt (i : Fin 4) (y : Fin 4 → ℝ) :
    HasFDerivAt (fun z : Fin 4 → ℝ => z i) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) y :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).hasFDerivAt

/-- `∂_k arctan(t + r)`. -/
lemma pd_arctan_add (y : Fin 4 → ℝ) (k : Fin 4) :
    pd k (fun z => arctan (z 0 + z 1)) y = (if k = 0 ∨ k = 1 then 1 else 0) / (1 + (y 0 + y 1) ^ 2) := by
  have hl : HasFDerivAt (fun z : Fin 4 → ℝ => z 0 + z 1) _ y := (proj_hasFDerivAt 0 y).add (proj_hasFDerivAt 1 y)
  have := (Real.hasDerivAt_arctan (y 0 + y 1)).comp_hasFDerivAt y hl
  unfold pd
  rw [show (fun z : Fin 4 → ℝ => arctan (z 0 + z 1)) = arctan ∘ fun z : Fin 4 → ℝ => z 0 + z 1 from rfl,
    this.fderiv]
  fin_cases k <;> simp [Pi.single_apply, ContinuousLinearMap.proj_apply] <;> ring

/-- `∂_k arctan(t - r)`. -/
lemma pd_arctan_sub (y : Fin 4 → ℝ) (k : Fin 4) :
    pd k (fun z => arctan (z 0 - z 1)) y =
      (if k = 0 then 1 else if k = 1 then -1 else 0) / (1 + (y 0 - y 1) ^ 2) := by
  have hl : HasFDerivAt (fun z : Fin 4 → ℝ => z 0 - z 1) _ y := (proj_hasFDerivAt 0 y).sub (proj_hasFDerivAt 1 y)
  have := (Real.hasDerivAt_arctan (y 0 - y 1)).comp_hasFDerivAt y hl
  unfold pd
  rw [show (fun z : Fin 4 → ℝ => arctan (z 0 - z 1)) = arctan ∘ fun z : Fin 4 → ℝ => z 0 - z 1 from rfl,
    this.fderiv]
  fin_cases k <;> simp [Pi.single_apply, ContinuousLinearMap.proj_apply] <;> ring

/-- The Jacobian of the compactification, with `p = 1/(1 + (t+r)²)`, `q = 1/(1 + (t-r)²)`. -/
lemma jac_compactify (y : Fin 4 → ℝ) :
    jac compactify y =
      !![(1 / (1 + (y 0 + y 1) ^ 2) + 1 / (1 + (y 0 - y 1) ^ 2)) / 2,
          (1 / (1 + (y 0 + y 1) ^ 2) - 1 / (1 + (y 0 - y 1) ^ 2)) / 2, 0, 0;
         (1 / (1 + (y 0 + y 1) ^ 2) - 1 / (1 + (y 0 - y 1) ^ 2)) / 2,
          (1 / (1 + (y 0 + y 1) ^ 2) + 1 / (1 + (y 0 - y 1) ^ 2)) / 2, 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] := by
  have hT : ∀ k, pd k (fun z => (arctan (z 0 + z 1) + arctan (z 0 - z 1)) / 2) y =
      (pd k (fun z => arctan (z 0 + z 1)) y + pd k (fun z => arctan (z 0 - z 1)) y) / 2 := by
    intro k
    have dS : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => arctan (z 0 + z 1) + arctan (z 0 - z 1)) y :=
      (diff_arctan_add y).add (diff_arctan_sub y)
    have := pd_const_mul (2⁻¹ : ℝ) dS k
    rw [show (fun z : Fin 4 → ℝ => (arctan (z 0 + z 1) + arctan (z 0 - z 1)) / 2) =
      fun z => 2⁻¹ * (arctan (z 0 + z 1) + arctan (z 0 - z 1)) from by ext z; ring, this,
      pd_add (diff_arctan_add y) (diff_arctan_sub y) k]
    ring
  have hR : ∀ k, pd k (fun z => (arctan (z 0 + z 1) - arctan (z 0 - z 1)) / 2) y =
      (pd k (fun z => arctan (z 0 + z 1)) y - pd k (fun z => arctan (z 0 - z 1)) y) / 2 := by
    intro k
    have dS : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => arctan (z 0 + z 1) - arctan (z 0 - z 1)) y :=
      (diff_arctan_add y).sub (diff_arctan_sub y)
    have := pd_const_mul (2⁻¹ : ℝ) dS k
    rw [show (fun z : Fin 4 → ℝ => (arctan (z 0 + z 1) - arctan (z 0 - z 1)) / 2) =
      fun z => 2⁻¹ * (arctan (z 0 + z 1) - arctan (z 0 - z 1)) from by ext z; ring, this,
      pd_sub (diff_arctan_add y) (diff_arctan_sub y) k]
    ring
  have P2 : ∀ k : Fin 4, pd k (fun z => z 2) y = if k = 2 then 1 else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_id' (y 2))
  have P3 : ∀ k : Fin 4, pd k (fun z => z 3) y = if k = 3 then 1 else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_id' (y 3))
  ext μ a
  fin_cases μ <;> fin_cases a <;> simp only [jac, compactify] <;>
    simp [hT, hR, pd_arctan_add, pd_arctan_sub, P2, P3] <;> ring

/-- The sphere factor: `(sin 2R / 2)² = r² · conformalFactor`. -/
lemma sin_two_R_sq (y : Fin 4 → ℝ) :
    (sin (2 * ((arctan (y 0 + y 1) - arctan (y 0 - y 1)) / 2)) / 2) ^ 2 = y 1 ^ 2 * conformalFactor y := by
  rw [show 2 * ((arctan (y 0 + y 1) - arctan (y 0 - y 1)) / 2) = arctan (y 0 + y 1) - arctan (y 0 - y 1) by ring,
    Real.sin_sub, Real.sin_arctan, Real.sin_arctan, Real.cos_arctan, Real.cos_arctan]
  have hv : 0 < 1 + (y 0 + y 1) ^ 2 := by positivity
  have hu : 0 < 1 + (y 0 - y 1) ^ 2 := by positivity
  have hsv : √(1 + (y 0 + y 1) ^ 2) ^ 2 = 1 + (y 0 + y 1) ^ 2 := Real.sq_sqrt hv.le
  have hsu : √(1 + (y 0 - y 1) ^ 2) ^ 2 = 1 + (y 0 - y 1) ^ 2 := Real.sq_sqrt hu.le
  have hsv0 : 0 < √(1 + (y 0 + y 1) ^ 2) := Real.sqrt_pos.2 hv
  have hsu0 : 0 < √(1 + (y 0 - y 1) ^ 2) := Real.sqrt_pos.2 hu
  unfold conformalFactor
  field_simp
  rw [hsv, hsu]
  ring

/-- **Conformal compactification of Minkowski space.** The pullback of `compactMetric` by `compactify` is
the Minkowski metric times `1/((1 + (t+r)²)(1 + (t-r)²))`. -/
theorem pullback_compact (y : Fin 4 → ℝ) :
    pullback compactMetric compactify y = conformalFactor y • minkSph y := by
  have hsq := sin_two_R_sq y
  rw [pullback_eq_mul, jac_compactify]
  have hg : compactMetric (compactify y) = diagonal ![-1, 1, y 1 ^ 2 * conformalFactor y,
      y 1 ^ 2 * conformalFactor y * sin (y 2) ^ 2] := by
    simp only [compactMetric, compactify, Matrix.cons_val_one, Matrix.cons_val_zero]
    simp [hsq]
  rw [hg]
  have hc : conformalFactor y = (1 / (1 + (y 0 + y 1) ^ 2)) * (1 / (1 + (y 0 - y 1) ^ 2)) := by
    unfold conformalFactor; rw [one_div_mul_one_div]
  rw [hc]
  generalize 1 / (1 + (y 0 + y 1) ^ 2) = p
  generalize 1 / (1 + (y 0 - y 1) ^ 2) = q
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, minkSph, Matrix.diagonal_apply] <;> ring

/-- **The image lies in the compact region** `|T ± R| < π/2`, `R > 0`: the compactified Minkowski space is a
diamond in the `(T, R)` half-plane (a region of the Einstein static universe). -/
theorem compactify_mem {y : Fin 4 → ℝ} (hr : 0 < y 1) :
    -(π / 2) < compactify y 0 + compactify y 1 ∧ compactify y 0 + compactify y 1 < π / 2 ∧
    -(π / 2) < compactify y 0 - compactify y 1 ∧ compactify y 0 - compactify y 1 < π / 2 ∧
    0 < compactify y 1 := by
  have hT : compactify y 0 + compactify y 1 = arctan (y 0 + y 1) := by simp [compactify]; ring
  have hT' : compactify y 0 - compactify y 1 = arctan (y 0 - y 1) := by simp [compactify]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hT]; exact Real.neg_pi_div_two_lt_arctan _
  · rw [hT]; exact Real.arctan_lt_pi_div_two _
  · rw [hT']; exact Real.neg_pi_div_two_lt_arctan _
  · rw [hT']; exact Real.arctan_lt_pi_div_two _
  · have : arctan (y 0 - y 1) < arctan (y 0 + y 1) := Real.arctan_strictMono (by linarith)
    simp [compactify]; linarith

/-- **Null infinity is at finite distance**: along `r → ∞` at fixed `t, θ, φ` the conformal factor tends
to `0`. -/
theorem conformalFactor_tendsto (t θ φ : ℝ) :
    Filter.Tendsto (fun r : ℝ => conformalFactor ![t, r, θ, φ]) Filter.atTop (nhds 0) := by
  unfold conformalFactor
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : Filter.Tendsto (fun r : ℝ => 1 + (t + r) ^ 2) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun r : ℝ => t + r) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_left _ _ Filter.tendsto_id
    exact Filter.tendsto_atTop_add_const_left _ _ ((Filter.tendsto_pow_atTop two_ne_zero).comp this)
  have h1 : Filter.Tendsto (fun r : ℝ => (1 + (t + r) ^ 2) * (1 + (t - r) ^ 2)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun r => by nlinarith [sq_nonneg (t - r), sq_nonneg (t + r)]) h0
  exact tendsto_const_nhds.div_atTop h1

/-- The separate rescaling `(t, r) ↦ (arctan t, arctan r)`: a non-conformal attempt at compactifying. -/
def nonConf (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![arctan (y 0), arctan (y 1), y 2, y 3]

lemma jac_nonConf (y : Fin 4 → ℝ) :
    jac nonConf y = diagonal ![1 / (1 + y 0 ^ 2), 1 / (1 + y 1 ^ 2), 1, 1] := by
  have A0 : ∀ k : Fin 4, pd k (fun z => arctan (z 0)) y = if k = 0 then 1 / (1 + y 0 ^ 2) else 0 := fun k =>
    pd_coord (n := 4) 0 k (Real.hasDerivAt_arctan (y 0))
  have A1 : ∀ k : Fin 4, pd k (fun z => arctan (z 1)) y = if k = 1 then 1 / (1 + y 1 ^ 2) else 0 := fun k =>
    pd_coord (n := 4) 1 k (Real.hasDerivAt_arctan (y 1))
  have P2 : ∀ k : Fin 4, pd k (fun z => z 2) y = if k = 2 then 1 else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_id' (y 2))
  have P3 : ∀ k : Fin 4, pd k (fun z => z 3) y = if k = 3 then 1 else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_id' (y 3))
  ext μ a
  fin_cases μ <;> fin_cases a <;> simp [jac, nonConf, A0, A1, P2, P3, Matrix.diagonal_apply]

/-- **A non-conformal rescaling fails.** Rescaling `t` and `r` separately by `arctan` does not pull
`compactMetric` back to a multiple of the Minkowski metric: at `(t, r) = (1, 2)` the `tt` and `rr`
components are `-1/4` and `1/25`, whose ratio is not `-1`. -/
theorem arctan_not_conformal :
    ¬ ∃ c : ℝ, pullback compactMetric nonConf ![1, 2, π / 2, 0] = c • minkSph ![1, 2, π / 2, 0] := by
  rintro ⟨c, hc⟩
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  rw [pullback_eq_mul, jac_nonConf] at h00 h11
  simp [compactMetric, nonConf, minkSph, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] at h00 h11
  norm_num at h00 h11
  linarith

/-- The Einstein static universe `R × S³`, `-dT² + dR² + sin²R dΩ²`, in coordinates `(T, R, θ, φ)`
(`R ∈ (0, π)`: the polar angle of the `S³`). -/
def esuMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  diagonal ![-1, 1, sin (y 1) ^ 2, sin (y 1) ^ 2 * sin (y 2) ^ 2]

/-- The doubling `(T, R) ↦ (2T, 2R)`. -/
def doubling (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![2 * y 0, 2 * y 1, y 2, y 3]

lemma jac_doubling (y : Fin 4 → ℝ) : jac doubling y = diagonal ![2, 2, 1, 1] := by
  have D0 : ∀ k : Fin 4, pd k (fun z => 2 * z 0) y = if k = 0 then 2 else 0 := fun k =>
    pd_coord (n := 4) 0 k (f := fun t => 2 * t) (f' := 2) (by simpa using (hasDerivAt_id' (y 0)).const_mul 2)
  have D1 : ∀ k : Fin 4, pd k (fun z => 2 * z 1) y = if k = 1 then 2 else 0 := fun k =>
    pd_coord (n := 4) 1 k (f := fun t => 2 * t) (f' := 2) (by simpa using (hasDerivAt_id' (y 1)).const_mul 2)
  have P2 : ∀ k : Fin 4, pd k (fun z => z 2) y = if k = 2 then 1 else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_id' (y 2))
  have P3 : ∀ k : Fin 4, pd k (fun z => z 3) y = if k = 3 then 1 else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_id' (y 3))
  ext μ a
  fin_cases μ <;> fin_cases a <;> simp [jac, doubling, D0, D1, P2, P3, Matrix.diagonal_apply]

/-- **The compactified Minkowski metric is a quarter of the Einstein static universe metric** in the
doubled coordinates `(2T, 2R)`: `compactMetric` is `esuMetric` up to the constant factor `4`, so
`pullback_compact` exhibits Minkowski space as conformal to the region `|T ± R| < π/2`, `R > 0` of `R × S³`. -/
theorem pullback_esu_doubling (y : Fin 4 → ℝ) :
    pullback esuMetric doubling y = (4 : ℝ) • compactMetric y := by
  rw [pullback_eq_mul, jac_doubling]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, esuMetric, doubling, compactMetric, Matrix.diagonal_apply] <;>
    (try rw [Real.sin_two_mul]) <;> ring

end Lightlike
