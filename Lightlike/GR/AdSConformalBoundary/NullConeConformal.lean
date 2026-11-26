import Lightlike.GR.AdSConformalBoundary.NullConeAction

/-!
# An isometry of anti-de Sitter space acts conformally on the boundary

The third layer of the action of `SO(2,3)` on the conformal boundary of anti-de Sitter space (GE7). Write
`X = (cos τ, sin τ, ω)` for a boundary point (`|ω| = 1`) and `T = (-a sin τ, a cos τ, v)` for a tangent vector
(`dτ = a`, `v ⊥ ω`); its square `adsSq T = -a² + |v|²` is the boundary metric `-dτ² + dΩ²` of `adsBdyMetric`. For
`w = Λ X` and `q = Λ T`, the image curve is `t ↦ (w + t q)` normalised by `ρ(t) = ((w₀ + t q₀)² + (w₁ + t q₁)²)^{1/2}`:

* `hasDerivAt_adsRatio`: the derivative at `0` of a component over `ρ(t)` is `(q_c ρ² - w_c R) / ρ³`,
  with `R = w₀ q₀ + w₁ q₁`;
* `adsAngleDeriv`: the angular velocity `dτ' = (w₀ q₁ - w₁ q₀) / ρ²`, with `hasDerivAt_cos_adsCurve` and
  `hasDerivAt_sin_adsCurve`: `d cos τ' = -sin τ' dτ'` and `d sin τ' = cos τ' dτ'`;
* `adsDirDeriv`: the velocity `dω'ᵢ = (q_{i+2} ρ² - w_{i+2} R) / ρ³` of the direction, `hasDerivAt_adsDirCurve`;
* `adsBdyMetric_conformal`: **conformality**, `-(dτ')² + |dω'|² = (-a² + |v|²) / ρ²`: the map is conformal on the
  boundary metric with factor `ρ⁻²` (the proof uses only that `Λ` preserves `adsSq` of `X`, of `T` and their product).
-/

open Matrix

noncomputable section

namespace Lightlike

/-- The tangent vector `T = (-a sin τ, a cos τ, v)` of the section at `(τ, ω)` for `dτ = a`, `dω = v`. -/
def adsTan (τ a : ℝ) (v : Fin 3 → ℝ) : Fin 5 → ℝ := ![-(a * Real.sin τ), a * Real.cos τ, v 0, v 1, v 2]

/-- `adsSq T = -a² + |v|²`, the boundary metric. -/
theorem adsSq_adsTan (τ a : ℝ) (v : Fin 3 → ℝ) :
    adsSq (adsTan τ a v) = -a ^ 2 + ∑ i, v i ^ 2 := by
  have h := Real.sin_sq_add_cos_sq τ
  simp only [Fin.sum_univ_three]
  simp [adsSq, adsTan]
  nlinarith [h]

/-- The bilinear form of `adsSq`. -/
def adsDot (x y : Fin 5 → ℝ) : ℝ := x ⬝ᵥ (adsEta *ᵥ y)

theorem adsDot_mulVec {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (v w : Fin 5 → ℝ) :
    adsDot (Λ *ᵥ v) (Λ *ᵥ w) = adsDot v w := by
  unfold adsDot
  have h : Λ *ᵥ v ⬝ᵥ adsEta *ᵥ (Λ *ᵥ w) = v ⬝ᵥ (Λᵀ * adsEta * Λ) *ᵥ w := by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  rw [h, hΛ]

theorem adsDot_adsNullVec_adsTan (τ a : ℝ) {ω v : Fin 3 → ℝ} (hv : ∑ i, ω i * v i = 0) :
    adsDot (adsNullVec τ ω) (adsTan τ a v) = 0 := by
  simp only [Fin.sum_univ_three] at hv
  simp only [adsDot, adsEta, adsNullVec, adsTan, mulVec_diagonal, dotProduct, Fin.sum_univ_succ]
  simp
  nlinarith [hv, Real.sin_sq_add_cos_sq τ]

/-- The derivative at `0` of `(c + t d) / √((p + t r)² + (s + t u)²)`. -/
theorem hasDerivAt_adsRatio {c d p r s u : ℝ} (hP : 0 < p ^ 2 + s ^ 2) :
    HasDerivAt (fun t : ℝ => (c + t * d) / Real.sqrt ((p + t * r) ^ 2 + (s + t * u) ^ 2))
      ((d * (p ^ 2 + s ^ 2) - c * (p * r + s * u)) / Real.sqrt (p ^ 2 + s ^ 2) ^ 3) 0 := by
  have hn : HasDerivAt (fun t : ℝ => c + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c
  have hp : HasDerivAt (fun t : ℝ => (p + t * r) ^ 2 + (s + t * u) ^ 2) (2 * (p * r + s * u)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => p + t * r) r 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const r).const_add p
    have h2 : HasDerivAt (fun t : ℝ => s + t * u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add s
    convert (h1.pow 2).add (h2.pow 2) using 1
    simp; ring
  have hP0 : (p + 0 * r) ^ 2 + (s + 0 * u) ^ 2 ≠ 0 := by simpa using hP.ne'
  have hsq := hp.sqrt hP0
  have hρ : 0 < Real.sqrt (p ^ 2 + s ^ 2) := Real.sqrt_pos.mpr hP
  have hρ0 : Real.sqrt ((p + 0 * r) ^ 2 + (s + 0 * u) ^ 2) ≠ 0 := by simpa using hρ.ne'
  have h := hn.div hsq hρ0
  convert h using 1
  have hs2 : Real.sqrt (p ^ 2 + s ^ 2) ^ 2 = p ^ 2 + s ^ 2 := Real.sq_sqrt hP.le
  simp only [zero_mul, add_zero]
  field_simp
  rw [hs2]

theorem adsDot_eq (x y : Fin 5 → ℝ) :
    adsDot x y = -(x 0 * y 0) - x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 := by
  simp [adsDot, adsEta, mulVec_diagonal, dotProduct, Fin.sum_univ_succ]
  ring

/-- The image curve `t ↦ Λ (X + t T)` of a boundary point `X` in the tangent direction `T`. -/
def adsCurve (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) (a : ℝ) (v : Fin 3 → ℝ) (t : ℝ) :
    Fin 5 → ℝ := Λ *ᵥ (adsNullVec τ ω + t • adsTan τ a v)

theorem adsCurve_apply (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) (a : ℝ) (v : Fin 3 → ℝ)
    (t : ℝ) (j : Fin 5) :
    adsCurve Λ τ ω a v t j = (Λ *ᵥ adsNullVec τ ω) j + t * (Λ *ᵥ adsTan τ a v) j := by
  simp [adsCurve, mulVec_add, mulVec_smul]

/-- The angular velocity `dτ' = (w₀ q₁ - w₁ q₀) / ρ²`. -/
def adsAngleDeriv (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) (a : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ((Λ *ᵥ adsNullVec τ ω) 0 * (Λ *ᵥ adsTan τ a v) 1 - (Λ *ᵥ adsNullVec τ ω) 1 * (Λ *ᵥ adsTan τ a v) 0) /
    adsNullFactor Λ τ ω ^ 2

/-- The velocity `dω'ᵢ = (q_{i+2} ρ² - w_{i+2} R) / ρ³` of the direction. -/
def adsDirDeriv (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) (a : ℝ) (v : Fin 3 → ℝ)
    (i : Fin 3) : ℝ :=
  ((Λ *ᵥ adsTan τ a v) i.succ.succ * adsNullFactor Λ τ ω ^ 2 -
      (Λ *ᵥ adsNullVec τ ω) i.succ.succ *
        ((Λ *ᵥ adsNullVec τ ω) 0 * (Λ *ᵥ adsTan τ a v) 0 + (Λ *ᵥ adsNullVec τ ω) 1 * (Λ *ᵥ adsTan τ a v) 1)) /
    adsNullFactor Λ τ ω ^ 3

theorem adsNullFactor_sq (Λ : Matrix (Fin 5) (Fin 5) ℝ) (τ : ℝ) (ω : Fin 3 → ℝ) :
    adsNullFactor Λ τ ω ^ 2 = (Λ *ᵥ adsNullVec τ ω) 0 ^ 2 + (Λ *ᵥ adsNullVec τ ω) 1 ^ 2 := by
  unfold adsNullFactor
  exact Real.sq_sqrt (by positivity)

/-- The direction of the image curve, as a function of the parameter: `(Λ (X + tT))ₖ / ρ(t)`. -/
theorem hasDerivAt_adsCurveRatio {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) (a : ℝ) (v : Fin 3 → ℝ) (k : Fin 5) :
    HasDerivAt (fun t : ℝ => adsCurve Λ τ ω a v t k /
        Real.sqrt (adsCurve Λ τ ω a v t 0 ^ 2 + adsCurve Λ τ ω a v t 1 ^ 2))
      (((Λ *ᵥ adsTan τ a v) k * adsNullFactor Λ τ ω ^ 2 -
        (Λ *ᵥ adsNullVec τ ω) k * ((Λ *ᵥ adsNullVec τ ω) 0 * (Λ *ᵥ adsTan τ a v) 0 +
          (Λ *ᵥ adsNullVec τ ω) 1 * (Λ *ᵥ adsTan τ a v) 1)) / adsNullFactor Λ τ ω ^ 3) 0 := by
  have hP : 0 < (Λ *ᵥ adsNullVec τ ω) 0 ^ 2 + (Λ *ᵥ adsNullVec τ ω) 1 ^ 2 := by
    rw [← adsNullFactor_sq]; exact pow_pos (adsNullFactor_pos hΛ τ hω) 2
  have h := hasDerivAt_adsRatio (c := (Λ *ᵥ adsNullVec τ ω) k) (d := (Λ *ᵥ adsTan τ a v) k)
    (p := (Λ *ᵥ adsNullVec τ ω) 0) (r := (Λ *ᵥ adsTan τ a v) 0) (s := (Λ *ᵥ adsNullVec τ ω) 1)
    (u := (Λ *ᵥ adsTan τ a v) 1) hP
  simp only [adsCurve_apply]
  rw [adsNullFactor_sq]
  convert h using 1
  simp only [adsNullFactor]

/-- The direction of the image curve has velocity `adsDirDeriv`. -/
theorem hasDerivAt_adsDirCurve {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) (a : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => adsCurve Λ τ ω a v t i.succ.succ /
        Real.sqrt (adsCurve Λ τ ω a v t 0 ^ 2 + adsCurve Λ τ ω a v t 1 ^ 2))
      (adsDirDeriv Λ τ ω a v i) 0 :=
  hasDerivAt_adsCurveRatio hΛ τ hω a v i.succ.succ

/-- `d cos τ' = -sin τ' dτ'`. -/
theorem hasDerivAt_cos_adsCurve {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) (a : ℝ) (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => adsCurve Λ τ ω a v t 0 /
        Real.sqrt (adsCurve Λ τ ω a v t 0 ^ 2 + adsCurve Λ τ ω a v t 1 ^ 2))
      (-(Real.sin (adsAngle Λ τ ω)) * adsAngleDeriv Λ τ ω a v) 0 := by
  have hρ := adsNullFactor_pos hΛ τ hω
  have h := hasDerivAt_adsCurveRatio hΛ τ hω a v 0
  convert h using 1
  rw [sin_adsAngle hΛ τ hω]
  have h2 := adsNullFactor_sq Λ τ ω
  unfold adsAngleDeriv
  field_simp
  rw [h2]
  ring

/-- `d sin τ' = cos τ' dτ'`. -/
theorem hasDerivAt_sin_adsCurve {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) (a : ℝ) (v : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => adsCurve Λ τ ω a v t 1 /
        Real.sqrt (adsCurve Λ τ ω a v t 0 ^ 2 + adsCurve Λ τ ω a v t 1 ^ 2))
      (Real.cos (adsAngle Λ τ ω) * adsAngleDeriv Λ τ ω a v) 0 := by
  have hρ := adsNullFactor_pos hΛ τ hω
  have h := hasDerivAt_adsCurveRatio hΛ τ hω a v 1
  convert h using 1
  rw [cos_adsAngle hΛ τ hω]
  have h2 := adsNullFactor_sq Λ τ ω
  unfold adsAngleDeriv
  field_simp
  rw [h2]
  ring

/-- **Conformality on the boundary**: `-(dτ')² + |dω'|² = (-a² + |v|²) / ρ²` for a unit `ω` and `v ⊥ ω`. -/
theorem adsBdyMetric_conformal {Λ : Matrix (Fin 5) (Fin 5) ℝ} (hΛ : Λᵀ * adsEta * Λ = adsEta) (τ : ℝ)
    {ω v : Fin 3 → ℝ} (hω : ∑ i, ω i ^ 2 = 1) (hv : ∑ i, ω i * v i = 0) (a : ℝ) :
    -(adsAngleDeriv Λ τ ω a v) ^ 2 + ∑ i, adsDirDeriv Λ τ ω a v i ^ 2 =
      (-a ^ 2 + ∑ i, v i ^ 2) / adsNullFactor Λ τ ω ^ 2 := by
  have hρ := adsNullFactor_pos hΛ τ hω
  have hρ2 := adsNullFactor_sq Λ τ ω
  set w := Λ *ᵥ adsNullVec τ ω with hw
  set q := Λ *ᵥ adsTan τ a v with hq
  have h1 : adsSq w = 0 := by rw [hw, adsSq_mulVec hΛ]; exact adsSq_adsNullVec τ hω
  have h2 : adsSq q = -a ^ 2 + ∑ i, v i ^ 2 := by rw [hq, adsSq_mulVec hΛ]; exact adsSq_adsTan τ a v
  have h3 : adsDot w q = 0 := by
    rw [hw, hq, adsDot_mulVec hΛ]; exact adsDot_adsNullVec_adsTan τ a hv
  rw [adsDot_eq] at h3
  simp only [adsSq] at h1 h2
  set P := w 0 ^ 2 + w 1 ^ 2 with hP
  have hPpos : 0 < P := by rw [← hρ2]; exact pow_pos hρ 2
  have hnum : ∑ i : Fin 3, (q i.succ.succ * P - w i.succ.succ * (w 0 * q 0 + w 1 * q 1)) ^ 2 =
      P ^ 2 * (-a ^ 2 + ∑ i, v i ^ 2) + P * (w 0 * q 1 - w 1 * q 0) ^ 2 := by
    generalize (-a ^ 2 + ∑ i, v i ^ 2) = D at h2 ⊢
    simp only [Fin.sum_univ_three, Fin.reduceSucc]
    rw [hP]
    linear_combination (w 0 ^ 2 + w 1 ^ 2) ^ 2 * h2 + (-2) * (w 0 ^ 2 + w 1 ^ 2) * (w 0 * q 0 + w 1 * q 1) * h3 +
      (w 0 * q 0 + w 1 * q 1) ^ 2 * h1
  have h6 : (adsNullFactor Λ τ ω ^ 3) ^ 2 = P ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hρ2]
  unfold adsAngleDeriv adsDirDeriv
  simp only [div_pow, ← Finset.sum_div, ← hw, ← hq, h6, hρ2]
  rw [hnum]
  field_simp
  ring

/-- Non-vacuity: the boost `adsBoost` at `(0, e₁)` has factor `2` and sends the tangent vector `e₂` to `e₂ / 2`. -/
theorem adsDirDeriv_adsBoost :
    ∀ i : Fin 3, adsDirDeriv adsBoost 0 ![1, 0, 0] 0 ![0, 1, 0] i = ![0, 1 / 2, 0] i := by
  intro i
  have hf : adsNullFactor adsBoost 0 ![1, 0, 0] = 2 := adsNullFactor_adsBoost_zero
  simp only [adsDirDeriv, hf]
  fin_cases i <;>
    simp [adsTan, adsNullVec, adsBoost, mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals norm_num

end Lightlike
