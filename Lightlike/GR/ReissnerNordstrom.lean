import Lightlike.GR.SAdSVacuum
import Lightlike.Spacetime.MaxwellCoord
import Lightlike.Spacetime.EnergyConditions
import Lightlike.Spacetime.OpenCoordMetric

/-!
# The Reissner–Nordström solution of the Einstein–Maxwell equations

In coordinates `(t, r, θ, φ)`, the Reissner–Nordström metric `ds² = -Δ dt² + Δ⁻¹ dr² + r² dΩ²`,
`Δ = 1 - 2M/r + (q² + p²)/r²` (`rnMetric`, a static spherical metric `ssMetric`), with the field strength
`F_{tr} = -q/r²`, `F_{θφ} = p sin θ` (`rnField`, electric charge `q`, magnetic charge `p`), solves the
Einstein–Maxwell equations (`G = 8π T` with `T = (1/4π)(F F − ¼ g F²)`, units `G = 1`, Gaussian charges) on
`r > 0`, `Δ ≠ 0`, `0 < θ < π`: `rn_einstein` (the Einstein tensor is `2 emT`, with Regge's electromagnetic stress-energy
`emT` of `EnergyConditions.lean` evaluated on the coordinate tangent space) and `rn_maxwell` (the source-free Maxwell
equations, `MaxwellCoord.lean`). The horizons are the roots `r± = M ± √(M² − q² − p²)` of `Δ` (`rnF_eq_factor`,
`rnF_rplus`, `rnF_rminus`); in the extremal case `M² = q² + p²` they coincide at `r = M`, `Δ = (1 − M/r)²`, and the
horizon is degenerate: `Δ(M) = Δ'(M) = 0` (`rn_extremal`), its surface gravity `Δ'(r₊)/2 = (r₊ − r₋)/(2r₊²)` vanishes
(`rn_surfaceGravity`). Trust checks: `q = p = 0` is Schwarzschild with `F = 0`; with `q² + p² ≠ 0` the metric is not
a vacuum solution (`rn_not_vacuum`); the chart domain is nonempty (`rnU_nonempty`).

The classical extremality bound (Carroll, pp. 202–206): `Δ` has a zero at some `r > 0`, a horizon, iff `0 < M` and
`q² + p² ≤ M²`, i.e. `M ≥ |Q|` with `|Q| = √(q² + p²)` (`rn_horizon_iff`, `rn_horizon_iff_sqrt`); below the bound `Δ > 0`
everywhere (`rnF_pos_of_lt`); the bound is saturated exactly by the degenerate horizon (`rn_degenerate_iff`). The BPS
bound `2m ≥ |Z|` of the `N = 2` supersymmetry algebra is `Lightlike/GR/BPSBound.lean`.

Gap row G3-056 (partial row "BPS bounds and extremal black holes (Reissner–Nordström as m = |Q|)"). Not proved: that
the extremal Reissner–Nordström black hole is a BPS state of `N = 2` supergravity, i.e. that its mass and charge are the
`m` and `|Z|` of the asymptotic supersymmetry algebra (Gibbons–Hull); see `docs/notes/g3-056-reissner-nordstrom.md`.

Source read (pdftotext): S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7: the
electromagnetic stress-energy `T_μν = (1/4π)(F_μρ F_ν^ρ − ¼ g_μν F_ρσ F^ρσ)` (7.107), the spherically symmetric
field strength (7.108), the Einstein–Maxwell equations (7.109), p. 201; the metric (7.110)–(7.111), the field
(7.112), the horizons `r± = GM ± √(G²M² − G(p² + q²))` (7.113), p. 202; the extremal case "GM² = p² + q² ... The
extremal black holes have Δ(r) = 0 at a single radius, r = GM", p. 206; the three cases "GM² < p² + q²" (Δ always positive,
a naked singularity), p. 202, "GM² > p² + q²" (two horizons), p. 204, "GM² = p² + q²", p. 206; Einstein's equation `R_μν − ½ R g_μν =
8πG T_μν` (4.52), p. 112. Differences: the units `G = 1` (representation); Regge's `emT` omits the Gaussian factor
`1/4π` (so `G = 8π T = 2 emT`); the Maxwell equations in their coordinate form (`MaxwellCoord.lean`, representation).
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

/-! ## Regge's `emT` on the coordinate tangent space, through the library's `matForm` -/

lemma matForm_toBilinForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (matForm A).toBilinForm = Matrix.toBilin' A := by
  ext v w
  simp [ContinuousLinearMap.toBilinForm, matForm_eq_dotProduct, Matrix.toBilin'_apply']

lemma matForm_nondegenerate {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (h : A.det ≠ 0) :
    (matForm A).toBilinForm.Nondegenerate := by
  rw [matForm_toBilinForm]
  exact LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.2 h

/-- **Regge's `emA` in coordinates**: `A v = G⁻¹ Fᵀ v` for a symmetric invertible `G`. -/
theorem emA_coord {n : ℕ} {G F : Matrix (Fin n) (Fin n) ℝ} (hG : Gᵀ = G) (hdet : G.det ≠ 0)
    (v : Fin n → ℝ) :
    emA (matForm G) (matForm_nondegenerate hdet) (Matrix.toBilin' F) v = (G⁻¹ * Fᵀ) *ᵥ v := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  unfold emA
  show ((matForm G).toBilinForm.toDual (matForm_nondegenerate hdet)).symm (Matrix.toBilin' F v) = _
  rw [LinearEquiv.symm_apply_eq]
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.BilinForm.toDual_def, matForm_toBilinForm, Matrix.toBilin'_apply', Matrix.toBilin'_apply',
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
  congr 1
  rw [← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose, hG, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- **Regge's `emF2` in coordinates**: `F_ab F^ab = −tr((G⁻¹Fᵀ)²)`. -/
theorem emF2_coord {n : ℕ} {G F : Matrix (Fin n) (Fin n) ℝ} (hG : Gᵀ = G) (hdet : G.det ≠ 0) :
    emF2 (matForm G) (matForm_nondegenerate hdet) (Matrix.toBilin' F) =
      -Matrix.trace ((G⁻¹ * Fᵀ) * (G⁻¹ * Fᵀ)) := by
  have h : emA (matForm G) (matForm_nondegenerate hdet) (Matrix.toBilin' F) = Matrix.toLin' (G⁻¹ * Fᵀ) :=
    LinearMap.ext fun v => by rw [emA_coord hG hdet, Matrix.toLin'_apply]
  unfold emF2
  rw [h, ← Matrix.toLin'_mul, LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin n)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

/-- **Regge's `emT` in coordinates.** -/
theorem emT_coord {n : ℕ} {G F : Matrix (Fin n) (Fin n) ℝ} (hG : Gᵀ = G) (hdet : G.det ≠ 0)
    (v w : Fin n → ℝ) :
    emT (matForm G) (matForm_nondegenerate hdet) (Matrix.toBilin' F) v w =
      ((G⁻¹ * Fᵀ) *ᵥ v) ⬝ᵥ (G *ᵥ ((G⁻¹ * Fᵀ) *ᵥ w)) -
        (1 / 4) * (-Matrix.trace ((G⁻¹ * Fᵀ) * (G⁻¹ * Fᵀ))) * (v ⬝ᵥ (G *ᵥ w)) := by
  unfold emT
  rw [matForm_eq_dotProduct, matForm_eq_dotProduct, emA_coord hG hdet, emA_coord hG hdet, emF2_coord hG hdet]

/-! ## The Reissner–Nordström metric and its Ricci tensor -/

/-- `Δ(r) = 1 − 2M/r + Q²/r²`, with `Q² = q² + p²`. -/
def rnF (M Q2 r : ℝ) : ℝ := 1 - 2 * M / r + Q2 / r ^ 2

/-- `Δ'(r)`. -/
def rnF1 (M Q2 r : ℝ) : ℝ := 2 * M / r ^ 2 - 2 * Q2 / r ^ 3

/-- `Δ''(r)`. -/
def rnF2 (M Q2 r : ℝ) : ℝ := -(4 * M / r ^ 3) + 6 * Q2 / r ^ 4

lemma rnF_hasDeriv (M Q2 : ℝ) {r : ℝ} (hr : 0 < r) : HasDerivAt (rnF M Q2) (rnF1 M Q2 r) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * M / r) (-(2 * M / r ^ 2)) r := by
    have := (hasDerivAt_const r (2 * M)).div (hasDerivAt_id' r) hr.ne'
    refine this.congr_deriv ?_
    field_simp
    try ring
  have h2 : HasDerivAt (fun r : ℝ => Q2 / r ^ 2) (-(2 * Q2 / r ^ 3)) r := by
    have := (hasDerivAt_const r Q2).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr.ne')
    refine this.congr_deriv ?_
    field_simp
    try ring
  have := ((hasDerivAt_const r (1 : ℝ)).sub h1).add h2
  refine this.congr_deriv ?_
  unfold rnF1
  ring

lemma rnF1_hasDeriv (M Q2 : ℝ) {r : ℝ} (hr : 0 < r) : HasDerivAt (rnF1 M Q2) (rnF2 M Q2 r) r := by
  have h1 : HasDerivAt (fun r : ℝ => 2 * M / r ^ 2) (-(4 * M / r ^ 3)) r := by
    have := (hasDerivAt_const r (2 * M)).div (hasDerivAt_pow 2 r) (pow_ne_zero 2 hr.ne')
    refine this.congr_deriv ?_
    field_simp
    try ring
  have h2 : HasDerivAt (fun r : ℝ => 2 * Q2 / r ^ 3) (-(6 * Q2 / r ^ 4)) r := by
    have := (hasDerivAt_const r (2 * Q2)).div (hasDerivAt_pow 3 r) (pow_ne_zero 3 hr.ne')
    refine this.congr_deriv ?_
    field_simp
    try ring
  have := h1.sub h2
  refine this.congr_deriv ?_
  unfold rnF2
  ring

lemma rnF_contDiffOn (M Q2 : ℝ) : ContDiffOn ℝ ∞ (rnF M Q2) (Set.Ioi 0) := by
  unfold rnF
  have h0 : ∀ r ∈ Set.Ioi (0 : ℝ), r ≠ 0 := fun r hr => (Set.mem_Ioi.1 hr).ne'
  exact (contDiffOn_const.sub (contDiffOn_const.div contDiffOn_id h0)).add
    (contDiffOn_const.div (contDiffOn_id.pow 2) fun r hr => pow_ne_zero 2 (h0 r hr))

/-- The Reissner–Nordström metric `-Δ dt² + Δ⁻¹ dr² + r² dΩ²` (`Q2 = q² + p²`). -/
abbrev rnMetric (M Q2 : ℝ) : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := ssMetric (rnF M Q2)

/-- The domain `r > 0`, `Δ ≠ 0`, `0 < θ < π`. -/
abbrev rnU (M Q2 : ℝ) : Set (Fin 4 → ℝ) := ssU (rnF M Q2)

lemma isCoordMetric_rn (M Q2 : ℝ) : IsCoordMetric (rnMetric M Q2) (rnU M Q2) :=
  isCoordMetric_ss (rnF_contDiffOn M Q2)

lemma isOpen_rnU (M Q2 : ℝ) : IsOpen (rnU M Q2) := isOpen_ssU (rnF_contDiffOn M Q2).continuousOn

/-- The Ricci tensor of the Reissner–Nordström metric, as a matrix. -/
def rnRicci (M Q2 : ℝ) (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (Q2 / y 1 ^ 4) • diagonal ![rnF M Q2 (y 1), -(1 / rnF M Q2 (y 1)), y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- **The Ricci tensor of Reissner–Nordström**: `R = (Q²/r⁴) diag(Δ, −Δ⁻¹, r², r² sin²θ)`. -/
theorem ricci_rn (M Q2 : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ rnU M Q2) (σ ν : Fin 4) :
    ricci (rnMetric M Q2) σ ν y = rnRicci M Q2 y σ ν := by
  have hA : ∀ r, 0 < r → HasDerivAt (rnF M Q2) (rnF1 M Q2 r) r := fun r hr => rnF_hasDeriv M Q2 hr
  have hB : ∀ r, 0 < r → HasDerivAt (rnF1 M Q2) (rnF2 M Q2 r) r := fun r hr => rnF1_hasDeriv M Q2 hr
  have hg := isCoordMetric_rn M Q2
  have hU := isOpen_rnU M Q2
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : rnF M Q2 (y 1) ≠ 0 := hy.2.1
  fin_cases σ <;> fin_cases ν
  all_goals first
    | refine (ricci_ss_00 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_01 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_02 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_03 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_10 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_11 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_12 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_13 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_20 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_21 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_22 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_23 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_30 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_31 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_32 _ _ _ hA hB hy hU hg).trans ?_
    | refine (ricci_ss_33 _ _ _ hA hB hy hU hg).trans ?_
  all_goals simp [rnRicci, rnF, rnF1, rnF2, diagonal_apply]
  all_goals (try field_simp)
  all_goals (try ring)

/-- **The scalar curvature of Reissner–Nordström vanishes.** -/
theorem scalarCurvature_rn (M Q2 : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ rnU M Q2) :
    scalarCurvature (rnMetric M Q2) y = 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : rnF M Q2 (y 1) ≠ 0 := hy.2.1
  have hs : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  unfold scalarCurvature
  rw [ssMetric_inv (rnF M Q2) hy]
  simp only [ricci_rn M Q2 hy, Fin.sum_univ_four]
  simp [rnRicci, diagonal_apply]
  field_simp
  ring

/-- The Einstein tensor of Reissner–Nordström is its Ricci tensor. -/
theorem einsteinTensor_rn (M Q2 : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ rnU M Q2) (σ ν : Fin 4) :
    einsteinTensor (rnMetric M Q2) σ ν y = rnRicci M Q2 y σ ν := by
  simp [einsteinTensor, scalarCurvature_rn M Q2 hy, ricci_rn M Q2 hy]

/-! ## The field strength and the Einstein–Maxwell equations -/

/-- The Reissner–Nordström field strength `F_{tr} = −q/r²`, `F_{θφ} = p sin θ` (Carroll (7.112)). -/
def rnField (q p : ℝ) (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -(q / y 1 ^ 2), 0, 0;
     q / y 1 ^ 2, 0, 0, 0;
     0, 0, 0, p * sin (y 2);
     0, 0, -(p * sin (y 2)), 0]

lemma ssMetric_symm (f : ℝ → ℝ) (y : Fin 4 → ℝ) : (ssMetric f y)ᵀ = ssMetric f y := by
  simp [ssMetric]

lemma det_ssMetric {f : ℝ → ℝ} {y : Fin 4 → ℝ} (hy : y ∈ ssU f) :
    (ssMetric f y).det = -(y 1 ^ 4 * sin (y 2) ^ 2) := by
  have hf : f (y 1) ≠ 0 := hy.2.1
  rw [ssMetric, det_diagonal, Fin.prod_univ_four]
  simp
  field_simp
  try ring

lemma det_ssMetric_ne {f : ℝ → ℝ} {y : Fin 4 → ℝ} (hy : y ∈ ssU f) : (ssMetric f y).det ≠ 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hs : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  rw [det_ssMetric hy]
  exact neg_ne_zero.2 (by positivity)

/-- The endomorphism `A = G⁻¹ Fᵀ` of the Reissner–Nordström field. -/
lemma rn_A (M q p : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ rnU M (q ^ 2 + p ^ 2)) :
    (rnMetric M (q ^ 2 + p ^ 2) y)⁻¹ * (rnField q p y)ᵀ =
      !![0, -(q / (rnF M (q ^ 2 + p ^ 2) (y 1) * y 1 ^ 2)), 0, 0;
         -(rnF M (q ^ 2 + p ^ 2) (y 1) * q / y 1 ^ 2), 0, 0, 0;
         0, 0, 0, -(p * sin (y 2) / y 1 ^ 2);
         0, 0, p / (y 1 ^ 2 * sin (y 2)), 0] := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : rnF M (q ^ 2 + p ^ 2) (y 1) ≠ 0 := hy.2.1
  have hs : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  rw [ssMetric_inv _ hy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rnField, Matrix.mul_apply, Fin.sum_univ_four, diagonal_apply] <;> field_simp

/-- **Reissner–Nordström solves the Einstein equations with the Maxwell source**: `G_μν = 8π T_μν = 2 emT_μν`
(Carroll (4.52), (7.107), `G = 1`), with Regge's `emT` of the field `rnField q p`, for `Q² = q² + p²`. -/
theorem rn_einstein (M q p : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ rnU M (q ^ 2 + p ^ 2)) (σ ν : Fin 4) :
    einsteinTensor (rnMetric M (q ^ 2 + p ^ 2)) σ ν y =
      2 * emT (matForm (rnMetric M (q ^ 2 + p ^ 2) y)) (matForm_nondegenerate (det_ssMetric_ne hy))
        (Matrix.toBilin' (rnField q p y)) (Pi.single σ 1) (Pi.single ν 1) := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : rnF M (q ^ 2 + p ^ 2) (y 1) ≠ 0 := hy.2.1
  have hs : sin (y 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2).ne'
  rw [einsteinTensor_rn _ _ hy, emT_coord (ssMetric_symm _ _) (det_ssMetric_ne hy), rn_A M q p hy]
  fin_cases σ <;> fin_cases ν <;>
    simp [rnRicci, ssMetric, Matrix.trace, Fin.sum_univ_four, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      diagonal_apply, Pi.single_apply] <;> field_simp <;> ring

/-! ## The Maxwell equations -/

/-- The derivatives `∂_μ F_{νρ}` of the Reissner–Nordström field. -/
def rnFieldD (q p : ℝ) (y : Fin 4 → ℝ) (μ ν ρ : Fin 4) : ℝ :=
  if μ = 1 ∧ ν = 0 ∧ ρ = 1 then 2 * q / y 1 ^ 3
  else if μ = 1 ∧ ν = 1 ∧ ρ = 0 then -(2 * q / y 1 ^ 3)
  else if μ = 2 ∧ ν = 2 ∧ ρ = 3 then p * cos (y 2)
  else if μ = 2 ∧ ν = 3 ∧ ρ = 2 then -(p * cos (y 2))
  else 0

lemma pd_rnField (q p : ℝ) {y : Fin 4 → ℝ} (hr : y 1 ≠ 0) (μ ν ρ : Fin 4) :
    pd μ (fun z => rnField q p z ν ρ) y = rnFieldD q p y μ ν ρ := by
  have d1 : HasDerivAt (fun t : ℝ => -(q / t ^ 2)) (2 * q / y 1 ^ 3) (y 1) := by
    have := ((hasDerivAt_const (y 1) q).div (hasDerivAt_pow 2 (y 1)) (pow_ne_zero 2 hr)).neg
    refine this.congr_deriv ?_
    field_simp
    ring
  have d2 : HasDerivAt (fun t : ℝ => q / t ^ 2) (-(2 * q / y 1 ^ 3)) (y 1) := by
    have := (hasDerivAt_const (y 1) q).div (hasDerivAt_pow 2 (y 1)) (pow_ne_zero 2 hr)
    refine this.congr_deriv ?_
    field_simp
    ring
  have d3 : HasDerivAt (fun t : ℝ => p * sin t) (p * cos (y 2)) (y 2) := (hasDerivAt_sin (y 2)).const_mul p
  have d4 : HasDerivAt (fun t : ℝ => -(p * sin t)) (-(p * cos (y 2))) (y 2) := d3.neg
  have c1 := pd_coord (n := 4) 1 μ d1
  have c2 := pd_coord (n := 4) 1 μ d2
  have c3 := pd_coord (n := 4) 2 μ d3
  have c4 := pd_coord (n := 4) 2 μ d4
  fin_cases ν <;> fin_cases ρ <;> simp only [rnField] <;> simp [rnFieldD] <;>
    first
    | (rw [c1]; try (fin_cases μ <;> simp))
    | (rw [c2]; try (fin_cases μ <;> simp))
    | (rw [c3]; try (fin_cases μ <;> simp))
    | (rw [c4]; try (fin_cases μ <;> simp))
    | (simp only [pd_const]; done)
    | (rw [pd_const]; try (split_ifs <;> rfl))
    | (fin_cases μ <;> simp [pd_const])

/-- `√|det g| F^{μν}` for Reissner–Nordström. -/
def rnDiv (q p : ℝ) (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, q * sin (y 2), 0, 0;
     -(q * sin (y 2)), 0, 0, 0;
     0, 0, 0, p / y 1 ^ 2;
     0, 0, -(p / y 1 ^ 2), 0]

lemma rn_densityField (M q p : ℝ) {y : Fin 4 → ℝ} (hy : y ∈ rnU M (q ^ 2 + p ^ 2)) (μ ν : Fin 4) :
    Real.sqrt |(rnMetric M (q ^ 2 + p ^ 2) y).det| *
        raiseBoth (rnMetric M (q ^ 2 + p ^ 2) y) (rnField q p y) μ ν = rnDiv q p y μ ν := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hf : rnF M (q ^ 2 + p ^ 2) (y 1) ≠ 0 := hy.2.1
  have hs0 : 0 < sin (y 2) := sin_pos_of_pos_of_lt_pi hy.2.2.1 hy.2.2.2
  have hs : sin (y 2) ≠ 0 := hs0.ne'
  have hsq : Real.sqrt |(rnMetric M (q ^ 2 + p ^ 2) y).det| = y 1 ^ 2 * sin (y 2) := by
    rw [det_ssMetric hy, abs_neg, abs_of_nonneg (by positivity),
      show y 1 ^ 4 * sin (y 2) ^ 2 = (y 1 ^ 2 * sin (y 2)) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq, raiseBoth, ssMetric_inv _ hy]
  fin_cases μ <;> fin_cases ν <;>
    simp [rnField, rnDiv, Matrix.mul_apply, Fin.sum_univ_four, diagonal_apply] <;> field_simp <;> ring

lemma pd_rnDiv_diag (q p : ℝ) {y : Fin 4 → ℝ} (hr : y 1 ≠ 0) (μ ν : Fin 4) :
    pd μ (fun z => rnDiv q p z μ ν) y = 0 := by
  have e1 : HasDerivAt (fun t : ℝ => q * sin t) (q * cos (y 2)) (y 2) := (hasDerivAt_sin (y 2)).const_mul q
  have e2 : HasDerivAt (fun t : ℝ => -(q * sin t)) (-(q * cos (y 2))) (y 2) := e1.neg
  have e3 : HasDerivAt (fun t : ℝ => p / t ^ 2) (-(2 * p / y 1 ^ 3)) (y 1) := by
    have := (hasDerivAt_const (y 1) p).div (hasDerivAt_pow 2 (y 1)) (pow_ne_zero 2 hr)
    refine this.congr_deriv ?_
    field_simp
    ring
  have e4 : HasDerivAt (fun t : ℝ => -(p / t ^ 2)) (-(-(2 * p / y 1 ^ 3))) (y 1) := e3.neg
  fin_cases μ <;> fin_cases ν <;> simp only [rnDiv] <;> simp <;>
    first
    | exact pd_const _ _ _
    | (rw [pd_coord (n := 4) 2 _ e1]; try simp)
    | (rw [pd_coord (n := 4) 2 _ e2]; try simp)
    | (rw [pd_coord (n := 4) 1 _ e3]; try simp)
    | (rw [pd_coord (n := 4) 1 _ e4]; try simp)

/-- **The Reissner–Nordström field solves the source-free Maxwell equations** (Carroll (7.109), in the coordinate
form of `MaxwellCoord.lean`). -/
theorem rn_maxwell (M q p : ℝ) :
    IsSourceFreeMaxwell (rnMetric M (q ^ 2 + p ^ 2)) (rnField q p) (rnU M (q ^ 2 + p ^ 2)) where
  antisymm := fun y _ => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rnField]
  closed := fun y hy μ ν ρ => by
    have hr : y 1 ≠ 0 := hy.1.ne'
    rw [pd_rnField q p hr, pd_rnField q p hr, pd_rnField q p hr]
    fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> simp [rnFieldD]
  divergence := fun y hy ν => by
    have hr : y 1 ≠ 0 := hy.1.ne'
    refine Finset.sum_eq_zero fun μ _ => ?_
    have hev : (fun z => Real.sqrt |(rnMetric M (q ^ 2 + p ^ 2) z).det| *
        raiseBoth (rnMetric M (q ^ 2 + p ^ 2) z) (rnField q p z) μ ν) =ᶠ[nhds y]
          fun z => rnDiv q p z μ ν := by
      filter_upwards [(isOpen_rnU M (q ^ 2 + p ^ 2)).mem_nhds hy] with z hz
      exact rn_densityField M q p hz μ ν
    rw [pd_congr hev]
    exact pd_rnDiv_diag q p hr μ ν

/-! ## Horizons and the extremal case -/

/-- The outer horizon `r₊ = M + √(M² − Q²)` (Carroll (7.113), `G = 1`). -/
def rnRplus (M Q2 : ℝ) : ℝ := M + √(M ^ 2 - Q2)

/-- The inner horizon `r₋ = M − √(M² − Q²)`. -/
def rnRminus (M Q2 : ℝ) : ℝ := M - √(M ^ 2 - Q2)

/-- **`Δ` factors through the horizons**: `Δ(r) = (r − r₊)(r − r₋)/r²` for `Q² ≤ M²`. -/
theorem rnF_eq_factor {M Q2 : ℝ} (h : Q2 ≤ M ^ 2) {r : ℝ} (hr : r ≠ 0) :
    rnF M Q2 r = (r - rnRplus M Q2) * (r - rnRminus M Q2) / r ^ 2 := by
  have hs := Real.sq_sqrt (sub_nonneg.2 h)
  have e : rnF M Q2 r = (r ^ 2 - 2 * M * r + Q2) / r ^ 2 := by
    unfold rnF
    field_simp
    try ring
  rw [e]
  congr 1
  unfold rnRplus rnRminus
  linear_combination hs

/-- `Δ(r₊) = 0`. -/
theorem rnF_rplus {M Q2 : ℝ} (h : Q2 ≤ M ^ 2) (hr : rnRplus M Q2 ≠ 0) : rnF M Q2 (rnRplus M Q2) = 0 := by
  rw [rnF_eq_factor h hr]
  simp

/-- `Δ(r₋) = 0`. -/
theorem rnF_rminus {M Q2 : ℝ} (h : Q2 ≤ M ^ 2) (hr : rnRminus M Q2 ≠ 0) : rnF M Q2 (rnRminus M Q2) = 0 := by
  rw [rnF_eq_factor h hr]
  simp

/-- **The extremal case `M² = Q²`** (`M > 0`): the horizons coincide at `r = M`, `Δ = (1 − M/r)²`, and the
horizon is degenerate, `Δ(M) = Δ'(M) = 0` (Carroll p. 206: "Δ(r) = 0 at a single radius, r = GM"). -/
theorem rn_extremal {M Q2 : ℝ} (hM : 0 < M) (h : M ^ 2 = Q2) :
    rnRplus M Q2 = M ∧ rnRminus M Q2 = M ∧ (∀ r : ℝ, r ≠ 0 → rnF M Q2 r = (1 - M / r) ^ 2) ∧
      rnF M Q2 M = 0 ∧ rnF1 M Q2 M = 0 := by
  have h0 : M ^ 2 - Q2 = 0 := by linarith
  have hM0 : M ≠ 0 := hM.ne'
  refine ⟨by simp [rnRplus, h0], by simp [rnRminus, h0], fun r hr => ?_, ?_, ?_⟩
  · unfold rnF
    rw [← h]
    field_simp
    try ring
  · unfold rnF
    rw [← h]
    field_simp
    try ring
  · unfold rnF1
    rw [← h]
    field_simp
    try ring

/-- **In the extremal case `r` is never timelike** (Carroll p. 206: "the r coordinate is never timelike; it becomes null at
r = GM, but is spacelike on either side"): `Δ ≥ 0` everywhere, `Δ > 0` off `r = M`, so `g_rr = Δ⁻¹ > 0` off the horizon. -/
theorem rn_extremal_nonneg {M Q2 : ℝ} (h : M ^ 2 = Q2) {r : ℝ} (hr : r ≠ 0) :
    0 ≤ rnF M Q2 r ∧ (r ≠ M → 0 < rnF M Q2 r) := by
  have e : rnF M Q2 r = (1 - M / r) ^ 2 := by
    unfold rnF
    rw [← h]
    field_simp
    try ring
  rw [e]
  refine ⟨sq_nonneg _, fun hrM => ?_⟩
  have h0 : 1 - M / r ≠ 0 := by
    intro h0
    apply hrM
    have : M / r = 1 := by linarith
    field_simp at this
    linarith
  positivity

/-- **No horizon below the bound** (Carroll, Case One, p. 202): for `M² < Q²` the function `Δ` is
positive at every `r ≠ 0`, so the singularity at `r = 0` is not hidden by a horizon. -/
theorem rnF_pos_of_lt {M Q2 : ℝ} (h : M ^ 2 < Q2) {r : ℝ} (hr : r ≠ 0) : 0 < rnF M Q2 r := by
  have e : r ^ 2 * rnF M Q2 r = (r - M) ^ 2 + (Q2 - M ^ 2) := by
    unfold rnF; field_simp; ring
  have h2 : 0 < r ^ 2 := by positivity
  have h3 : 0 < (r - M) ^ 2 + (Q2 - M ^ 2) := by nlinarith [sq_nonneg (r - M)]
  rw [← e] at h3
  exact pos_of_mul_pos_right h3 h2.le

/-- **The classical extremality bound** (Carroll, pp. 202–206, Cases One–Three): `Δ` vanishes at some
`r > 0`, i.e. there is a horizon, iff `0 < M` and `Q² ≤ M²`, where `Q² = q² + p²`. -/
theorem rn_horizon_iff (M : ℝ) {Q2 : ℝ} (hQ : 0 ≤ Q2) :
    (∃ r, 0 < r ∧ rnF M Q2 r = 0) ↔ 0 < M ∧ Q2 ≤ M ^ 2 := by
  constructor
  · rintro ⟨r, hr, h0⟩
    have e : r ^ 2 - 2 * M * r + Q2 = r ^ 2 * rnF M Q2 r := by
      unfold rnF; field_simp
    rw [h0, mul_zero] at e
    refine ⟨?_, by nlinarith [sq_nonneg (r - M)]⟩
    by_contra hM
    have hM' : M ≤ 0 := not_lt.1 hM
    nlinarith [mul_nonneg (neg_nonneg.2 hM') hr.le, mul_pos hr hr]
  · rintro ⟨hM, h⟩
    have hpos : 0 < rnRplus M Q2 := by unfold rnRplus; positivity
    exact ⟨rnRplus M Q2, hpos, rnF_rplus h hpos.ne'⟩

/-- **The bound as `M ≥ |Q|`**, `|Q| = √(q² + p²)`: the Reissner–Nordström solution has a horizon iff
`0 < M` and `√(q² + p²) ≤ M`. -/
theorem rn_horizon_iff_sqrt (M q p : ℝ) :
    (∃ r, 0 < r ∧ rnF M (q ^ 2 + p ^ 2) r = 0) ↔ 0 < M ∧ √(q ^ 2 + p ^ 2) ≤ M := by
  rw [rn_horizon_iff M (by positivity)]
  constructor
  · rintro ⟨hM, h⟩
    exact ⟨hM, Real.sqrt_le_iff.2 ⟨hM.le, h⟩⟩
  · rintro ⟨hM, h⟩
    exact ⟨hM, (Real.sqrt_le_iff.1 h).2⟩

/-- **The bound is saturated exactly by the degenerate horizon**: `Δ` and `Δ'` vanish together at some
`r > 0` iff `0 < M` and `M² = Q²`; the double zero is then `r = M` (`rn_extremal`). -/
theorem rn_degenerate_iff (M Q2 : ℝ) :
    (∃ r, 0 < r ∧ rnF M Q2 r = 0 ∧ rnF1 M Q2 r = 0) ↔ 0 < M ∧ M ^ 2 = Q2 := by
  constructor
  · rintro ⟨r, hr, h0, h1⟩
    have e0 : r ^ 2 - 2 * M * r + Q2 = r ^ 2 * rnF M Q2 r := by
      unfold rnF; field_simp
    have e1 : 2 * M * r - 2 * Q2 = r ^ 3 * rnF1 M Q2 r := by
      unfold rnF1; field_simp
    rw [h0, mul_zero] at e0
    rw [h1, mul_zero] at e1
    have hQ : Q2 = M * r := by linarith
    have hrM : r = M := by
      have h' : r * (r - M) = 0 := by nlinarith
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' hr.ne'
      · linarith
    exact ⟨by rw [← hrM]; exact hr, by rw [hQ, hrM]; ring⟩
  · rintro ⟨hM, h⟩
    obtain ⟨-, -, -, h0, h1⟩ := rn_extremal hM h
    exact ⟨M, hM, h0, h1⟩

/-- The domain of the chart is nonempty for `Q² ≥ 0`: the point `t = 0`, `r = 2|M| + Q² + 1`,
`θ = π/2`, `φ = 0` lies in it. -/
theorem rnU_nonempty (M : ℝ) {Q2 : ℝ} (hQ : 0 ≤ Q2) : (rnU M Q2).Nonempty := by
  set r : ℝ := 2 * |M| + Q2 + 1 with hr
  have hr0 : 0 < r := by positivity
  refine ⟨![0, r, π / 2, 0], ?_⟩
  refine ⟨by simpa using hr0, ?_, by simpa using Real.pi_pos, by simp; linarith [Real.pi_pos]⟩
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  have e : r ^ 2 * rnF M Q2 r = r * (r - 2 * M) + Q2 := by
    unfold rnF; field_simp
  have h1 : 0 < r * (r - 2 * M) + Q2 := by
    have : 0 < r - 2 * M := by have := le_abs_self M; linarith
    positivity
  intro h0
  rw [h0, mul_zero] at e
  linarith

/-- **The surface gravity `Δ'(r₊)/2 = (r₊ − r₋)/(2r₊²)`**, zero exactly in the extremal case (`rn_extremal`).
Supporting lemma, not compared with a source. -/
theorem rn_surfaceGravity {M Q2 : ℝ} (h : Q2 ≤ M ^ 2) (hr : rnRplus M Q2 ≠ 0) :
    rnF1 M Q2 (rnRplus M Q2) / 2 = (rnRplus M Q2 - rnRminus M Q2) / (2 * rnRplus M Q2 ^ 2) := by
  have hs := Real.sq_sqrt (sub_nonneg.2 h)
  unfold rnF1 rnRminus
  unfold rnRplus at hr ⊢
  generalize √(M ^ 2 - Q2) = t at hs hr ⊢
  have hQ : Q2 = M ^ 2 - t ^ 2 := by linarith
  subst hQ
  field_simp
  ring

/-! ## Trust checks -/

/-- **`q = p = 0` is Schwarzschild** with vanishing field. -/
theorem rn_schwarzschild (M : ℝ) (y : Fin 4 → ℝ) :
    rnMetric M (0 ^ 2 + 0 ^ 2) y = schMetric M y ∧ rnField 0 0 y = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [ssMetric, schMetric, schD, rnF]
    congr 1
    ext i
    fin_cases i <;> simp
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rnField]

/-- **Wrong-model control**: with `q² + p² ≠ 0` the Reissner–Nordström metric is not a vacuum solution
(`R_θθ = Q²/r² ≠ 0`). -/
theorem rn_not_vacuum (M q p : ℝ) (hQ : q ^ 2 + p ^ 2 ≠ 0) :
    ¬ IsVacuumSolution 0 (rnMetric M (q ^ 2 + p ^ 2)) (rnU M (q ^ 2 + p ^ 2)) := by
  intro h
  obtain ⟨y, hy⟩ := rnU_nonempty M (Q2 := q ^ 2 + p ^ 2) (by positivity)
  have hr : y 1 ≠ 0 := hy.1.ne'
  have := h.2 y hy 2 2
  rw [einsteinTensor_rn _ _ hy] at this
  simp [rnRicci, diagonal_apply] at this
  rcases this with h1 | h1
  · exact hQ h1
  · exact hr h1

end Lightlike
