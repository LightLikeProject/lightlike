module

public import Lightlike.GR.Schwarzschild
public import Lightlike.Spacetime.RiemannSymmetry

/-!
# Non-trivial tests of the coordinate curvature definitions

Flat Minkowski space cannot detect wrong curvature definitions (any formula built from derivatives
of the metric vanishes for a constant metric). These are **Lean proofs** (kernel-checked, no `sorry`)
that the definitions in `Lightlike/Spacetime/Curvature.lean` and `Lightlike/GR/Einstein.lean` give
the textbook answers on curved metrics. Every hand-derived Christoffel symbol is *proven* equal to
the definition (`christoffel_two`, `christoffel_sch`, `christoffel_wsch`), so no hand computation is
trusted.

* (a) `sphere_scalar` - round 2-sphere of radius `r`: scalar curvature `2/r²`
  (plus `ricci_two`, `riemann_two_0101`: full Ricci tensor and `R^θ_{φθφ}` of the family
  `A dθ² + B sin²θ dφ²`, `scalar_two`: `R = 2/A`).
* (b) Riemann symmetries: now library theorems in `Lightlike/Spacetime/RiemannSymmetry.lean`
  (all four symmetries, unconditional for coordinate metrics).
* (c) Schwarzschild is Ricci-flat: now library theorems in `Lightlike/GR/Schwarzschild.lean`
  (`ricci_sch`, `einstein_sch_exterior`, `sch_isVacuumSolution`).
* (c') **wrong Schwarzschild** - `g_rr = 1 - 2M/r` instead of `(1 - 2M/r)⁻¹`: `ricci_wsch` gives
  all 16 Ricci components (`R_θθ = -2M/(r - 2M)`), `wsch_ricci_ne_zero`, and
  `wsch_not_isVacuumSolution` (it is a coordinate metric on `r > 2M`, `isCoordMetric_wsch`, but
  not a vacuum solution).
* (d) `flipped_θθ_scalar`, `flipped_φφ` - sign-flipped spheres: flipping `g_θθ` changes `R`
  to `-2/r²`; flipping `g_φφ` leaves `R = 2/r²` (correct: `R = 2/g_θθ` for this family) but flips
  `R_φφ`.
* Rejection tests: the zero matrix (`zero_not_isCoordMetric`) and any domain touching the
  Schwarzschild horizon `r = 2M` (`sch_not_isCoordMetric_at_horizon`) are rejected by
  `IsCoordMetric`, although Lean's junk conventions would give them curvature values.
-/

@[expose] public section

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike.Test

variable {n : ℕ}

/-! ## Degenerate "metrics" are rejected by the predicates -/

/-- The zero matrix is not a coordinate metric on any nonempty set (`n ≥ 1`). Without this
check it would be a "vacuum solution": its Lean inverse is `0`, so all its curvature is `0`. -/
theorem zero_not_isCoordMetric (hn : 0 < n) {U : Set (Fin n → ℝ)} (hU : U.Nonempty) :
    ¬ IsCoordMetric (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) U := by
  rintro ⟨-, -, hdet, -⟩
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa [Matrix.det_zero] using hdet x hx

/-- **Rejection test.** The zero matrix is not a vacuum solution on any nonempty set (it is not a
coordinate metric), although its junk Einstein tensor vanishes (`zero_einsteinTensor`). -/
theorem zero_not_isVacuumSolution (hn : 0 < n) {U : Set (Fin n → ℝ)} (hU : U.Nonempty) (Λ : ℝ) :
    ¬ IsVacuumSolution Λ (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) U :=
  fun h => zero_not_isCoordMetric hn hU h.1

/-- …even though its Einstein tensor is identically `0` (the junk value the predicate guards
against). -/
theorem zero_einsteinTensor (μ ν : Fin n) (x : Fin n → ℝ) :
    einsteinTensor (fun _ => (0 : Matrix (Fin n) (Fin n) ℝ)) μ ν x = 0 :=
  einsteinTensor_eq_zero_of_riemann_eq_zero (fun ρ σ μ ν => riemann_const 0 ρ σ μ ν x) μ ν

/-! ## Test (a) + (d): metrics `diag(A, B sin²θ)` on coordinates `(θ, φ)` -/

/-- `ds² = A dθ² + B sin²θ dφ²`. The round sphere of radius `r` is `A = B = r²`.
Flipping one sign gives `B = -r²` or `A = -r²`. -/
def twoD (A B : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![A, B * sin (y 0) ^ 2]

/-- The metric `A dθ² + B sin²θ dφ²` in coordinates `(θ, φ)`. -/
def twoMetric (A B : ℝ) : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ := fun y => diagonal (twoD A B y)

/-- Expected Christoffel symbols (computed by hand):
`Γ^θ_{φφ} = -(B/A) sinθ cosθ`, `Γ^φ_{θφ} = Γ^φ_{φθ} = cotθ`, all others `0`. -/
def twoΓ (A B : ℝ) (i j k : Fin 2) (y : Fin 2 → ℝ) : ℝ :=
  if i = 0 ∧ j = 1 ∧ k = 1 then -(B / A) * (sin (y 0) * cos (y 0))
  else if i = 1 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then cos (y 0) / sin (y 0)
  else 0

lemma pd_twoD0 (A B : ℝ) (k : Fin 2) (y : Fin 2 → ℝ) : pd k (fun y => twoD A B y 0) y = 0 := by
  simp [twoD, pd_const]

lemma pd_twoD1 (B : ℝ) (k : Fin 2) (y : Fin 2 → ℝ) :
    pd k (fun y => B * sin (y 0) ^ 2) y = if k = 0 then B * (2 * sin (y 0) * cos (y 0)) else 0 := by
  have hf : HasDerivAt (fun θ => B * sin θ ^ 2) (B * (2 * sin (y 0) * cos (y 0))) (y 0) := by
    have := ((Real.hasDerivAt_sin (y 0)).pow 2).const_mul B
    convert this using 1; push_cast; ring
  simpa using pd_coord (n := 2) 0 k hf

lemma christoffel_two {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) {y : Fin 2 → ℝ} (hy : sin (y 0) ≠ 0)
    (i j k : Fin 2) : christoffel (twoMetric A B) i j k y = twoΓ A B i j k y := by
  have hd : ∀ i, twoD A B y i ≠ 0 := by
    intro i; fin_cases i <;> simp [twoD, hA, hB, hy]
  change christoffel (fun y => diagonal (twoD A B y)) i j k y = _
  rw [christoffel_diagonal _ y hd]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [twoΓ, pd_const, pd_twoD1, twoD] <;> field_simp

/-- `θ`-derivatives of the expected Christoffel symbols. -/
def twoDΓ (A B : ℝ) (i j k : Fin 2) (y : Fin 2 → ℝ) : ℝ :=
  if i = 0 ∧ j = 1 ∧ k = 1 then -(B / A) * (cos (y 0) ^ 2 - sin (y 0) ^ 2)
  else if i = 1 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then -1 / sin (y 0) ^ 2
  else 0

lemma pd_twoΓ (A B : ℝ) {x : Fin 2 → ℝ} (hx : sin (x 0) ≠ 0) (m i j k : Fin 2) :
    pd m (fun y => twoΓ A B i j k y) x = if m = 0 then twoDΓ A B i j k x else 0 := by
  have h1 : HasDerivAt (fun θ => -(B / A) * (sin θ * cos θ))
      (-(B / A) * (cos (x 0) ^ 2 - sin (x 0) ^ 2)) (x 0) := by
    have := ((Real.hasDerivAt_sin (x 0)).mul (Real.hasDerivAt_cos (x 0))).const_mul (-(B / A))
    convert this using 1; ring
  have h2 : HasDerivAt (fun θ => cos θ / sin θ) (-1 / sin (x 0) ^ 2) (x 0) := by
    have := (Real.hasDerivAt_cos (x 0)).div (Real.hasDerivAt_sin (x 0)) hx
    convert this using 1
    field_simp
    nlinarith [sin_sq_add_cos_sq (x 0)]
  have hc1 := pd_coord (n := 2) 0 m h1
  have hc2 := pd_coord (n := 2) 0 m h2
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [twoΓ, twoDΓ] <;> (try simp) <;> first | simpa using hc1 | simpa using hc2 | simp [pd_const]

lemma pd_christoffel_two {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) {x : Fin 2 → ℝ}
    (hx : sin (x 0) ≠ 0) (m i j k : Fin 2) :
    pd m (christoffel (twoMetric A B) i j k) x = if m = 0 then twoDΓ A B i j k x else 0 := by
  have hopen : IsOpen {y : Fin 2 → ℝ | sin (y 0) ≠ 0} :=
    isOpen_ne_fun (continuous_sin.comp (continuous_apply 0)) continuous_const
  have hev : christoffel (twoMetric A B) i j k =ᶠ[nhds x] twoΓ A B i j k :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => christoffel_two hA hB hy i j k
  rw [pd_congr hev, pd_twoΓ A B hx]

lemma inv_twoMetric {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) {x : Fin 2 → ℝ} (hx : sin (x 0) ≠ 0) :
    (twoMetric A B x)⁻¹ = diagonal ![A⁻¹, (B * sin (x 0) ^ 2)⁻¹] := by
  rw [twoMetric, inv_diagonal_of_ne]
  · congr 1; ext i; fin_cases i <;> simp [twoD]
  · intro i; fin_cases i <;> simp [twoD, hA, hB, hx]

/-- The `R^θ_{φθφ}` component: `(B/A) sin²θ`. -/
theorem riemann_two_0101 {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) {x : Fin 2 → ℝ}
    (hx : sin (x 0) ≠ 0) : riemann (twoMetric A B) 0 1 0 1 x = (B / A) * sin (x 0) ^ 2 := by
  simp [riemann, pd_christoffel_two hA hB hx, christoffel_two hA hB hx,
    twoΓ, twoDΓ]
  field_simp
  ring

/-- Ricci components of `diag(A, B sin²θ)`: `R_θθ = 1`, `R_φφ = (B/A) sin²θ`, off-diagonal `0`. -/
theorem ricci_two {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) {x : Fin 2 → ℝ} (hx : sin (x 0) ≠ 0) :
    ricci (twoMetric A B) 0 0 x = 1 ∧ ricci (twoMetric A B) 1 1 x = (B / A) * sin (x 0) ^ 2 ∧
    ricci (twoMetric A B) 0 1 x = 0 ∧ ricci (twoMetric A B) 1 0 x = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [ricci, riemann, Fin.sum_univ_two, pd_christoffel_two hA hB hx,
      christoffel_two hA hB hx, twoΓ, twoDΓ]
    try field_simp
    try nlinarith [sin_sq_add_cos_sq (x 0)]

/-- Scalar curvature of `diag(A, B sin²θ)` is `2 / A`. -/
theorem scalar_two {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) {x : Fin 2 → ℝ} (hx : sin (x 0) ≠ 0) :
    scalarCurvature (twoMetric A B) x = 2 / A := by
  obtain ⟨h00, h11, h01, h10⟩ := ricci_two hA hB hx
  simp only [scalarCurvature, Fin.sum_univ_two, inv_twoMetric hA hB hx, h00, h11, h01, h10]
  simp
  field_simp
  ring

/-- Coordinate domain of the sphere chart: `0 < θ < π`. -/
def sphereU : Set (Fin 2 → ℝ) := {y | 0 < y 0 ∧ y 0 < π}

lemma sin_ne_zero_of_mem_sphereU {y : Fin 2 → ℝ} (hy : y ∈ sphereU) : sin (y 0) ≠ 0 :=
  (sin_pos_of_pos_of_lt_pi hy.1 hy.2).ne'

/-- `diag(A, B sin²θ)` is a coordinate metric (smooth, symmetric, invertible) on `0 < θ < π`. -/
theorem isCoordMetric_two {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) :
    IsCoordMetric (twoMetric A B) sphereU := by
  refine isCoordMetric_diagonal (twoD A B)
    ((isOpen_lt continuous_const (continuous_apply 0)).inter
      (isOpen_lt (continuous_apply 0) continuous_const)) (fun i => ?_) (fun x hx i => ?_)
  · fin_cases i
    · exact contDiffOn_const
    · exact (contDiff_const.mul ((Real.contDiff_sin.comp (by fun_prop : ContDiff ℝ ∞ fun y : Fin 2 → ℝ => y 0)).pow 2)).contDiffOn
  · fin_cases i <;> simp [twoD, hA, hB, sin_ne_zero_of_mem_sphereU hx]

/-- **Test (a).** Round 2-sphere of radius `r`: scalar curvature `2/r²`. -/
theorem sphere_scalar {r : ℝ} (hr : r ≠ 0) {x : Fin 2 → ℝ} (hx : sin (x 0) ≠ 0) :
    scalarCurvature (twoMetric (r ^ 2) (r ^ 2)) x = 2 / r ^ 2 :=
  scalar_two (pow_ne_zero 2 hr) (pow_ne_zero 2 hr) hx

/-- **Test (a), domain form.** The round sphere is a coordinate metric on `0 < θ < π` and its
scalar curvature is `2/r²` at every point of that domain. -/
theorem sphere_scalar_on {r : ℝ} (hr : r ≠ 0) :
    IsCoordMetric (twoMetric (r ^ 2) (r ^ 2)) sphereU ∧
      ∀ x ∈ sphereU, scalarCurvature (twoMetric (r ^ 2) (r ^ 2)) x = 2 / r ^ 2 :=
  ⟨isCoordMetric_two (pow_ne_zero 2 hr) (pow_ne_zero 2 hr),
    fun _ hx => sphere_scalar hr (sin_ne_zero_of_mem_sphereU hx)⟩

/-- **Test (d1).** Flip the sign of `g_θθ`: scalar curvature becomes `-2/r² ≠ 2/r²`. -/
theorem flipped_θθ_scalar {r : ℝ} (hr : r ≠ 0) {x : Fin 2 → ℝ} (hx : sin (x 0) ≠ 0) :
    scalarCurvature (twoMetric (-r ^ 2) (r ^ 2)) x = -(2 / r ^ 2) ∧
    scalarCurvature (twoMetric (-r ^ 2) (r ^ 2)) x ≠ scalarCurvature (twoMetric (r ^ 2) (r ^ 2)) x := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [scalar_two (neg_ne_zero.mpr hr2) hr2 hx, sphere_scalar hr hx]
  refine ⟨by ring, ?_⟩
  have : 0 < 2 / r ^ 2 := by positivity
  intro h; linarith [show 2 / -r ^ 2 = -(2 / r ^ 2) by ring]

/-- **Test (d2).** Flip the sign of `g_φφ` (a 2D Lorentzian metric): the *scalar* curvature is
still `2/r²` (this is correct, not a bug: `R = 2/g_θθ` for this family), but the Ricci tensor
differs: `R_φφ = -sin²θ` instead of `+sin²θ`. -/
theorem flipped_φφ {r : ℝ} (hr : r ≠ 0) {x : Fin 2 → ℝ} (hx : sin (x 0) ≠ 0) :
    scalarCurvature (twoMetric (r ^ 2) (-r ^ 2)) x = 2 / r ^ 2 ∧
    ricci (twoMetric (r ^ 2) (-r ^ 2)) 1 1 x = -sin (x 0) ^ 2 ∧
    ricci (twoMetric (r ^ 2) (r ^ 2)) 1 1 x = sin (x 0) ^ 2 := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  refine ⟨scalar_two hr2 (neg_ne_zero.mpr hr2) hx, ?_, ?_⟩
  · rw [(ricci_two hr2 (neg_ne_zero.mpr hr2) hx).2.1]; field_simp
  · rw [(ricci_two hr2 hr2 hx).2.1]; field_simp

/-! ## Test (b): symmetries of the Riemann tensor

Moved to the library: `Lightlike/Spacetime/RiemannSymmetry.lean` proves, for every coordinate
metric, last-pair and first-pair antisymmetry, the first Bianchi identity and pair symmetry. -/

/-! ## Schwarzschild: negative tests and signature of Minkowski

The Schwarzschild theorems themselves are in `Lightlike/GR/Schwarzschild.lean`. -/

section Schwarzschild

variable (M : ℝ)

/-- Minkowski components have Lorentzian signature (`P = 1`). -/
theorem minkowski_isLorentzian (x₀ : Fin n → ℝ) :
    IsLorentzianCoordMetric ((minkowskiMetric n).coordMetric x₀) Set.univ :=
  ⟨minkowski_isCoordMetric x₀, fun x _ => ⟨1, by simp, by simp [minkowski_coordMetric]⟩⟩

/-- **Junk trap at the horizon.** Any set containing a point with `r = 2M` (`M ≠ 0`) is rejected:
there `1 - 2M/r = 0`, Lean evaluates `g_rr = 0⁻¹ = 0`, and the matrix is singular. Without the
`IsCoordMetric` hypothesis, curvature at `r = 2M` would be silently computed from this junk. -/
theorem sch_not_isCoordMetric_at_horizon (hM : M ≠ 0) {U : Set (Fin 4 → ℝ)}
    (hU : ∃ y ∈ U, y 1 = 2 * M) : ¬ IsCoordMetric (schMetric M) U := by
  rintro ⟨-, -, hdet, -⟩
  obtain ⟨y, hy, hr⟩ := hU
  have := hdet y hy
  have h2M : (2 * M) ≠ 0 := mul_ne_zero two_ne_zero hM
  simp [schMetric, Matrix.det_diagonal, Fin.prod_univ_four, schD, hr, h2M] at this

/-! ### Negative test: a wrong Schwarzschild metric is not Ricci-flat

The wrong metric has `g_rr = 1 - 2M/r` instead of `(1 - 2M/r)⁻¹` (wrong power). It is a genuine
coordinate metric on the exterior (`isCoordMetric_wsch`), so it fails the vacuum equations because
of its curvature, not because of a junk value. SymPy cross-check, with Schwarzschild as the
control: `scripts/wrong_schwarzschild_check.py`. -/

/-- The wrong metric `diag(-(1-2M/r), 1-2M/r, r², r² sin²θ)`. -/
def wschD (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-(1 - 2 * M / y 1), 1 - 2 * M / y 1, y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The wrong Schwarzschild metric (`g_rr = 1 - 2M/r`) as a matrix-valued function. -/
def wschMetric : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := fun y => diagonal (wschD M y)

/-- Coordinate derivatives `∂_k g_ii` of the wrong metric. -/
def wschDD (k i : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 then (if k = 1 then -(2 * M / y 1 ^ 2) else 0)
  else if i = 1 then (if k = 1 then 2 * M / y 1 ^ 2 else 0)
  else if i = 2 then (if k = 1 then 2 * y 1 else 0)
  else (if k = 1 then 2 * y 1 else 0) * sin (y 2) ^ 2 +
    y 1 ^ 2 * (if k = 2 then 2 * sin (y 2) * cos (y 2) else 0)

lemma pd_wschD {y : Fin 4 → ℝ} (h1 : y 1 ≠ 0) (k i : Fin 4) :
    pd k (fun y => wschD M y i) y = wschDD M k i y := by
  have hb : HasDerivAt (fun r => 1 - 2 * M / r) (2 * M / y 1 ^ 2) (y 1) :=
    (((hasDerivAt_const (y 1) (2 * M)).div (hasDerivAt_id' (y 1)) h1).const_sub 1).congr_deriv
      (by ring)
  have e0 : HasDerivAt (fun r => -(1 - 2 * M / r)) (-(2 * M / y 1 ^ 2)) (y 1) := hb.neg
  have e2 : HasDerivAt (fun r => r ^ 2) (2 * y 1) (y 1) := by
    simpa using (hasDerivAt_pow 2 (y 1))
  have e3 : HasDerivAt (fun θ => sin θ ^ 2) (2 * sin (y 2) * cos (y 2)) (y 2) := by
    convert (Real.hasDerivAt_sin (y 2)).pow 2 using 1; push_cast; ring
  have c0 := pd_coord (n := 4) 1 k e0
  have c1 := pd_coord (n := 4) 1 k hb
  have c2 := pd_coord (n := 4) 1 k e2
  have c3 := pd_coord_mul (n := 4) 1 2 k e2 e3
  fin_cases i <;> simp only [wschD, wschDD] <;> simp <;>
    first
    | simpa using c0
    | simpa using c1
    | simpa using c2
    | simpa using c3

/-- Christoffel symbols of the wrong metric (hand computation, proven below). -/
def wschΓ (i j k : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then M / (y 1 * (y 1 - 2 * M))
  else if i = 1 ∧ j = 0 ∧ k = 0 then M / (y 1 * (y 1 - 2 * M))
  else if i = 1 ∧ j = 1 ∧ k = 1 then M / (y 1 * (y 1 - 2 * M))
  else if i = 1 ∧ j = 2 ∧ k = 2 then -(y 1 ^ 2 / (y 1 - 2 * M))
  else if i = 1 ∧ j = 3 ∧ k = 3 then -(y 1 ^ 2 / (y 1 - 2 * M)) * sin (y 2) ^ 2
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then 1 / y 1
  else if i = 2 ∧ j = 3 ∧ k = 3 then -(sin (y 2) * cos (y 2))
  else if i = 3 ∧ ((j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1)) then 1 / y 1
  else if i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) then cos (y 2) / sin (y 2)
  else 0

/-- The Christoffel symbols of the wrong Schwarzschild metric equal the hand-computed `wschΓ` on
the chart region. -/
lemma christoffel_wsch {y : Fin 4 → ℝ} (hy : y ∈ schRegion M) (i j k : Fin 4) :
    christoffel (wschMetric M) i j k y = wschΓ M i j k y := by
  obtain ⟨h1, h2, h3⟩ := hy
  have h1' : y 1 ≠ 0 := h1.ne'
  have hf : 1 - 2 * M / y 1 ≠ 0 := by
    rw [one_sub_div h1']; exact div_ne_zero h2 h1'
  have h2b : 2 * M - y 1 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - y 1 ≠ 0 := fun h => h2 (by linarith)
  have h2d : y 1 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have hd : ∀ i, wschD M y i ≠ 0 := by
    intro i; fin_cases i <;> simp [wschD, h1', hf, h3]; intro h; apply hf; linarith
  change christoffel (fun y => diagonal (wschD M y)) i j k y = _
  rw [christoffel_diagonal _ y hd]
  simp only [pd_wschD M h1']
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [wschΓ, wschDD, wschD] <;> field_simp <;> ring

/-- Coordinate derivatives of the wrong metric's Christoffel symbols. -/
def wschDΓ (m i j k : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then
    (if m = 1 then -(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2 else 0)
  else if i = 1 ∧ j = 0 ∧ k = 0 then
    (if m = 1 then -(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2 else 0)
  else if i = 1 ∧ j = 1 ∧ k = 1 then
    (if m = 1 then -(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2 else 0)
  else if i = 1 ∧ j = 2 ∧ k = 2 then
    (if m = 1 then -(x 1 * (x 1 - 4 * M)) / (x 1 - 2 * M) ^ 2 else 0)
  else if i = 1 ∧ j = 3 ∧ k = 3 then
    (if m = 1 then -(x 1 * (x 1 - 4 * M)) / (x 1 - 2 * M) ^ 2 else 0) * sin (x 2) ^ 2 +
      -(x 1 ^ 2 / (x 1 - 2 * M)) * (if m = 2 then 2 * sin (x 2) * cos (x 2) else 0)
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then (if m = 1 then -1 / x 1 ^ 2 else 0)
  else if i = 2 ∧ j = 3 ∧ k = 3 then
    (if m = 2 then -(cos (x 2) ^ 2 - sin (x 2) ^ 2) else 0)
  else if i = 3 ∧ ((j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1)) then (if m = 1 then -1 / x 1 ^ 2 else 0)
  else if i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) then
    (if m = 2 then -1 / sin (x 2) ^ 2 else 0)
  else 0

lemma pd_wschΓ {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (m i j k : Fin 4) :
    pd m (fun y => wschΓ M i j k y) x = wschDΓ M m i j k x := by
  obtain ⟨h1, h2, h3⟩ := hx
  have h1' : x 1 ≠ 0 := h1.ne'
  have hq : x 1 * (x 1 - 2 * M) ≠ 0 := mul_ne_zero h1' h2
  have hlin : HasDerivAt (fun r => r * (r - 2 * M)) (2 * x 1 - 2 * M) (x 1) :=
    ((hasDerivAt_id' (x 1)).mul ((hasDerivAt_id' (x 1)).sub_const (2 * M))).congr_deriv (by ring)
  have d1 : HasDerivAt (fun r => M / (r * (r - 2 * M)))
      (-(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2) (x 1) :=
    ((hasDerivAt_const (x 1) M).div hlin hq).congr_deriv (by ring)
  have e2 : HasDerivAt (fun r => r ^ 2) (2 * x 1) (x 1) := by
    simpa using (hasDerivAt_pow 2 (x 1))
  have d9 : HasDerivAt (fun r => -(r ^ 2 / (r - 2 * M)))
      (-(x 1 * (x 1 - 4 * M)) / (x 1 - 2 * M) ^ 2) (x 1) :=
    (e2.div ((hasDerivAt_id' (x 1)).sub_const (2 * M)) h2).neg.congr_deriv (by ring)
  have d5 : HasDerivAt (fun r => 1 / r) (-1 / x 1 ^ 2) (x 1) :=
    ((hasDerivAt_const (x 1) (1 : ℝ)).div (hasDerivAt_id' (x 1)) h1').congr_deriv (by ring)
  have d6 : HasDerivAt (fun θ => sin θ ^ 2) (2 * sin (x 2) * cos (x 2)) (x 2) := by
    convert (Real.hasDerivAt_sin (x 2)).pow 2 using 1; push_cast; ring
  have d7 : HasDerivAt (fun θ => -(sin θ * cos θ)) (-(cos (x 2) ^ 2 - sin (x 2) ^ 2)) (x 2) := by
    convert ((Real.hasDerivAt_sin (x 2)).mul (Real.hasDerivAt_cos (x 2))).neg using 1; ring
  have d8 : HasDerivAt (fun θ => cos θ / sin θ) (-1 / sin (x 2) ^ 2) (x 2) := by
    convert (Real.hasDerivAt_cos (x 2)).div (Real.hasDerivAt_sin (x 2)) h3 using 1
    field_simp; nlinarith [sin_sq_add_cos_sq (x 2)]
  have c1 := pd_coord (n := 4) 1 m d1
  have c9 := pd_coord (n := 4) 1 m d9
  have c5 := pd_coord (n := 4) 1 m d5
  have c10 := pd_coord_mul (n := 4) 1 2 m d9 d6
  have c7 := pd_coord (n := 4) 2 m d7
  have c8 := pd_coord (n := 4) 2 m d8
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [wschΓ, wschDΓ] <;> (try simp) <;>
    first
    | simpa using c1
    | simpa using c9
    | simpa using c5
    | simpa using c10
    | simpa using c7
    | simpa using c8
    | simp [pd_const]

lemma pd_christoffel_wsch {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (m i j k : Fin 4) :
    pd m (christoffel (wschMetric M) i j k) x = wschDΓ M m i j k x := by
  have hev : christoffel (wschMetric M) i j k =ᶠ[nhds x] fun y => wschΓ M i j k y :=
    Filter.eventually_of_mem ((schRegion_open M).mem_nhds hx) fun y hy =>
      christoffel_wsch M hy i j k
  rw [pd_congr hev, pd_wschΓ M hx]

/-- The Ricci tensor of the wrong metric (SymPy: `scripts/wrong_schwarzschild_check.py`). -/
def wschRic (σ ν : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if σ = 0 ∧ ν = 0 then -(2 * M ^ 2) / (x 1 ^ 2 * (x 1 - 2 * M) ^ 2)
  else if σ = 1 ∧ ν = 1 then 2 * M * (2 * x 1 - 3 * M) / (x 1 ^ 2 * (x 1 - 2 * M) ^ 2)
  else if σ = 2 ∧ ν = 2 then -(2 * M) / (x 1 - 2 * M)
  else if σ = 3 ∧ ν = 3 then -(2 * M) * sin (x 2) ^ 2 / (x 1 - 2 * M)
  else 0

/-- **Negative test, full form.** The Ricci tensor of the wrong metric, all 16 components. -/
theorem ricci_wsch {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (σ ν : Fin 4) :
    ricci (wschMetric M) σ ν x = wschRic M σ ν x := by
  have hx' := hx
  obtain ⟨h1, h2, h3⟩ := hx'
  have h1' : x 1 ≠ 0 := h1.ne'
  have hc : cos (x 2) ^ 2 = 1 - sin (x 2) ^ 2 := cos_sq' _
  have h2b : 2 * M - x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2d : x 1 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have h2e : -(M * 2) + x 1 ≠ 0 := fun h => h2 (by linarith)
  have h2f : x 1 + -(M * 2) ≠ 0 := fun h => h2 (by linarith)
  have h2g : -(2 * M) + x 1 ≠ 0 := fun h => h2 (by linarith)
  fin_cases σ <;> fin_cases ν <;>
    simp [ricci, riemann, Fin.sum_univ_four, pd_christoffel_wsch M hx, christoffel_wsch M hx,
      wschΓ, wschDΓ, wschRic] <;> field_simp <;> (try simp only [hc]) <;> ring

/-- **Negative test.** With the wrong `g_rr`, `R_θθ = -2M/(r - 2M) ≠ 0` (for `M ≠ 0`), at every
point of the chart region. -/
theorem wsch_ricci_ne_zero (hM : M ≠ 0) {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) :
    ricci (wschMetric M) 2 2 x ≠ 0 := by
  rw [ricci_wsch M hx]
  simp only [wschRic]
  norm_num
  exact ⟨hM, hx.2.1⟩

/-- The wrong metric is still a coordinate metric on the exterior (so the failure below is
curvature, not a junk value). -/
theorem isCoordMetric_wsch (hM : 0 < M) : IsCoordMetric (wschMetric M) (schU M) := by
  have hopen : IsOpen (schU M) :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const))
  have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 1) (schU M) :=
    (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
  have hθ : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 2) := by fun_prop
  have hr0 : ∀ y ∈ schU M, y 1 ≠ 0 := fun y hy => by have := hy.1; linarith
  have hf0 : ∀ y ∈ schU M, 1 - 2 * M / y 1 ≠ 0 := fun y hy => by
    have h1 : 0 < y 1 := by have := hy.1; linarith
    rw [one_sub_div h1.ne']; exact div_ne_zero (by linarith [hy.1]) h1.ne'
  have hfs : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => 1 - 2 * M / y 1) (schU M) :=
    contDiffOn_const.sub (contDiffOn_const.div hr hr0)
  refine isCoordMetric_diagonal (wschD M) hopen (fun i => ?_) (fun y hy i => ?_)
  · fin_cases i
    · exact hfs.neg
    · exact hfs
    · exact hr.pow 2
    · exact (hr.pow 2).mul ((Real.contDiff_sin.comp hθ).pow 2).contDiffOn
  · have hs := (schU_subset M hM hy).2.2
    fin_cases i <;> simp [wschD, hr0 y hy, hf0 y hy, hs]
    · intro h; apply hf0 y hy; linarith

/-- **Negative test, domain form.** Contrast with `sch_isVacuumSolution`: the wrong metric is a
coordinate metric on the exterior but does **not** solve the vacuum Einstein equations there. -/
theorem wsch_not_isVacuumSolution (hM : 0 < M) : ¬ IsVacuumSolution 0 (wschMetric M) (schU M) := by
  intro hvac
  have hx : (![0, 3 * M, π / 2, 0] : Fin 4 → ℝ) ∈ schU M := by
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith [pi_pos]
  have h0 := (vacuum_iff_ricci_eq_zero (by norm_num) hvac.1).mp hvac _ hx 2 2
  exact wsch_ricci_ne_zero M hM.ne' (schU_subset M hM hx) h0

end Schwarzschild

end Lightlike.Test

