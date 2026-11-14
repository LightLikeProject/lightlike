module

public import Lightlike.GR.Einstein

/-!
# The Schwarzschild solution

Schwarzschild in coordinates `(t, r, θ, φ)`:
`ds² = -(1-2M/r) dt² + (1-2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`.

* `christoffel_sch`: its Christoffel symbols, **proven** equal to the definition (no hand
  computation is trusted).
* `ricci_sch`, `einstein_sch`, `einstein_sch_exterior`: all 16 Ricci components vanish, so
  `G_{μν} = 0`, wherever the chart is valid (`r > 0`, `r ≠ 2M`, `sin θ ≠ 0`).
* `isCoordMetric_sch`, `sch_isVacuumSolution`, `sch_isLorentzian`: on the exterior `r > 2M`,
  `0 < θ < π` (`M > 0`) it is a smooth, invertible coordinate metric of Lorentzian signature that
  solves the vacuum Einstein equations.

The calculus helpers for diagonal metrics (`christoffel_diagonal`, `pd_coord`, …) are shared with
the curvature tests (`Lightlike/Tests/Curvature.lean`), which also hold the negative tests: the
horizon `r = 2M` is rejected, and a wrong Schwarzschild metric is shown **not** Ricci-flat.
-/

@[expose] public section

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-! ## Calculus helpers for diagonal metrics -/

lemma pd_congr {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h : f =ᶠ[nhds x] g) (k : Fin n) :
    pd k f x = pd k g x := by
  simp only [pd, h.fderiv_eq]

lemma pd_coord {f : ℝ → ℝ} {f' : ℝ} (i k : Fin n) {x : Fin n → ℝ} (hf : HasDerivAt f f' (x i)) :
    pd k (fun y => f (y i)) x = if k = i then f' else 0 := by
  have h : HasFDerivAt (fun y : Fin n → ℝ => f (y i)) (f' • ContinuousLinearMap.proj i) x :=
    have hp : HasFDerivAt (fun y : Fin n → ℝ => y i) (ContinuousLinearMap.proj i) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
    hf.comp_hasFDerivAt x hp
  simp only [pd, h.fderiv]
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]

lemma pd_ite (p : Prop) [Decidable p] (k : Fin n) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    pd k (fun y => if p then f y else 0) x = if p then pd k f x else 0 := by
  split_ifs <;> simp [pd]

lemma inv_diagonal_of_ne {d : Fin n → ℝ} (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases h : i = j
  · subst h; simp [hd]
  · simp [h, one_apply]

/-- Christoffel symbols of a diagonal metric `g = diag(d₀, …, d_{n-1})`. -/
lemma christoffel_diagonal (d : (Fin n → ℝ) → Fin n → ℝ) (y : Fin n → ℝ)
    (hd : ∀ i, d y i ≠ 0) (i j k : Fin n) :
    christoffel (fun y => diagonal (d y)) i j k y =
      (1 / 2) * (d y i)⁻¹ * ((if i = k then pd j (fun y => d y i) y else 0) +
        (if i = j then pd k (fun y => d y i) y else 0) -
        (if j = k then pd i (fun y => d y j) y else 0)) := by
  have hdiag : ∀ a b : Fin n, (fun y => diagonal (d y) a b) = fun y => if a = b then d y a else 0 := by
    intro a b; funext y; simp [diagonal_apply]
  simp only [christoffel, inv_diagonal_of_ne hd, hdiag, pd_ite]
  rw [Finset.sum_eq_single i]
  · simp only [diagonal_apply_eq]
    by_cases hik : i = k <;> by_cases hij : i = j <;> simp_all [eq_comm] <;> ring_nf
  · intro l _ hl; simp [Ne.symm hl]
  · simp

/-! ## Schwarzschild solves the vacuum equations -/

section Schwarzschild

lemma hasFDerivAt_coord {f : ℝ → ℝ} {f' : ℝ} (i : Fin n) {x : Fin n → ℝ}
    (hf : HasDerivAt f f' (x i)) :
    HasFDerivAt (fun y : Fin n → ℝ => f (y i))
      (f' • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have hp : HasFDerivAt (fun y : Fin n → ℝ => y i) (ContinuousLinearMap.proj i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt
  exact hf.comp_hasFDerivAt x hp

lemma pd_coord_mul {f g : ℝ → ℝ} {f' g' : ℝ} (i j k : Fin n) {x : Fin n → ℝ}
    (hf : HasDerivAt f f' (x i)) (hg : HasDerivAt g g' (x j)) :
    pd k (fun y => f (y i) * g (y j)) x =
      (if k = i then f' else 0) * g (x j) + f (x i) * (if k = j then g' else 0) := by
  have h : HasFDerivAt (fun y : Fin n → ℝ => f (y i) * g (y j)) _ x :=
    (hasFDerivAt_coord i hf).mul (hasFDerivAt_coord j hg)
  simp only [pd, h.fderiv]
  simp [Pi.single_apply]
  split_ifs <;> (try subst_vars) <;> (try simp_all) <;> ring

variable (M : ℝ)

/-- Schwarzschild in coordinates `(t, r, θ, φ) = (y 0, y 1, y 2, y 3)`:
`ds² = -(1-2M/r) dt² + (1-2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`. -/
def schD (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-(1 - 2 * M / y 1), (1 - 2 * M / y 1)⁻¹, y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The Schwarzschild metric `diag(-(1-2M/r), (1-2M/r)⁻¹, r², r² sin²θ)` as a matrix-valued function
of the coordinates `(t, r, θ, φ)`. -/
def schMetric : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := fun y => diagonal (schD M y)

/-- Coordinate derivatives `∂_k g_ii`. -/
def schDD (k i : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 then (if k = 1 then -(2 * M / y 1 ^ 2) else 0)
  else if i = 1 then (if k = 1 then -(2 * M / y 1 ^ 2) / (1 - 2 * M / y 1) ^ 2 else 0)
  else if i = 2 then (if k = 1 then 2 * y 1 else 0)
  else (if k = 1 then 2 * y 1 else 0) * sin (y 2) ^ 2 +
    y 1 ^ 2 * (if k = 2 then 2 * sin (y 2) * cos (y 2) else 0)

lemma pd_schD {y : Fin 4 → ℝ} (h1 : y 1 ≠ 0) (h2 : 1 - 2 * M / y 1 ≠ 0) (k i : Fin 4) :
    pd k (fun y => schD M y i) y = schDD M k i y := by
  have hb : HasDerivAt (fun r => 1 - 2 * M / r) (2 * M / y 1 ^ 2) (y 1) :=
    (((hasDerivAt_const (y 1) (2 * M)).div (hasDerivAt_id' (y 1)) h1).const_sub 1).congr_deriv
      (by ring)
  have e0 : HasDerivAt (fun r => -(1 - 2 * M / r)) (-(2 * M / y 1 ^ 2)) (y 1) := hb.neg
  have e1 : HasDerivAt (fun r => (1 - 2 * M / r)⁻¹)
      (-(2 * M / y 1 ^ 2) / (1 - 2 * M / y 1) ^ 2) (y 1) := hb.inv h2
  have e2 : HasDerivAt (fun r => r ^ 2) (2 * y 1) (y 1) := by
    simpa using (hasDerivAt_pow 2 (y 1))
  have e3 : HasDerivAt (fun θ => sin θ ^ 2) (2 * sin (y 2) * cos (y 2)) (y 2) := by
    convert (Real.hasDerivAt_sin (y 2)).pow 2 using 1; push_cast; ring
  have c0 := pd_coord (n := 4) 1 k e0
  have c1 := pd_coord (n := 4) 1 k e1
  have c2 := pd_coord (n := 4) 1 k e2
  have c3 := pd_coord_mul (n := 4) 1 2 k e2 e3
  fin_cases i <;> simp only [schD, schDD] <;> simp <;>
    first
    | simpa using c0
    | simpa using c1
    | simpa using c2
    | simpa using c3

/-- Expected Christoffel symbols (hand computation). -/
def schΓ (i j k : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then M / (y 1 * (y 1 - 2 * M))
  else if i = 1 ∧ j = 0 ∧ k = 0 then M * (y 1 - 2 * M) / y 1 ^ 3
  else if i = 1 ∧ j = 1 ∧ k = 1 then -(M / (y 1 * (y 1 - 2 * M)))
  else if i = 1 ∧ j = 2 ∧ k = 2 then -(y 1 - 2 * M)
  else if i = 1 ∧ j = 3 ∧ k = 3 then -(y 1 - 2 * M) * sin (y 2) ^ 2
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then 1 / y 1
  else if i = 2 ∧ j = 3 ∧ k = 3 then -(sin (y 2) * cos (y 2))
  else if i = 3 ∧ ((j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1)) then 1 / y 1
  else if i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) then cos (y 2) / sin (y 2)
  else 0

/-- Region where the coordinate expression is valid: `r > 0`, `r ≠ 2M`, `sin θ ≠ 0`. -/
def schRegion : Set (Fin 4 → ℝ) := {y | 0 < y 1 ∧ y 1 - 2 * M ≠ 0 ∧ sin (y 2) ≠ 0}

lemma schRegion_open : IsOpen (schRegion M) := by
  refine (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_ne_fun ((continuous_apply 1).sub continuous_const) continuous_const).inter
      (isOpen_ne_fun (continuous_sin.comp (continuous_apply 2)) continuous_const))

lemma christoffel_sch {y : Fin 4 → ℝ} (hy : y ∈ schRegion M) (i j k : Fin 4) :
    christoffel (schMetric M) i j k y = schΓ M i j k y := by
  obtain ⟨h1, h2, h3⟩ := hy
  have h1' : y 1 ≠ 0 := h1.ne'
  have hf : 1 - 2 * M / y 1 ≠ 0 := by
    rw [one_sub_div h1']; exact div_ne_zero h2 h1'
  have h2b : 2 * M - y 1 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - y 1 ≠ 0 := fun h => h2 (by linarith)
  have h2d : y 1 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have hd : ∀ i, schD M y i ≠ 0 := by
    intro i; fin_cases i <;> simp [schD, h1', hf, h3]; intro h; apply hf; linarith
  change christoffel (fun y => diagonal (schD M y)) i j k y = _
  rw [christoffel_diagonal _ y hd]
  simp only [pd_schD M h1' hf]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [schΓ, schDD, schD] <;> field_simp <;> ring

/-- Coordinate derivatives of the expected Christoffel symbols. -/
def schDΓ (m i j k : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then
    (if m = 1 then -(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2 else 0)
  else if i = 1 ∧ j = 0 ∧ k = 0 then (if m = 1 then M * (6 * M - 2 * x 1) / x 1 ^ 4 else 0)
  else if i = 1 ∧ j = 1 ∧ k = 1 then
    (if m = 1 then M * (2 * x 1 - 2 * M) / (x 1 * (x 1 - 2 * M)) ^ 2 else 0)
  else if i = 1 ∧ j = 2 ∧ k = 2 then (if m = 1 then -1 else 0)
  else if i = 1 ∧ j = 3 ∧ k = 3 then
    (if m = 1 then -1 else 0) * sin (x 2) ^ 2 +
      -(x 1 - 2 * M) * (if m = 2 then 2 * sin (x 2) * cos (x 2) else 0)
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then (if m = 1 then -1 / x 1 ^ 2 else 0)
  else if i = 2 ∧ j = 3 ∧ k = 3 then
    (if m = 2 then -(cos (x 2) ^ 2 - sin (x 2) ^ 2) else 0)
  else if i = 3 ∧ ((j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1)) then (if m = 1 then -1 / x 1 ^ 2 else 0)
  else if i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) then
    (if m = 2 then -1 / sin (x 2) ^ 2 else 0)
  else 0

lemma pd_schΓ {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (m i j k : Fin 4) :
    pd m (fun y => schΓ M i j k y) x = schDΓ M m i j k x := by
  obtain ⟨h1, h2, h3⟩ := hx
  have h1' : x 1 ≠ 0 := h1.ne'
  have hq : x 1 * (x 1 - 2 * M) ≠ 0 := mul_ne_zero h1' h2
  have hlin : HasDerivAt (fun r => r * (r - 2 * M)) (2 * x 1 - 2 * M) (x 1) :=
    ((hasDerivAt_id' (x 1)).mul ((hasDerivAt_id' (x 1)).sub_const (2 * M))).congr_deriv (by ring)
  have d1 : HasDerivAt (fun r => M / (r * (r - 2 * M)))
      (-(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2) (x 1) :=
    ((hasDerivAt_const (x 1) M).div hlin hq).congr_deriv (by ring)
  have d2 : HasDerivAt (fun r => M * (r - 2 * M) / r ^ 3) (M * (6 * M - 2 * x 1) / x 1 ^ 4) (x 1) :=
    ((((hasDerivAt_id' (x 1)).sub_const (2 * M)).const_mul M).div
      (hasDerivAt_pow 3 (x 1)) (pow_ne_zero 3 h1')).congr_deriv (by
        norm_num; field_simp; ring)
  have d3 : HasDerivAt (fun r => -(M / (r * (r - 2 * M))))
      (M * (2 * x 1 - 2 * M) / (x 1 * (x 1 - 2 * M)) ^ 2) (x 1) :=
    d1.neg.congr_deriv (by ring)
  have d4 : HasDerivAt (fun r => -(r - 2 * M)) (-1) (x 1) :=
    ((hasDerivAt_id' (x 1)).sub_const (2 * M)).neg
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
  have c2 := pd_coord (n := 4) 1 m d2
  have c3 := pd_coord (n := 4) 1 m d3
  have c4 := pd_coord (n := 4) 1 m d4
  have c5 := pd_coord (n := 4) 1 m d5
  have c6 := pd_coord_mul (n := 4) 1 2 m d4 d6
  have c7 := pd_coord (n := 4) 2 m d7
  have c8 := pd_coord (n := 4) 2 m d8
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [schΓ, schDΓ] <;> (try simp) <;>
    first
    | simpa using c1
    | simpa using c2
    | simpa using c3
    | simpa using c4
    | simpa using c5
    | simpa using c6
    | simpa using c7
    | simpa using c8
    | simp [pd_const]

lemma pd_christoffel_sch {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (m i j k : Fin 4) :
    pd m (christoffel (schMetric M) i j k) x = schDΓ M m i j k x := by
  have hev : christoffel (schMetric M) i j k =ᶠ[nhds x] fun y => schΓ M i j k y :=
    Filter.eventually_of_mem ((schRegion_open M).mem_nhds hx) fun y hy => christoffel_sch M hy i j k
  rw [pd_congr hev, pd_schΓ M hx]

/-- The Ricci tensor of Schwarzschild vanishes (wherever the chart is valid). -/
theorem ricci_sch {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (σ ν : Fin 4) :
    ricci (schMetric M) σ ν x = 0 := by
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
    simp [ricci, riemann, Fin.sum_univ_four, pd_christoffel_sch M hx, christoffel_sch M hx,
      schΓ, schDΓ] <;> field_simp <;> (try simp only [hc]) <;> ring

/-- **Einstein form.** `G_{μν} = 0` for Schwarzschild at every point of the chart region
(`r > 0`, `r ≠ 2M`, `sin θ ≠ 0`; in particular everywhere outside `r = 2M` for `M ≥ 0`). -/
theorem einstein_sch {x : Fin 4 → ℝ} (hx : x ∈ schRegion M) (μ ν : Fin 4) :
    einsteinTensor (schMetric M) μ ν x = 0 := by
  simp [einsteinTensor, scalarCurvature, ricci_sch M hx]

/-- Exterior Schwarzschild domain: `r > 2M`, `0 < θ < π`. -/
def schU : Set (Fin 4 → ℝ) := {y | 2 * M < y 1 ∧ 0 < y 2 ∧ y 2 < π}

lemma schU_subset (hM : 0 < M) : schU M ⊆ schRegion M := fun y ⟨h1, h2, h3⟩ =>
  ⟨by linarith, by linarith, (sin_pos_of_pos_of_lt_pi h2 h3).ne'⟩

/-- Schwarzschild is a coordinate metric (smooth, symmetric, invertible) on `r > 2M`, `0<θ<π`. -/
theorem isCoordMetric_sch (hM : 0 < M) : IsCoordMetric (schMetric M) (schU M) := by
  have hopen : IsOpen (schU M) :=
    (isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const))
  have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 1) (schU M) := (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
  have hθ : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 2) := by fun_prop
  have hr0 : ∀ y ∈ schU M, y 1 ≠ 0 := fun y hy => by have := hy.1; linarith
  have hf0 : ∀ y ∈ schU M, 1 - 2 * M / y 1 ≠ 0 := fun y hy => by
    have h1 : 0 < y 1 := by have := hy.1; linarith
    rw [one_sub_div h1.ne']; exact div_ne_zero (by linarith [hy.1]) h1.ne'
  have hfs : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => 1 - 2 * M / y 1) (schU M) :=
    contDiffOn_const.sub (contDiffOn_const.div hr hr0)
  refine isCoordMetric_diagonal (schD M) hopen (fun i => ?_) (fun y hy i => ?_)
  · fin_cases i
    · exact hfs.neg
    · exact hfs.inv hf0
    · exact hr.pow 2
    · exact (hr.pow 2).mul ((Real.contDiff_sin.comp hθ).pow 2).contDiffOn
  · have hs := (schU_subset M hM hy).2.2
    fin_cases i <;> simp [schD, hr0 y hy, hf0 y hy, hs]
    · intro h; apply hf0 y hy; linarith

/-- **Domain form.** Schwarzschild (`M > 0`) **solves the vacuum Einstein equations**
on the exterior domain `r > 2M`, `0 < θ < π`, in the hardened sense: it is a smooth, symmetric,
invertible coordinate metric there and `G_{μν} = 0` at every point. -/
theorem sch_isVacuumSolution (hM : 0 < M) : IsVacuumSolution 0 (schMetric M) (schU M) :=
  ⟨isCoordMetric_sch M hM, fun x hx μ ν => by
    simp [einstein_sch M (schU_subset M hM hx) μ ν]⟩

/-- **Signature.** Exterior Schwarzschild has Lorentzian signature: with `f = 1 - 2M/r > 0`,
`g = Pᵀ η P` for `P = diag(√f, 1/√f, r, r sin θ)`. -/
theorem sch_isLorentzian (hM : 0 < M) : IsLorentzianCoordMetric (schMetric M) (schU M) := by
  refine ⟨isCoordMetric_sch M hM, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hy
  have hr : 0 < y 1 := by linarith
  have hf : 0 < 1 - 2 * M / y 1 := by
    rw [sub_pos, div_lt_one hr]; exact h1
  have hs : 0 < sin (y 2) := sin_pos_of_pos_of_lt_pi h2 h3
  have hsq : 0 < √(1 - 2 * M / y 1) := Real.sqrt_pos.mpr hf
  refine ⟨diagonal ![√(1 - 2 * M / y 1), (√(1 - 2 * M / y 1))⁻¹, y 1, y 1 * sin (y 2)], ?_, ?_⟩
  · rw [det_diagonal, Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
    exact (mul_pos (mul_pos (mul_pos hsq (inv_pos.mpr hsq)) hr) (mul_pos hr hs)).ne'.isUnit
  · rw [diagonal_transpose, eta, diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [schMetric]
    congr 1
    ext i
    have hsq2 : √(1 - 2 * M / y 1) ^ 2 = 1 - 2 * M / y 1 := Real.sq_sqrt hf.le
    have hmul : √(1 - 2 * M / y 1) * √(1 - 2 * M / y 1) = 1 - 2 * M / y 1 :=
      Real.mul_self_sqrt hf.le
    fin_cases i
    · simp only [schD, etaDiag]; simp [hmul]
    · simp only [schD, etaDiag]; simp [← mul_inv, hmul]
    · simp [schD, etaDiag]; ring
    · simp [schD, etaDiag]; ring

/-- Exterior region version: `0 ≤ M`, `r > 2M`, `0 < θ < π`. -/
theorem einstein_sch_exterior {x : Fin 4 → ℝ} (hM : 0 ≤ M) (hr : 2 * M < x 1)
    (hθ : 0 < x 2 ∧ x 2 < π) (μ ν : Fin 4) : einsteinTensor (schMetric M) μ ν x = 0 :=
  einstein_sch M ⟨by linarith, by linarith, (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'⟩ μ ν

end Schwarzschild

end Lightlike
