import Lightlike.GR.Schwarzschild

/-!
# The Euclidean Schwarzschild metric

`ds² = (1 - 2M/r) dτ² + (1 - 2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²` in coordinates
`(τ, r, θ, φ)`: the Wick rotation `t = -iτ` of exterior Schwarzschild, a Riemannian metric for
`r > 2M`. It solves the Euclidean vacuum equations: its Ricci tensor vanishes
(`ricci_euc`, same computation as `ricci_sch` with the sign of `g_ττ` reversed).

Gap row G1-058 (Euclidean Schwarzschild, regularity at the horizon fixes `β = 8πM`).
Compared with I. Kuntz, G. Paci, O. Zanusso, *Euclidean actions and static black hole
entropy in teleparallel theories*, arXiv:2410.04510, Appendix A, eqs. (A1)–(A6), pp. 20–21 (read: the Euclidean section
(A2), the near-horizon form (A5), the period `τ ∼ τ + 8πm`, `β_H = 8πm` as the inverse Hawking temperature, the conical
singularity for `β ≠ β_H` and its curvature integral (A6)) and D. Harlow, *Jerusalem Lectures on Black Holes and Quantum
Information*, arXiv:1409.1231, section 4.8, eqs. (4.42)–(4.44), p. 43 (read: the smooth period); see
`docs/notes/g1-058-euclidean-schwarzschild-source.md`. Gibbons–Hawking (1977) and Carroll's book: not read.
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- Schwarzeucild in coordinates `(t, r, θ, φ) = (y 0, y 1, y 2, y 3)`:
`ds² = -(1-2M/r) dt² + (1-2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`. -/
def eucD (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(1 - 2 * M / y 1), (1 - 2 * M / y 1)⁻¹, y 1 ^ 2, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The Schwarzeucild metric `diag(-(1-2M/r), (1-2M/r)⁻¹, r², r² sin²θ)` as a matrix-valued function
of the coordinates `(t, r, θ, φ)`. -/
def eucMetric : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := fun y => diagonal (eucD M y)

/-- Coordinate derivatives `∂_k g_ii`. -/
def eucDD (k i : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 then (if k = 1 then 2 * M / y 1 ^ 2 else 0)
  else if i = 1 then (if k = 1 then -(2 * M / y 1 ^ 2) / (1 - 2 * M / y 1) ^ 2 else 0)
  else if i = 2 then (if k = 1 then 2 * y 1 else 0)
  else (if k = 1 then 2 * y 1 else 0) * sin (y 2) ^ 2 +
    y 1 ^ 2 * (if k = 2 then 2 * sin (y 2) * cos (y 2) else 0)

lemma pd_eucD {y : Fin 4 → ℝ} (h1 : y 1 ≠ 0) (h2 : 1 - 2 * M / y 1 ≠ 0) (k i : Fin 4) :
    pd k (fun y => eucD M y i) y = eucDD M k i y := by
  have hb : HasDerivAt (fun r => 1 - 2 * M / r) (2 * M / y 1 ^ 2) (y 1) :=
    (((hasDerivAt_const (y 1) (2 * M)).div (hasDerivAt_id' (y 1)) h1).const_sub 1).congr_deriv
      (by ring)
  have e0 : HasDerivAt (fun r => (1 - 2 * M / r)) (2 * M / y 1 ^ 2) (y 1) := hb
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
  fin_cases i <;> simp only [eucD, eucDD] <;> simp <;>
    first
    | simpa using c0
    | simpa using c1
    | simpa using c2
    | simpa using c3

/-- Expected Christoffel symbols (hand computation). -/
def eucΓ (i j k : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then M / (y 1 * (y 1 - 2 * M))
  else if i = 1 ∧ j = 0 ∧ k = 0 then -(M * (y 1 - 2 * M) / y 1 ^ 3)
  else if i = 1 ∧ j = 1 ∧ k = 1 then -(M / (y 1 * (y 1 - 2 * M)))
  else if i = 1 ∧ j = 2 ∧ k = 2 then -(y 1 - 2 * M)
  else if i = 1 ∧ j = 3 ∧ k = 3 then -(y 1 - 2 * M) * sin (y 2) ^ 2
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then 1 / y 1
  else if i = 2 ∧ j = 3 ∧ k = 3 then -(sin (y 2) * cos (y 2))
  else if i = 3 ∧ ((j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1)) then 1 / y 1
  else if i = 3 ∧ ((j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2)) then cos (y 2) / sin (y 2)
  else 0

/-- Region where the coordinate expression is valid: `r > 0`, `r ≠ 2M`, `sin θ ≠ 0`. -/
def eucRegion : Set (Fin 4 → ℝ) := {y | 0 < y 1 ∧ y 1 - 2 * M ≠ 0 ∧ sin (y 2) ≠ 0}

lemma eucRegion_open : IsOpen (eucRegion M) := by
  refine (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_ne_fun ((continuous_apply 1).sub continuous_const) continuous_const).inter
      (isOpen_ne_fun (continuous_sin.comp (continuous_apply 2)) continuous_const))

lemma christoffel_euc {y : Fin 4 → ℝ} (hy : y ∈ eucRegion M) (i j k : Fin 4) :
    christoffel (eucMetric M) i j k y = eucΓ M i j k y := by
  obtain ⟨h1, h2, h3⟩ := hy
  have h1' : y 1 ≠ 0 := h1.ne'
  have hf : 1 - 2 * M / y 1 ≠ 0 := by
    rw [one_sub_div h1']; exact div_ne_zero h2 h1'
  have h2b : 2 * M - y 1 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - y 1 ≠ 0 := fun h => h2 (by linarith)
  have h2d : y 1 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have hd : ∀ i, eucD M y i ≠ 0 := by
    intro i; fin_cases i <;> simp [eucD, h1', hf, h3]
  change christoffel (fun y => diagonal (eucD M y)) i j k y = _
  rw [christoffel_diagonal _ y hd]
  simp only [pd_eucD M h1' hf]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [eucΓ, eucDD, eucD] <;> field_simp <;> ring

/-- Coordinate derivatives of the expected Christoffel symbols. -/
def eucDΓ (m i j k : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  if i = 0 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then
    (if m = 1 then -(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2 else 0)
  else if i = 1 ∧ j = 0 ∧ k = 0 then (if m = 1 then -(M * (6 * M - 2 * x 1) / x 1 ^ 4) else 0)
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

lemma pd_eucΓ {x : Fin 4 → ℝ} (hx : x ∈ eucRegion M) (m i j k : Fin 4) :
    pd m (fun y => eucΓ M i j k y) x = eucDΓ M m i j k x := by
  obtain ⟨h1, h2, h3⟩ := hx
  have h1' : x 1 ≠ 0 := h1.ne'
  have hq : x 1 * (x 1 - 2 * M) ≠ 0 := mul_ne_zero h1' h2
  have hlin : HasDerivAt (fun r => r * (r - 2 * M)) (2 * x 1 - 2 * M) (x 1) :=
    ((hasDerivAt_id' (x 1)).mul ((hasDerivAt_id' (x 1)).sub_const (2 * M))).congr_deriv (by ring)
  have d1 : HasDerivAt (fun r => M / (r * (r - 2 * M)))
      (-(M * (2 * x 1 - 2 * M)) / (x 1 * (x 1 - 2 * M)) ^ 2) (x 1) :=
    ((hasDerivAt_const (x 1) M).div hlin hq).congr_deriv (by ring)
  have d2 : HasDerivAt (fun r => -(M * (r - 2 * M) / r ^ 3)) (-(M * (6 * M - 2 * x 1) / x 1 ^ 4)) (x 1) :=
    (((((hasDerivAt_id' (x 1)).sub_const (2 * M)).const_mul M).div
      (hasDerivAt_pow 3 (x 1)) (pow_ne_zero 3 h1')).neg).congr_deriv (by
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
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [eucΓ, eucDΓ] <;> (try simp) <;>
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

lemma pd_christoffel_euc {x : Fin 4 → ℝ} (hx : x ∈ eucRegion M) (m i j k : Fin 4) :
    pd m (christoffel (eucMetric M) i j k) x = eucDΓ M m i j k x := by
  have hev : christoffel (eucMetric M) i j k =ᶠ[nhds x] fun y => eucΓ M i j k y :=
    Filter.eventually_of_mem ((eucRegion_open M).mem_nhds hx) fun y hy => christoffel_euc M hy i j k
  rw [pd_congr hev, pd_eucΓ M hx]

/-- The Ricci tensor of Schwarzeucild vanishes (wherever the chart is valid). -/
theorem ricci_euc {x : Fin 4 → ℝ} (hx : x ∈ eucRegion M) (σ ν : Fin 4) :
    ricci (eucMetric M) σ ν x = 0 := by
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
    simp [ricci, riemann, Fin.sum_univ_four, pd_christoffel_euc M hx, christoffel_euc M hx,
      eucΓ, eucDΓ] <;> field_simp <;> (try simp only [hc]) <;> ring


end Lightlike
