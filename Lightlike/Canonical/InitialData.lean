import Mathlib
import Lightlike.Canonical.ADM
import Lightlike.GR.Schwarzschild
import Lightlike.Cosmology.FLRW

/-!
# Schwarzschild and FLRW initial data satisfy the ADM constraints

Two exact solutions of the library, `Lightlike.schMetric` (`Lightlike/GR/Schwarzschild.lean`) and
`Lightlike.Cosmology.flrwMetric` (`Lightlike/Cosmology/FLRW.lean`), give initial data `(h, π)` on a slice
`t = const`, and these data satisfy the constraints of `Lightlike/Canonical/ADM.lean`.

* **Schwarzschild, time symmetric.** `schSlice M` is the metric induced on the slice `t = 0` in Schwarzschild
  coordinates: the spatial block `g_ij` of `schMetric M`, which is
  `diag((1 - 2M/r)⁻¹, r², r² sin²θ)` in the chart `(r, θ, φ)` (`schSlice_eq`). The shift `g_{0i}` vanishes and
  the block does not depend on `t` (`schMetric_shift`, `schSlice_static`), so the extrinsic curvature and the
  momentum vanish and the data are `(schSlice M, 0)`. The scalar curvature of the slice is zero although its
  Ricci tensor is not (`ricci_schSlice`, `scalarCurvature_schSlice`), so both constraints hold on the chart
  region (`schSlice_hamiltonianConstraint`, `schSlice_momentumConstraint`).
* **Spatially flat FLRW.** `flrwSlice a t` is the spatial block of `flrwMetric a 0` at time `t`, which is
  `a(t)² · 1` (`flrwSlice_eq`); the lapse is `1` and the shift `0` (`flrwMetric_lapse`, `flrwMetric_shift`). Its
  momentum is `flrwMomentum a t = −2 a'(t) · 1`, the value of `π^{ij} = √γ (K γ^{ij} − K^{ij})` for
  `K_ij = −½ ∂_t γ_ij` (`flrwMomentum_eq`). The Hamiltonian constraint with the energy density `ρ` of the
  comoving fluid holds exactly when the first Friedmann equation does (`flrw_hamiltonian_iff`), and the momentum
  constraint holds with zero matter momentum (`flrw_momentumConstraint`).

**Sources (read at the cited locations).** E. Gourgoulhon, *3+1 Formalism and Bases of Numerical Relativity*,
arXiv:gr-qc/0703035: the Hamiltonian constraint `R + K² − K_ij K^ij = 16πE` (eq. (4.19), p. 54) and the
momentum constraint `D_j K^j_i − D_i K = 8π p_i` (eq. (4.22), p. 54); the extrinsic curvature
`K_ij = (1/2N)(γ_ik D_j β^k + γ_jk D_i β^k − ∂_t γ_ij)` (eq. (4.104), p. 67) and the momentum
`π^{ij} = √γ (K γ^{ij} − K^{ij})` (eq. (4.108), p. 67); the Schwarzschild metric (7.16) and the metric
`γ_ij = diag((1 − 2m/r)⁻¹, r², r² sin²θ)` induced on `t = const` (eq. (7.17), p. 107); the extrinsic
curvature of these slices vanishes (the example after eq. (7.56), p. 112). J. C. Aurrekoetxea, K. Clough and
E. A. Lim, *Cosmology using numerical relativity*, arXiv:2409.01939v2: the flat Friedmann equations (eq. (3),
p. 4), `γ_ij = a² δ_ij`, `K_ij = −H γ_ij` (eq. (23), p. 10), the constraints (eqs. (25), (26), p. 10) and the
statement (pp. 10-11) that for FLRW the momentum constraints hold trivially and the Hamiltonian constraint is
the first Friedmann equation.

**Conventions.** The library's density is `ℋ = −√γ (R + K² − K_ij K^ij)` in terms of `K` (for `d = 3`, see
`Lightlike.Canonical.kineticDensity`), so Gourgoulhon's (4.19) with `E = ρ` and Newton's constant `G` reads
`ℋ + 16πG √γ ρ = 0`; Gourgoulhon and Aurrekoetxea–Clough–Lim's (25) use `G = 1`, their eq. (3) keeps `G`. The
cosmological constant and the spatial curvature are zero (`Λ = 0`, `k = 0`), as in Aurrekoetxea–Clough–Lim's
eq. (3). The momentum constraint of the library is `∇_k π^{ik} = 0`, which for `π^{ij} = √γ (Kγ^{ij} − K^{ij})`
is `√γ` times Gourgoulhon's (4.22) with `p_i = 0`.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

/-! ## The time-symmetric Schwarzschild slice -/

section Schwarzschild

variable (M : ℝ)

/-- The metric induced on the slice `t = 0` of Schwarzschild spacetime in Schwarzschild coordinates: the spatial
block `g_ij` (`i, j ∈ {r, θ, φ}`) of `Lightlike.schMetric M`, as a tensor field on the chart
`(r, θ, φ) = (y 0, y 1, y 2)` (Gourgoulhon, arXiv:gr-qc/0703035, eq. (7.17)). -/
def schSlice : TensorField 3 := fun y => (Lightlike.schMetric M (Fin.cons 0 y)).submatrix Fin.succ Fin.succ

/-- The diagonal entries `((1 - 2M/r)⁻¹, r², r² sin²θ)` of the slice metric. -/
def schSliceD (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(1 - 2 * M / y 0)⁻¹, y 0 ^ 2, y 0 ^ 2 * Real.sin (y 1) ^ 2]

/-- The spatial block of Schwarzschild at any time `t` is `diag((1 - 2M/r)⁻¹, r², r² sin²θ)`. -/
theorem schMetric_block (t : ℝ) (y : Fin 3 → ℝ) :
    (Lightlike.schMetric M (Fin.cons t y)).submatrix Fin.succ Fin.succ = diagonal (schSliceD M y) := by
  ext i j
  simp only [submatrix_apply, Lightlike.schMetric, diagonal_apply, Fin.succ_inj]
  have e1 : (Fin.cons t y : Fin 4 → ℝ) 1 = y 0 := rfl
  have e2 : (Fin.cons t y : Fin 4 → ℝ) 2 = y 1 := rfl
  split_ifs with h
  · subst h
    fin_cases i <;> simp [Lightlike.schD, schSliceD, e1, e2]
  · rfl

theorem schSlice_eq (y : Fin 3 → ℝ) : schSlice M y = diagonal (schSliceD M y) :=
  schMetric_block M 0 y

/-- The shift of the Schwarzschild coordinates vanishes: `g_{0i} = 0`. -/
theorem schMetric_shift (t : ℝ) (y : Fin 3 → ℝ) (i : Fin 3) :
    Lightlike.schMetric M (Fin.cons t y) 0 i.succ = 0 := by
  simp [Lightlike.schMetric, (Fin.succ_ne_zero i).symm]

/-- The slices `t = const` are static: `∂_t g_ij = 0`. With the zero shift, Gourgoulhon's (4.104) gives
`K_ij = 0`, hence `π^{ij} = 0` by (4.108): the data are time symmetric. -/
theorem schSlice_static (y : Fin 3 → ℝ) (i j : Fin 3) (t : ℝ) :
    deriv (fun s => (Lightlike.schMetric M (Fin.cons s y)).submatrix Fin.succ Fin.succ i j) t = 0 := by
  have : (fun s => (Lightlike.schMetric M (Fin.cons s y)).submatrix Fin.succ Fin.succ i j) =
      fun _ => diagonal (schSliceD M y) i j := funext fun s => by rw [schMetric_block]
  rw [this, deriv_const]

/-- Coordinate derivatives `∂_k γ_ii` of the slice metric. -/
def schSliceDD (k i : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  if i = 0 then (if k = 0 then -(2 * M / y 0 ^ 2) / (1 - 2 * M / y 0) ^ 2 else 0)
  else if i = 1 then (if k = 0 then 2 * y 0 else 0)
  else (if k = 0 then 2 * y 0 else 0) * Real.sin (y 1) ^ 2 +
    y 0 ^ 2 * (if k = 1 then 2 * Real.sin (y 1) * Real.cos (y 1) else 0)

lemma pd_schSliceD {y : Fin 3 → ℝ} (h1 : y 0 ≠ 0) (h2 : 1 - 2 * M / y 0 ≠ 0) (k i : Fin 3) :
    Lightlike.pd k (fun y => schSliceD M y i) y = schSliceDD M k i y := by
  have hb : HasDerivAt (fun r => 1 - 2 * M / r) (2 * M / y 0 ^ 2) (y 0) :=
    (((hasDerivAt_const (y 0) (2 * M)).div (hasDerivAt_id' (y 0)) h1).const_sub 1).congr_deriv
      (by ring)
  have e1 : HasDerivAt (fun r => (1 - 2 * M / r)⁻¹)
      (-(2 * M / y 0 ^ 2) / (1 - 2 * M / y 0) ^ 2) (y 0) := hb.inv h2
  have e2 : HasDerivAt (fun r => r ^ 2) (2 * y 0) (y 0) := by
    simpa using (hasDerivAt_pow 2 (y 0))
  have e3 : HasDerivAt (fun θ => Real.sin θ ^ 2) (2 * Real.sin (y 1) * Real.cos (y 1)) (y 1) := by
    convert (Real.hasDerivAt_sin (y 1)).pow 2 using 1; push_cast; ring
  have c1 := Lightlike.pd_coord (n := 3) 0 k e1
  have c2 := Lightlike.pd_coord (n := 3) 0 k e2
  have c3 := Lightlike.pd_coord_mul (n := 3) 0 1 k e2 e3
  fin_cases i <;> simp only [schSliceD, schSliceDD] <;> simp <;>
    first
    | simpa using c1
    | simpa using c2
    | simpa using c3

/-- The Christoffel symbols of the slice (hand computation, proved equal to the definition in
`christoffel_schSlice`). -/
def schSliceΓ (i j k : Fin 3) (y : Fin 3 → ℝ) : ℝ :=
  if i = 0 ∧ j = 0 ∧ k = 0 then -(M / (y 0 * (y 0 - 2 * M)))
  else if i = 0 ∧ j = 1 ∧ k = 1 then -(y 0 - 2 * M)
  else if i = 0 ∧ j = 2 ∧ k = 2 then -(y 0 - 2 * M) * Real.sin (y 1) ^ 2
  else if i = 1 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then 1 / y 0
  else if i = 1 ∧ j = 2 ∧ k = 2 then -(Real.sin (y 1) * Real.cos (y 1))
  else if i = 2 ∧ ((j = 0 ∧ k = 2) ∨ (j = 2 ∧ k = 0)) then 1 / y 0
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then Real.cos (y 1) / Real.sin (y 1)
  else 0

/-- The region of the chart where the coordinate expressions are valid: `r > 0`, `r ≠ 2M`, `sin θ ≠ 0`. -/
def schSliceRegion : Set (Fin 3 → ℝ) := {y | 0 < y 0 ∧ y 0 - 2 * M ≠ 0 ∧ Real.sin (y 1) ≠ 0}

lemma schSliceRegion_open : IsOpen (schSliceRegion M) := by
  refine (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_ne_fun ((continuous_apply 0).sub continuous_const) continuous_const).inter
      (isOpen_ne_fun (Real.continuous_sin.comp (continuous_apply 1)) continuous_const))

lemma christoffel_schSlice {y : Fin 3 → ℝ} (hy : y ∈ schSliceRegion M) (i j k : Fin 3) :
    Lightlike.christoffel (schSlice M) i j k y = schSliceΓ M i j k y := by
  obtain ⟨h1, h2, h3⟩ := hy
  have h1' : y 0 ≠ 0 := h1.ne'
  have hf : 1 - 2 * M / y 0 ≠ 0 := by
    rw [one_sub_div h1']; exact div_ne_zero h2 h1'
  have h2b : 2 * M - y 0 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - y 0 ≠ 0 := fun h => h2 (by linarith)
  have h2d : y 0 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have hd : ∀ i, schSliceD M y i ≠ 0 := by
    intro i; fin_cases i <;> simp [schSliceD, h1', hf, h3]
  have hfun : schSlice M = fun y => diagonal (schSliceD M y) := funext (schSlice_eq M)
  rw [hfun, Lightlike.christoffel_diagonal _ y hd]
  simp only [pd_schSliceD M h1' hf]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [schSliceΓ, schSliceDD, schSliceD] <;> field_simp <;> ring

/-- Coordinate derivatives `∂_m Γ^i_{jk}` of the expected Christoffel symbols. -/
def schSliceDΓ (m i j k : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  if i = 0 ∧ j = 0 ∧ k = 0 then
    (if m = 0 then M * (2 * x 0 - 2 * M) / (x 0 * (x 0 - 2 * M)) ^ 2 else 0)
  else if i = 0 ∧ j = 1 ∧ k = 1 then (if m = 0 then -1 else 0)
  else if i = 0 ∧ j = 2 ∧ k = 2 then
    (if m = 0 then -1 else 0) * Real.sin (x 1) ^ 2 +
      -(x 0 - 2 * M) * (if m = 1 then 2 * Real.sin (x 1) * Real.cos (x 1) else 0)
  else if i = 1 ∧ ((j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0)) then (if m = 0 then -1 / x 0 ^ 2 else 0)
  else if i = 1 ∧ j = 2 ∧ k = 2 then
    (if m = 1 then -(Real.cos (x 1) ^ 2 - Real.sin (x 1) ^ 2) else 0)
  else if i = 2 ∧ ((j = 0 ∧ k = 2) ∨ (j = 2 ∧ k = 0)) then (if m = 0 then -1 / x 0 ^ 2 else 0)
  else if i = 2 ∧ ((j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1)) then
    (if m = 1 then -1 / Real.sin (x 1) ^ 2 else 0)
  else 0

lemma pd_schSliceΓ {x : Fin 3 → ℝ} (hx : x ∈ schSliceRegion M) (m i j k : Fin 3) :
    Lightlike.pd m (fun y => schSliceΓ M i j k y) x = schSliceDΓ M m i j k x := by
  obtain ⟨h1, h2, h3⟩ := hx
  have h1' : x 0 ≠ 0 := h1.ne'
  have hq : x 0 * (x 0 - 2 * M) ≠ 0 := mul_ne_zero h1' h2
  have hlin : HasDerivAt (fun r => r * (r - 2 * M)) (2 * x 0 - 2 * M) (x 0) :=
    ((hasDerivAt_id' (x 0)).mul ((hasDerivAt_id' (x 0)).sub_const (2 * M))).congr_deriv (by ring)
  have d1 : HasDerivAt (fun r => M / (r * (r - 2 * M)))
      (-(M * (2 * x 0 - 2 * M)) / (x 0 * (x 0 - 2 * M)) ^ 2) (x 0) :=
    ((hasDerivAt_const (x 0) M).div hlin hq).congr_deriv (by ring)
  have d3 : HasDerivAt (fun r => -(M / (r * (r - 2 * M))))
      (M * (2 * x 0 - 2 * M) / (x 0 * (x 0 - 2 * M)) ^ 2) (x 0) :=
    d1.neg.congr_deriv (by ring)
  have d4 : HasDerivAt (fun r => -(r - 2 * M)) (-1) (x 0) :=
    ((hasDerivAt_id' (x 0)).sub_const (2 * M)).neg
  have d5 : HasDerivAt (fun r => 1 / r) (-1 / x 0 ^ 2) (x 0) :=
    ((hasDerivAt_const (x 0) (1 : ℝ)).div (hasDerivAt_id' (x 0)) h1').congr_deriv (by ring)
  have d6 : HasDerivAt (fun θ => Real.sin θ ^ 2) (2 * Real.sin (x 1) * Real.cos (x 1)) (x 1) := by
    convert (Real.hasDerivAt_sin (x 1)).pow 2 using 1; push_cast; ring
  have d7 : HasDerivAt (fun θ => -(Real.sin θ * Real.cos θ))
      (-(Real.cos (x 1) ^ 2 - Real.sin (x 1) ^ 2)) (x 1) := by
    convert ((Real.hasDerivAt_sin (x 1)).mul (Real.hasDerivAt_cos (x 1))).neg using 1; ring
  have d8 : HasDerivAt (fun θ => Real.cos θ / Real.sin θ) (-1 / Real.sin (x 1) ^ 2) (x 1) := by
    convert (Real.hasDerivAt_cos (x 1)).div (Real.hasDerivAt_sin (x 1)) h3 using 1
    field_simp; nlinarith [Real.sin_sq_add_cos_sq (x 1)]
  have c3 := Lightlike.pd_coord (n := 3) 0 m d3
  have c4 := Lightlike.pd_coord (n := 3) 0 m d4
  have c5 := Lightlike.pd_coord (n := 3) 0 m d5
  have c6 := Lightlike.pd_coord_mul (n := 3) 0 1 m d4 d6
  have c7 := Lightlike.pd_coord (n := 3) 1 m d7
  have c8 := Lightlike.pd_coord (n := 3) 1 m d8
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [schSliceΓ, schSliceDΓ] <;> (try simp) <;>
    first
    | simpa using c3
    | simpa using c4
    | simpa using c5
    | simpa using c6
    | simpa using c7
    | simpa using c8
    | simp [Lightlike.pd_const]

lemma pd_christoffel_schSlice {x : Fin 3 → ℝ} (hx : x ∈ schSliceRegion M) (m i j k : Fin 3) :
    Lightlike.pd m (Lightlike.christoffel (schSlice M) i j k) x = schSliceDΓ M m i j k x := by
  have hev : Lightlike.christoffel (schSlice M) i j k =ᶠ[nhds x] fun y => schSliceΓ M i j k y :=
    Filter.eventually_of_mem ((schSliceRegion_open M).mem_nhds hx) fun y hy =>
      christoffel_schSlice M hy i j k
  rw [Lightlike.pd_congr hev, pd_schSliceΓ M hx]

/-- The Ricci tensor of the slice: `R_rr = −2M/(r²(r − 2M))`, `R_θθ = M/r`, `R_φφ = M sin²θ/r`, the others
zero. -/
def schSliceRic (σ ν : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  if σ = 0 ∧ ν = 0 then -(2 * M / (x 0 ^ 2 * (x 0 - 2 * M)))
  else if σ = 1 ∧ ν = 1 then M / x 0
  else if σ = 2 ∧ ν = 2 then M * Real.sin (x 1) ^ 2 / x 0
  else 0

/-- **The Ricci tensor of the Schwarzschild slice** (it is not zero for `M ≠ 0`). -/
theorem ricci_schSlice {x : Fin 3 → ℝ} (hx : x ∈ schSliceRegion M) (σ ν : Fin 3) :
    Lightlike.ricci (schSlice M) σ ν x = schSliceRic M σ ν x := by
  have hx' := hx
  obtain ⟨h1, h2, h3⟩ := hx'
  have h1' : x 0 ≠ 0 := h1.ne'
  have hc : Real.cos (x 1) ^ 2 = 1 - Real.sin (x 1) ^ 2 := Real.cos_sq' _
  have h2b : 2 * M - x 0 ≠ 0 := fun h => h2 (by linarith)
  have h2c : M * 2 - x 0 ≠ 0 := fun h => h2 (by linarith)
  have h2d : x 0 - M * 2 ≠ 0 := fun h => h2 (by linarith)
  have h2e : -(M * 2) + x 0 ≠ 0 := fun h => h2 (by linarith)
  have h2f : x 0 + -(M * 2) ≠ 0 := fun h => h2 (by linarith)
  have h2g : -(2 * M) + x 0 ≠ 0 := fun h => h2 (by linarith)
  fin_cases σ <;> fin_cases ν <;>
    simp [Lightlike.ricci, Lightlike.riemann, Fin.sum_univ_three, pd_christoffel_schSlice M hx,
      christoffel_schSlice M hx, schSliceΓ, schSliceDΓ, schSliceRic] <;>
    field_simp <;> (try simp only [hc]) <;> ring

/-- **The scalar curvature of the time-symmetric Schwarzschild slice vanishes** on the chart region. -/
theorem scalarCurvature_schSlice {x : Fin 3 → ℝ} (hx : x ∈ schSliceRegion M) :
    Lightlike.scalarCurvature (schSlice M) x = 0 := by
  have hx' := hx
  obtain ⟨h1, h2, h3⟩ := hx'
  have h1' : x 0 ≠ 0 := h1.ne'
  have hf : 1 - 2 * M / x 0 ≠ 0 := by
    rw [one_sub_div h1']; exact div_ne_zero h2 h1'
  have hd : ∀ i, schSliceD M x i ≠ 0 := by
    intro i; fin_cases i <;> simp [schSliceD, h1', hf, h3]
  simp only [Lightlike.scalarCurvature, ricci_schSlice M hx, schSlice_eq M x,
    Lightlike.inv_diagonal_of_ne hd, Fin.sum_univ_three]
  simp [schSliceRic, schSliceD]
  field_simp
  ring

/-- **The time-symmetric Schwarzschild data satisfy the Hamiltonian constraint**: `ℋ(γ, 0) = 0` at every point
of the chart region. -/
theorem schSlice_hamiltonianConstraint {x : Fin 3 → ℝ} (hx : x ∈ schSliceRegion M) :
    HamiltonianConstraintAt (schSlice M) (fun _ => 0) x := by
  simp [HamiltonianConstraintAt, hamiltonianDensity, kineticDensity, scalarCurvature_schSlice M hx]

/-- **The time-symmetric Schwarzschild data satisfy the momentum constraint** (`π = 0`). -/
theorem schSlice_momentumConstraint (x : Fin 3 → ℝ) :
    MomentumConstraintAt (schSlice M) (fun _ => 0) x := by
  intro i
  simp [momentumDivergence, Lightlike.pd_const]

/-- On the exterior `r > 2M` (away from the axis) the slice metric is positive definite, so the data are
Riemannian initial data. -/
theorem schSlice_posDef {x : Fin 3 → ℝ} (h0 : 0 < x 0) (hr : 2 * M < x 0) (hs : Real.sin (x 1) ≠ 0) :
    (schSlice M x).PosDef := by
  rw [schSlice_eq, Matrix.posDef_diagonal_iff]
  have hf : 0 < 1 - 2 * M / x 0 := by
    rw [sub_pos, div_lt_one h0]; exact hr
  intro i
  fin_cases i <;> simp [schSliceD]
  · rw [div_lt_one h0]; exact hr
  · exact pow_pos h0 2
  · exact mul_pos (pow_pos h0 2) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs)))

/-- Trust check: for `M ≠ 0` the slice is curved (`R_θθ = M/r ≠ 0`), so `scalarCurvature_schSlice` is not a
consequence of flatness. -/
theorem ricci_schSlice_ne_zero (hM : M ≠ 0) {x : Fin 3 → ℝ} (hx : x ∈ schSliceRegion M) :
    Lightlike.ricci (schSlice M) 1 1 x ≠ 0 := by
  rw [ricci_schSlice M hx]
  simp [schSliceRic, hM, hx.1.ne']

/-- Non-vacuity: the chart region of the exterior contains the point `r = 2|M| + 1`, `θ = π/2`. -/
theorem schSliceRegion_nonempty :
    (![2 * |M| + 1, Real.pi / 2, 0] : Fin 3 → ℝ) ∈ schSliceRegion M ∧
      2 * M < (![2 * |M| + 1, Real.pi / 2, 0] : Fin 3 → ℝ) 0 := by
  have hM : M ≤ |M| := le_abs_self M
  have hM0 : 0 ≤ |M| := abs_nonneg M
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp
  · linarith
  · intro h; linarith
  · linarith

end Schwarzschild

/-! ## The spatially flat FLRW slice -/

section FLRW

variable (a : ℝ → ℝ)

/-- The metric induced on the slice at time `t` of the spatially flat FLRW spacetime: the spatial block of
`Lightlike.Cosmology.flrwMetric a 0` at `(t, x)`. -/
def flrwSlice (t : ℝ) : TensorField 3 :=
  fun x => (Lightlike.Cosmology.flrwMetric a 0 (Fin.cons t x)).submatrix Fin.succ Fin.succ

/-- The slice metric is `γ_ij = a(t)² δ_ij` (Aurrekoetxea–Clough–Lim, arXiv:2409.01939v2, eq. (23)). -/
theorem flrwSlice_eq (t : ℝ) (x : Fin 3 → ℝ) :
    flrwSlice a t x = (a t ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  simp [flrwSlice, Lightlike.Cosmology.flrwMetric, diagonal_apply, Fin.succ_inj, one_apply,
    Fin.succ_ne_zero]

/-- The lapse of the FLRW chart is `1`: `g_00 = −1`. -/
theorem flrwMetric_lapse (t : ℝ) (x : Fin 3 → ℝ) :
    Lightlike.Cosmology.flrwMetric a 0 (Fin.cons t x) 0 0 = -1 := by
  simp [Lightlike.Cosmology.flrwMetric]

/-- The shift of the FLRW chart vanishes: `g_{0i} = 0`. -/
theorem flrwMetric_shift (t : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    Lightlike.Cosmology.flrwMetric a 0 (Fin.cons t x) 0 i.succ = 0 := by
  simp [Lightlike.Cosmology.flrwMetric, (Fin.succ_ne_zero i).symm]

/-- The momentum of the FLRW data, `π^{ij} = −2 a'(t) δ^{ij}`. -/
def flrwMomentum (t : ℝ) : TensorField 3 := fun _ => (-2 * deriv a t) • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- **The FLRW momentum is the ADM momentum of the slice**: with lapse `1` and shift `0`
(`flrwMetric_lapse`, `flrwMetric_shift`), Gourgoulhon's (4.104) gives `K_ij = −½ ∂_t γ_ij` (here `−a a' δ_ij`,
that is `K_ij = −H γ_ij` as in Aurrekoetxea–Clough–Lim's (23)), and his (4.108)
`π^{ij} = √γ (K γ^{ij} − K^{ij})` is `flrwMomentum a t`. -/
theorem flrwMomentum_eq {t : ℝ} (ha : DifferentiableAt ℝ a t) (hpos : 0 < a t) (x : Fin 3 → ℝ) :
    flrwMomentum a t x =
      Real.sqrt (flrwSlice a t x).det •
        (((flrwSlice a t x)⁻¹ *
              Matrix.of fun i j => -(1 / 2) * deriv (fun s => flrwSlice a s x i j) t).trace •
            (flrwSlice a t x)⁻¹ -
          (flrwSlice a t x)⁻¹ * (Matrix.of fun i j => -(1 / 2) * deriv (fun s => flrwSlice a s x i j) t) *
            (flrwSlice a t x)⁻¹) := by
  have hK : (Matrix.of fun i j => -(1 / 2) * deriv (fun s => flrwSlice a s x i j) t) =
      (-(a t * deriv a t)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    rw [Matrix.of_apply]
    by_cases hij : i = j
    · subst hij
      have hfun : (fun s => flrwSlice a s x i i) = fun s => a s ^ 2 :=
        funext fun s => by rw [flrwSlice_eq]; simp
      have h : HasDerivAt (fun s => a s ^ 2) (2 * a t * deriv a t) t := by
        convert ha.hasDerivAt.pow 2 using 1; push_cast; ring
      rw [hfun, h.deriv]
      simp
      ring
    · have hfun : (fun s => flrwSlice a s x i j) = fun _ => 0 :=
        funext fun s => by rw [flrwSlice_eq]; simp [hij]
      rw [hfun, deriv_const]
      simp [hij]
  have ha2 : a t ^ 2 ≠ 0 := pow_ne_zero 2 hpos.ne'
  have hinv : ((a t ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹ = (a t ^ 2)⁻¹ • 1 := by
    apply Matrix.inv_eq_left_inv
    rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ ha2, one_smul]
  have hdet : ((a t ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = (a t ^ 3) ^ 2 := by
    rw [det_smul, det_one]; simp; ring
  rw [hK, flrwSlice_eq, hinv, hdet, Real.sqrt_sq (by positivity)]
  unfold flrwMomentum
  ext i j
  simp only [smul_mul_smul_comm, Matrix.one_mul, trace_smul, trace_one, Fintype.card_fin,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- `√det γ = a(t)³` for the FLRW slice (`a(t) > 0`). -/
theorem flrwSlice_sqrt_det {t : ℝ} (hpos : 0 < a t) (x : Fin 3 → ℝ) :
    Real.sqrt (flrwSlice a t x).det = a t ^ 3 := by
  rw [flrwSlice_eq, det_smul, det_one]
  rw [show (a t ^ 2) ^ Fintype.card (Fin 3) * 1 = (a t ^ 3) ^ 2 by simp; ring]
  exact Real.sqrt_sq (by positivity)

/-- The Hamiltonian density of the FLRW data, `ℋ = −6 a a'²` (the slice is flat). -/
theorem flrw_hamiltonianDensity {t : ℝ} (hpos : 0 < a t) (x : Fin 3 → ℝ) :
    hamiltonianDensity (flrwSlice a t) (flrwMomentum a t) x = -6 * a t * deriv a t ^ 2 := by
  have hR : Lightlike.scalarCurvature (flrwSlice a t) x = 0 := by
    have : flrwSlice a t = fun _ => (a t ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
      funext (flrwSlice_eq a t)
    rw [this]
    exact Lightlike.scalarCurvature_eq_zero_of_riemann_eq_zero fun ρ σ μ ν =>
      Lightlike.riemann_const _ ρ σ μ ν x
  have hsq := flrwSlice_sqrt_det a hpos x
  simp only [hamiltonianDensity, kineticDensity, hR, mul_zero, sub_zero, hsq]
  rw [flrwSlice_eq]
  unfold flrwMomentum
  simp only [smul_mul_smul_comm, Matrix.one_mul, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  have ha3 : a t ^ 3 ≠ 0 := pow_ne_zero 3 hpos.ne'
  field_simp
  push_cast
  ring

/-- **FLRW initial data satisfy the Hamiltonian constraint exactly when the first Friedmann equation holds.**
For `a(t) > 0`, the Hamiltonian constraint with the energy density `ρ(t)` of the comoving fluid,
`ℋ + 16πG √γ ρ = 0` (Gourgoulhon's (4.19) times `−√γ`, with `E = ρ`), holds iff
`(a'/a)² = 8πGρ/3` (`k = 0`, `Λ = 0`; Aurrekoetxea–Clough–Lim, eq. (3) and pp. 10-11). -/
theorem flrw_hamiltonian_iff {t : ℝ} (hpos : 0 < a t) (ρ : ℝ → ℝ) (Gn : ℝ) (x : Fin 3 → ℝ) :
    hamiltonianDensity (flrwSlice a t) (flrwMomentum a t) x +
        16 * Real.pi * Gn * Real.sqrt (flrwSlice a t x).det * ρ t = 0 ↔
      Lightlike.Cosmology.FirstFriedmann a ρ 0 0 Gn t := by
  rw [flrw_hamiltonianDensity a hpos, flrwSlice_sqrt_det a hpos]
  have ha : a t ≠ 0 := hpos.ne'
  unfold Lightlike.Cosmology.FirstFriedmann
  rw [zero_div, zero_div, sub_zero, add_zero, div_pow, div_eq_iff (pow_ne_zero 2 ha)]
  constructor
  · intro h
    have h' : a t * (deriv a t ^ 2 - 8 * Real.pi * Gn / 3 * ρ t * a t ^ 2) = 0 := by
      linear_combination (-1 / 6) * h
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 ha
    · linarith
  · intro h
    linear_combination (-6 * a t) * h

/-- **FLRW initial data satisfy the momentum constraint** (zero matter momentum, as for the comoving fluid):
the slice metric and the momentum are constant in space. -/
theorem flrw_momentumConstraint (t : ℝ) (x : Fin 3 → ℝ) :
    MomentumConstraintAt (flrwSlice a t) (flrwMomentum a t) x := by
  have : flrwSlice a t = fun _ => (a t ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := funext (flrwSlice_eq a t)
  intro i
  rw [this]
  simp [momentumDivergence, flrwMomentum, Lightlike.christoffel_const, Lightlike.pd_const]

/-- Non-vacuity: de Sitter. For `a(t) = e^{Ht}` and the constant density `ρ_Λ` with `H² = 8πGρ_Λ/3`, the FLRW
data satisfy the Hamiltonian constraint at every time (through `Lightlike.Cosmology.deSitter_friedmann_iff`). -/
theorem deSitter_hamiltonianConstraint (H ρΛ Gn : ℝ) (hH : H ^ 2 = 8 * Real.pi * Gn * ρΛ / 3)
    (t : ℝ) (x : Fin 3 → ℝ) :
    hamiltonianDensity (flrwSlice (fun t => Real.exp (H * t)) t)
        (flrwMomentum (fun t => Real.exp (H * t)) t) x +
      16 * Real.pi * Gn * Real.sqrt (flrwSlice (fun t => Real.exp (H * t)) t x).det * ρΛ = 0 :=
  (flrw_hamiltonian_iff (fun t => Real.exp (H * t)) (Real.exp_pos _) (fun _ => ρΛ) Gn x).2
    (((Lightlike.Cosmology.deSitter_friedmann_iff H ρΛ Gn).2 hH t).1)

/-- Trust check: without matter an expanding slice violates the Hamiltonian constraint. For
`a(t) = e^{Ht}` with `H ≠ 0` and `ρ = 0`, `ℋ ≠ 0`. -/
theorem expanding_vacuum_violates (H : ℝ) (hH : H ≠ 0) (Gn t : ℝ) (x : Fin 3 → ℝ) :
    hamiltonianDensity (flrwSlice (fun t => Real.exp (H * t)) t)
        (flrwMomentum (fun t => Real.exp (H * t)) t) x +
      16 * Real.pi * Gn * Real.sqrt (flrwSlice (fun t => Real.exp (H * t)) t x).det * 0 ≠ 0 := by
  intro h
  have hF := (flrw_hamiltonian_iff (fun t => Real.exp (H * t)) (Real.exp_pos _) (fun _ => 0) Gn x).1 h
  unfold Lightlike.Cosmology.FirstFriedmann at hF
  have hd : deriv (fun t => Real.exp (H * t)) t = H * Real.exp (H * t) := by
    simpa [mul_comm] using (((hasDerivAt_id t).const_mul H).exp).deriv
  rw [hd] at hF
  have he := (Real.exp_pos (H * t)).ne'
  field_simp at hF
  simp at hF
  exact hH hF

end FLRW

end Lightlike.Canonical
