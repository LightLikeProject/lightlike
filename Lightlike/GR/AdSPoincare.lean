import Lightlike.GR.Schwarzschild

/-!
# Anti-de Sitter space in the Poincaré patch

In coordinates `(t, x, y, z) = (y 0, y 1, y 2, y 3)` with `z > 0`, the Poincaré patch of
anti-de Sitter space of radius `L` has the metric
`ds² = (L²/z²) (-dt² + dx² + dy² + dz²)`
(`adsMetric`). It is a smooth Lorentzian coordinate metric for `z > 0`
(`isCoordMetric_ads`, `ads_isLorentzian`) and solves the vacuum Einstein equations with the
cosmological constant `Λ = -3/L²` (`ads_isVacuumSolution`): `Ric = Λ g`.

Gap row G3-022. The comparison with Carroll, *Spacetime and Geometry*, ch. 8, and the AdS/CFT
literature (Maldacena 1999) is pending: not read at a location.
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (L : ℝ)

/-- The diagonal entries `(L²/z²) (-1, 1, 1, 1)` of the Poincaré metric. -/
def adsD (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-(L ^ 2 / y 3 ^ 2), L ^ 2 / y 3 ^ 2, L ^ 2 / y 3 ^ 2, L ^ 2 / y 3 ^ 2]

/-- The Poincaré patch metric of anti-de Sitter space of radius `L`. -/
def adsMetric : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ := fun y => diagonal (adsD L y)

/-- The Poincaré patch `z > 0`. -/
def adsU : Set (Fin 4 → ℝ) := {y | 0 < y 3}

lemma isOpen_adsU : IsOpen adsU := isOpen_lt continuous_const (continuous_apply 3)

/-- The Poincaré metric is a coordinate metric on `z > 0` (`L ≠ 0`). -/
theorem isCoordMetric_ads (hL : L ≠ 0) : IsCoordMetric (adsMetric L) adsU := by
  have hz : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 3) adsU :=
    (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 3).contDiffOn
  have hz0 : ∀ y ∈ adsU, y 3 ≠ 0 := fun y hy => hy.ne'
  have hq : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => L ^ 2 / y 3 ^ 2) adsU :=
    contDiffOn_const.div (hz.pow 2) fun y hy => pow_ne_zero 2 (hz0 y hy)
  refine isCoordMetric_diagonal (adsD L) isOpen_adsU (fun i => ?_) (fun y hy i => ?_)
  · fin_cases i <;> simp only [adsD, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> first | exact hq.neg | exact hq
  · have := hz0 y hy
    have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
    fin_cases i <;> simp [adsD, this, hL2]

/-- Coordinate derivatives `∂_k g_ii` of the Poincaré metric. -/
def adsDD (k i : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if k = 3 then (if i = 0 then 2 * L ^ 2 / y 3 ^ 3 else -(2 * L ^ 2 / y 3 ^ 3)) else 0

lemma pd_adsD {y : Fin 4 → ℝ} (hz : y 3 ≠ 0) (k i : Fin 4) :
    pd k (fun y => adsD L y i) y = adsDD L k i y := by
  have hb : HasDerivAt (fun z => L ^ 2 / z ^ 2) (-(2 * L ^ 2 / y 3 ^ 3)) (y 3) :=
    ((hasDerivAt_const (y 3) (L ^ 2)).div (hasDerivAt_pow 2 (y 3)) (pow_ne_zero 2 hz)).congr_deriv
      (by field_simp; ring)
  have c1 := pd_coord (n := 4) 3 k hb
  have c0 := pd_coord (n := 4) 3 k hb.neg
  fin_cases i <;> simp only [adsD, adsDD] <;> simp
  · simpa using c0
  all_goals simpa using c1

/-- The expected Christoffel symbols (`Γ^z_{zz} = Γ^i_{iz} = -1/z`, `Γ^z_{jj} = ±1/z`). -/
def adsΓ (i j k : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if i = 3 ∧ j = 3 ∧ k = 3 then -(1 / y 3)
  else if i ≠ 3 ∧ ((j = i ∧ k = 3) ∨ (j = 3 ∧ k = i)) then -(1 / y 3)
  else if i = 3 ∧ j = k ∧ j ≠ 3 then (if j = 0 then -(1 / y 3) else 1 / y 3)
  else 0

lemma christoffel_ads {y : Fin 4 → ℝ} (hz : y 3 ≠ 0) (hL : L ≠ 0) (i j k : Fin 4) :
    christoffel (adsMetric L) i j k y = adsΓ i j k y := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hd : ∀ i, adsD L y i ≠ 0 := by
    intro i; fin_cases i <;> simp [adsD, hz, hL2]
  change christoffel (fun y => diagonal (adsD L y)) i j k y = _
  rw [christoffel_diagonal _ y hd]
  simp only [pd_adsD L hz]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [adsΓ, adsDD, adsD] <;> field_simp <;> ring

/-- Coordinate derivatives of the expected Christoffel symbols. -/
def adsDΓ (m i j k : Fin 4) (y : Fin 4 → ℝ) : ℝ :=
  if m = 3 then
    (if i = 3 ∧ j = 3 ∧ k = 3 then 1 / y 3 ^ 2
     else if i ≠ 3 ∧ ((j = i ∧ k = 3) ∨ (j = 3 ∧ k = i)) then 1 / y 3 ^ 2
     else if i = 3 ∧ j = k ∧ j ≠ 3 then (if j = 0 then 1 / y 3 ^ 2 else -(1 / y 3 ^ 2))
     else 0)
  else 0

lemma pd_adsΓ {y : Fin 4 → ℝ} (hz : y 3 ≠ 0) (m i j k : Fin 4) :
    pd m (fun y => adsΓ i j k y) y = adsDΓ m i j k y := by
  have d1 : HasDerivAt (fun z : ℝ => -(1 / z)) (1 / y 3 ^ 2) (y 3) :=
    (((hasDerivAt_const (y 3) (1 : ℝ)).div (hasDerivAt_id' (y 3)) hz).neg).congr_deriv (by
      field_simp; ring)
  have d2 : HasDerivAt (fun z : ℝ => 1 / z) (-(1 / y 3 ^ 2)) (y 3) :=
    ((hasDerivAt_const (y 3) (1 : ℝ)).div (hasDerivAt_id' (y 3)) hz).congr_deriv (by
      field_simp; ring)
  have c1 := pd_coord (n := 4) 3 m d1
  have c2 := pd_coord (n := 4) 3 m d2
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [adsΓ, adsDΓ] <;> (try simp) <;>
    first
    | simpa using c1
    | simpa using c2
    | simp [pd_const]

lemma pd_christoffel_ads {y : Fin 4 → ℝ} (hz : y 3 ≠ 0) (hL : L ≠ 0) (m i j k : Fin 4) :
    pd m (christoffel (adsMetric L) i j k) y = adsDΓ m i j k y := by
  have hev : christoffel (adsMetric L) i j k =ᶠ[nhds y] fun y => adsΓ i j k y :=
    Filter.eventually_of_mem ((isOpen_ne_fun (continuous_apply 3) continuous_const).mem_nhds hz)
      fun w hw => christoffel_ads L hw hL i j k
  rw [pd_congr hev, pd_adsΓ hz]

/-- **The Ricci tensor of the Poincaré patch is `-(3/L²) g`.** -/
theorem ricci_ads {y : Fin 4 → ℝ} (hz : y 3 ≠ 0) (hL : L ≠ 0) (σ ν : Fin 4) :
    ricci (adsMetric L) σ ν y = -(3 / L ^ 2) * adsMetric L y σ ν := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  fin_cases σ <;> fin_cases ν <;>
    simp [ricci, riemann, Fin.sum_univ_four, pd_christoffel_ads L hz hL, christoffel_ads L hz hL,
      adsΓ, adsDΓ, adsMetric, adsD] <;> field_simp <;> ring

/-- The scalar curvature of the Poincaré patch is `-12/L²`. -/
theorem scalarCurvature_ads {y : Fin 4 → ℝ} (hz : y 3 ≠ 0) (hL : L ≠ 0) :
    scalarCurvature (adsMetric L) y = -(12 / L ^ 2) := by
  have hL2 : L ^ 2 ≠ 0 := pow_ne_zero 2 hL
  have hd : ∀ i, adsD L y i ≠ 0 := by
    intro i; fin_cases i <;> simp [adsD, hz, hL2]
  unfold scalarCurvature
  simp only [adsMetric, inv_diagonal_of_ne hd]
  simp [ricci_ads L hz hL, Fin.sum_univ_four, adsMetric, adsD, diagonal_apply]
  field_simp
  ring

/-- **The Poincaré patch of anti-de Sitter space solves the vacuum Einstein equations with
cosmological constant `Λ = -3/L²`**: `G_{μν} + Λ g_{μν} = 0`. -/
theorem ads_isVacuumSolution (hL : L ≠ 0) : IsVacuumSolution (-(3 / L ^ 2)) (adsMetric L) adsU :=
  ⟨isCoordMetric_ads L hL, fun y hy μ ν => by
    have hz : y 3 ≠ 0 := hy.ne'
    simp only [einsteinTensor, scalarCurvature_ads L hz hL, ricci_ads L hz hL]
    ring⟩

/-- **Signature.** The Poincaré patch has Lorentzian signature: `g = Pᵀ η P` for
`P = (L/z) · 1`. -/
theorem ads_isLorentzian (hL : L ≠ 0) : IsLorentzianCoordMetric (adsMetric L) adsU := by
  refine ⟨isCoordMetric_ads L hL, fun y hy => ?_⟩
  have hz : y 3 ≠ 0 := hy.ne'
  refine ⟨diagonal ![L / y 3, L / y 3, L / y 3, L / y 3], ?_, ?_⟩
  · rw [det_diagonal, Fin.prod_univ_four]
    simp [hL, hz]
  · rw [diagonal_transpose, eta, diagonal_mul_diagonal, diagonal_mul_diagonal]
    simp only [adsMetric]
    congr 1
    ext i
    fin_cases i <;> simp [adsD, etaDiag] <;> field_simp

/-- **Wrong-model control.** The Poincaré patch is not a solution with `Λ = 0`: it is not Ricci-flat. -/
theorem ads_not_vacuumSolution_zero (hL : L ≠ 0) : ¬ IsVacuumSolution 0 (adsMetric L) adsU := by
  intro h
  have hy : (![0, 0, 0, 1] : Fin 4 → ℝ) ∈ adsU := by simp [adsU]
  have := h.2 _ hy 0 0
  have hz : (![0, 0, 0, 1] : Fin 4 → ℝ) 3 ≠ 0 := by simp
  simp only [einsteinTensor, scalarCurvature_ads L hz hL, ricci_ads L hz hL] at this
  simp [adsMetric, adsD, hL] at this
  field_simp at this
  nlinarith [sq_pos_of_ne_zero hL]

end Lightlike
