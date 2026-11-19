import Lightlike.GR.EuclideanSchwarzschild
import Lightlike.Spacetime.ChartChange
import Lightlike.Spacetime.RicciContinuous
import Lightlike.Spacetime.SchwarzschildManifold

/-!
# The cigar: Euclidean Schwarzschild is smooth at the horizon exactly for `β = 8πM`

Near the horizon `r = 2M` put `r = 2M + σ²` and `ψ = τ/(4M)`: the Euclidean Schwarzschild metric
becomes `A(σ²) dσ² + B(σ²) σ² dψ²` with `A(0) = B(0) = 8M`, the metric of a smooth surface in
polar coordinates `(σ, ψ)` if `ψ` has period `2π`, that is `τ` has period `β = 8πM`; otherwise there is a
conical singularity. In the Cartesian coordinates `(x, y) = σ (cos ψ, sin ψ)` the metric is the explicit,
smooth, everywhere defined
`B(s) (dx² + dy²) + C(s) (x dx + y dy)² + (2M + s)² dΩ²`,  `s = x² + y²`,
`B(s) = 16M²/(s + 2M)`, `C(s) = 4(s + 4M)/(s + 2M)` (`cigMetric`): a coordinate metric on all
`(x, y) ∈ ℝ²` (`isCoordMetric_cig`), the pullback of Euclidean Schwarzschild by the polar map away from the
origin (`pullback_cig_euc`), Ricci-flat everywhere including the origin (`ricci_cig_eq_zero`), so
Euclidean Schwarzschild closes smoothly at `r = 2M` iff `τ` has period `8πM`
(`cigChange_periodic`).

Gap row G1-058.
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

/-- `B(s) = 16 M² / (s + 2M)`. -/
def cigB (s : ℝ) : ℝ := 16 * M ^ 2 / (s + 2 * M)

/-- `C(s) = 4 (s + 4M) / (s + 2M)`. -/
def cigC (s : ℝ) : ℝ := 4 * (s + 4 * M) / (s + 2 * M)

/-- The cigar metric in coordinates `(x, y, θ, φ)`:
`B (dx² + dy²) + C (x dx + y dy)² + (2M + s)² dΩ²`, `s = x² + y²`. -/
def cigMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let s := y 0 ^ 2 + y 1 ^ 2
  !![cigB M s + cigC M s * y 0 ^ 2, cigC M s * (y 0 * y 1), 0, 0;
     cigC M s * (y 0 * y 1), cigB M s + cigC M s * y 1 ^ 2, 0, 0;
     0, 0, (2 * M + s) ^ 2, 0;
     0, 0, 0, (2 * M + s) ^ 2 * sin (y 2) ^ 2]

/-- The domain: all `(x, y)`, `0 < θ < π`. -/
def cigU : Set (Fin 4 → ℝ) := {y | 0 < y 2 ∧ y 2 < π}

lemma isOpen_cigU : IsOpen cigU :=
  (isOpen_lt continuous_const (continuous_apply 2)).inter (isOpen_lt (continuous_apply 2) continuous_const)

lemma cigB_pos (hM : 0 < M) {s : ℝ} (hs : 0 ≤ s) : 0 < cigB M s := by
  unfold cigB; positivity

lemma cigC_pos (hM : 0 < M) {s : ℝ} (hs : 0 ≤ s) : 0 < cigC M s := by
  unfold cigC; positivity

/-- The determinant of the cigar metric is `B (B + C s) (2M + s)⁴ sin²θ`. -/
lemma det_cigMetric (y : Fin 4 → ℝ) :
    (cigMetric M y).det = cigB M (y 0 ^ 2 + y 1 ^ 2) *
      (cigB M (y 0 ^ 2 + y 1 ^ 2) + cigC M (y 0 ^ 2 + y 1 ^ 2) * (y 0 ^ 2 + y 1 ^ 2)) *
      ((2 * M + (y 0 ^ 2 + y 1 ^ 2)) ^ 4 * sin (y 2) ^ 2) := by
  simp [cigMetric, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **The cigar metric is a coordinate metric for every `(x, y)`**: smooth, symmetric, invertible,
also at the origin (`M > 0`). -/
theorem isCoordMetric_cig (hM : 0 < M) : IsCoordMetric (cigMetric M) cigU where
  isOpen := isOpen_cigU
  symm := fun y _ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cigMetric] <;> ring
  isUnit_det := fun y hy => by
    rw [det_cigMetric]
    have hs : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
    have hsin := sin_pos_of_pos_of_lt_pi hy.1 hy.2
    have hB := cigB_pos M hM hs
    have hC := cigC_pos M hM hs
    refine (mul_ne_zero (mul_ne_zero hB.ne' (by positivity)) (by positivity)).isUnit
  smooth := fun i j => by
    have hx : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 0 := by fun_prop
    have hy : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1 := by fun_prop
    have hθ : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 2 := by fun_prop
    have hs : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 0 ^ 2 + y 1 ^ 2 := by fun_prop
    have hne : ∀ y : Fin 4 → ℝ, y 0 ^ 2 + y 1 ^ 2 + 2 * M ≠ 0 := fun y => by
      have : 0 ≤ y 0 ^ 2 + y 1 ^ 2 := by positivity
      linarith
    have hB : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => cigB M (y 0 ^ 2 + y 1 ^ 2) :=
      contDiff_const.div (hs.add contDiff_const) hne
    have hC : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => cigC M (y 0 ^ 2 + y 1 ^ 2) :=
      (contDiff_const.mul (hs.add contDiff_const)).div (hs.add contDiff_const) hne
    refine ContDiff.contDiffOn ?_
    fin_cases i <;> fin_cases j <;> simp only [cigMetric] <;> simp <;>
      first
      | exact contDiff_const
      | exact hB.add (hC.mul (hx.pow 2))
      | exact hC.mul (hx.mul hy)
      | exact hB.add (hC.mul (hy.pow 2))
      | exact (contDiff_const.add hs).pow 2
      | exact ((contDiff_const.add hs).pow 2).mul ((Real.contDiff_sin.comp hθ).pow 2)

/-! ## The polar chart change -/

/-- The polar change of coordinates from Euclidean Schwarzschild `(τ, r, θ, φ)` to the cigar
`(x, y, θ, φ)`: `(x, y) = √(r - 2M) (cos (τ/(4M)), sin (τ/(4M)))`. -/
def cigChange (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![√(y 1 - 2 * M) * cos (y 0 / (4 * M)), √(y 1 - 2 * M) * sin (y 0 / (4 * M)), y 2, y 3]

/-- The exterior region `r > 2M`, `0 < θ < π`. -/
def eucU : Set (Fin 4 → ℝ) := {y | 2 * M < y 1 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_eucU : IsOpen (eucU M) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))

/-- The Jacobian of the polar map. -/
lemma jac_cigChange (hM : 0 < M) {y : Fin 4 → ℝ} (hr : 2 * M < y 1) :
    jac (cigChange M) y =
      !![-(√(y 1 - 2 * M) * sin (y 0 / (4 * M))) / (4 * M),
          cos (y 0 / (4 * M)) / (2 * √(y 1 - 2 * M)), 0, 0;
         √(y 1 - 2 * M) * cos (y 0 / (4 * M)) / (4 * M),
          sin (y 0 / (4 * M)) / (2 * √(y 1 - 2 * M)), 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] := by
  have hq : 0 < y 1 - 2 * M := by linarith
  have hsq : HasDerivAt (fun r : ℝ => √(r - 2 * M)) (1 / (2 * √(y 1 - 2 * M))) (y 1) := by
    have := ((hasDerivAt_id' (y 1)).sub_const (2 * M)).sqrt hq.ne'
    simpa using this
  have hc : HasDerivAt (fun t : ℝ => cos (t / (4 * M))) (-(sin (y 0 / (4 * M))) / (4 * M)) (y 0) :=
    (((hasDerivAt_id' (y 0)).div_const (4 * M)).cos).congr_deriv (by ring)
  have hsn : HasDerivAt (fun t : ℝ => sin (t / (4 * M))) (cos (y 0 / (4 * M)) / (4 * M)) (y 0) :=
    (((hasDerivAt_id' (y 0)).div_const (4 * M)).sin).congr_deriv (by ring)
  have Px : ∀ k : Fin 4, pd k (fun z => √(z 1 - 2 * M) * cos (z 0 / (4 * M))) y =
      (if k = 1 then 1 / (2 * √(y 1 - 2 * M)) else 0) * cos (y 0 / (4 * M)) +
        √(y 1 - 2 * M) * (if k = 0 then -(sin (y 0 / (4 * M))) / (4 * M) else 0) := fun k =>
    pd_coord_mul (n := 4) 1 0 k hsq hc
  have Py : ∀ k : Fin 4, pd k (fun z => √(z 1 - 2 * M) * sin (z 0 / (4 * M))) y =
      (if k = 1 then 1 / (2 * √(y 1 - 2 * M)) else 0) * sin (y 0 / (4 * M)) +
        √(y 1 - 2 * M) * (if k = 0 then cos (y 0 / (4 * M)) / (4 * M) else 0) := fun k =>
    pd_coord_mul (n := 4) 1 0 k hsq hsn
  have P2 : ∀ k : Fin 4, pd k (fun z => z 2) y = if k = 2 then 1 else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_id' (y 2))
  have P3 : ∀ k : Fin 4, pd k (fun z => z 3) y = if k = 3 then 1 else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_id' (y 3))
  have hq' : √(y 1 - 2 * M) ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  ext μ a
  fin_cases μ <;> fin_cases a <;> simp only [jac, cigChange] <;>
    simp [Px, Py, P2, P3] <;> field_simp <;> ring

/-- **Euclidean Schwarzschild in cigar coordinates**: the pullback of the cigar metric by the polar map
is the Euclidean Schwarzschild metric, for `r > 2M`. -/
lemma pullback_cig_euc (hM : 0 < M) {y : Fin 4 → ℝ} (hr : 2 * M < y 1) :
    pullback (cigMetric M) (cigChange M) y = Matrix.diagonal (eucD M y) := by
  have hq : 0 < y 1 - 2 * M := by linarith
  rw [pullback_eq_mul, jac_cigChange M hM hr]
  have hq0 : 0 < √(y 1 - 2 * M) := Real.sqrt_pos.2 hq
  have hq2 : √(y 1 - 2 * M) ^ 2 = y 1 - 2 * M := Real.sq_sqrt hq.le
  have hcs := sin_sq_add_cos_sq (y 0 / (4 * M))
  have hr0 : y 1 ≠ 0 := by linarith
  have hM0 : M ≠ 0 := hM.ne'
  have hs : (√(y 1 - 2 * M) * cos (y 0 / (4 * M))) ^ 2 + (√(y 1 - 2 * M) * sin (y 0 / (4 * M))) ^ 2 =
      y 1 - 2 * M := by nlinarith [hcs, hq2]
  have hmetric : cigMetric M (cigChange M y) =
      !![cigB M (y 1 - 2 * M) + cigC M (y 1 - 2 * M) * (√(y 1 - 2 * M) * cos (y 0 / (4 * M))) ^ 2,
         cigC M (y 1 - 2 * M) * ((√(y 1 - 2 * M) * cos (y 0 / (4 * M))) *
           (√(y 1 - 2 * M) * sin (y 0 / (4 * M)))), 0, 0;
         cigC M (y 1 - 2 * M) * ((√(y 1 - 2 * M) * cos (y 0 / (4 * M))) *
           (√(y 1 - 2 * M) * sin (y 0 / (4 * M)))),
         cigB M (y 1 - 2 * M) + cigC M (y 1 - 2 * M) * (√(y 1 - 2 * M) * sin (y 0 / (4 * M))) ^ 2,
           0, 0;
         0, 0, (2 * M + (y 1 - 2 * M)) ^ 2, 0;
         0, 0, 0, (2 * M + (y 1 - 2 * M)) ^ 2 * sin (y 2) ^ 2] := by
    simp only [cigMetric, cigChange, Matrix.cons_val_zero, Matrix.cons_val_one, hs]
    rfl
  rw [hmetric]
  generalize √(y 1 - 2 * M) = q at *
  generalize cos (y 0 / (4 * M)) = c at *
  generalize sin (y 0 / (4 * M)) = sn at *
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, eucD, cigB, cigC, Matrix.diagonal_apply] <;>
    first | rfl | skip
  all_goals (field_simp; grind)

/-- The polar map is a chart change from the exterior to the cigar (its Jacobian determinant is the
constant `-1/(8M)`). -/
theorem isChartChange_cigChange (hM : 0 < M) : IsChartChange (cigChange M) (eucU M) cigU where
  isOpen := isOpen_eucU M
  mapsTo := fun y hy => ⟨by simpa [cigChange] using hy.2.1, by simpa [cigChange] using hy.2.2⟩
  smooth := fun μ => by
    have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => √(y 1 - 2 * M)) (eucU M) :=
      ContDiffOn.sqrt ((by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1 - 2 * M).contDiffOn)
        fun y hy => by have := hy.1; linarith
    have hc : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => cos (y 0 / (4 * M)) := by fun_prop
    have hsn : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => sin (y 0 / (4 * M)) := by fun_prop
    fin_cases μ <;> simp only [cigChange, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> simp
    · exact hr.mul hc.contDiffOn
    · exact hr.mul hsn.contDiffOn
    · exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 2).contDiffOn
    · exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 3).contDiffOn
  isUnit_det := fun y hy => by
    have hr := hy.1
    have hq : 0 < y 1 - 2 * M := by linarith
    have hq0 : 0 < √(y 1 - 2 * M) := Real.sqrt_pos.2 hq
    rw [jac_cigChange M hM hr]
    have hcs := sin_sq_add_cos_sq (y 0 / (4 * M))
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    have : -(√(y 1 - 2 * M) * sin (y 0 / (4 * M))) / (4 * M) * (sin (y 0 / (4 * M)) / (2 * √(y 1 - 2 * M))) -
        cos (y 0 / (4 * M)) / (2 * √(y 1 - 2 * M)) * (√(y 1 - 2 * M) * cos (y 0 / (4 * M)) / (4 * M)) =
        -(1 / (8 * M)) := by
      field_simp; grind
    rw [← sub_eq_add_neg, this]
    have : 0 < 1 / (8 * M) := by positivity
    linarith

/-- Every point of the cigar chart off the axis `x = y = 0` is the polar image of an exterior point. -/
lemma exists_cigChange_eq (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ cigU)
    (h0 : 0 < z 0 ^ 2 + z 1 ^ 2) : ∃ y ∈ eucU M, cigChange M y = z := by
  set w : ℂ := ⟨z 0, z 1⟩ with hw
  have hn2 : ‖w‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hw]; ring
  have hn : 0 < ‖w‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hn2; nlinarith
  refine ⟨![4 * M * Complex.arg w, 2 * M + ‖w‖ ^ 2, z 2, z 3], ⟨by simp; positivity, by simpa using hz.1,
    by simpa using hz.2⟩, ?_⟩
  have hsq : √(2 * M + ‖w‖ ^ 2 - 2 * M) = ‖w‖ := by
    rw [show 2 * M + ‖w‖ ^ 2 - 2 * M = ‖w‖ ^ 2 by ring]; exact Real.sqrt_sq hn.le
  have hM0 : M ≠ 0 := hM.ne'
  have e0 : 4 * M * Complex.arg w / (4 * M) = Complex.arg w := by field_simp
  ext i
  fin_cases i
  · simp [cigChange, hsq, e0]
    have := Complex.norm_mul_cos_arg w
    simpa [hw] using this
  · simp [cigChange, hsq, e0]
    have := Complex.norm_mul_sin_arg w
    simpa [hw] using this
  · simp [cigChange]
  · simp [cigChange]

/-- **Ricci-flatness off the axis**, from the pullback identity. -/
theorem ricci_cig_of_pos (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ cigU)
    (h0 : 0 < z 0 ^ 2 + z 1 ^ 2) (b d : Fin 4) : ricci (cigMetric M) b d z = 0 := by
  obtain ⟨y, hy, rfl⟩ := exists_cigChange_eq M hM hz h0
  have hφ := isChartChange_cigChange M hM
  have hzero : ∀ b d, ricci (pullback (cigMetric M) (cigChange M)) b d y = 0 := fun b d => by
    rw [ricci_congr_on (isOpen_eucU M) (fun y' hy' => pullback_cig_euc M hM hy'.1) hy]
    exact ricci_euc M ⟨by linarith [hy.1, hM], by linarith [hy.1], (sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2).ne'⟩ b d
  set R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun ν l => ricci (cigMetric M) ν l (cigChange M y)
  set J := jac (cigChange M) y
  have hJ : IsUnit J.det := hφ.isUnit_det y hy
  have hmul : Jᵀ * R * J = 0 := by
    ext b d
    have := hzero b d
    rw [ricci_pullback (isCoordMetric_cig M hM) hφ hy] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, R, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hR : R = 0 := by
    have hJt : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
    have h1 : R * J = 0 := by
      have := congrArg (fun A => (Jᵀ)⁻¹ * A) hmul
      simp only [mul_zero, Matrix.mul_assoc] at this
      rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJt, Matrix.one_mul] at this
    have := congrArg (fun A => A * J⁻¹) h1
    simp only [zero_mul, Matrix.mul_assoc] at this
    rwa [Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one] at this
  have := congrFun (congrFun hR b) d
  simpa [R] using this

/-- **The cigar metric is Ricci-flat everywhere, including the tip `x = y = 0`** (by continuity of the
Ricci tensor, from the points off the axis). -/
theorem ricci_cig_eq_zero (hM : 0 < M) {z : Fin 4 → ℝ} (hz : z ∈ cigU) (b d : Fin 4) :
    ricci (cigMetric M) b d z = 0 := by
  by_cases h0 : 0 < z 0 ^ 2 + z 1 ^ 2
  · exact ricci_cig_of_pos M hM hz h0 b d
  have hx : z 0 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hy : z 1 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have hcont : ContinuousAt (ricci (cigMetric M) b d) z :=
    (continuousOn_ricci (isCoordMetric_cig M hM) b d).continuousAt (isOpen_cigU.mem_nhds hz)
  set c : ℝ → Fin 4 → ℝ := fun t => z + t • Pi.single 0 1 with hc
  have hcc : Continuous c := continuous_const.add (continuous_id.smul continuous_const)
  have hc0 : c 0 = z := by simp [hc]
  have hlim : Filter.Tendsto (fun t => ricci (cigMetric M) b d (c t)) (nhds 0)
      (nhds (ricci (cigMetric M) b d z)) := by
    have h0 := hcc.tendsto 0
    rw [hc0] at h0
    exact hcont.tendsto.comp h0
  have hzero : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, ricci (cigMetric M) b d (c t) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht0
    have h1 : (c t) 0 = t := by simp [hc, hx]
    have h2 : (c t) 1 = 0 := by simp [hc, hy, Pi.single_apply]
    have h3 : (c t) 2 = z 2 := by simp [hc, Pi.single_apply]
    refine ricci_cig_of_pos M hM ⟨by rw [h3]; exact hz.1, by rw [h3]; exact hz.2⟩ ?_ b d
    rw [h1, h2]; have : t ≠ 0 := ht0
    positivity
  have h0' : Filter.Tendsto (fun t => ricci (cigMetric M) b d (c t)) (nhdsWithin (0 : ℝ) {0}ᶜ)
      (nhds 0) := tendsto_const_nhds.congr' (hzero.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique (hlim.mono_left nhdsWithin_le_nhds) h0'

/-- **The cigar metric solves the vacuum Einstein equations on all of `ℝ² × S²`-chart, including the
tip.** -/
theorem cig_isVacuumSolution (hM : 0 < M) : IsVacuumSolution 0 (cigMetric M) cigU :=
  ⟨isCoordMetric_cig M hM, fun y hy μ ν => by
    simp [einsteinTensor, scalarCurvature, ricci_cig_eq_zero M hM hy]⟩

/-- **The period.** The polar map is invariant under `τ ↦ τ + 8πM`, the shift by which the angle `τ/(4M)` advances by `2π`
(minimality of this period is not proved here). So Euclidean Schwarzschild, glued at
`r = 2M` into the smooth, Ricci-flat cigar, has `τ`-period `β = 8πM`; any other period leaves a conical
singularity at the tip. -/
theorem cigChange_periodic (hM : 0 < M) (y : Fin 4 → ℝ) :
    cigChange M (y + (8 * π * M) • Pi.single 0 1) = cigChange M y := by
  have hM0 : M ≠ 0 := hM.ne'
  have h : (y 0 + 8 * π * M) / (4 * M) = y 0 / (4 * M) + 2 * π := by field_simp; ring
  ext i
  fin_cases i <;> simp [cigChange, Pi.single_apply, h, cos_add_two_pi, sin_add_two_pi]

end Lightlike
