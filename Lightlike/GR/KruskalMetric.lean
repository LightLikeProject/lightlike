import Lightlike.GR.KruskalFunction
import Lightlike.GR.EddingtonFinkelstein
import Lightlike.Spacetime.ChartChange
import Lightlike.Spacetime.RicciContinuous

/-!
# The Kruskal–Szekeres metric

In coordinates `(T, X, θ, φ)` on `X² - T² > -1`,
`ds² = h(r)(-dT² + dX²) + r² dΩ²`, `h(r) = (32M³/r) e^{-r/2M}`, `r = kG(X² - T²)`
(`kruskalMetric`), the radius being the inverse of `F(r) = (r/2M - 1) e^{r/2M}` (`KruskalFunction`).
It is a coordinate metric on all of `X² - T² > -1` (`isCoordMetric_kruskal`), also across the horizon
`T = ±X`. The chart change from ingoing Eddington–Finkelstein `(v, r, θ, φ)`,
`T = (e^{v/4M} - F(r) e^{-v/4M})/2`, `X = (e^{v/4M} + F(r) e^{-v/4M})/2` (`kruskalChange`) pulls the
Kruskal metric back to the EF metric (`pullback_kruskal_ef`).

Gap row G1-020. Comparison with Kruskal (1960), Szekeres (1960) and Carroll, ch. 5: pending.
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- The conformal factor `h(r) = (32M³/r) e^{-r/2M}`. -/
def kh (r : ℝ) : ℝ := 32 * M ^ 3 / r * exp (-(r / (2 * M)))

/-- The radius as a function of the Kruskal coordinates: `r = kG(X² - T²)`. -/
def kr (y : Fin 4 → ℝ) : ℝ := kG M (y 1 ^ 2 - y 0 ^ 2)

/-- The Kruskal metric in coordinates `(T, X, θ, φ)`. -/
def kruskalMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-kh M (kr M y), 0, 0, 0;
     0, kh M (kr M y), 0, 0;
     0, 0, kr M y ^ 2, 0;
     0, 0, 0, kr M y ^ 2 * sin (y 2) ^ 2]

/-- The domain `X² - T² > -1`, `0 < θ < π`. -/
def kruskalU : Set (Fin 4 → ℝ) := {y | -1 < y 1 ^ 2 - y 0 ^ 2 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_kruskalU : IsOpen kruskalU :=
  (isOpen_lt (continuous_const : Continuous fun _ : Fin 4 → ℝ => (-1 : ℝ))
    (by fun_prop : Continuous fun y : Fin 4 → ℝ => y 1 ^ 2 - y 0 ^ 2)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))

lemma kr_pos (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) : 0 < kr M y :=
  kG_pos M hM hy.1

lemma contDiffAt_kr (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ kruskalU) :
    ContDiffAt ℝ ∞ (kr M) y := by
  have h1 : ContDiffAt ℝ ∞ (kG M) (y 1 ^ 2 - y 0 ^ 2) := contDiffAt_kG M hM hy.1
  exact h1.comp y (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1 ^ 2 - y 0 ^ 2).contDiffAt

lemma contDiffAt_kh (hM : 0 < M) {r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ∞ (kh M) r := by
  unfold kh
  exact (contDiffAt_const.div contDiffAt_id hr.ne').mul (by fun_prop : ContDiff ℝ ∞ fun r : ℝ => exp (-(r / (2 * M)))).contDiffAt

/-- **The Kruskal metric is a coordinate metric on all of `X² - T² > -1`.** -/
theorem isCoordMetric_kruskal (hM : 0 < M) : IsCoordMetric (kruskalMetric M) kruskalU where
  isOpen := isOpen_kruskalU
  symm := fun y _ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [kruskalMetric]
  isUnit_det := fun y hy => by
    have hr := kr_pos M hM hy
    have hs := sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2
    have hh : 0 < kh M (kr M y) := by unfold kh; positivity
    have : (kruskalMetric M y).det = -(kh M (kr M y) ^ 2 * (kr M y ^ 4 * sin (y 2) ^ 2)) := by
      simp [kruskalMetric, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]; ring
    rw [this]
    exact (neg_ne_zero.2 (by positivity)).isUnit
  smooth := fun i j => by
    intro y hy
    refine ContDiffAt.contDiffWithinAt ?_
    have hkr := contDiffAt_kr M hM hy
    have hkh : ContDiffAt ℝ ∞ (fun y => kh M (kr M y)) y :=
      (contDiffAt_kh M hM (kr_pos M hM hy)).comp y hkr
    have hθ : ContDiffAt ℝ ∞ (fun y : Fin 4 → ℝ => sin (y 2)) y :=
      (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => sin (y 2)).contDiffAt
    fin_cases i <;> fin_cases j <;> simp only [kruskalMetric] <;> simp <;>
      first
      | exact contDiffAt_const
      | exact hkh.neg
      | exact hkh
      | exact hkr.pow 2
      | exact (hkr.pow 2).mul (hθ.pow 2)

/-- Kruskal coordinates from ingoing Eddington–Finkelstein ones: `V = T + X = e^{v/4M}`,
`U = T - X = -F(r) e^{-v/4M}`. -/
def kruskalChange (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(exp (y 0 / (4 * M)) - kF M (y 1) * exp (-(y 0 / (4 * M)))) / 2,
    (exp (y 0 / (4 * M)) + kF M (y 1) * exp (-(y 0 / (4 * M)))) / 2, y 2, y 3]

lemma diff_kF (hM : 0 < M) : Differentiable ℝ (kF M) := (contDiff_kF M hM.ne').differentiable (by simp)

lemma pd_expA (hM : 0 < M) (y : Fin 4 → ℝ) (k : Fin 4) :
    pd k (fun z => exp (z 0 / (4 * M))) y = if k = 0 then exp (y 0 / (4 * M)) / (4 * M) else 0 := by
  have h : HasDerivAt (fun t : ℝ => exp (t / (4 * M))) (exp (y 0 / (4 * M)) / (4 * M)) (y 0) :=
    (((hasDerivAt_id' (y 0)).div_const (4 * M)).exp).congr_deriv (by ring)
  exact pd_coord (n := 4) 0 k h

lemma pd_expB (hM : 0 < M) (y : Fin 4 → ℝ) (k : Fin 4) :
    pd k (fun z => kF M (z 1) * exp (-(z 0 / (4 * M)))) y =
      (if k = 1 then y 1 / (4 * M ^ 2) * exp (y 1 / (2 * M)) else 0) * exp (-(y 0 / (4 * M))) +
      kF M (y 1) * (if k = 0 then -(exp (-(y 0 / (4 * M))) / (4 * M)) else 0) := by
  have hF := hasDerivAt_kF M hM.ne' (y 1)
  have hE : HasDerivAt (fun t : ℝ => exp (-(t / (4 * M)))) (-(exp (-(y 0 / (4 * M))) / (4 * M))) (y 0) :=
    ((((hasDerivAt_id' (y 0)).div_const (4 * M)).neg).exp).congr_deriv (by simp; ring)
  exact pd_coord_mul (n := 4) 1 0 k hF hE

/-- The Jacobian of the Kruskal change. Write `E = e^{v/4M}`, `E' = e^{-v/4M}`, `F = F(r)`,
`F' = r e^{r/2M}/(4M²)`. -/
lemma jac_kruskalChange (hM : 0 < M) (y : Fin 4 → ℝ) :
    jac (kruskalChange M) y =
      !![(exp (y 0 / (4 * M)) / (4 * M) + kF M (y 1) * exp (-(y 0 / (4 * M))) / (4 * M)) / 2,
          -(y 1 / (4 * M ^ 2) * exp (y 1 / (2 * M)) * exp (-(y 0 / (4 * M)))) / 2, 0, 0;
         (exp (y 0 / (4 * M)) / (4 * M) - kF M (y 1) * exp (-(y 0 / (4 * M))) / (4 * M)) / 2,
          (y 1 / (4 * M ^ 2) * exp (y 1 / (2 * M)) * exp (-(y 0 / (4 * M)))) / 2, 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] := by
  have dA : ∀ _k : Fin 4, DifferentiableAt ℝ (fun z : Fin 4 → ℝ => exp (z 0 / (4 * M))) y := fun _ => by
    fun_prop
  have dB : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => kF M (z 1) * exp (-(z 0 / (4 * M)))) y :=
    ((diff_kF M hM).differentiableAt.comp y (by fun_prop : Differentiable ℝ fun z : Fin 4 → ℝ => z 1).differentiableAt).mul (by fun_prop)
  have P2 : ∀ k : Fin 4, pd k (fun z => z 2) y = if k = 2 then 1 else 0 := fun k =>
    pd_coord (n := 4) 2 k (hasDerivAt_id' (y 2))
  have P3 : ∀ k : Fin 4, pd k (fun z => z 3) y = if k = 3 then 1 else 0 := fun k =>
    pd_coord (n := 4) 3 k (hasDerivAt_id' (y 3))
  have hT : ∀ k, pd k (fun z => (exp (z 0 / (4 * M)) - kF M (z 1) * exp (-(z 0 / (4 * M)))) / 2) y =
      (pd k (fun z => exp (z 0 / (4 * M))) y - pd k (fun z => kF M (z 1) * exp (-(z 0 / (4 * M)))) y) / 2 := by
    intro k
    have dS : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => exp (z 0 / (4 * M)) - kF M (z 1) * exp (-(z 0 / (4 * M)))) y :=
      (dA k).sub dB
    have := pd_const_mul (2⁻¹ : ℝ) dS k
    rw [show (fun z : Fin 4 → ℝ => (exp (z 0 / (4 * M)) - kF M (z 1) * exp (-(z 0 / (4 * M)))) / 2) =
      fun z => 2⁻¹ * (exp (z 0 / (4 * M)) - kF M (z 1) * exp (-(z 0 / (4 * M)))) from by ext z; ring, this,
      pd_sub (dA k) dB]
    ring
  have hX : ∀ k, pd k (fun z => (exp (z 0 / (4 * M)) + kF M (z 1) * exp (-(z 0 / (4 * M)))) / 2) y =
      (pd k (fun z => exp (z 0 / (4 * M))) y + pd k (fun z => kF M (z 1) * exp (-(z 0 / (4 * M)))) y) / 2 := by
    intro k
    have dP : DifferentiableAt ℝ (fun z : Fin 4 → ℝ => exp (z 0 / (4 * M)) + kF M (z 1) * exp (-(z 0 / (4 * M)))) y :=
      (dA k).add dB
    have := pd_const_mul (2⁻¹ : ℝ) dP k
    rw [show (fun z : Fin 4 → ℝ => (exp (z 0 / (4 * M)) + kF M (z 1) * exp (-(z 0 / (4 * M)))) / 2) =
      fun z => 2⁻¹ * (exp (z 0 / (4 * M)) + kF M (z 1) * exp (-(z 0 / (4 * M)))) from by ext z; ring, this,
      pd_add (dA k) dB]
    ring
  ext μ a
  fin_cases μ <;> fin_cases a <;> simp only [jac, kruskalChange] <;>
    simp [hT, hX, pd_expA M hM, pd_expB M hM, P2, P3] <;> ring

/-- `X² - T² = F(r)` at the image of the Kruskal change. -/
lemma sq_sub_sq_kruskalChange (y : Fin 4 → ℝ) :
    kruskalChange M y 1 ^ 2 - kruskalChange M y 0 ^ 2 = kF M (y 1) := by
  have h : exp (y 0 / (4 * M)) * exp (-(y 0 / (4 * M))) = 1 := by rw [← exp_add]; simp
  simp only [kruskalChange, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination kF M (y 1) * h

lemma kruskalChange_mem (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ efU) :
    kruskalChange M y ∈ kruskalU := by
  refine ⟨?_, by simpa [kruskalChange] using hy.2.1, by simpa [kruskalChange] using hy.2.2⟩
  rw [sq_sub_sq_kruskalChange]
  rw [← kF_zero M hM.ne']
  exact kF_strictMonoOn M hM (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.1.le) hy.1

lemma kr_kruskalChange (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ efU) :
    kr M (kruskalChange M y) = y 1 := by
  unfold kr; rw [sq_sub_sq_kruskalChange]; exact kG_kF M hM hy.1

/-- **The Kruskal metric pulls back to the ingoing Eddington–Finkelstein metric** under the Kruskal
change `(v, r) ↦ (T, X)`. -/
lemma pullback_kruskal_ef (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ efU) :
    pullback (kruskalMetric M) (kruskalChange M) y = efMetric M y := by
  have hr := hy.1
  have hM0 : M ≠ 0 := hM.ne'
  rw [pullback_eq_mul, jac_kruskalChange M hM]
  have hk : kruskalMetric M (kruskalChange M y) =
      !![-kh M (y 1), 0, 0, 0; 0, kh M (y 1), 0, 0; 0, 0, y 1 ^ 2, 0; 0, 0, 0, y 1 ^ 2 * sin (y 2) ^ 2] := by
    simp only [kruskalMetric, kr_kruskalChange M hM hy]
    simp [kruskalChange]
  rw [hk]
  have hE : exp (y 0 / (4 * M)) * exp (-(y 0 / (4 * M))) = 1 := by rw [← exp_add]; simp
  have hw : exp (y 1 / (2 * M)) * exp (-(y 1 / (2 * M))) = 1 := by rw [← exp_add]; simp
  unfold kh kF efMetric
  generalize exp (y 0 / (4 * M)) = E at *
  generalize exp (-(y 0 / (4 * M))) = E' at *
  generalize exp (y 1 / (2 * M)) = w at *
  generalize exp (-(y 1 / (2 * M))) = w' at *
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> (field_simp; grind)

/-- The determinant of the Jacobian of the Kruskal change is `F'(r)/(8M) > 0`. -/
lemma det_jac_kruskalChange (hM : 0 < M) (y : Fin 4 → ℝ) :
    (jac (kruskalChange M) y).det = y 1 / (4 * M ^ 2) * exp (y 1 / (2 * M)) / (8 * M) := by
  have hE : exp (y 0 / (4 * M)) * exp (-(y 0 / (4 * M))) = 1 := by rw [← exp_add]; simp
  have hM0 : M ≠ 0 := hM.ne'
  rw [jac_kruskalChange M hM]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  generalize exp (y 0 / (4 * M)) = E at *
  generalize exp (-(y 0 / (4 * M))) = E' at *
  field_simp
  grind

theorem isChartChange_kruskalChange (hM : 0 < M) : IsChartChange (kruskalChange M) efU kruskalU where
  isOpen := isOpen_efU
  mapsTo := fun y hy => kruskalChange_mem M hM hy
  smooth := fun μ => by
    have hF : ContDiff ℝ ∞ (kF M) := contDiff_kF M hM.ne'
    have h1 : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => kF M (y 1) := hF.comp (by fun_prop)
    have h2 : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => exp (y 0 / (4 * M)) := by fun_prop
    have h3 : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => exp (-(y 0 / (4 * M))) := by fun_prop
    refine ContDiff.contDiffOn ?_
    fin_cases μ <;> simp only [kruskalChange] <;> simp
    · exact (h2.sub (h1.mul h3)).div_const 2
    · exact (h2.add (h1.mul h3)).div_const 2
    · fun_prop
    · fun_prop
  isUnit_det := fun y hy => by
    rw [det_jac_kruskalChange M hM]
    have := hy.1
    exact (by positivity : y 1 / (4 * M ^ 2) * exp (y 1 / (2 * M)) / (8 * M) ≠ 0).isUnit

/-- **Transport of Ricci-flatness along a chart change**: if the pullback of `g` by `φ` has vanishing
Ricci tensor at `y`, then `g` has vanishing Ricci tensor at `φ y`. -/
theorem ricci_eq_zero_of_pullback {g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {φ : (Fin 4 → ℝ) → (Fin 4 → ℝ)} {U V : Set (Fin 4 → ℝ)} (hg : IsCoordMetric g U)
    (hφ : IsChartChange φ V U) {y : Fin 4 → ℝ} (hy : y ∈ V)
    (h0 : ∀ b d, ricci (pullback g φ) b d y = 0) (b d : Fin 4) : ricci g b d (φ y) = 0 := by
  set R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun ν l => ricci g ν l (φ y)
  set J := jac φ y
  have hJ : IsUnit J.det := hφ.isUnit_det y hy
  have hmul : Jᵀ * R * J = 0 := by
    ext b d
    have := h0 b d
    rw [ricci_pullback hg hφ hy] at this
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

/-- Ricci-flatness at the image of the Kruskal change. -/
theorem ricci_kruskal_of_mem_image (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ efU) (b d : Fin 4) :
    ricci (kruskalMetric M) b d (kruskalChange M y) = 0 :=
  ricci_eq_zero_of_pullback (isCoordMetric_kruskal M hM) (isChartChange_kruskalChange M hM) hy
    (fun b d => by
      rw [ricci_congr_on isOpen_efU (fun y' hy' => pullback_kruskal_ef M hM hy') hy]
      exact ricci_ef_eq_zero_of_mem M hM hy b d) b d

end Lightlike
