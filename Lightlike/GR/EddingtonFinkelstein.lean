import Lightlike.GR.Schwarzschild
import Lightlike.Spacetime.ChartChange
import Lightlike.Spacetime.SchwarzschildManifold
import Lightlike.Spacetime.RicciContinuous

/-!
# The ingoing Eddington–Finkelstein chart of Schwarzschild

In ingoing Eddington–Finkelstein coordinates `(v, r, θ, φ) = (y 0, y 1, y 2, y 3)` the Schwarzschild
metric is
`ds² = -(1 - 2M/r) dv² + 2 dv dr + r² dθ² + r² sin²θ dφ²`,
smooth and Lorentzian for every `r > 0`, in particular across the horizon `r = 2M`
(`efMetric`, `isCoordMetric_ef`, `ef_isLorentzian`).

Gap row G1-020 (Kruskal–Szekeres, Eddington–Finkelstein, event horizon, interior). The comparison
with Carroll, *Spacetime and Geometry*, ch. 5 and 7, and Wald, ch. 6, is pending (not read at a
location).
-/

open Matrix Real
open scoped ContDiff

noncomputable section

namespace Lightlike

variable (M : ℝ)

/-- The ingoing Eddington–Finkelstein metric in coordinates `(v, r, θ, φ)`. -/
def efMetric (y : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-(1 - 2 * M / y 1), 1, 0, 0;
     1, 0, 0, 0;
     0, 0, y 1 ^ 2, 0;
     0, 0, 0, y 1 ^ 2 * sin (y 2) ^ 2]

/-- The domain `r > 0`, `0 < θ < π` of the chart. -/
def efU : Set (Fin 4 → ℝ) := {y | 0 < y 1 ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_efU : IsOpen (efU) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))

/-- The determinant of the Eddington–Finkelstein metric is `-r⁴ sin²θ`. -/
lemma det_efMetric (y : Fin 4 → ℝ) : (efMetric M y).det = -(y 1 ^ 4 * sin (y 2) ^ 2) := by
  simp [efMetric, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- **The ingoing Eddington–Finkelstein metric is a coordinate metric for every `r > 0`**: smooth,
symmetric and invertible, also at the horizon `r = 2M`. -/
theorem isCoordMetric_ef : IsCoordMetric (efMetric M) efU where
  isOpen := isOpen_efU
  symm := fun y _ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [efMetric]
  isUnit_det := fun y hy => by
    rw [det_efMetric]
    have hs := sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2
    have hr := hy.1
    exact (neg_ne_zero.2 (mul_pos (pow_pos hr 4) (pow_pos hs 2)).ne').isUnit
  smooth := fun i j => by
    have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 1) efU :=
      (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
    have hθ : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 2) := by fun_prop
    have hr0 : ∀ y ∈ efU, y 1 ≠ 0 := fun y hy => hy.1.ne'
    fin_cases i <;> fin_cases j <;> simp [efMetric]
    · exact (contDiffOn_const.div hr hr0).sub contDiffOn_const
    all_goals first
      | exact contDiffOn_const
      | exact hr.pow 2
      | exact (hr.pow 2).mul ((Real.contDiff_sin.comp hθ).pow 2).contDiffOn

/-- **Signature.** The Eddington–Finkelstein metric has Lorentzian signature for every `r > 0`, also
at `r = 2M`: with `f = 1 - 2M/r`, `g = Pᵀ η P` for the block matrix `P` with the `2 × 2` block
`[[-(1+f)/2, 1], [(1-f)/2, 1]]` and `r`, `r sin θ` on the rest of the diagonal. -/
theorem ef_isLorentzian : IsLorentzianCoordMetric (efMetric M) efU := by
  refine ⟨isCoordMetric_ef M, fun y hy => ?_⟩
  obtain ⟨hr, h2, h3⟩ := hy
  have hs := sin_pos_of_pos_of_lt_pi h2 h3
  set f : ℝ := 1 - 2 * M / y 1 with hf
  refine ⟨!![-(1 + f) / 2, 1, 0, 0;
             (1 - f) / 2, 1, 0, 0;
             0, 0, y 1, 0;
             0, 0, 0, y 1 * sin (y 2)], ?_, ?_⟩
  · simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    have hK : 0 < y 1 * (y 1 * sin (y 2)) := mul_pos hr (mul_pos hr hs)
    intro h
    have : (-f + -1) / 2 * (y 1 * (y 1 * sin (y 2))) + -((1 - f) / 2 * (y 1 * (y 1 * sin (y 2)))) =
        -(y 1 * (y 1 * sin (y 2))) := by ring
    rw [this] at h
    exact hK.ne' (neg_eq_zero.1 h)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [efMetric, eta, etaDiag, Matrix.mul_apply, Fin.sum_univ_four, hf] <;> ring

/-! ## The chart change to Schwarzschild coordinates -/

/-- The change of coordinates from ingoing Eddington–Finkelstein `(v, r, θ, φ)` to Schwarzschild
coordinates `(t, r, θ, φ)`: `t = v - r*(r)` for a function `rs = r*` (the tortoise coordinate). -/
def efChange (rs : ℝ → ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![y 0 - rs (y 1), y 1, y 2, y 3]

/-- The region of `ℝ⁴` where `r ∈ S` and `0 < θ < π`. -/
def efRegion (S : Set ℝ) : Set (Fin 4 → ℝ) := {y | y 1 ∈ S ∧ 0 < y 2 ∧ y 2 < π}

lemma isOpen_efRegion {S : Set ℝ} (hS : IsOpen S) : IsOpen (efRegion S) :=
  (hS.preimage (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      (isOpen_lt (continuous_apply 2) continuous_const))

/-- The Jacobian of the change of coordinates. -/
lemma jac_efChange {rs : ℝ → ℝ} {d : ℝ} {y : Fin 4 → ℝ} (hrs : HasDerivAt rs d (y 1)) :
    jac (efChange rs) y = !![1, -d, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  have hproj : ∀ k : Fin 4, HasFDerivAt (fun z : Fin 4 → ℝ => z k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k) y := fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k).hasFDerivAt
  have h0 : HasFDerivAt (fun z : Fin 4 → ℝ => z 0 - rs (z 1))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0 -
        d • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1) y :=
    (hproj 0).sub (hrs.comp_hasFDerivAt y (hproj 1))
  ext μ a
  fin_cases μ <;> fin_cases a <;>
    simp [jac, efChange, pd, (hproj _).fderiv, h0.fderiv, Pi.single_apply]

/-- **The Schwarzschild metric in Eddington–Finkelstein coordinates**: the pullback of `schMetric`
by `t = v - r*` is the Eddington–Finkelstein metric, where `r*' = (1 - 2M/r)⁻¹` and `r ≠ 2M`. -/
lemma pullback_sch_ef {rs : ℝ → ℝ} {y : Fin 4 → ℝ} (hr : y 1 ≠ 0) (hr2 : y 1 - 2 * M ≠ 0)
    (hrs : HasDerivAt rs (1 - 2 * M / y 1)⁻¹ (y 1)) :
    pullback (schMetric M) (efChange rs) y = efMetric M y := by
  have hf : 1 - 2 * M / y 1 ≠ 0 := by
    rw [one_sub_div hr]; exact div_ne_zero hr2 hr
  rw [pullback_eq_mul, jac_efChange hrs]
  have hg : schMetric M (efChange rs y) = Matrix.diagonal (schD M y) := by
    simp [schMetric, schD, efChange]
  rw [hg]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [efMetric, schD, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply] <;>
    field_simp <;> ring

/-! ## Schwarzschild is a coordinate metric on a region of `r ≠ 2M` -/

/-- Schwarzschild is a coordinate metric on `{r ∈ S, 0 < θ < π}` if `S` is open, `S ⊆ (0, ∞)` and
`2M ∉ S`. -/
theorem isCoordMetric_sch_region {S : Set ℝ} (hS : IsOpen S) (hpos : ∀ r ∈ S, 0 < r)
    (hh : ∀ r ∈ S, r ≠ 2 * M) : IsCoordMetric (schMetric M) (efRegion S) := by
  have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 1) (efRegion S) :=
    (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
  have hθ : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 2) := by fun_prop
  have hr0 : ∀ y ∈ efRegion S, y 1 ≠ 0 := fun y hy => (hpos _ hy.1).ne'
  have hf0 : ∀ y ∈ efRegion S, 1 - 2 * M / y 1 ≠ 0 := fun y hy => by
    rw [one_sub_div (hr0 y hy)]
    exact div_ne_zero (fun h => hh _ hy.1 (by linarith)) (hr0 y hy)
  have hfs : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => 1 - 2 * M / y 1) (efRegion S) :=
    contDiffOn_const.sub (contDiffOn_const.div hr hr0)
  refine isCoordMetric_diagonal (schD M) (isOpen_efRegion hS) (fun i => ?_) (fun y hy i => ?_)
  · fin_cases i
    · exact hfs.neg
    · exact hfs.inv hf0
    · exact hr.pow 2
    · exact (hr.pow 2).mul ((Real.contDiff_sin.comp hθ).pow 2).contDiffOn
  · have hs := sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2
    fin_cases i <;> simp [schD, hr0 y hy, hf0 y hy, hs.ne']
    · intro h; apply hf0 y hy; linarith

/-- The change of coordinates `t = v - r*` is a chart change of the region to itself, if `r*` is
smooth with derivative `(1 - 2M/r)⁻¹` on `S`. -/
theorem isChartChange_efChange {S : Set ℝ} (hS : IsOpen S) {rs : ℝ → ℝ}
    (hrs : ∀ r ∈ S, HasDerivAt rs (1 - 2 * M / r)⁻¹ r) (hsm : ContDiffOn ℝ ∞ rs S) :
    IsChartChange (efChange rs) (efRegion S) (efRegion S) where
  isOpen := isOpen_efRegion hS
  mapsTo := fun y hy => ⟨by simpa [efChange] using hy.1, by simpa [efChange] using hy.2.1,
    by simpa [efChange] using hy.2.2⟩
  smooth := fun μ => by
    have hr : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => y 1) (efRegion S) :=
      (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
    fin_cases μ
    · simp only [efChange]
      exact ((by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 0).contDiffOn).sub
        (hsm.comp hr fun y hy => hy.1)
    all_goals
      simp only [efChange]
      first
        | exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 1).contDiffOn
        | exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 2).contDiffOn
        | exact (by fun_prop : ContDiff ℝ ∞ fun y : Fin 4 → ℝ => y 3).contDiffOn
  isUnit_det := fun y hy => by
    rw [jac_efChange (hrs _ hy.1)]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- **Ricci-flatness of Eddington–Finkelstein off the horizon.** On `{r ∈ S, 0 < θ < π}` (`S` open,
positive, `2M ∉ S`, `r*` smooth with derivative `(1 - 2M/r)⁻¹`) the Ricci tensor of the
Eddington–Finkelstein metric vanishes: it is the pullback of Schwarzschild. -/
theorem ricci_ef_eq_zero {S : Set ℝ} (hS : IsOpen S) (hpos : ∀ r ∈ S, 0 < r)
    (hh : ∀ r ∈ S, r ≠ 2 * M) {rs : ℝ → ℝ}
    (hrs : ∀ r ∈ S, HasDerivAt rs (1 - 2 * M / r)⁻¹ r) (hsm : ContDiffOn ℝ ∞ rs S)
    {y : Fin 4 → ℝ} (hy : y ∈ efRegion S) (b d : Fin 4) : ricci (efMetric M) b d y = 0 := by
  have hCM := isCoordMetric_sch_region M hS hpos hh
  have hφ := isChartChange_efChange M hS hrs hsm
  have hcongr : ∀ z ∈ efRegion S, efMetric M z = pullback (schMetric M) (efChange rs) z :=
    fun z hz => (pullback_sch_ef M (hpos _ hz.1).ne' (sub_ne_zero.2 (hh _ hz.1)) (hrs _ hz.1)).symm
  rw [ricci_congr_on (isOpen_efRegion hS) hcongr hy b d, ricci_pullback hCM hφ hy]
  refine Finset.sum_eq_zero fun ν _ => Finset.sum_eq_zero fun l _ => ?_
  have hreg : efChange rs y ∈ schRegion M :=
    ⟨by simpa [efChange] using hpos _ hy.1,
     by simpa [efChange] using sub_ne_zero.2 (hh _ hy.1),
     by simpa [efChange] using (sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2).ne'⟩
  rw [ricci_sch M hreg, zero_mul, zero_mul]

/-! ## The tortoise coordinate outside and inside the horizon -/

/-- The tortoise coordinate outside the horizon: `r* = r + 2M log (r/(2M) - 1)`, `r > 2M`. -/
def tortoiseExt (r : ℝ) : ℝ := r + 2 * M * Real.log (r / (2 * M) - 1)

/-- The tortoise coordinate inside the horizon: `r* = r + 2M log (1 - r/(2M))`, `0 < r < 2M`. -/
def tortoiseInt (r : ℝ) : ℝ := r + 2 * M * Real.log (1 - r / (2 * M))

lemma hasDerivAt_tortoiseExt (hM : 0 < M) {r : ℝ} (hr : 2 * M < r) :
    HasDerivAt (tortoiseExt M) (1 - 2 * M / r)⁻¹ r := by
  unfold tortoiseExt
  have h1 : r / (2 * M) - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, div_eq_one_iff_eq (by positivity)]; intro h; linarith
  have h2 : HasDerivAt (fun r : ℝ => r / (2 * M) - 1) (1 / (2 * M)) r :=
    ((hasDerivAt_id r).div_const (2 * M)).sub_const 1
  have h4 := (hasDerivAt_id' r).add ((h2.log h1).const_mul (2 * M))
  refine h4.congr_deriv ?_
  have hr0 : r ≠ 0 := by linarith
  have hr2 : r - 2 * M ≠ 0 := by linarith
  field_simp
  ring

lemma hasDerivAt_tortoiseInt (hM : 0 < M) {r : ℝ} (hr0 : 0 < r) (hr : r < 2 * M) :
    HasDerivAt (tortoiseInt M) (1 - 2 * M / r)⁻¹ r := by
  unfold tortoiseInt
  have h1 : 1 - r / (2 * M) ≠ 0 := by
    rw [sub_ne_zero, Ne, eq_comm, div_eq_one_iff_eq (by positivity)]; intro h; linarith
  have h2 : HasDerivAt (fun r : ℝ => 1 - r / (2 * M)) (-(1 / (2 * M))) r := by
    simpa using ((hasDerivAt_id r).div_const (2 * M)).const_sub 1
  have h4 := (hasDerivAt_id' r).add ((h2.log h1).const_mul (2 * M))
  refine h4.congr_deriv ?_
  have hr2 : r - 2 * M ≠ 0 := by linarith
  field_simp
  ring

lemma contDiffOn_tortoiseExt (hM : 0 < M) : ContDiffOn ℝ ∞ (tortoiseExt M) (Set.Ioi (2 * M)) := by
  unfold tortoiseExt
  refine contDiffOn_id.add (contDiffOn_const.mul (ContDiffOn.log ?_ ?_))
  · exact (contDiffOn_id.div_const (2 * M)).sub contDiffOn_const
  · intro r hr
    have : 2 * M < r := hr
    rw [sub_ne_zero, Ne, div_eq_one_iff_eq (by positivity)]; intro h; linarith

lemma contDiffOn_tortoiseInt (hM : 0 < M) : ContDiffOn ℝ ∞ (tortoiseInt M) (Set.Ioo 0 (2 * M)) := by
  unfold tortoiseInt
  refine contDiffOn_id.add (contDiffOn_const.mul (ContDiffOn.log ?_ ?_))
  · exact contDiffOn_const.sub (contDiffOn_id.div_const (2 * M))
  · intro r hr
    rw [sub_ne_zero, Ne, eq_comm, div_eq_one_iff_eq (by positivity)]; intro h; linarith [hr.2]

/-- **Eddington–Finkelstein is Ricci-flat outside the horizon.** -/
theorem ricci_ef_exterior (hM : 0 < M) {y : Fin 4 → ℝ} (hr : 2 * M < y 1) (hθ : 0 < y 2)
    (hθ' : y 2 < π) (b d : Fin 4) : ricci (efMetric M) b d y = 0 :=
  ricci_ef_eq_zero M (S := Set.Ioi (2 * M)) isOpen_Ioi (fun r hr => by have : 2 * M < r := hr; linarith)
    (fun r hr => (ne_of_gt hr)) (fun r hr => hasDerivAt_tortoiseExt M hM hr)
    (contDiffOn_tortoiseExt M hM) ⟨hr, hθ, hθ'⟩ b d

/-- **Eddington–Finkelstein is Ricci-flat inside the horizon** (`0 < r < 2M`). -/
theorem ricci_ef_interior (hM : 0 < M) {y : Fin 4 → ℝ} (hr0 : 0 < y 1) (hr : y 1 < 2 * M)
    (hθ : 0 < y 2) (hθ' : y 2 < π) (b d : Fin 4) : ricci (efMetric M) b d y = 0 :=
  ricci_ef_eq_zero M (S := Set.Ioo 0 (2 * M)) isOpen_Ioo (fun r hr => hr.1)
    (fun r hr => (ne_of_lt hr.2)) (fun r hr => hasDerivAt_tortoiseInt M hM hr.1 hr.2)
    (contDiffOn_tortoiseInt M hM) ⟨⟨hr0, hr⟩, hθ, hθ'⟩ b d

/-- **Eddington–Finkelstein is Ricci-flat across the horizon.** For `M > 0` the Ricci tensor of the
ingoing Eddington–Finkelstein metric vanishes at every point `r > 0`, `0 < θ < π`, including the
horizon `r = 2M`: it is continuous (`continuousOn_ricci`) and vanishes at all points with `r ≠ 2M`
(`ricci_ef_exterior`, `ricci_ef_interior`), which accumulate at the horizon. -/
theorem ricci_ef_eq_zero_of_mem (hM : 0 < M) {y : Fin 4 → ℝ} (hy : y ∈ efU) (b d : Fin 4) :
    ricci (efMetric M) b d y = 0 := by
  obtain ⟨hr, hθ, hθ'⟩ := hy
  rcases lt_trichotomy (y 1) (2 * M) with h | h | h
  · exact ricci_ef_interior M hM hr h hθ hθ' b d
  · -- the horizon: a limit of points off the horizon
    have hcont : ContinuousAt (ricci (efMetric M) b d) y :=
      (continuousOn_ricci (isCoordMetric_ef M) b d).continuousAt
        (isOpen_efU.mem_nhds ⟨hr, hθ, hθ'⟩)
    set c : ℝ → Fin 4 → ℝ := fun t => y + t • Pi.single 1 1 with hc
    have hcc : Continuous c := continuous_const.add (continuous_id.smul continuous_const)
    have hc0 : c 0 = y := by simp [hc]
    have hlim : Filter.Tendsto (fun t => ricci (efMetric M) b d (c t)) (nhds 0)
        (nhds (ricci (efMetric M) b d y)) := by
      have h0 := hcc.tendsto 0
      rw [hc0] at h0
      exact hcont.tendsto.comp h0
    have hzero : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, ricci (efMetric M) b d (c t) = 0 := by
      have hU : ∀ᶠ t in nhds (0 : ℝ), c t ∈ efU :=
        hcc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact isOpen_efU.mem_nhds ⟨hr, hθ, hθ'⟩)
      filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with t ht ht0
      have h1 : (c t) 1 = 2 * M + t := by simp [hc, h, Pi.single_apply]
      have h2 : (c t) 2 = y 2 := by simp [hc, Pi.single_apply]
      rcases lt_or_gt_of_ne (show t ≠ 0 from ht0) with hlt | hgt
      · exact ricci_ef_interior M hM ht.1 (by rw [h1]; linarith) ht.2.1 ht.2.2 b d
      · exact ricci_ef_exterior M hM (by rw [h1]; linarith) ht.2.1 ht.2.2 b d
    have h0 : Filter.Tendsto (fun t => ricci (efMetric M) b d (c t)) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhds 0) := tendsto_const_nhds.congr' (hzero.mono fun t ht => ht.symm)
    exact tendsto_nhds_unique (hlim.mono_left nhdsWithin_le_nhds) h0
  · exact ricci_ef_exterior M hM h hθ hθ' b d

/-- **The ingoing Eddington–Finkelstein metric solves the vacuum Einstein equations for every
`r > 0`**, across the horizon `r = 2M`, with Lorentzian signature there (`ef_isLorentzian`). -/
theorem ef_isVacuumSolution (hM : 0 < M) : IsVacuumSolution 0 (efMetric M) efU :=
  ⟨isCoordMetric_ef M, fun y hy μ ν => by
    simp [einsteinTensor, scalarCurvature, ricci_ef_eq_zero_of_mem M hM hy]⟩

end Lightlike
