module

public import Lightlike.Lorentz.HaarChart

/-!
# The Haar measure of SL(2,ℂ) in a chart adapted to a point of ℂ

Fix `z ∈ ℂ`. Every `g ∈ SL(2,ℂ)` with `den g z ≠ 0` is determined by the three numbers

  `b = g₀₁`,   `w = mob g z`,   `λ = den g z`   (`fixCoords`),

and conversely (`fixChart`)

  `g_z(b, w, λ) = [[bw + 1/λ, b], [λw - bwz - z/λ, λ - bz]]`,   `λ ≠ 0`.

**Theorem (`haarC_eq_map_fixChart`).** In these coordinates the Haar measure `haarC` of
`HaarChart.lean` is Lebesgue measure: `dg = d²b d²w d²λ`.

Proof. In Bruhat coordinates `(b, c, d)` the chart is the holomorphic map
`(b, w, λ) ↦ (b, λw - bwz - z/λ, λ - bz)` (`fixTrans`), whose complex Jacobian determinant is
`λ - bz = d` (`det_fixJac`). Its real Jacobian `|d|²` cancels the density `|d|⁻²` of `haarC`. The
exceptional sets `{λ = 0}`, `{λ = bz}` and `{d = 0}`, `{bz + d = 0}` are complex hyperplanes, hence
null.

This chart turns the operators of the principal series into integral operators: since
`(π(g)φ)(z) = m(λ) φ(w)`, integrating `f(g) π(g)φ` over `g` first over `(b, λ)` gives the kernel
`K_f(z, w)` (`PlancherelKernel.lean`).

## References

* I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR 11 (1947), §5.
* M. A. Naimark, *Linear Representations of the Lorentz Group*, Pergamon 1964, ch. III §11.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology
open scoped ENNReal

namespace Lightlike.Lorentz

/-! ## The chart -/

/-- The matrix `[[bw + 1/λ, b], [λw - bwz - z/λ, λ - bz]]` of the coordinates `y = (b, w, λ)`
(and `1` where `λ = 0`). -/
noncomputable def fixMat (z : ℂ) (y : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if y 2 = 0 then 1 else
    !![y 0 * y 1 + (y 2)⁻¹, y 0; y 2 * y 1 - y 0 * y 1 * z - z / y 2, y 2 - y 0 * z]

/-- The matrix `fixMat z y` has determinant one. -/
lemma det_fixMat (z : ℂ) (y : Fin 3 → ℂ) : (fixMat z y).det = 1 := by
  unfold fixMat
  split_ifs with h
  · simp
  · rw [det_fin_two_of]; field_simp; ring

/-- **The chart at `z`**: `g_z(b, w, λ) = [[bw + 1/λ, b], [λw - bwz - z/λ, λ - bz]]`. -/
noncomputable def fixChart (z : ℂ) (y : Fin 3 → ℂ) : SL2C := ⟨fixMat z y, det_fixMat z y⟩

/-- The entries of `fixChart z y` off the null set `y 2 = 0`. -/
lemma fixChart_apply (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) :
    (fixChart z y : Matrix (Fin 2) (Fin 2) ℂ) =
      !![y 0 * y 1 + (y 2)⁻¹, y 0; y 2 * y 1 - y 0 * y 1 * z - z / y 2, y 2 - y 0 * z] := by
  simp [fixChart, fixMat, hy]

/-- `den (g_z(b, w, λ)) z = λ`. -/
lemma den_fixChart (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) : den (fixChart z y) z = y 2 := by
  simp [den, fixChart_apply z hy]

/-- `num (g_z(b, w, λ)) z = λw`. -/
lemma num_fixChart (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) :
    num (fixChart z y) z = y 2 * y 1 := by
  simp [num, fixChart_apply z hy]
  field_simp
  ring

/-- `mob (g_z(b, w, λ)) z = w`. -/
lemma mob_fixChart (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) : mob (fixChart z y) z = y 1 := by
  rw [mob_def, num_fixChart z hy, den_fixChart z hy]
  field_simp

/-- `(g_z(b, w, λ))₀₁ = b`. -/
lemma fixChart_zero_one (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) : fixChart z y 0 1 = y 0 := by
  simp [fixChart_apply z hy]

/-- The coordinates `(g₀₁, mob g z, den g z)` of a group element. -/
noncomputable def fixCoords (z : ℂ) (g : SL2C) : Fin 3 → ℂ := ![g 0 1, mob g z, den g z]

/-- `fixCoords z` is a left inverse of `fixChart z` off the null set `y 2 = 0`. -/
lemma fixCoords_fixChart (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) :
    fixCoords z (fixChart z y) = y := by
  ext i
  fin_cases i
  · exact fixChart_zero_one z hy
  · exact mob_fixChart z hy
  · exact den_fixChart z hy

/-- `fixChart z` is a left inverse of `fixCoords z` wherever `den g z ≠ 0`. -/
lemma fixChart_fixCoords (z : ℂ) {g : SL2C} (hg : den g z ≠ 0) :
    fixChart z (fixCoords z g) = g := by
  have hdet := SL2C.det_eq g
  have h2 : fixCoords z g 2 = den g z := rfl
  apply Subtype.ext
  rw [fixChart_apply z (by rwa [h2])]
  have hden : g 0 1 * z + g 1 1 ≠ 0 := hg
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fixCoords, mob_def, num, den]
  · field_simp
    linear_combination (-1 : ℂ) * hdet
  · field_simp
    linear_combination z * hdet

/-! ## The chart in Bruhat coordinates -/

/-- The Bruhat coordinates `(b, c, d)` of `g_z(b, w, λ)`: `(b, λw - bwz - z/λ, λ - bz)`. -/
noncomputable def fixTrans (z : ℂ) (y : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![y 0, y 2 * y 1 - y 0 * y 1 * z - z / y 2, y 2 - y 0 * z]

/-- The last coordinate of `fixTrans z y` is `λ − b z`. -/
lemma fixTrans_two (z : ℂ) (y : Fin 3 → ℂ) : fixTrans z y 2 = y 2 - y 0 * z := rfl

/-- The Bruhat chart composed with `fixTrans z` is `fixChart z`. -/
lemma bruhat_fixTrans (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) (hd : y 2 - y 0 * z ≠ 0) :
    bruhat (fixTrans z y) = fixChart z y := by
  apply Subtype.ext
  rw [bruhat_apply (by rwa [fixTrans_two]), fixChart_apply z hy]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fixTrans]
  field_simp
  ring

/-- The complex Jacobian matrix of `fixTrans z`. -/
noncomputable def fixJac (z : ℂ) (y : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
    -(y 1 * z), y 2 - y 0 * z, y 1 + z / y 2 ^ 2;
    -z, 0, 1]

/-- **The Jacobian determinant is `λ - bz = d`.** -/
lemma det_fixJac (z : ℂ) (y : Fin 3 → ℂ) : (fixJac z y).det = y 2 - y 0 * z := by
  rw [det_fin_three]
  simp [fixJac]

/-- The derivative of `fixTrans z` as a continuous `ℂ`-linear map. -/
noncomputable def fixDeriv (z : ℂ) (y : Fin 3 → ℂ) : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ j, fixJac z y i j • ContinuousLinearMap.proj j

/-- The linear map underlying `fixDeriv z y` is given by the matrix `fixJac z y`. -/
lemma fixDeriv_toLinearMap (z : ℂ) (y : Fin 3 → ℂ) :
    (fixDeriv z y : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) = Matrix.toLin' (fixJac z y) := by
  apply LinearMap.ext; intro v; funext i
  simp [fixDeriv, Matrix.toLin'_apply, mulVec, dotProduct]

/-- `fixDeriv z y` is the derivative of `fixTrans z` at `y` when `y 2 ≠ 0`. -/
lemma hasFDerivAt_fixTrans (z : ℂ) {y : Fin 3 → ℂ} (hy : y 2 ≠ 0) :
    HasFDerivAt (fixTrans z) (fixDeriv z y) y := by
  rw [hasFDerivAt_pi']
  intro i
  simp only [fixDeriv, ContinuousLinearMap.proj_pi]
  have p : ∀ j : Fin 3, HasFDerivAt (fun y : Fin 3 → ℂ => y j)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j) y :=
    fun j => hasFDerivAt_apply j y
  fin_cases i
  · refine (p 0).congr_fderiv ?_
    ext v; simp [fixJac, Fin.sum_univ_three]
  · have h1 := (((p 2).mul (p 1)).sub (((p 0).mul (p 1)).mul_const z)).sub
      (((hasDerivAt_inv hy).comp_hasFDerivAt y (p 2)).const_mul z)
    have e : (fun y : Fin 3 → ℂ => fixTrans z y 1) =
        fun y => y 2 * y 1 - y 0 * y 1 * z - z * (y 2)⁻¹ := by
      funext y; simp [fixTrans, div_eq_mul_inv]
    simp only [Fin.mk_one, Fin.isValue]
    rw [e]
    refine h1.congr_fderiv ?_
    ext v; simp [fixJac, Fin.sum_univ_three]
    field_simp
    ring
  · have := (p 2).sub ((p 0).mul_const z)
    refine this.congr_fderiv ?_
    ext v; simp [fixJac, Fin.sum_univ_three]
    ring

/-- The real Jacobian determinant is `|λ - bz|²`. -/
lemma abs_det_fixDeriv (z : ℂ) (y : Fin 3 → ℂ) :
    |((fixDeriv z y).restrictScalars ℝ).det| = ‖y 2 - y 0 * z‖ ^ 2 := by
  have e : ((fixDeriv z y).restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (fixDeriv z y : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))) :=
    LinearMap.det_restrictScalars
  rw [e, fixDeriv_toLinearMap, LinearMap.det_toLin', det_fixJac,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

/-! ## The change of variables -/

/-- The domain `{λ ≠ 0, λ ≠ bz}` of the chart inside the Bruhat chart. -/
def fixDom (z : ℂ) : Set (Fin 3 → ℂ) := {y | y 2 ≠ 0 ∧ y 2 - y 0 * z ≠ 0}

/-- Its image `{d ≠ 0, bz + d ≠ 0}` in Bruhat coordinates. -/
def fixImg (z : ℂ) : Set (Fin 3 → ℂ) := {x | x 2 ≠ 0 ∧ z * x 0 + x 2 ≠ 0}

/-- The domain `fixDom z` is open. -/
lemma isOpen_fixDom (z : ℂ) : IsOpen (fixDom z) := by
  have h1 : Continuous fun y : Fin 3 → ℂ => y 2 := continuous_apply 2
  have h2 : Continuous fun y : Fin 3 → ℂ => y 2 - y 0 * z := by fun_prop
  exact (isOpen_ne_fun h1 continuous_const).inter (isOpen_ne_fun h2 continuous_const)

/-- Almost every point of `ℂ³` lies in `fixDom z`. -/
lemma ae_fixDom (z : ℂ) : ∀ᵐ y ∂(volume : Measure (Fin 3 → ℂ)), y ∈ fixDom z := by
  have h1 := volume_hyperplane (u := 0) (v := 1) (Or.inr one_ne_zero)
  have h2 := volume_hyperplane (u := -z) (v := 1) (Or.inr one_ne_zero)
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (measure_union_null h1 h2)
  simp only [fixDom, Set.mem_ofPred_eq, not_and_or, not_not] at hy
  rcases hy with hy | hy
  · left; simpa using hy
  · right; simp only [Set.mem_ofPred_eq]; linear_combination hy

/-- Almost every point of `ℂ³` lies in `fixImg z`. -/
lemma ae_fixImg (z : ℂ) : ∀ᵐ x ∂(volume : Measure (Fin 3 → ℂ)), x ∈ fixImg z := by
  have h1 := volume_hyperplane (u := 0) (v := 1) (Or.inr one_ne_zero)
  have h2 := volume_hyperplane (u := z) (v := 1) (Or.inr one_ne_zero)
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
  simp only [fixImg, Set.mem_ofPred_eq, not_and_or, not_not] at hx
  rcases hx with hx | hx
  · left; simpa using hx
  · right; simpa using hx

/-- `fixTrans z` maps `fixDom z` onto `fixImg z`. -/
lemma image_fixTrans (z : ℂ) : fixTrans z '' fixDom z = fixImg z := by
  ext x; constructor
  · rintro ⟨y, ⟨hy, hd⟩, rfl⟩
    refine ⟨hd, ?_⟩
    simp only [fixTrans]
    simpa [mul_comm] using hy
  · rintro ⟨hx, hx'⟩
    refine ⟨![x 0, (x 1 + z / (z * x 0 + x 2)) / x 2, z * x 0 + x 2], ⟨hx', ?_⟩, ?_⟩
    · simp only [Matrix.cons_val]; ring_nf; exact hx
    · ext i
      fin_cases i <;> simp [fixTrans]
      · field_simp; ring
      · ring

/-- `fixTrans z` is injective on `fixDom z`. -/
lemma injOn_fixTrans (z : ℂ) : Set.InjOn (fixTrans z) (fixDom z) := by
  intro y ⟨hy, hd⟩ y' ⟨hy', hd'⟩ e
  have e0 : y 0 = y' 0 := by simpa [fixTrans] using congrFun e 0
  have e1 := congrFun e 1
  have e2 : y 2 - y 0 * z = y' 2 - y' 0 * z := by simpa [fixTrans] using congrFun e 2
  have e2' : y 2 = y' 2 := by rw [e0] at e2; linear_combination e2
  simp only [fixTrans, Matrix.cons_val] at e1
  -- `c + z/λ = w (λ - bz)` determines `w`
  have e1' : y 1 * (y 2 - y 0 * z) = y' 1 * (y' 2 - y' 0 * z) := by
    rw [← e2', ← e0] at e1 ⊢; linear_combination e1
  rw [← e2] at e1'
  have e1'' : y 1 = y' 1 := mul_right_cancel₀ hd e1'
  ext i; fin_cases i
  · exact e0
  · exact e1''
  · exact e2'

/-- **The Haar measure in the chart at `z`**: `∫⁻ F dhaarC = ∫⁻ F(g_z(b, w, λ)) d²b d²w d²λ`. -/
theorem lintegral_fixChart (z : ℂ) {F : SL2C → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, F (fixChart z y) = ∫⁻ g, F g ∂haarC := by
  have hs : MeasurableSet (fixDom z) := (isOpen_fixDom z).measurableSet
  have hf' : ∀ y ∈ fixDom z, HasFDerivWithinAt (fixTrans z)
      ((fixDeriv z y).restrictScalars ℝ) (fixDom z) y :=
    fun y hy => ((hasFDerivAt_fixTrans z hy.1).restrictScalars ℝ).hasFDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf' (injOn_fixTrans z)
    (fun x => bruhatDensity x * F (bruhat x))
  calc ∫⁻ y, F (fixChart z y)
      = ∫⁻ y in fixDom z, F (fixChart z y) := by
        rw [Measure.restrict_eq_self_of_ae_mem (ae_fixDom z)]
    _ = ∫⁻ y in fixDom z, ENNReal.ofReal |((fixDeriv z y).restrictScalars ℝ).det| *
          (bruhatDensity (fixTrans z y) * F (bruhat (fixTrans z y))) := by
        refine setLIntegral_congr_fun hs (fun y hy => ?_)
        -- the Jacobian `|d|²` cancels the density `|d|⁻²`
        have hd : ‖y 2 - y 0 * z‖ ≠ 0 := norm_ne_zero_iff.mpr hy.2
        rw [bruhat_fixTrans z hy.1 hy.2, abs_det_fixDeriv, ← mul_assoc]
        conv_lhs => rw [← one_mul (F (fixChart z y))]
        congr 1
        simp only [bruhatDensity, fixTrans_two]
        rw [← ENNReal.ofReal_mul (by positivity)]
        rw [mul_inv_cancel₀ (pow_ne_zero 2 hd), ENNReal.ofReal_one]
    _ = ∫⁻ x in fixImg z, bruhatDensity x * F (bruhat x) := by rw [← image_fixTrans z, key]
    _ = ∫⁻ g, F g ∂haarC := by
        rw [Measure.restrict_eq_self_of_ae_mem (ae_fixImg z), lintegral_haarC hF]

/-- `fixChart z` is continuous off the null set `y 2 = 0`. -/
lemma continuousOn_fixChart (z : ℂ) : ContinuousOn (fixChart z) {y | y 2 ≠ 0} := by
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  refine ContinuousOn.congr (f := fun y : Fin 3 → ℂ =>
    !![y 0 * y 1 + (y 2)⁻¹, y 0; y 2 * y 1 - y 0 * y 1 * z - z / y 2, y 2 - y 0 * z])
    ?_ (fun y hy => fixChart_apply z hy)
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp
  all_goals fun_prop (disch := (intro y hy; simpa using hy))

/-- `fixChart z` is measurable. -/
lemma measurable_fixChart (z : ℂ) : Measurable (fixChart z) := by
  classical
  have h0 : ContinuousOn (fixChart z) {y : Fin 3 → ℂ | y 2 ≠ 0}ᶜ := by
    refine continuousOn_const (c := (1 : SL2C)) |>.congr fun y hy => ?_
    have : y 2 = 0 := by simpa using hy
    exact Subtype.ext (by simp [fixChart, fixMat, this])
  have hs : MeasurableSet {y : Fin 3 → ℂ | y 2 ≠ 0} :=
    (measurableSet_eq_fun (measurable_pi_apply 2) measurable_const).compl
  have := (continuousOn_fixChart z).measurable_piecewise h0 hs
  rwa [Set.piecewise_same] at this

/-- **The Haar measure is Lebesgue measure in the chart at `z`**: `haarC = (g_z)_* (d²b d²w d²λ)`.
-/
theorem haarC_eq_map_fixChart (z : ℂ) :
    haarC = (volume : Measure (Fin 3 → ℂ)).map (fixChart z) := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_fixChart z) hA, ← lintegral_indicator_one hA,
    ← lintegral_fixChart z (measurable_one.indicator hA), ← lintegral_indicator_one
      (measurable_fixChart z hA)]
  rfl

end Lightlike.Lorentz
