module

public import Lightlike.Lorentz.Mobius

/-!
# The Haar measure of SL(2,ℂ) in the Bruhat chart

On the open dense set `{d ≠ 0}` every element of `SL(2,ℂ)` is

  `g = [[(1 + bc)/d, b], [c, d]]`,   `(b, c, d) ∈ ℂ × ℂ × ℂ^×`

(`bruhat`). **Theorem (`isHaarMeasure_haarC`).** The measure

  `haarC = bruhat_* (|d|⁻² d²b d²c d²d)`

is a Haar measure of `SL(2,ℂ)`: left-invariant (`lintegral_bruhat_mul`), finite near every point
and nonzero. By uniqueness it is a positive multiple of `SL2C.haar` (`haarC_eq_smul`,
`haarScalarFactor_haarC_ne_zero`), hence also positive on open sets and right-invariant. This is
the classical formula `dg = d²b d²c d²d / |d|²` (Gelfand–Naimark; W. Rühl, *The Lorentz Group and
Harmonic Analysis*, Benjamin 1970, Chapter 2).

Proof of left-invariance. In the chart, left multiplication by `h = [[α, β], [γ, δ]]` is the
holomorphic map `T_h(b, c, d) = (αb + βd, γ(1+bc)/d + δc, γb + δd)` (`bruhatTrans`), whose complex
Jacobian determinant is `d'/d` with `d' = γb + δd` (`det_bruhatJac`). The real Jacobian is its
squared modulus, which cancels the change of the density `|d|⁻²`. The exceptional sets
`{d = 0}` and `{γb + δd = 0}` are complex hyperplanes, hence null.

## References

* I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR 11 (1947).
* M. A. Naimark, *Linear Representations of the Lorentz Group*, Pergamon 1964, ch. III.
* W. Rühl, *The Lorentz Group and Harmonic Analysis*, Benjamin 1970, ch. 2.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology
open scoped ENNReal

namespace Lightlike.Lorentz

/-! ## The chart -/

/-- The matrix `[[(1 + bc)/d, b], [c, d]]` of the coordinates `x = (b, c, d)`. -/
noncomputable def bruhatMat (x : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if x 2 = 0 then 1 else !![(1 + x 0 * x 1) / x 2, x 0; x 1, x 2]

lemma det_bruhatMat (x : Fin 3 → ℂ) : (bruhatMat x).det = 1 := by
  unfold bruhatMat
  split_ifs with h
  · simp
  · rw [det_fin_two_of]; field_simp; ring

/-- **The Bruhat chart** `(b, c, d) ↦ [[(1 + bc)/d, b], [c, d]]` (and `1` where `d = 0`). -/
noncomputable def bruhat (x : Fin 3 → ℂ) : SL2C := ⟨bruhatMat x, det_bruhatMat x⟩

lemma bruhat_apply {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) :
    (bruhat x : Matrix (Fin 2) (Fin 2) ℂ) = !![(1 + x 0 * x 1) / x 2, x 0; x 1, x 2] := by
  simp [bruhat, bruhatMat, hx]

/-- The coordinates `(b, c, d)` of a group element. -/
def bruhatCoords (g : SL2C) : Fin 3 → ℂ := ![g 0 1, g 1 0, g 1 1]

lemma bruhatCoords_bruhat {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) : bruhatCoords (bruhat x) = x := by
  ext i; fin_cases i <;> simp [bruhatCoords, bruhat_apply hx]

lemma bruhat_bruhatCoords {g : SL2C} (hg : g 1 1 ≠ 0) : bruhat (bruhatCoords g) = g := by
  have hdet := SL2C.det_eq g
  apply Subtype.ext
  rw [bruhat_apply (by simpa [bruhatCoords] using hg)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [bruhatCoords]
  field_simp
  linear_combination (-1 : ℂ) * hdet

/-- **Left multiplication in the chart**: `T_h(b, c, d) = (αb + βd, γ(1+bc)/d + δc, γb + δd)`. -/
noncomputable def bruhatTrans (h : SL2C) (x : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![h 0 0 * x 0 + h 0 1 * x 2, h 1 0 * ((1 + x 0 * x 1) / x 2) + h 1 1 * x 1,
    h 1 0 * x 0 + h 1 1 * x 2]

lemma bruhatTrans_two (h : SL2C) (x : Fin 3 → ℂ) :
    bruhatTrans h x 2 = h 1 0 * x 0 + h 1 1 * x 2 := by simp [bruhatTrans]

lemma mul_bruhat (h : SL2C) {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) (hx' : bruhatTrans h x 2 ≠ 0) :
    h * bruhat x = bruhat (bruhatTrans h x) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, bruhat_apply hx, bruhat_apply hx']
  have hdet := SL2C.det_eq h
  rw [bruhatTrans_two] at hx'
  have hA : (1 + x 0 * x 1) / x 2 * x 2 = 1 + x 0 * x 1 := div_mul_cancel₀ _ hx
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [bruhatTrans, mul_apply, Fin.sum_univ_two]
  -- the only nontrivial entry, the top-left one: `(αA + βc) d' = 1 + a'c'` with `A d = 1 + bc`
  rw [eq_div_iff hx']
  generalize (1 + x 0 * x 1) / x 2 = A at hA ⊢
  linear_combination (A * x 2 - x 0 * x 1) * hdet + hA

lemma bruhatTrans_eq_coords (h : SL2C) {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) :
    bruhatTrans h x = bruhatCoords (h * bruhat x) := by
  ext i; fin_cases i <;>
    simp [bruhatTrans, bruhatCoords, Matrix.SpecialLinearGroup.coe_mul, bruhat_apply hx, mul_apply,
      Fin.sum_univ_two]

lemma bruhatTrans_inv (h : SL2C) {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) (hx' : bruhatTrans h x 2 ≠ 0) :
    bruhatTrans h⁻¹ (bruhatTrans h x) = x ∧ bruhatTrans h⁻¹ (bruhatTrans h x) 2 ≠ 0 := by
  rw [bruhatTrans_eq_coords h⁻¹ hx', ← mul_bruhat h hx hx', ← mul_assoc, inv_mul_cancel, one_mul,
    bruhatCoords_bruhat hx]
  exact ⟨rfl, hx⟩

/-! ## The Jacobian -/

/-- The complex Jacobian matrix of `T_h`. -/
noncomputable def bruhatJac (h : SL2C) (x : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![h 0 0, 0, h 0 1;
    h 1 0 * x 1 / x 2, h 1 0 * x 0 / x 2 + h 1 1, -(h 1 0 * (1 + x 0 * x 1)) / x 2 ^ 2;
    h 1 0, 0, h 1 1]

/-- **The Jacobian determinant is `d'/d`.** -/
lemma det_bruhatJac (h : SL2C) {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) :
    (bruhatJac h x).det = bruhatTrans h x 2 / x 2 := by
  have hdet := SL2C.det_eq h
  rw [det_fin_three, bruhatTrans_two]
  simp [bruhatJac]
  field_simp
  linear_combination (h 1 0 * x 0 + h 1 1 * x 2) * hdet

/-- The derivative of `T_h` as a continuous `ℂ`-linear map. -/
noncomputable def bruhatDeriv (h : SL2C) (x : Fin 3 → ℂ) : (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ j, bruhatJac h x i j • ContinuousLinearMap.proj j

lemma bruhatDeriv_toLinearMap (h : SL2C) (x : Fin 3 → ℂ) :
    (bruhatDeriv h x : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) = Matrix.toLin' (bruhatJac h x) := by
  apply LinearMap.ext; intro v; funext i
  simp [bruhatDeriv, Matrix.toLin'_apply, mulVec, dotProduct]

lemma hasFDerivAt_bruhatTrans (h : SL2C) {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) :
    HasFDerivAt (bruhatTrans h) (bruhatDeriv h x) x := by
  rw [hasFDerivAt_pi']
  intro i
  simp only [bruhatDeriv, ContinuousLinearMap.proj_pi]
  have p : ∀ j : Fin 3, HasFDerivAt (fun y : Fin 3 → ℂ => y j)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) j) x :=
    fun j => hasFDerivAt_apply j x
  fin_cases i
  · have := ((p 0).const_mul (h 0 0)).add ((p 2).const_mul (h 0 1))
    refine this.congr_fderiv ?_
    ext v; simp [bruhatJac, Fin.sum_univ_three]
  · have h1 := ((((p 0).mul (p 1)).const_add 1).mul
      ((hasDerivAt_inv hx).comp_hasFDerivAt x (p 2))).const_mul (h 1 0)
    have e : (fun y : Fin 3 → ℂ => bruhatTrans h y 1) =
        fun y => h 1 0 * ((1 + y 0 * y 1) * (y 2)⁻¹) + h 1 1 * y 1 := by
      funext y; simp [bruhatTrans, div_eq_mul_inv]
    simp only [Fin.mk_one, Fin.isValue]
    rw [e]
    refine (h1.add ((p 1).const_mul (h 1 1))).congr_fderiv ?_
    ext v; simp [bruhatJac, Fin.sum_univ_three]
    field_simp
    ring
  · have := ((p 0).const_mul (h 1 0)).add ((p 2).const_mul (h 1 1))
    refine this.congr_fderiv ?_
    ext v; simp [bruhatJac, Fin.sum_univ_three]

/-- The real Jacobian determinant is `|d'/d|²`. -/
lemma abs_det_bruhatDeriv (h : SL2C) {x : Fin 3 → ℂ} (hx : x 2 ≠ 0) :
    |((bruhatDeriv h x).restrictScalars ℝ).det| =
      ‖bruhatTrans h x 2‖ ^ 2 / ‖x 2‖ ^ 2 := by
  have e : ((bruhatDeriv h x).restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (bruhatDeriv h x : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))) :=
    LinearMap.det_restrictScalars
  rw [e, bruhatDeriv_toLinearMap, LinearMap.det_toLin', det_bruhatJac h hx,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity),
    norm_div, div_pow]

/-! ## The change of variables -/

/-- The density `|d|⁻²` (Lean's `0⁻¹ = 0` makes it vanish off the chart). -/
noncomputable def bruhatDensity (x : Fin 3 → ℂ) : ℝ≥0∞ := ENNReal.ofReal ((‖x 2‖ ^ 2)⁻¹)

/-- The set where `T_h` is defined and lands in the chart. -/
def bruhatDom (h : SL2C) : Set (Fin 3 → ℂ) := {x | x 2 ≠ 0 ∧ bruhatTrans h x 2 ≠ 0}

lemma isOpen_bruhatDom (h : SL2C) : IsOpen (bruhatDom h) := by
  have h1 : Continuous fun x : Fin 3 → ℂ => x 2 := continuous_apply 2
  have h2 : Continuous fun x : Fin 3 → ℂ => bruhatTrans h x 2 := by
    simp only [bruhatTrans_two]; fun_prop
  exact (isOpen_ne_fun h1 continuous_const).inter (isOpen_ne_fun h2 continuous_const)

/-- A complex hyperplane `{x | u x₀ + v x₂ = 0}`, `(u, v) ≠ 0`, is Lebesgue-null. -/
lemma volume_hyperplane {u v : ℂ} (huv : u ≠ 0 ∨ v ≠ 0) :
    (volume : Measure (Fin 3 → ℂ)) {x | u * x 0 + v * x 2 = 0} = 0 := by
  let L : (Fin 3 → ℂ) →ₗ[ℝ] ℂ :=
    { toFun := fun x => u * x 0 + v * x 2
      map_add' := fun x y => by simp; ring
      map_smul' := fun r x => by simp [Complex.real_smul]; ring }
  have hne : LinearMap.ker L ≠ ⊤ := by
    intro htop
    rcases huv with hu | hv
    · have : L (Pi.single 0 1) = 0 := by
        rw [← LinearMap.mem_ker, htop]; trivial
      simp [L, hu] at this
    · have : L (Pi.single 2 1) = 0 := by
        rw [← LinearMap.mem_ker, htop]; trivial
      simp [L, hv] at this
  exact Measure.addHaar_submodule volume _ hne

lemma ae_bruhatDom (h : SL2C) : ∀ᵐ x ∂(volume : Measure (Fin 3 → ℂ)), x ∈ bruhatDom h := by
  have h1 := volume_hyperplane (u := 0) (v := 1) (Or.inr one_ne_zero)
  have hrow : h 1 0 ≠ 0 ∨ h 1 1 ≠ 0 := by
    by_contra hc; push Not at hc
    have := SL2C.det_eq h; rw [hc.1, hc.2] at this; simp at this
  have h2 := volume_hyperplane hrow
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h1 h2)
  simp only [bruhatDom, Set.mem_ofPred_eq, not_and_or, not_not, bruhatTrans_two] at hx
  rcases hx with hx | hx
  · left; simpa using hx
  · right; exact hx

lemma image_bruhatTrans (h : SL2C) : bruhatTrans h '' bruhatDom h = bruhatDom h⁻¹ := by
  ext y; constructor
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    obtain ⟨_, he⟩ := bruhatTrans_inv h hx hx'
    exact ⟨hx', he⟩
  · rintro ⟨hy, hy'⟩
    obtain ⟨e, he⟩ := bruhatTrans_inv h⁻¹ hy hy'
    rw [inv_inv] at e he
    exact ⟨bruhatTrans h⁻¹ y, ⟨hy', by rwa [e]⟩, e⟩

/-- **Left-invariance in the chart**: `∫ |d|⁻² F(h · g(x)) dx = ∫ |d|⁻² F(g(x)) dx`. -/
theorem lintegral_bruhat_mul (h : SL2C) (F : SL2C → ℝ≥0∞) :
    ∫⁻ x, bruhatDensity x * F (h * bruhat x) = ∫⁻ x, bruhatDensity x * F (bruhat x) := by
  have hs : MeasurableSet (bruhatDom h) := (isOpen_bruhatDom h).measurableSet
  have hf' : ∀ x ∈ bruhatDom h, HasFDerivWithinAt (bruhatTrans h)
      ((bruhatDeriv h x).restrictScalars ℝ) (bruhatDom h) x :=
    fun x hx => ((hasFDerivAt_bruhatTrans h hx.1).restrictScalars ℝ).hasFDerivWithinAt
  have hinj : Set.InjOn (bruhatTrans h) (bruhatDom h) := by
    intro x hx y hy hxy
    rw [← (bruhatTrans_inv h hx.1 hx.2).1, ← (bruhatTrans_inv h hy.1 hy.2).1, hxy]
  have key := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf' hinj
    (fun y => bruhatDensity y * F (bruhat y))
  calc ∫⁻ x, bruhatDensity x * F (h * bruhat x)
      = ∫⁻ x in bruhatDom h, bruhatDensity x * F (h * bruhat x) := by
        rw [Measure.restrict_eq_self_of_ae_mem (ae_bruhatDom h)]
    _ = ∫⁻ x in bruhatDom h, ENNReal.ofReal |((bruhatDeriv h x).restrictScalars ℝ).det| *
          (bruhatDensity (bruhatTrans h x) * F (bruhat (bruhatTrans h x))) := by
        refine setLIntegral_congr_fun hs (fun x hx => ?_)
        -- the density factors cancel: `|d'|²/|d|² · |d'|⁻² = |d|⁻²`
        have h1 : ‖x 2‖ ≠ 0 := norm_ne_zero_iff.mpr hx.1
        have h2 : ‖bruhatTrans h x 2‖ ≠ 0 := norm_ne_zero_iff.mpr hx.2
        rw [mul_bruhat h hx.1 hx.2, abs_det_bruhatDeriv h hx.1, ← mul_assoc]
        congr 1
        simp only [bruhatDensity]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = ∫⁻ y in bruhatTrans h '' bruhatDom h, bruhatDensity y * F (bruhat y) := key.symm
    _ = ∫⁻ x, bruhatDensity x * F (bruhat x) := by
        rw [image_bruhatTrans, Measure.restrict_eq_self_of_ae_mem (ae_bruhatDom h⁻¹)]

/-! ## The Haar measure -/

lemma continuousOn_bruhat : ContinuousOn bruhat {x | x 2 ≠ 0} := by
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  refine ContinuousOn.congr (f := fun x : Fin 3 → ℂ => !![(1 + x 0 * x 1) / x 2, x 0; x 1, x 2])
    ?_ (fun x hx => bruhat_apply hx)
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp
  · exact ((continuous_const.add ((continuous_apply 0).mul (continuous_apply 1))).continuousOn).div
      (continuous_apply 2).continuousOn fun x hx => hx
  all_goals fun_prop

lemma measurable_bruhat : Measurable bruhat := by
  classical
  have h0 : ContinuousOn bruhat {x : Fin 3 → ℂ | x 2 ≠ 0}ᶜ := by
    refine continuousOn_const (c := (1 : SL2C)) |>.congr fun x hx => ?_
    have : x 2 = 0 := by simpa using hx
    exact Subtype.ext (by simp [bruhat, bruhatMat, this])
  have hs : MeasurableSet {x : Fin 3 → ℂ | x 2 ≠ 0} :=
    (measurableSet_eq_fun (measurable_pi_apply 2) measurable_const).compl
  have := continuousOn_bruhat.measurable_piecewise h0 hs
  rwa [Set.piecewise_same] at this

/-- The density is measurable. -/
lemma measurable_bruhatDensity : Measurable bruhatDensity := by
  unfold bruhatDensity; fun_prop

/-- **The Haar measure in the Bruhat chart**: `bruhat_* (|d|⁻² d²b d²c d²d)`. -/
noncomputable def haarC : Measure SL2C := (volume.withDensity bruhatDensity).map bruhat

/-- Integrals against `haarC` in the chart. -/
lemma lintegral_haarC {F : SL2C → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F g ∂haarC = ∫⁻ x, bruhatDensity x * F (bruhat x) := by
  rw [haarC, lintegral_map hF measurable_bruhat]
  exact lintegral_withDensity_eq_lintegral_mul _ measurable_bruhatDensity
    (hF.comp measurable_bruhat)

instance : haarC.IsMulLeftInvariant := by
  refine ⟨fun h => Measure.ext fun A hA => ?_⟩
  have hA' : MeasurableSet ((h * ·) ⁻¹' A) := measurable_const_mul h hA
  rw [Measure.map_apply (measurable_const_mul h) hA, ← lintegral_indicator_one hA',
    ← lintegral_indicator_one hA, lintegral_haarC (measurable_one.indicator hA'),
    lintegral_haarC (measurable_one.indicator hA)]
  exact lintegral_bruhat_mul h (A.indicator 1)

lemma continuous_entry (i j : Fin 2) : Continuous fun g : SL2C => g i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

/-- The box `{|b|, |c|, |d| ≤ R, |d| ≥ ε}` has finite measure. -/
lemma haarC_box_lt_top (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    haarC {g | ‖g 0 1‖ ≤ R ∧ ‖g 1 0‖ ≤ R ∧ ‖g 1 1‖ ≤ R ∧ ε ≤ ‖g 1 1‖} < ∞ := by
  set B := {g : SL2C | ‖g 0 1‖ ≤ R ∧ ‖g 1 0‖ ≤ R ∧ ‖g 1 1‖ ≤ R ∧ ε ≤ ‖g 1 1‖}
  have c := fun i j => (continuous_entry i j).norm
  have hB : MeasurableSet B :=
    ((isClosed_le (c 0 1) continuous_const).inter ((isClosed_le (c 1 0) continuous_const).inter
      ((isClosed_le (c 1 1) continuous_const).inter
        (isClosed_le continuous_const (c 1 1))))).measurableSet
  rw [← lintegral_indicator_one hB, lintegral_haarC (measurable_one.indicator hB)]
  calc ∫⁻ x, bruhatDensity x * B.indicator 1 (bruhat x)
      ≤ ∫⁻ x, (Metric.closedBall (0 : Fin 3 → ℂ) R).indicator
          (fun _ => ENNReal.ofReal ((ε ^ 2)⁻¹)) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x 2 = 0
        · simp [bruhatDensity, hx]
        by_cases hm : bruhat x ∈ B
        · have hm' := hm
          simp only [B, Set.mem_ofPred_eq, bruhat_apply hx] at hm'
          simp at hm'
          obtain ⟨h0, h1, h2, h3⟩ := hm'
          have hR : 0 ≤ R := (norm_nonneg _).trans h0
          have hball : x ∈ Metric.closedBall (0 : Fin 3 → ℂ) R := by
            rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
            intro i; fin_cases i <;> assumption
          rw [Set.indicator_of_mem hm, Set.indicator_of_mem hball]
          simp only [Pi.one_apply, mul_one, bruhatDensity]
          refine ENNReal.ofReal_le_ofReal (inv_anti₀ (by positivity) ?_)
          exact pow_le_pow_left₀ hε.le h3 2
        · simp [Set.indicator_of_notMem hm]
    _ = ENNReal.ofReal ((ε ^ 2)⁻¹) * volume (Metric.closedBall (0 : Fin 3 → ℂ) R) :=
        lintegral_indicator_const Metric.isClosed_closedBall.measurableSet _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

lemma exists_nhds_haarC_lt_top {g : SL2C} (hg : g 1 1 ≠ 0) : ∃ U ∈ 𝓝 g, haarC U < ∞ := by
  have c := fun i j => (continuous_entry i j).norm
  have hpos := norm_pos_iff.2 hg
  have h01 := norm_nonneg (g 0 1)
  have h10 := norm_nonneg (g 1 0)
  refine ⟨{g' | ‖g' 0 1‖ < ‖g 0 1‖ + ‖g 1 0‖ + ‖g 1 1‖ + 1 ∧
      ‖g' 1 0‖ < ‖g 0 1‖ + ‖g 1 0‖ + ‖g 1 1‖ + 1 ∧ ‖g' 1 1‖ < ‖g 0 1‖ + ‖g 1 0‖ + ‖g 1 1‖ + 1 ∧
      ‖g 1 1‖ / 2 < ‖g' 1 1‖}, IsOpen.mem_nhds ?_ ?_, ?_⟩
  · exact (isOpen_lt (c 0 1) continuous_const).inter ((isOpen_lt (c 1 0) continuous_const).inter
      ((isOpen_lt (c 1 1) continuous_const).inter (isOpen_lt continuous_const (c 1 1))))
  · exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · refine (measure_mono ?_).trans_lt
      (haarC_box_lt_top (‖g 0 1‖ + ‖g 1 0‖ + ‖g 1 1‖ + 1) (half_pos hpos))
    intro g' hg'
    exact ⟨hg'.1.le, hg'.2.1.le, hg'.2.2.1.le, hg'.2.2.2.le⟩

instance : IsLocallyFiniteMeasure haarC := by
  refine ⟨fun g => ?_⟩
  by_cases hg : g 1 1 = 0
  · -- move `g` into the chart: `s = [[0, -1], [1, 0]]` has `(s g)₁₁ = g₀₁ ≠ 0`
    let s : SL2C := SL2C.mk 0 (-1) 1 0 (by ring)
    have hs : (s * g) 1 1 ≠ 0 := by
      have := SL2C.det_eq g
      rw [hg] at this
      simp [s, Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
      intro h; rw [h] at this; simp at this
    obtain ⟨U, hU, hfin⟩ := exists_nhds_haarC_lt_top hs
    refine ⟨(s * ·) ⁻¹' U, (continuous_const_mul s).continuousAt.preimage_mem_nhds hU, ?_⟩
    rwa [measure_preimage_mul]
  · exact exists_nhds_haarC_lt_top hg

/-- The chart measure is not zero. -/
theorem haarC_ne_zero : haarC ≠ 0 := by
  intro h0
  have h1 : ∫⁻ x, bruhatDensity x = 0 := by
    have := lintegral_haarC (F := fun _ => (1 : ℝ≥0∞)) measurable_const
    simp only [mul_one] at this
    rw [← this, h0, lintegral_zero_measure]
  rw [lintegral_eq_zero_iff measurable_bruhatDensity] at h1
  have : ∀ᵐ x ∂(volume : Measure (Fin 3 → ℂ)), False := by
    filter_upwards [h1, ae_bruhatDom 1] with x hx hd
    simp only [bruhatDensity, Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
    have := norm_pos_iff.2 hd.1
    have : 0 < (‖x 2‖ ^ 2)⁻¹ := by positivity
    linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
  exact (NeZero.ne (volume : Measure (Fin 3 → ℂ))) this

/-- **Uniqueness**: the chart measure is a multiple of Mathlib's Haar measure. -/
theorem haarC_eq_smul : haarC = Measure.haarScalarFactor haarC SL2C.haar • SL2C.haar :=
  Measure.isMulLeftInvariant_eq_smul _ _

/-- The scalar factor between `haarC` and `SL2C.haar` is nonzero. -/
theorem haarScalarFactor_haarC_ne_zero : Measure.haarScalarFactor haarC SL2C.haar ≠ 0 := by
  intro h; apply haarC_ne_zero; rw [haarC_eq_smul, h, zero_smul]

/-- **`haarC` is a Haar measure** of `SL(2,ℂ)`. -/
instance isHaarMeasure_haarC : haarC.IsHaarMeasure := by
  rw [haarC_eq_smul]; exact Measure.IsHaarMeasure.nnreal_smul _ haarScalarFactor_haarC_ne_zero

/-- `haarC` is also right-invariant (`SL(2,ℂ)` is unimodular). -/
instance : haarC.IsMulRightInvariant := by
  rw [haarC_eq_smul]; infer_instance

end Lightlike.Lorentz
