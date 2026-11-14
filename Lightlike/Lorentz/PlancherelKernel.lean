module

public import Lightlike.Lorentz.FixedChart
public import Lightlike.Lorentz.PrincipalSeries

/-!
# Integral kernels of the principal series of SL(2,ℂ)

For `f : SL(2,ℂ) → ℂ` the operator `π_{n,ρ}(f) = ∫ f(g) π_{n,ρ}(g) dg` of the principal series is
an integral operator on `L²(ℂ)`. In the chart `g_z(b, w, λ)` at a point `z` (`FixedChart.lean`),
whose coordinates are `b = g₀₁`, `w = mob g z` and `λ = den g z`, its kernel is
`K_f(z, w) = ∫ f(g_z(b, w, λ)) m(λ) d²b d²λ` (`psKernel`).

The main result is the **diagonal identity** for `f* ∗ f` (`selfConv`), proven pointwise by
changes of variables, for `f` continuous with compact support:

    K_{f*∗f}(z, z) = ∫ |K_f(z', z)|² d²z'      (`psKernel_selfConv_diag`).

Integrated over `z`, the left side is the trace of `π(f* ∗ f)` and the right side is the squared
Hilbert–Schmidt norm of `π(f)`. This is the step of the Plancherel formula that connects the
group side with the kernels.

## Ingredients

* `isInvInvariant_haarC`: the Haar measure is inversion invariant (`SL(2,ℂ)` is unimodular).
* `fixChart_inv`, `fixChart_mul`: inverses and products of chart points, from
  `g_z(b, w, λ) = n_z⁻¹ t(λ, b) n_w` with `n_z = [[1, 0], [z, 1]]`, `t(λ, b) = [[1/λ, b], [0, λ]]`.
* `haarC_eq_map_invChart`: in the inverse chart `(z', b, λ) ↦ g_{z'}(b, z, λ)` (all elements
  that map `z'` to the fixed point `z`), the Haar measure is `|λ|⁻⁴ d²z' d²b d²λ`.
* `measurePreserving_shearMap`: `(b, λ) ↦ (b/λ₀ + b₀λ, λ₀λ)` preserves Lebesgue measure.
* `chart_bound`, `integrable_selfConv_integrand`: the integrability behind the uses of Fubini.

## References

* I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR 11 (1947).
* M. A. Naimark, *Linear Representations of the Lorentz Group*, Pergamon 1964, ch. III.
* I. M. Gel'fand, M. I. Graev, N. Ya. Vilenkin, *Generalized Functions*, vol. 5, Academic
  Press 1966, ch. III.
-/

@[expose] public section

open MeasureTheory Matrix Complex Filter Topology
open scoped ENNReal NNReal ComplexConjugate Pointwise

namespace Lightlike.Lorentz

/-! ## Inversion invariance of the Haar measure -/

/-- **`haarC` is inversion invariant** (`SL(2,ℂ)` is unimodular). The inverse measure is left
invariant, hence `c • haarC` for some `c ≥ 0`, and inverting twice gives `c² = 1`. -/
instance isInvInvariant_haarC : haarC.IsInvInvariant := by
  set c := Measure.haarScalarFactor haarC.inv haarC
  have hc : haarC.inv = c • haarC := Measure.isMulLeftInvariant_eq_smul _ _
  have h2 : haarC = (c * c) • haarC := by
    have h := congrArg Measure.inv hc
    rw [Measure.inv_inv] at h
    rw [mul_smul, ← hc]
    exact h.trans (Measure.map_smul _ measurable_inv.aemeasurable)
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : SL2C)
  have hpos : haarC K ≠ 0 := (Measure.measure_pos_of_mem_nhds haarC hK1).ne'
  have hfin : haarC K ≠ ∞ := hK.measure_lt_top.ne
  have hcc : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := by
    have h := congrArg (fun μ : Measure SL2C => μ K) h2
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.smul_def] at h
    exact (ENNReal.mul_eq_right hpos hfin).mp h.symm
  have hc1 : c = 1 := by
    have : (c : ℝ) * c = 1 := by exact_mod_cast hcc
    nlinarith [c.coe_nonneg, sq_nonneg ((c : ℝ) - 1)]
  exact ⟨by rw [hc, hc1, one_smul]⟩

/-! ## Algebra of the charts -/

/-- **Inverse of a chart point**: `g_z(b, w, λ)⁻¹ = g_w(-b, z, 1/λ)`. (Both sides are `1` when
`λ = 0`.) -/
theorem fixChart_inv (z w b l : ℂ) :
    (fixChart z ![b, w, l])⁻¹ = fixChart w ![-b, z, l⁻¹] := by
  by_cases hl : l = 0
  · subst hl
    have h1 : fixChart z ![b, w, 0] = 1 := Subtype.ext (by simp [fixChart, fixMat])
    have h2 : fixChart w ![-b, z, (0 : ℂ)⁻¹] = 1 := Subtype.ext (by simp [fixChart, fixMat])
    rw [h1, h2, inv_one]
  · have hl' : l⁻¹ ≠ 0 := inv_ne_zero hl
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_inv, fixChart_apply z (by simpa using hl),
      fixChart_apply w (by simpa using hl'), Matrix.adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

/-- **Product of chart points**:
`g_{z'}(b₀, w₀, λ₀) · g_{w₀}(b, w, λ) = g_{z'}(b/λ₀ + b₀λ, w, λ₀λ)`,
because `g_z(b, w, λ) = n_z⁻¹ t(λ, b) n_w` with `n_z = [[1, 0], [z, 1]]` and
`t(λ, b) = [[1/λ, b], [0, λ]]`. -/
theorem fixChart_mul (z' w₀ w b₀ l₀ b l : ℂ) (h₀ : l₀ ≠ 0) (h : l ≠ 0) :
    fixChart z' ![b₀, w₀, l₀] * fixChart w₀ ![b, w, l] =
      fixChart z' ![l₀⁻¹ * b + b₀ * l, w, l₀ * l] := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, fixChart_apply z' (by simpa using h₀),
    fixChart_apply w₀ (by simpa using h), fixChart_apply z' (by simpa using mul_ne_zero h₀ h)]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- `(z, y) ↦ g_z(y)` is continuous off the null set `y 2 = 0`. -/
lemma continuousOn_fixChart_uncurry :
    ContinuousOn (fun p : ℂ × (Fin 3 → ℂ) => fixChart p.1 p.2) {p | p.2 2 ≠ 0} := by
  refine Topology.IsInducing.subtypeVal.continuousOn_iff.2 ?_
  refine ContinuousOn.congr (f := fun p : ℂ × (Fin 3 → ℂ) =>
    !![p.2 0 * p.2 1 + (p.2 2)⁻¹, p.2 0;
      p.2 2 * p.2 1 - p.2 0 * p.2 1 * p.1 - p.1 / p.2 2, p.2 2 - p.2 0 * p.1])
    ?_ (fun p hp => fixChart_apply p.1 hp)
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j <;> simp
  all_goals fun_prop (disch := (intro p hp; simpa using hp))

/-- `(z, y) ↦ g_z(y)` is measurable. -/
lemma measurable_fixChart_uncurry :
    Measurable (fun p : ℂ × (Fin 3 → ℂ) => fixChart p.1 p.2) := by
  classical
  have h0 : ContinuousOn (fun p : ℂ × (Fin 3 → ℂ) => fixChart p.1 p.2) {p | p.2 2 ≠ 0}ᶜ := by
    refine continuousOn_const (c := (1 : SL2C)) |>.congr fun p hp => ?_
    have : p.2 2 = 0 := by simpa using hp
    exact Subtype.ext (by simp [fixChart, fixMat, this])
  have hs : MeasurableSet {p : ℂ × (Fin 3 → ℂ) | p.2 2 ≠ 0} :=
    (measurableSet_eq_fun ((measurable_pi_apply 2).comp measurable_snd) measurable_const).compl
  have := continuousOn_fixChart_uncurry.measurable_piecewise h0 hs
  rwa [Set.piecewise_same] at this

/-! ## The Haar measure in product coordinates -/

/-- The coordinates `(w, (b, λ)) ↦ (b, w, λ)` of the chart at a point. -/
def tripleOf (p : ℂ × ℂ × ℂ) : Fin 3 → ℂ := ![p.2.1, p.1, p.2.2]

/-- `tripleOf` preserves Lebesgue measure. -/
lemma measurePreserving_tripleOf : MeasurePreserving tripleOf volume volume := by
  have e1 := MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℂ) 1)
  have e2 := MeasurePreserving.symm _ (volume_preserving_finTwoArrow ℂ)
  have := e1.comp ((MeasurePreserving.id (volume : Measure ℂ)).prod e2)
  convert this using 1
  funext p; ext i; fin_cases i <;> rfl

/-- **Haar measure in product coordinates**: `haarC = (g_z)_* (d²w d²b d²λ)`, with the
coordinates ordered as `(w, (b, λ))`. -/
theorem haarC_eq_map_prod (z : ℂ) :
    haarC = (volume : Measure (ℂ × ℂ × ℂ)).map (fun p => fixChart z (tripleOf p)) := by
  rw [haarC_eq_map_fixChart z, ← measurePreserving_tripleOf.map_eq,
    Measure.map_map (measurable_fixChart z) measurePreserving_tripleOf.measurable]
  rfl

/-- The density `|λ|⁻⁴` of the inversion `λ ↦ 1/λ` of `ℂ`. -/
noncomputable def invDensity (l : ℂ) : ℝ≥0 := (‖l‖₊ ^ 4)⁻¹

/-- `invDensity` is measurable. -/
lemma measurable_invDensity : Measurable invDensity := by
  unfold invDensity; fun_prop

/-- The element `[[0, 1], [-1, 0]]` of `SL(2,ℂ)`, acting by `z ↦ -1/z`. -/
noncomputable def sInv : SL2C := SL2C.mk 0 1 (-1) 0 (by ring)

/-- **Inversion of `ℂ`**: `λ ↦ 1/λ` maps `|λ|⁻⁴ d²λ` to `d²λ`. -/
theorem map_inv_withDensity :
    (volume.withDensity fun l : ℂ => (invDensity l : ℝ≥0∞)).map Inv.inv = volume := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_inv, lintegral_withDensity_eq_lintegral_mul _
    measurable_invDensity.coe_nnreal_ennreal
    (show Measurable fun a : ℂ => f a⁻¹ from hf.comp measurable_inv)]
  have key := lintegral_mob sInv (fun w => f (-w))
  rw [lintegral_neg_eq_self (fun w => f w)] at key
  rw [key]
  refine lintegral_congr fun l => ?_
  have hden : den sInv l = l := by simp [den, sInv]
  have hmob : mob sInv l = -l⁻¹ := by
    simp [mob, num, den, sInv, div_eq_mul_inv]
  simp only [Pi.mul_apply, hden, hmob, neg_neg, invDensity]
  congr 1
  rw [show (‖l‖ ^ 4)⁻¹ = (((‖l‖₊ ^ 4)⁻¹ : ℝ≥0) : ℝ) by simp, ENNReal.ofReal_coe_nnreal]

/-- The measure `|λ|⁻⁴ d²z' d²b d²λ` on the coordinates `(z', (b, λ))` of the inverse chart. -/
noncomputable def invChartMeasure : Measure (ℂ × ℂ × ℂ) :=
  (volume : Measure (ℂ × ℂ × ℂ)).withDensity fun p => (invDensity p.2.2 : ℝ≥0∞)

/-- `(z', b, λ) ↦ (z', -b, 1/λ)` maps Lebesgue measure to `invChartMeasure`. -/
lemma map_negInv_volume :
    (volume : Measure (ℂ × ℂ × ℂ)).map (Prod.map id (Prod.map Neg.neg Inv.inv)) =
      invChartMeasure := by
  have h1 : (volume : Measure ℂ).map Inv.inv =
      volume.withDensity fun l => (invDensity l : ℝ≥0∞) := by
    conv_lhs => rw [← map_inv_withDensity, Measure.map_map measurable_inv measurable_inv]
    simp
  rw [show (volume : Measure (ℂ × ℂ × ℂ)) = volume.prod (volume.prod volume) from rfl,
    ← Measure.map_prod_map _ _ measurable_id (measurable_neg.prodMap measurable_inv),
    ← Measure.map_prod_map _ _ measurable_neg measurable_inv, Measure.map_id,
    Measure.map_neg_eq_self, h1,
    prod_withDensity_right measurable_invDensity.coe_nnreal_ennreal,
    prod_withDensity_right (g := fun z : ℂ × ℂ => (invDensity z.2 : ℝ≥0∞))
      (measurable_invDensity.coe_nnreal_ennreal.comp measurable_snd)]
  rfl

/-- The inverse chart `(z', b, λ) ↦ g_{z'}(b, z, λ)` into the elements `g` with `mob g z' = z`. -/
noncomputable def invChart (z : ℂ) (p : ℂ × ℂ × ℂ) : SL2C := fixChart p.1 ![p.2.1, z, p.2.2]

/-- `invChart z` is measurable. -/
lemma measurable_invChart (z : ℂ) : Measurable (invChart z) := by
  refine measurable_fixChart_uncurry.comp (measurable_fst.prodMk ?_)
  exact (continuous_snd.fst.matrixVecCons (continuous_const.matrixVecCons
    (continuous_snd.snd.matrixVecCons continuous_const))).measurable

/-- **Haar measure in the inverse chart**: `haarC = (g_{·}(·, z, ·))_* (|λ|⁻⁴ d²z' d²b d²λ)`.
The chart `(z', b, λ) ↦ g_{z'}(b, z, λ)` fixes the image `z` of `z'`, and is the inverse of the
chart `g_z` composed with `(b, λ) ↦ (-b, 1/λ)`; the density comes from `λ ↦ 1/λ`. -/
theorem haarC_eq_map_invChart (z : ℂ) : haarC = invChartMeasure.map (invChart z) := by
  have hm : Measurable fun p : ℂ × ℂ × ℂ => fixChart z (tripleOf p) :=
    (measurable_fixChart z).comp measurePreserving_tripleOf.measurable
  conv_lhs => rw [← Measure.map_inv_eq_self haarC, haarC_eq_map_prod z,
    Measure.map_map measurable_inv hm]
  rw [← map_negInv_volume, Measure.map_map (measurable_invChart z)
    (measurable_id.prodMap (measurable_neg.prodMap measurable_inv))]
  congr 1
  funext p
  simp only [Function.comp_apply, tripleOf, fixChart_inv, invChart, Prod.map_fst, Prod.map_snd,
    id_eq]

/-! ## A shear of `ℂ²` -/

/-- The map `(b, λ) ↦ (b/λ₀ + b₀λ, λ₀λ)` of `ℂ²`: the coordinates of
`g_{z'}(b₀, z, λ₀) g_z(b, z, λ)` (`fixChart_mul`). -/
noncomputable def shearMap (b₀ l₀ : ℂ) (q : ℂ × ℂ) : ℂ × ℂ := (l₀⁻¹ * q.1 + b₀ * q.2, l₀ * q.2)

/-- `shearMap b₀ λ₀` preserves Lebesgue measure: it is `ℂ`-linear with matrix
`[[1/λ₀, b₀], [0, λ₀]]` of determinant `1`, so its real determinant is `|1|² = 1`. -/
lemma measurePreserving_shearMap (b₀ l₀ : ℂ) (h₀ : l₀ ≠ 0) :
    MeasurePreserving (shearMap b₀ l₀) volume volume := by
  set A : Matrix (Fin 2) (Fin 2) ℂ := !![l₀⁻¹, b₀; 0, l₀]
  set L : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) := (Matrix.toLin' A).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_fin_two_of,
      inv_mul_cancel₀ h₀, mul_zero, sub_zero, map_one]
  have hL : MeasurePreserving L volume volume := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
    simp
  have e := volume_preserving_finTwoArrow ℂ
  have := e.comp (hL.comp e.symm)
  convert this using 1
  funext q
  simp [shearMap, L, A, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    MeasurableEquiv.finTwoArrow]

/-! ## The integral kernel -/

/-- The point `g_z(b, w, λ)` of the chart at `z`, with `q = (b, λ)`: the elements of `SL(2,ℂ)`
with `mob g z = w`, `den g z = λ` and `g₀₁ = b`. -/
noncomputable def chartPt (z w : ℂ) (q : ℂ × ℂ) : SL2C := fixChart z ![q.1, w, q.2]

/-- `chartPt z w` is measurable. -/
lemma measurable_chartPt (z w : ℂ) : Measurable (chartPt z w) :=
  (measurable_fixChart z).comp (continuous_fst.matrixVecCons (continuous_const.matrixVecCons
    (continuous_snd.matrixVecCons continuous_const))).measurable

/-- **The integral kernel of `π_{n,ρ}(f)`**: `K_f(z, w) = ∫ f(g_z(b, w, λ)) m(λ) d²b d²λ`, so that
`(π(f)φ)(z) = ∫ f(g) m(den g z) φ(mob g z) dg = ∫ K_f(z, w) φ(w) d²w` (chart at `z`). -/
noncomputable def psKernel (n : ℤ) (ρ : ℝ) (f : SL2C → ℂ) (z w : ℂ) : ℂ :=
  ∫ q : ℂ × ℂ, f (chartPt z w q) * mult n ρ q.2

/-- **`f* ∗ f`**: `x ↦ ∫ conj f(h) f(h x) dh`. Its value at `1` is `‖f‖²_{L²(G)}`. -/
noncomputable def selfConv (f : SL2C → ℂ) (x : SL2C) : ℂ := ∫ h, conj (f h) * f (h * x) ∂haarC

/-- The multiplier vanishes at `0` (Lean's `0 ^ s = 0` for `s ≠ 0`). -/
lemma mult_zero_right (n : ℤ) (ρ : ℝ) : mult n ρ 0 = 0 := by
  have h : (2 * I * (ρ : ℂ) - 2) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  simp [mult, Complex.zero_cpow h]

/-- For `λ ≠ 0`: `m(1/λ) = m(λ)⁻¹`. -/
lemma mult_inv (n : ℤ) (ρ : ℝ) {l : ℂ} (hl : l ≠ 0) : mult n ρ l⁻¹ = (mult n ρ l)⁻¹ := by
  have h := mult_mul n ρ hl (inv_ne_zero hl)
  rw [mul_inv_cancel₀ hl, mult_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

/-- For real `ρ` and `λ ≠ 0`: `|λ|⁻⁴ m(1/λ) = conj m(λ)`. -/
lemma invDensity_mul_mult_inv (n : ℤ) (ρ : ℝ) {l : ℂ} (hl : l ≠ 0) :
    ((invDensity l : ℝ) : ℂ) * mult n ρ l⁻¹ = conj (mult n ρ l) := by
  have hm : mult n ρ l ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_mult n ρ hl]; positivity
  rw [mult_inv n ρ hl, Complex.inv_def, Complex.normSq_eq_norm_sq, norm_mult n ρ hl]
  have : (invDensity l : ℝ) = ((‖l‖ ^ 2)⁻¹) ^ 2 := by
    simp [invDensity]; ring
  have ha : (((‖l‖ ^ 2)⁻¹ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [this, Complex.ofReal_inv, mul_comm, mul_assoc, inv_mul_cancel₀ ha, mul_one]

/-- Lebesgue-almost every `(b, λ) ∈ ℂ²` has `λ ≠ 0`. -/
lemma ae_snd_ne_zero : ∀ᵐ q : ℂ × ℂ, q.2 ≠ 0 := by
  have h : ∀ᵐ l : ℂ, l ≠ 0 := by
    rw [ae_iff]; simp
  exact Measure.quasiMeasurePreserving_snd.ae h

/-- **Left translation in the chart**: for `λ₀ ≠ 0`,
`∫ f(g_{z'}(b₀, z, λ₀) g_z(b, z, λ)) m(λ) d²b d²λ = m(1/λ₀) K_f(z', z)`. -/
lemma integral_mul_chartPt (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Measurable f)
    (z z' b₀ l₀ : ℂ) (h₀ : l₀ ≠ 0) :
    ∫ q : ℂ × ℂ, f (fixChart z' ![b₀, z, l₀] * chartPt z z q) * mult n ρ q.2 =
      mult n ρ l₀⁻¹ * psKernel n ρ f z' z := by
  set Ψ : ℂ × ℂ → ℂ := fun q => f (chartPt z' z q) * mult n ρ (l₀⁻¹ * q.2)
  have hΨ : Measurable Ψ := (hf.comp (measurable_chartPt z' z)).mul
    ((measurable_mult n ρ).comp (measurable_const.mul measurable_snd))
  have hT := measurePreserving_shearMap b₀ l₀ h₀
  have e1 : ∀ᵐ q : ℂ × ℂ ∂volume,
      f (fixChart z' ![b₀, z, l₀] * chartPt z z q) * mult n ρ q.2 = Ψ (shearMap b₀ l₀ q) := by
    filter_upwards [ae_snd_ne_zero] with q hq
    simp only [Ψ, chartPt, shearMap]
    rw [fixChart_mul z' z z b₀ l₀ q.1 q.2 h₀ hq, ← mul_assoc, inv_mul_cancel₀ h₀, one_mul]
  rw [integral_congr_ae e1, ← integral_map hT.measurable.aemeasurable
    (hT.map_eq ▸ hΨ.aestronglyMeasurable), hT.map_eq, psKernel, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_snd_ne_zero] with q hq
  simp only [Ψ, mult_mul n ρ (inv_ne_zero h₀) hq]
  ring

/-! ## Integrability -/

/-- **Chart bounds**: if `g_z(b, w, λ)` lies in a compact set `C` and `λ ≠ 0`, then `|(b, λ)|` and
`|1/λ|` are bounded, because `b = g₀₁`, `λ = g₁₁ + bz` and `1/λ = g₀₀ - bw`. -/
lemma chart_bound {C : Set SL2C} (hC : IsCompact C) (z w : ℂ) :
    ∃ R : ℝ, ∀ q : ℂ × ℂ, q.2 ≠ 0 → chartPt z w q ∈ C → ‖q‖ ≤ R ∧ ‖q.2⁻¹‖ ≤ R := by
  obtain ⟨A, hA⟩ := hC.exists_bound_of_continuousOn (continuous_entry 0 0).continuousOn
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (continuous_entry 0 1).continuousOn
  obtain ⟨D, hD⟩ := hC.exists_bound_of_continuousOn (continuous_entry 1 1).continuousOn
  refine ⟨max B (max (D + B * ‖z‖) (A + B * ‖w‖)), fun q hq hmem => ?_⟩
  have hg := fixChart_apply z (y := ![q.1, w, q.2]) (by simpa using hq)
  have e00 : (chartPt z w q : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = q.1 * w + q.2⁻¹ := by
    simp [chartPt, hg]
  have e01 : (chartPt z w q : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = q.1 := by simp [chartPt, hg]
  have e11 : (chartPt z w q : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = q.2 - q.1 * z := by
    simp [chartPt, hg]
  have h1 : ‖q.1‖ ≤ B := by have := hB _ hmem; simpa only [e01] using this
  have h00 : ‖q.1 * w + q.2⁻¹‖ ≤ A := by have := hA _ hmem; simpa only [e00] using this
  have h11 : ‖q.2 - q.1 * z‖ ≤ D := by have := hD _ hmem; simpa only [e11] using this
  have hz : ‖q.1 * z‖ ≤ B * ‖z‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hw : ‖q.1 * w‖ ≤ B * ‖w‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have h2 : ‖q.2‖ ≤ D + B * ‖z‖ :=
    calc ‖q.2‖ = ‖(q.2 - q.1 * z) + q.1 * z‖ := by rw [sub_add_cancel]
      _ ≤ ‖q.2 - q.1 * z‖ + ‖q.1 * z‖ := norm_add_le _ _
      _ ≤ D + B * ‖z‖ := add_le_add h11 hz
  have h3 : ‖q.2⁻¹‖ ≤ A + B * ‖w‖ :=
    calc ‖q.2⁻¹‖ = ‖(q.1 * w + q.2⁻¹) - q.1 * w‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖q.1 * w + q.2⁻¹‖ + ‖q.1 * w‖ := norm_sub_le _ _
      _ ≤ A + B * ‖w‖ := add_le_add h00 hw
  refine ⟨?_, h3.trans (le_max_of_le_right (le_max_right _ _))⟩
  rw [Prod.norm_def]
  exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_of_le_right (le_max_left _ _)))

/-- The indicator of a compact set, with a constant value, is integrable. -/
lemma integrable_indicator_isCompact {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) (c : ℝ) : Integrable (K.indicator fun _ => c) μ :=
  (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet

/-- **Integrability of the integrand of `K_{f*∗f}`**: for `f` continuous with compact support,
`(q, h) ↦ conj f(h) f(h g_z(q.1, w, q.2)) m(q.2)` is integrable for `d²b d²λ × dh`. It vanishes
unless `h ∈ supp f` and `g_z(q.1, w, q.2) ∈ (supp f)⁻¹ supp f`, where `chart_bound` applies. -/
lemma integrable_selfConv_integrand (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (z w : ℂ) :
    Integrable (Function.uncurry fun (q : ℂ × ℂ) (h : SL2C) =>
      conj (f h) * f (h * chartPt z w q) * mult n ρ q.2)
      ((volume : Measure (ℂ × ℂ)).prod haarC) := by
  have hfm : Measurable f := hf.measurable
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  have hS : IsCompact (tsupport f) := hfc
  obtain ⟨R, hR⟩ := chart_bound (hS.inv.mul hS) z w
  have hD := (integrable_indicator_isCompact (μ := (volume : Measure (ℂ × ℂ)))
    (isCompact_closedBall (0 : ℂ × ℂ) R) (B * R ^ 2)).mul_prod
    (integrable_indicator_isCompact (μ := haarC) hS B)
  refine hD.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (((Complex.continuous_conj.measurable.comp (hfm.comp measurable_snd)).mul
      (hfm.comp (measurable_snd.mul ((measurable_chartPt z w).comp measurable_fst)))).mul
      ((measurable_mult n ρ).comp (measurable_snd.comp measurable_fst))).aestronglyMeasurable
  obtain ⟨q, h⟩ := x
  simp only [Function.uncurry_apply_pair]
  have hnn : 0 ≤ (Metric.closedBall (0 : ℂ × ℂ) R).indicator (fun _ => B * R ^ 2) q *
      (tsupport f).indicator (fun _ => B) h :=
    mul_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) _)
      (Set.indicator_nonneg (fun _ _ => hB0) _)
  by_cases h1 : f h = 0
  · simpa [h1] using hnn
  by_cases h2 : f (h * chartPt z w q) = 0
  · simpa [h2] using hnn
  by_cases hq : q.2 = 0
  · simpa [hq, mult_zero_right] using hnn
  have hS1 : h ∈ tsupport f := subset_tsupport f (Function.mem_support.2 h1)
  have hS2 : h * chartPt z w q ∈ tsupport f := subset_tsupport f (Function.mem_support.2 h2)
  have hmem : chartPt z w q ∈ (tsupport f)⁻¹ * tsupport f :=
    Set.mem_mul.2 ⟨h⁻¹, Set.inv_mem_inv.2 hS1, h * chartPt z w q, hS2, inv_mul_cancel_left _ _⟩
  obtain ⟨hqR, hq2⟩ := hR q hq hmem
  have hm : ‖mult n ρ q.2‖ ≤ R ^ 2 := by
    rw [norm_mult n ρ hq, ← inv_pow, ← norm_inv]
    exact pow_le_pow_left₀ (norm_nonneg _) hq2 2
  rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hqR), Set.indicator_of_mem hS1,
    norm_mul, norm_mul, Complex.norm_conj]
  calc ‖f h‖ * ‖f (h * chartPt z w q)‖ * ‖mult n ρ q.2‖ ≤ B * B * R ^ 2 :=
        mul_le_mul (mul_le_mul (hB h) (hB _) (norm_nonneg _) hB0) hm (norm_nonneg _)
          (by positivity)
    _ = B * R ^ 2 * B := by ring

/-! ## The diagonal of `f* ∗ f` -/

/-- The diagonal of the kernel of `f* ∗ f` before taking absolute values: for `f` continuous with
compact support, `z' ↦ conj K_f(z', z) K_f(z', z)` is integrable and its integral is
`K_{f*∗f}(z, z)`.

The proof writes `K_{f*∗f}(z, z) = ∫_h conj f(h) ∫_{(b,λ)} f(h g_z(b, z, λ)) m(λ)` (Fubini), puts
`h = g_{z'}(b₀, z, λ₀)` in the inverse chart (`haarC_eq_map_invChart`, density `|λ₀|⁻⁴`), and
evaluates the inner integral by the shear `(b, λ) ↦ (b/λ₀ + b₀λ, λ₀λ)` (`integral_mul_chartPt`),
which leaves `m(1/λ₀) K_f(z', z)`; finally `|λ₀|⁻⁴ m(1/λ₀) = conj m(λ₀)`. -/
theorem psKernel_selfConv_diag_aux (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    Integrable (fun z' => conj (psKernel n ρ f z' z) * psKernel n ρ f z' z) ∧
    psKernel n ρ (selfConv f) z z = ∫ z', conj (psKernel n ρ f z' z) * psKernel n ρ f z' z := by
  have hfm : Measurable f := hf.measurable
  have hI := integrable_selfConv_integrand n ρ hf hfc z z
  have step1 : psKernel n ρ (selfConv f) z z =
      ∫ h, (∫ q : ℂ × ℂ, conj (f h) * f (h * chartPt z z q) * mult n ρ q.2) ∂haarC := by
    simp only [psKernel, selfConv]
    simp_rw [← integral_mul_const]
    exact integral_integral_swap hI
  set G : SL2C → ℂ := fun h => ∫ q : ℂ × ℂ, conj (f h) * f (h * chartPt z z q) * mult n ρ q.2
    with hGdef
  have hG : Integrable G haarC := hI.integral_prod_right
  have hmap := haarC_eq_map_invChart z
  have hG' : Integrable G (invChartMeasure.map (invChart z)) := hmap ▸ hG
  have hmeasD : Measurable fun p : ℂ × ℂ × ℂ => invDensity p.2.2 :=
    measurable_invDensity.comp (measurable_snd.comp measurable_snd)
  have hH : Integrable (fun p : ℂ × ℂ × ℂ => invDensity p.2.2 • G (invChart z p)) volume := by
    have := (integrable_map_measure hG'.aestronglyMeasurable (measurable_invChart z).aemeasurable).1
      hG'
    rw [invChartMeasure] at this
    exact (integrable_withDensity_iff_integrable_smul hmeasD).1 this
  have step2 : ∫ h, G h ∂haarC = ∫ p : ℂ × ℂ × ℂ, invDensity p.2.2 • G (invChart z p) := by
    rw [hmap, integral_map (measurable_invChart z).aemeasurable hG'.aestronglyMeasurable,
      invChartMeasure, integral_withDensity_eq_integral_smul hmeasD]
  have step3 : ∫ p : ℂ × ℂ × ℂ, invDensity p.2.2 • G (invChart z p) =
      ∫ z', ∫ q₀ : ℂ × ℂ, invDensity q₀.2 • G (invChart z (z', q₀)) :=
    integral_prod (μ := volume) (ν := volume) _ hH
  have step4 : ∀ z', ∫ q₀ : ℂ × ℂ, invDensity q₀.2 • G (invChart z (z', q₀)) =
      conj (psKernel n ρ f z' z) * psKernel n ρ f z' z := by
    intro z'
    have e : ∀ᵐ q₀ : ℂ × ℂ, invDensity q₀.2 • G (invChart z (z', q₀)) =
        conj (f (chartPt z' z q₀) * mult n ρ q₀.2) * psKernel n ρ f z' z := by
      filter_upwards [ae_snd_ne_zero] with q₀ hq₀
      have hGq : G (invChart z (z', q₀)) =
          conj (f (chartPt z' z q₀)) * (mult n ρ q₀.2⁻¹ * psKernel n ρ f z' z) := by
        simp only [hGdef, invChart, mul_assoc]
        rw [integral_const_mul]
        congr 1
        exact integral_mul_chartPt n ρ hfm z z' q₀.1 q₀.2 hq₀
      rw [hGq, NNReal.smul_def, Complex.real_smul, map_mul, ← invDensity_mul_mult_inv n ρ hq₀]
      ring
    rw [integral_congr_ae e, integral_mul_const, integral_conj]
    rfl
  refine ⟨hH.integral_prod_left.congr (Eventually.of_forall step4), ?_⟩
  rw [step1, step2, step3]
  exact integral_congr_ae (Eventually.of_forall step4)

/-- **Diagonal of the kernel of `f* ∗ f`**: for `f` continuous with compact support and every `z`,
`K_{f*∗f}(z, z) = ∫ |K_f(z', z)|² d²z'` (see `psKernel_selfConv_diag_aux` for the proof). -/
theorem psKernel_selfConv_diag (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    psKernel n ρ (selfConv f) z z = ((∫ z', ‖psKernel n ρ f z' z‖ ^ 2 : ℝ) : ℂ) := by
  rw [(psKernel_selfConv_diag_aux n ρ hf hfc z).2]
  simp_rw [Complex.conj_mul', ← Complex.ofReal_pow]
  exact integral_ofReal

/-- **The kernel of `π_{n,ρ}(f)` is square integrable** in its first variable: for `f` continuous
with compact support and every `z`, `z' ↦ |K_f(z', z)|²` is integrable. -/
theorem integrable_psKernel_sq (n : ℤ) (ρ : ℝ) {f : SL2C → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (z : ℂ) :
    Integrable fun z' => ‖psKernel n ρ f z' z‖ ^ 2 := by
  refine (psKernel_selfConv_diag_aux n ρ hf hfc z).1.re.congr
    (Eventually.of_forall fun z' => ?_)
  simp only [Complex.conj_mul', ← Complex.ofReal_pow]
  rfl

end Lightlike.Lorentz
