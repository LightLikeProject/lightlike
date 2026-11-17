import Lightlike.Asymptotics.Lorentzian.CoherentVertex
import Lightlike.Lorentz.FixedChart
import Lightlike.Asymptotics.Lorentzian.Amplitude
import Lightlike.Asymptotics.Lorentzian.AsymptoticFormula

/-!
# The Haar measure of the vertex in the fixed chart

`FixedChart.lean` shows that the Haar measure `haarC` of `SL(2,ℂ)` is Lebesgue measure on `ℂ³` in
the chart `g_z(b, w, λ)`: the density is exactly `1` (`haarC_eq_map_fixChart`). Here this is used for
the vertex: the gauge-fixed vertex `lorVertex` is `(∏ c_e) s⁻⁴` times the Lebesgue integral of the
integrand over `(ℂ³)⁴ × ℂ¹⁰` (real dimension `24 + 20 = 44`) in these charts, `s = haarScalarFactor
haarC SL2C.haar` (`lorVertex_eq_fixChart_integral`). Because the density is `1`, the amplitude of
the chart integral is the product of the densities `Ω_e` alone, which is the explicit `a(x)` of the
asymptotic formula, with no further Jacobian, in this chart (a change of chart multiplies it by the
Jacobian of the transition map).

The vertex is defined as an iterated integral (`SL(2,ℂ)⁴` outside, `ℂ¹⁰` inside; finiteness of the
outer integral for coherent data is `integrable_lorOuter`); the joint integrability on the product
is a hypothesis here, which BDFHP use implicitly when they apply the stationary phase formula to the
whole integral.

## Limits

* **Joint integrability (`hjoint`) and measurability of the outer integral (`hF`) are hypotheses, not
  results.** They do not follow from `integrable_lorInner` and `integrable_lorOuter`: the inner
  integrability is per point of `SL(2,ℂ)⁵` and the outer one is the integrability of the *complex*
  inner integral `x ↦ ∫ G(x,w) dw` (the finiteness of the EPRL amplitude, which uses the decay of the
  matrix coefficients, i.e. cancellations in the sum over magnetic numbers); joint integrability is
  that of `‖G‖`, `∫ ∏_e N_e(x) dx` with `N_e(x) = ∫ ‖g_e(x, w)‖ dw`, which needs a separate estimate
  and is not proved here (the weights `e^{Re S} ≤ 1` give no decay in `x`).
* The statement is for the chart `g_0` of `SL(2,ℂ)`; the Haar density is `1` there, and the
  Jacobian of a change of chart enters when the Hessian is computed in another chart.

## Main results

* `integral_haar4_fixChart`: `∫ F d(haarC)⁴ = ∫ F(g_z(y₁), …, g_z(y₄)) dy`.
* `integral_pi_haar_eq`: the integral against `Measure.pi SL2C.haar` is `s⁻⁴` times the one against
  `Measure.pi haarC`.
* `lorVertex_eq_fixChart_integral`: the vertex as a Lebesgue integral in the fixed charts.
* `exists_measurePreserving_vertex_space`: `ℝ⁴⁴ ≃ (ℂ³)⁴ × ℂ¹⁰` preserving Lebesgue measure.
* `fixVertexChart`, `chartAmplitude`, `lorVertex_eq_chart_integral`,
  `lorVertex_scaled_eq_chart_integral`: the vertex (and the vertex of the scaled data `(λ j, λ p)`) as
  `(∏ c_e) s⁻⁴ ∫_{ℝ⁴⁴} a(x) e^{λ S(x)} dx` with the `λ`-independent amplitude `a = ∏ Ω_e`: the
  statement `hpull` of the asymptotic formula, without cutoff.
-/

open MeasureTheory Complex
open scoped NNReal
open Lightlike.Asymptotics.EPRL
open Lightlike.Lorentz (SL2C)

namespace Lightlike.Asymptotics.Lorentzian

/-- **The product Haar measure in the product of fixed charts**: for `F` measurable,
`∫ F d(haarC)⁴ = ∫ F(g_z(y₁), …, g_z(y₄)) dy` over `(ℂ³)⁴`. -/
theorem integral_haar4_fixChart (z : ℂ) {F : (Fin 4 → SL2C) → ℂ} (hF : AEStronglyMeasurable F
    (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC)) :
    ∫ x, F x ∂(Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
      ∫ y : Fin 4 → (Fin 3 → ℂ), F (fun a => Lightlike.Lorentz.fixChart z (y a)) := by
  have hm : ∀ _ : Fin 4, AEMeasurable (Lightlike.Lorentz.fixChart z) (volume : Measure (Fin 3 → ℂ)) :=
    fun _ => (Lightlike.Lorentz.measurable_fixChart z).aemeasurable
  have hsf : SigmaFinite ((volume : Measure (Fin 3 → ℂ)).map (Lightlike.Lorentz.fixChart z)) := by
    rw [← Lightlike.Lorentz.haarC_eq_map_fixChart z]; infer_instance
  have hmap : (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
      (Measure.pi fun _ : Fin 4 => (volume : Measure (Fin 3 → ℂ))).map
        (fun y a => Lightlike.Lorentz.fixChart z (y a)) := by
    rw [Measure.pi_map_pi (μ := fun _ : Fin 4 => (volume : Measure (Fin 3 → ℂ)))
      (f := fun _ => Lightlike.Lorentz.fixChart z) hm]
    simp only [← Lightlike.Lorentz.haarC_eq_map_fixChart z]
  have hmeas : Measurable (fun (y : Fin 4 → (Fin 3 → ℂ)) (a : Fin 4) =>
      Lightlike.Lorentz.fixChart z (y a)) :=
    Measurable.of_eval fun a => (Lightlike.Lorentz.measurable_fixChart z).comp (measurable_pi_apply a)
  rw [hmap, integral_map hmeas.aemeasurable (by rw [← hmap]; exact hF)]
  rfl

/-- The vertex integral against `Measure.pi SL2C.haar` is `s⁻⁴` times the one against `Measure.pi haarC`,
`s = haarScalarFactor haarC SL2C.haar`. -/
theorem integral_pi_haar_eq (F : (Fin 4 → SL2C) → ℂ) :
    ∫ x, F x ∂(Measure.pi fun _ : Fin 4 => SL2C.haar) =
      (((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ) : ℂ) *
        ∫ x, F x ∂(Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) := by
  obtain ⟨s, hs⟩ : ∃ s : NNReal, s = Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar := ⟨_, rfl⟩
  have hC : Lightlike.Lorentz.haarC = s • SL2C.haar := by rw [hs]; exact Lightlike.Lorentz.haarC_eq_smul
  have hs0 : s ≠ 0 := by rw [hs]; exact Lightlike.Lorentz.haarScalarFactor_haarC_ne_zero
  have hmeas : (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
      s ^ 4 • Measure.pi fun _ : Fin 4 => SL2C.haar := by
    have : (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) =
        Measure.pi fun _ : Fin 4 => s • SL2C.haar := by rw [hC]
    rw [this]
    exact pi_const_smul SL2C.haar s 4
  rw [← hs, hmeas, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have : ((s ^ 4 : NNReal) : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast this

/-- **The vertex as a Lebesgue integral in the fixed chart**: if the integrand of the vertex is
jointly integrable on `SL(2,ℂ)⁴ × ℂ¹⁰` (in the chart `g_0` of each `SL(2,ℂ)`) and the outer integral
is measurable, then
`lorVertex = (∏ c_e) s⁻⁴ ∫_{(ℂ³)⁴ × ℂ¹⁰} lorIntegrand (g_0(y₁), …, g_0(y₄), 1) w dy dw`
with `s = haarScalarFactor haarC SL2C.haar`: the Haar measure in the chart `g_0` of `FixedChart.lean`
is Lebesgue measure, with density `1` (`haarC_eq_map_fixChart`). Joint integrability is an assumption
(the vertex is defined as an iterated integral; BDFHP use the joint integral implicitly). -/
theorem lorVertex_eq_fixChart_integral (j p : Fin 10 → ℝ) (c : Fin 10 → ℂ) (g : BdryData)
    (hF : AEStronglyMeasurable (fun x : Fin 4 → SL2C => ∫ w : Fin 10 → ℂ,
      lorIntegrand j p g (Lightlike.Lorentz.gauge x) w) (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC))
    (hjoint : Integrable (fun q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ) =>
      lorIntegrand j p g (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2)) :
    lorVertex j p c g = (∏ e, c e) *
      ((((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ)) : ℂ) *
        ∫ q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ),
          lorIntegrand j p g (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2 := by
  unfold lorVertex
  rw [integral_pi_haar_eq, integral_haar4_fixChart 0 hF, ← integral_prod _ hjoint]
  rw [mul_assoc]
  rfl

/-- **Uncurrying `ι → κ → α` into `ι × κ → α` preserves the product measure.** -/
theorem measurePreserving_uncurry_pi (ι κ α : Type*) [Fintype ι] [Fintype κ] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (fun f : ι → κ → α => fun p : ι × κ => f p.1 p.2)
      (volume : Measure (ι → κ → α)) (volume : Measure (ι × κ → α)) := by
  have hmeas : Measurable (fun f : ι → κ → α => fun p : ι × κ => f p.1 p.2) :=
    Measurable.of_eval fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hmeas, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have : (fun f : ι → κ → α => fun p : ι × κ => f p.1 p.2) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi fun i => Set.univ.pi fun k => s (i, k) := by
    ext f; simp [Set.mem_pi]
  rw [this]
  rw [show (volume : Measure (ι → κ → α)) = Measure.pi fun _ => Measure.pi fun _ => volume from rfl]
  rw [Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- The composition of two `ℝ`-linear maps is linear. -/
theorem isLinearMap_comp' {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module ℝ E] [Module ℝ F] [Module ℝ G] {f : E → F} {g : F → G} (hf : IsLinearMap ℝ f)
    (hg : IsLinearMap ℝ g) : IsLinearMap ℝ (g ∘ f) :=
  ⟨fun x y => by simp [hf.map_add, hg.map_add], fun c x => by simp [hf.map_smul, hg.map_smul]⟩

/-- Currying `ι × κ → ℝ` into `ι → κ → ℝ` is `ℝ`-linear. -/
theorem isLinearMap_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    IsLinearMap ℝ (MeasurableEquiv.curry ι κ ℝ) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> ext j <;> simp [MeasurableEquiv.curry]

/-- A complex vector indexed by `ι` is a real vector indexed by `ι × Fin 2`, linearly and with the
same Lebesgue measure. -/
theorem exists_measurePreserving_complex_pi (ι : Type*) [Fintype ι] :
    ∃ e : (ι × Fin 2 → ℝ) ≃ᵐ (ι → ℂ), MeasurePreserving e volume volume ∧ IsLinearMap ℝ e := by
  let e1 : (ι × Fin 2 → ℝ) ≃ᵐ (ι → Fin 2 → ℝ) := MeasurableEquiv.curry ι (Fin 2) ℝ
  have h1 : MeasurePreserving e1 (volume : Measure (ι × Fin 2 → ℝ)) (volume : Measure (ι → Fin 2 → ℝ)) :=
    (measurePreserving_uncurry_pi ι (Fin 2) ℝ).symm (MeasurableEquiv.curry ι (Fin 2) ℝ).symm
  let e2 : (ι → Fin 2 → ℝ) ≃ᵐ (ι → ℂ) :=
    MeasurableEquiv.piCongrRight fun _ => Complex.measurableEquivPi.symm
  have h2 : MeasurePreserving e2 (volume : Measure (ι → Fin 2 → ℝ)) (volume : Measure (ι → ℂ)) :=
    volume_preserving_pi fun _ => Complex.volume_preserving_equiv_pi.symm
  have l1 : IsLinearMap ℝ e1 := isLinearMap_curry ι (Fin 2)
  have l2 : IsLinearMap ℝ e2 := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> ext j <;> apply Complex.ext <;>
      simp [e2, MeasurableEquiv.piCongrRight, Complex.measurableEquivPi]
  have l := isLinearMap_comp' l1 l2
  exact ⟨e1.trans e2, h1.trans h2, l⟩

/-- **A measure-preserving linear identification of `ℝ⁴⁴` with `(ℂ³)⁴ × ℂ¹⁰`** (the variables of the
vertex): `24 + 20 = 44` real coordinates. -/
theorem exists_measurePreserving_vertex_space :
    ∃ e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)),
      MeasurePreserving e volume volume ∧ IsLinearMap ℝ e := by
  obtain ⟨eA, hA, lA⟩ := exists_measurePreserving_complex_pi (Fin 4 × Fin 3)
  obtain ⟨eB, hB, lB⟩ := exists_measurePreserving_complex_pi (Fin 10)
  let κ := ((Fin 4 × Fin 3) × Fin 2) ⊕ (Fin 10 × Fin 2)
  have hcard : Fintype.card κ = 44 := by simp [κ]
  let f : Fin 44 ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let c1 : (Fin 44 → ℝ) ≃ᵐ (κ → ℝ) := MeasurableEquiv.piCongrLeft (fun _ => ℝ) f
  have h1 : MeasurePreserving c1 (volume : Measure (Fin 44 → ℝ)) (volume : Measure (κ → ℝ)) :=
    volume_measurePreserving_piCongrLeft (fun _ => ℝ) f
  have l1 : IsLinearMap ℝ c1 := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> ext j <;>
      simp [c1, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  let c2 : (κ → ℝ) ≃ᵐ (((Fin 4 × Fin 3) × Fin 2 → ℝ) × (Fin 10 × Fin 2 → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)
  have h2 : MeasurePreserving c2 (volume : Measure (κ → ℝ)) volume :=
    volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ)
  have l2 : IsLinearMap ℝ c2 := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> apply Prod.ext <;> ext j <;>
      simp [c2, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  let c3 := eA.prodCongr eB
  have h3 : MeasurePreserving c3 (volume : Measure (((Fin 4 × Fin 3) × Fin 2 → ℝ) × (Fin 10 × Fin 2 → ℝ)))
      (volume : Measure ((Fin 4 × Fin 3 → ℂ) × (Fin 10 → ℂ))) := hA.prod hB
  have l3 : IsLinearMap ℝ c3 := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩ <;> apply Prod.ext
    · exact lA.map_add _ _
    · exact lB.map_add _ _
    · exact lA.map_smul _ _
    · exact lB.map_smul _ _
  let c4 : (Fin 4 × Fin 3 → ℂ) ≃ᵐ (Fin 4 → Fin 3 → ℂ) := MeasurableEquiv.curry (Fin 4) (Fin 3) ℂ
  have h4 : MeasurePreserving c4 (volume : Measure (Fin 4 × Fin 3 → ℂ)) (volume : Measure (Fin 4 → Fin 3 → ℂ)) :=
    (measurePreserving_uncurry_pi (Fin 4) (Fin 3) ℂ).symm (MeasurableEquiv.curry (Fin 4) (Fin 3) ℂ).symm
  let c5 := c4.prodCongr (MeasurableEquiv.refl (Fin 10 → ℂ))
  have h5 : MeasurePreserving c5 (volume : Measure ((Fin 4 × Fin 3 → ℂ) × (Fin 10 → ℂ)))
      (volume : Measure ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) := h4.prod (MeasurePreserving.id _)
  have l5 : IsLinearMap ℝ c5 := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · apply Prod.ext
      · funext i k; simp [c5, c4, MeasurableEquiv.curry, MeasurableEquiv.prodCongr]
      · simp [c5, MeasurableEquiv.prodCongr]
    · apply Prod.ext
      · funext i k; simp [c5, c4, MeasurableEquiv.curry, MeasurableEquiv.prodCongr]
      · simp [c5, MeasurableEquiv.prodCongr]
  have l := isLinearMap_comp' (isLinearMap_comp' (isLinearMap_comp' l1 l2) l3) l5
  exact ⟨c1.trans (c2.trans (c3.trans c5)), h1.trans (h2.trans (h3.trans h5)), l⟩

/-- The vertex chart of the fixed charts, on `ℝ⁴⁴` through a measure-preserving identification
`e : ℝ⁴⁴ ≃ (ℂ³)⁴ × ℂ¹⁰`: `X_a = g_0(y_a)` for `a < 4`, `X_4 = 1` (the gauge) and `z_e = (w_e, 1)`. -/
noncomputable def fixVertexChart (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (x : Fin 44 → ℝ) : (Fin 5 → SL2C) × (Fin 10 → Spinor) :=
  (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 ((e x).1 a)),
    fun k => lorSpinor ((e x).2 k))

/-- The amplitude of the chart integral: the product of the densities `Ω_e = 1/(‖Z_ab‖² ‖Z_ba‖²)`. -/
noncomputable def chartAmplitude (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (x : Fin 44 → ℝ) : ℂ :=
  ∏ k, ((lorEdgeDensity (fixVertexChart e x).1 (fixVertexChart e x).2 k : ℝ) : ℂ)

/-- **The vertex as an integral over `ℝ⁴⁴` of `a(x) e^{S(x)}`** (the statement `hpull` of the
asymptotic formula, for the cutoff-free amplitude `a = ∏ Ω_e`), under joint integrability (named
limit above). -/
theorem lorVertex_eq_chart_integral (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : MeasurePreserving e volume volume) (j p : Fin 10 → ℝ) (c : Fin 10 → ℂ) (g : BdryData)
    (hF : AEStronglyMeasurable (fun x : Fin 4 → SL2C => ∫ w : Fin 10 → ℂ,
      lorIntegrand j p g (Lightlike.Lorentz.gauge x) w) (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC))
    (hjoint : Integrable (fun q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ) =>
      lorIntegrand j p g (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2)) :
    lorVertex j p c g = (∏ k, c k) *
      ((((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ)) : ℂ) *
        ∫ x : Fin 44 → ℝ, chartAmplitude e x *
          Complex.exp (lorChartAction j p g (fixVertexChart e) x) := by
  rw [lorVertex_eq_fixChart_integral j p c g hF hjoint]
  congr 1
  rw [← he.integral_comp' (fun q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ) =>
    lorIntegrand j p g (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [lorIntegrand, chartAmplitude, lorChartAction, fixVertexChart]
  ring

/-- **The scaled vertex** `(λ j, λ p)` (weights `c λ`): the integrand is `a(x) e^{λ S(x)}` with the
same `λ`-independent amplitude `a`, since `S(λ j, λ p) = λ S(j, p)` (`lorAction_smul`). -/
theorem lorVertex_scaled_eq_chart_integral (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : MeasurePreserving e volume volume) (j p : Fin 10 → ℝ) (lam : ℝ) (c : Fin 10 → ℂ)
    (g : BdryData)
    (hF : AEStronglyMeasurable (fun x : Fin 4 → SL2C => ∫ w : Fin 10 → ℂ,
      lorIntegrand (fun k => lam * j k) (fun k => lam * p k) g (Lightlike.Lorentz.gauge x) w)
      (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC))
    (hjoint : Integrable (fun q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ) =>
      lorIntegrand (fun k => lam * j k) (fun k => lam * p k) g
        (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2)) :
    lorVertex (fun k => lam * j k) (fun k => lam * p k) c g = (∏ k, c k) *
      ((((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ)) : ℂ) *
        ∫ x : Fin 44 → ℝ, chartAmplitude e x *
          Complex.exp ((lam : ℂ) * lorChartAction j p g (fixVertexChart e) x) := by
  rw [lorVertex_eq_chart_integral e he _ _ c g hF hjoint]
  have hfun : (fun x : Fin 44 → ℝ => chartAmplitude e x *
      Complex.exp (lorChartAction (fun k => lam * j k) (fun k => lam * p k) g (fixVertexChart e) x)) =
      fun x => chartAmplitude e x *
        Complex.exp ((lam : ℂ) * lorChartAction j p g (fixVertexChart e) x) := by
    funext x
    simp only [lorChartAction, lorAction_smul]
  rw [hfun]

end Lightlike.Asymptotics.Lorentzian
