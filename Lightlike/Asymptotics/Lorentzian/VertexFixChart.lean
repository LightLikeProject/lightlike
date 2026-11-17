import Lightlike.Asymptotics.Lorentzian.VertexHaarChart
import Lightlike.Asymptotics.Lorentzian.ActionSmooth
import Lightlike.Asymptotics.Lorentzian.VertexLocal

/-!
# Smoothness of the vertex chart of the fixed charts

`fixVertexChart e` (`VertexHaarChart.lean`) is smooth on the open set where the third coordinate
`λ_a` of each of the four charts `g_0(b_a, w_a, λ_a)` is nonzero (the chart `g_0` has the entries
`[[b w + 1/λ, b], [λ w, λ]]`); its pulled-back action is smooth where moreover the overlap products
are off the cut of the logarithm (`lorChartAction_contDiffOn`).

## Main results

* `fixDomain`, `isOpen_fixDomain`: the open set `λ_a ≠ 0`.
* `fixVertexChart_group_contDiffOn`, `fixVertexChart_spinor_contDiff`: smoothness of the chart.
* `lorChartAction_fixVertexChart_contDiffOn`: smoothness of the action.
-/

open Complex MeasureTheory
open scoped ComplexConjugate ContDiff Matrix NNReal
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- A linear identification of finite-dimensional spaces is smooth. -/
theorem contDiff_of_isLinearMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : IsLinearMap ℝ f) : ContDiff ℝ ∞ f :=
  (LinearMap.toContinuousLinearMap (hf.mk' f)).contDiff

/-- The open set on which the `λ`-coordinate of each of the four charts is nonzero. -/
def fixDomain (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) : Set (Fin 44 → ℝ) :=
  {x | ∀ a : Fin 4, (e x).1 a 2 ≠ 0}

theorem isOpen_fixDomain (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : IsLinearMap ℝ e) : IsOpen (fixDomain e) := by
  have hc : Continuous e := (contDiff_of_isLinearMap he).continuous
  have : fixDomain e = ⋂ a : Fin 4, (fun x => (e x).1 a 2) ⁻¹' {0}ᶜ := by
    ext x; simp [fixDomain]
  rw [this]
  exact isOpen_iInter_of_finite fun a => isOpen_compl_singleton.preimage
    ((continuous_apply 2).comp ((continuous_apply a).comp (continuous_fst.comp hc)))

/-- The matrix entries of the group elements of `fixVertexChart` are smooth on `fixDomain`. -/
theorem fixVertexChart_group_contDiffOn (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : IsLinearMap ℝ e) (a : Fin 5) (i k : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => ((fixVertexChart e x).1 a : Matrix (Fin 2) (Fin 2) ℂ) i k) (fixDomain e) := by
  have hE : ContDiff ℝ ∞ e := contDiff_of_isLinearMap he
  -- coordinates of the chart variables
  have hy : ∀ (a' : Fin 4) (m : Fin 3), ContDiff ℝ ∞ (fun x => (e x).1 a' m) := fun a' m =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) m).contDiff.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 3 → ℂ) a').contDiff.comp
        (contDiff_fst.comp hE)))
  induction a using Fin.lastCases with
  | last =>
    have : (fun x => ((fixVertexChart e x).1 (Fin.last 4) : Matrix (Fin 2) (Fin 2) ℂ) i k) =
        fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) i k := by
      funext x
      show ((Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 ((e x).1 a)) (Fin.last 4) :
        SL2C) : Matrix (Fin 2) (Fin 2) ℂ) i k = _
      rw [Lightlike.Lorentz.gauge_last]
      rfl
    rw [this]; exact contDiffOn_const
  | cast a' =>
    have hf : ∀ x ∈ fixDomain e,
        ((fixVertexChart e x).1 (Fin.castSucc a') : Matrix (Fin 2) (Fin 2) ℂ) i k =
          (!![(e x).1 a' 0 * (e x).1 a' 1 + ((e x).1 a' 2)⁻¹, (e x).1 a' 0;
            (e x).1 a' 2 * (e x).1 a' 1, (e x).1 a' 2] : Matrix (Fin 2) (Fin 2) ℂ) i k := by
      intro x hx
      have h2 : (e x).1 a' 2 ≠ 0 := hx a'
      simp only [fixVertexChart, Lightlike.Lorentz.gauge_castSucc]
      rw [Lightlike.Lorentz.fixChart_apply 0 h2]
      simp
    refine ContDiffOn.congr ?_ hf
    have h2 : ∀ x ∈ fixDomain e, (e x).1 a' 2 ≠ 0 := fun x hx => hx a'
    fin_cases i <;> fin_cases k
    · exact ((hy a' 0).mul (hy a' 1)).contDiffOn.add
        (ContDiffOn.inv (hy a' 2).contDiffOn h2)
    · exact (hy a' 0).contDiffOn
    · exact ((hy a' 2).mul (hy a' 1)).contDiffOn
    · exact (hy a' 2).contDiffOn

/-- The spinors of `fixVertexChart` are smooth functions of `x`. -/
theorem fixVertexChart_spinor_contDiff (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (he : IsLinearMap ℝ e) (k : Fin 10) : ContDiff ℝ ∞ (fun x => (fixVertexChart e x).2 k) := by
  have hE : ContDiff ℝ ∞ e := contDiff_of_isLinearMap he
  have hw : ContDiff ℝ ∞ (fun x => (e x).2 k) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 10 => ℂ) k).contDiff.comp (contDiff_snd.comp hE)
  have hiff : ∀ {w : (Fin 44 → ℝ) → Spinor}, (∀ i, ContDiff ℝ ∞ (fun x => w x i)) → ContDiff ℝ ∞ w := by
    intro w h
    let L : (Fin 2 → ℂ) →L[ℝ] Spinor :=
      ((EuclideanSpace.equiv (Fin 2) ℂ).symm.toContinuousLinearMap).restrictScalars ℝ
    exact L.contDiff.comp (contDiff_pi.2 h)
  refine hiff fun i => ?_
  fin_cases i
  · simpa [fixVertexChart, lorSpinor] using hw
  · simpa [fixVertexChart, lorSpinor] using contDiff_const

/-- **The pulled-back action of `fixVertexChart` is smooth** on an open `U ⊆ fixDomain` where on
every edge the overlap product is off the cut of the logarithm. -/
theorem lorChartAction_fixVertexChart_contDiffOn
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (he : IsLinearMap ℝ e)
    (j p : Fin 10 → ℝ) (g : BdryData) {U : Set (Fin 44 → ℝ)} (hU : IsOpen U) (hUc : U ⊆ fixDomain e)
    (hP : ∀ x ∈ U, ∀ k,
      inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((fixVertexChart e x).2 k)) ∈ Complex.slitPlane) :
    ContDiffOn ℝ ∞ (lorChartAction j p g (fixVertexChart e)) U :=
  lorChartAction_contDiffOn j p g hU
    (fun a i k => (fixVertexChart_group_contDiffOn e he a i k).mono hUc)
    (fun k => (fixVertexChart_spinor_contDiff e he k).contDiffOn) hP

open Filter MeasureTheory Lightlike.Oscillatory in
open _root_.Asymptotics in
/-- **Hypothesis `VertexJointIntegrable`** (open fact about `lorVertex`, not proved): for every
`λ ∈ ℕ` the outer integral of the vertex of the scaled data is measurable and the integrand is jointly
integrable on `(ℂ³)⁴ × ℂ¹⁰` in the fixed charts. The vertex is defined as an iterated integral and the
existing finiteness (`integrable_lorOuter`) is that of the complex inner integral, not of its modulus;
BDFHP use the joint integral implicitly (Sec. 6.4 p. 30). Provable in Lean only with an estimate of
`∏_e ∫ ‖g_e‖ dw` (a source for the finiteness of the EPRL vertex would be needed). -/
def VertexJointIntegrable (j p : Fin 10 → ℝ) (g : BdryData) : Prop :=
  ∀ lam : ℕ, AEStronglyMeasurable (fun x : Fin 4 → SL2C => ∫ w : Fin 10 → ℂ,
      lorIntegrand (fun k => (lam : ℝ) * j k) (fun k => (lam : ℝ) * p k) g (Lightlike.Lorentz.gauge x) w)
      (Measure.pi fun _ : Fin 4 => Lightlike.Lorentz.haarC) ∧
    Integrable (fun q : (Fin 4 → (Fin 3 → ℂ)) × (Fin 10 → ℂ) =>
      lorIntegrand (fun k => (lam : ℝ) * j k) (fun k => (lam : ℝ) * p k) g
        (Lightlike.Lorentz.gauge (fun a => Lightlike.Lorentz.fixChart 0 (q.1 a))) q.2)

open Filter MeasureTheory Lightlike.Oscillatory in
open _root_.Asymptotics in
/-- **Hypothesis `HessianInvertible`** (open fact, not proved): the Hessian of `-S` in the fixed charts
is invertible at every point of `K`. BDFHP assume it ("non-degenerate boundary data", Sec. 6.4 p. 30,
eq. (57); Sec. 7 p. 31: a geometric formula for the Hessian is missing; Appendix A pp. 32-33,
eqs. (58)-(61)). Checked numerically on the regular simplex
(`scripts/asymptotics/lorentzian_hessian_check.py`) and for the node blocks
(`scripts/asymptotics/lorentzian_hessian_xx_certificate.py`). -/
def HessianInvertible (j p : Fin 10 → ℝ) (g : BdryData)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (K : Finset (Fin 44 → ℝ)) : Prop :=
  ∀ x ∈ K, (-lorHessian j p g (fixVertexChart e) x).det ≠ 0

open Filter MeasureTheory Lightlike.Oscillatory in
open _root_.Asymptotics in
/-- **Hypothesis `FarRemainderBound`** (open fact, not proved; not in BDFHP): the remainder
`(1 - χ) a e^{λ S}` is integrable for `λ ∈ ℕ` and its integral is `O(λ^{-23})`. Assumed only along the
integer sequence the proof uses; the form for all real `τ` fails for `τ < 0` wherever an overlap
vanishes. Needs `Re S ≤ -δ` on the support of `1 - χ` or an integrability estimate in the
non-compact directions: a new estimate. -/
def FarRemainderBound (j p : Fin 10 → ℝ) (g : BdryData)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (χ : (Fin 44 → ℝ) → ℝ) : Prop :=
  (∀ lam : ℕ, Integrable fun x => (((1 - χ x : ℝ) : ℂ) * chartAmplitude e x) *
      cexp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x)) ∧
    (fun lam : ℕ => ∫ x, (((1 - χ x : ℝ) : ℂ) * chartAmplitude e x) *
        cexp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (-((44 : ℝ) / 2) - 1))

open Filter MeasureTheory Lightlike.Oscillatory in
open _root_.Asymptotics in
/-- **Hypothesis `CriticalSetIs`** (the classification of the critical points, not proved outside
SU(2)): the points of the support of the localised amplitude with `Re S = 0` and `dS = 0` are exactly
`K`. BDFHP Sec. 5.4.3 p. 23 (two parity-related critical points for Lorentzian data, via the bivector
reconstruction theorem of arXiv:0902.1170). -/
def CriticalSetIs (j p : Fin 10 → ℝ) (g : BdryData)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (χ : (Fin 44 → ℝ) → ℝ)
    (K : Finset (Fin 44 → ℝ)) : Prop :=
  (∀ x ∈ tsupport (fun x => (χ x : ℂ) * chartAmplitude e x),
      ((lorChartAction j p g (fixVertexChart e) x).re = 0 ∧
        fderiv ℝ (lorChartAction j p g (fixVertexChart e)) x = 0) ↔ x ∈ K) ∧
    ∀ x ∈ K, x ∈ tsupport (fun x => (χ x : ℂ) * chartAmplitude e x)

open Filter MeasureTheory Lightlike.Oscillatory in
open _root_.Asymptotics in
/-- **The asymptotics of the scaled vertex in the fixed charts** (BDFHP eq. (53), (57) in the
form of `lorVertex_asymptotics_local`): the vertex of the scaled data `(λ j, λ p)` with constants
`cc λ` equals `w(λ) ∫_{ℝ⁴⁴} a(x) e^{λ S(x)} dx` with `w(λ) = (∏ cc λ) s⁻⁴` (`lorVertex_scaled_eq_chart_integral`)
and `a = ∏ Ω_e`; with the cutoff `a = χ a + (1 - χ) a`, `χ` smooth with compact support in `U`, the sum
over the critical points `K` of `w(λ) e^{λ S(x₀)} (2π/λ)^{22} (det (-H(x₀)))^{-1/2} χ a (x₀)` approximates
it up to `O(λ^{m - 23})`.

**Named hypotheses (limits)**, each a `Prop` with its own docstring: `VertexJointIntegrable`,
`CriticalSetIs` (the classification), `HessianInvertible`, `FarRemainderBound`, and the weight bound
`hw` (a condition on the data). None is proved here. The error exponent: the stationary phase in 44
real dimensions gives the leading order `λ^{-22}`, the error one further power, times the order `λ^m`
of the weight (`hw`).

**Differences from BDFHP eq. (53)** (Sec. 6.4): this is the generic stationary-phase sum over an
abstract finite critical set `K`, with an error bound `O(λ^{m - 23})` where the source states an
asymptotic equivalence; it does not identify the phase with `γ Σ k Θ`, the sign `(-1)^{χ + M}`, the
order `λ^{-12}` or the two parity-related critical points of eq. (53); and `λ` runs over `ℕ`. Until a
maintainer approves these differences, the result is partial. -/
theorem lorVertex_asymptotics_fixChart
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (he : MeasurePreserving e volume volume)
    (hl : IsLinearMap ℝ e) {j p : Fin 10 → ℝ} (hj : ∀ k, 0 ≤ j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    {U : Set (Fin 44 → ℝ)} (hU : IsOpen U) (hUc : U ⊆ fixDomain e)
    (hP : ∀ x ∈ U, ∀ k,
      inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((fixVertexChart e x).2 k)) ∈ Complex.slitPlane)
    (χ : (Fin 44 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hA : ContDiffOn ℝ ∞ (chartAmplitude e) U)
    (K : Finset (Fin 44 → ℝ)) (hK : CriticalSetIs j p g e χ K)
    (hdet : HessianInvertible j p g e K) (hfarB : FarRemainderBound j p g e χ)
    (cc : ℕ → Fin 10 → ℂ) (m : ℝ)
    (hw : (fun lam : ℕ => (∏ k, cc lam k) *
        ((((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ)) : ℂ))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m))
    (hvertex : VertexJointIntegrable j p g) :
    (fun lam : ℕ => lorVertex (fun k => (lam : ℝ) * j k) (fun k => (lam : ℝ) * p k) (cc lam) g -
      ((∏ k, cc lam k) *
        ((((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ)) : ℂ)) *
        ∑ x₀ ∈ K, cexp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x₀) *
          ((2 * Real.pi / (lam : ℝ)) ^ ((44 : ℝ) / 2) : ℝ) *
            invSqrtDet (-lorHessian j p g (fixVertexChart e) x₀) *
              ((χ x₀ : ℂ) * chartAmplitude e x₀))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (44 : ℝ) / 2 - 1)) := by
  set A := chartAmplitude e with hAdef
  set S := lorChartAction j p g (fixVertexChart e) with hSdef
  set aLoc : (Fin 44 → ℝ) → ℂ := fun x => (χ x : ℂ) * A x with haLoc
  set aFar : (Fin 44 → ℝ) → ℂ := fun x => ((1 - χ x : ℝ) : ℂ) * A x with haFar
  have hsU : tsupport aLoc ⊆ U :=
    (tsupport_mul_subset_left (f := fun x => (χ x : ℂ)) (g := A)).trans
      ((tsupport_comp_subset (by simp) (g := fun r : ℝ => (r : ℂ)) (f := χ)).trans hχU)
  have ha : ContDiff ℝ ∞ aLoc := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt.mul ((hA.contDiffAt (hU.mem_nhds hx)))
    · have hz : ∀ᶠ y in nhds x, χ y = 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hχU h)))
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hz] with y hy
      simp [haLoc, hy]
  have hc : HasCompactSupport aLoc := by
    refine hχc.mono ?_
    intro x hx
    by_contra hχx
    exact hx (by simp [haLoc, show χ x = 0 from Function.notMem_support.mp hχx])
  have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
  have hne : ∀ x ∈ tsupport aLoc, ∀ k,
      inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((fixVertexChart e x).2 k)) ≠ 0 :=
    fun x hx k h => h0 (h ▸ hP x (hsU hx) k)
  have hmain := lorVertex_asymptotics_local (n := 44) (aLoc := aLoc) (aFar := aFar) hj hξ hξ'
    hU (lorChartAction_fixVertexChart_contDiffOn e hl j p g hU hUc hP) hsU ha hc
    (fun x hx k h => (left_ne_zero_of_mul (hne x hx k)) (by rw [h]; simp))
    (fun x hx k h => (right_ne_zero_of_mul (hne x hx k)) (by rw [h]; simp))
    (fun x hx k => left_ne_zero_of_mul (hne x hx k))
    (fun x hx k => right_ne_zero_of_mul (hne x hx k)) K hK.1 hK.2 hdet hfarB.1 hfarB.2
    (fun lam => (∏ k, cc lam k) *
        ((((((Measure.haarScalarFactor Lightlike.Lorentz.haarC SL2C.haar) ^ 4)⁻¹ : ℝ≥0) : ℝ)) : ℂ))
    m hw
  refine hmain.congr' ?_ EventuallyEq.rfl
  refine Eventually.of_forall fun lam => ?_
  beta_reduce
  have hsplit : (fun x => (aLoc x + aFar x) * cexp (((lam : ℝ) : ℂ) *
      lorChartAction j p g (fixVertexChart e) x)) =
      fun x => chartAmplitude e x * cexp (((lam : ℝ) : ℂ) * lorChartAction j p g (fixVertexChart e) x) := by
    funext x
    simp only [haLoc, haFar, hAdef]
    push_cast
    ring_nf
  rw [lorVertex_scaled_eq_chart_integral e he j p (lam : ℝ) (cc lam) g (hvertex lam).1 (hvertex lam).2]
  simp only [hsplit]
  simp only [haLoc, hSdef, hAdef]
  congr 2

end Lightlike.Asymptotics.Lorentzian
