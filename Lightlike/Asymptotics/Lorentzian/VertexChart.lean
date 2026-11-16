import Lightlike.Asymptotics.Lorentzian.CayleyChart
import Lightlike.Asymptotics.Lorentzian.VertexLocal

/-!
# The 44-variable chart of the vertex amplitude near a critical point

`vertexChart X₀ w₀ : ℝ⁴⁴ → SL(2,ℂ)⁵ × (ℂ²)¹⁰`: the group elements `X_a = X₀_a · cayley(φ_a + iθ_a)`
for `a < 4` (24 real variables `θ_a, φ_a ∈ ℝ³`, the rotation and boost coordinates of BDFHP
Appendix A) with `X_4 = X₀_4` fixed (the gauge `X₅ = 1`), and the spinors `z_e = (w₀_e + u_e + i v_e, 1)`
(20 real variables): the chart `z = (w, 1)` of `ℂℙ¹` used by the vertex integral. The chart is the
identity configuration `(X₀, (w₀,1))` at `0`, smooth on the open set where the Cayley denominators
do not vanish, and its action is smooth where the overlaps are off the cut of the logarithm.

## Main results

* `vertexChart`, `vertexChart_zero`: the chart and its value at the base point.
* `vertexChart_group_contDiffOn`, `vertexChart_spinor_contDiff`: smoothness.
* `lorChartAction_vertexChart_contDiffOn`: the pulled-back action is smooth on the open set where
  the Cayley denominators are nonzero and the overlap product is off the cut on every edge.

The Haar density of the chart and the identification of the vertex integral with the integral over
the chart are not here (named hypotheses of the asymptotic formula).
-/

open Complex
open scoped ComplexConjugate ContDiff Matrix
open Lightlike.Lorentz (SL2C)
open Lightlike.Asymptotics.EPRL

namespace Lightlike.Asymptotics.Lorentzian

/-- The chart coordinate `c_a = φ_a + iθ_a ∈ ℂ³` of the group element `X_a`, `a < 4`: the variable
`6a + m` is the rotation `θ_{a,m}` and `6a + 3 + m` the boost `φ_{a,m}`. -/
noncomputable def chartCoord (x : Fin 44 → ℝ) (a : Fin 4) : Fin 3 → ℂ := fun m =>
  (x ⟨6 * a + 3 + m, by omega⟩ : ℂ) + Complex.I * (x ⟨6 * a + m, by omega⟩ : ℂ)

/-- **The chart** `ℝ⁴⁴ → SL(2,ℂ)⁵ × (ℂ²)¹⁰` near the base point `(X₀, (w₀, 1))`. -/
noncomputable def vertexChart (X₀ : Fin 5 → SL2C) (w₀ : Fin 10 → ℂ) (x : Fin 44 → ℝ) :
    (Fin 5 → SL2C) × (Fin 10 → Spinor) :=
  (fun a => if h : a.val < 4 then X₀ a * cayley (chartCoord x ⟨a.val, h⟩) else X₀ a,
   fun e => !₂[w₀ e + (x ⟨24 + 2 * e, by omega⟩ : ℂ) + Complex.I * (x ⟨25 + 2 * e, by omega⟩ : ℂ), 1])

/-- At `x = 0` the chart is the base point. -/
theorem vertexChart_zero (X₀ : Fin 5 → SL2C) (w₀ : Fin 10 → ℂ) :
    vertexChart X₀ w₀ 0 = (X₀, fun e => !₂[w₀ e, 1]) := by
  have hc : ∀ a : Fin 4, chartCoord 0 a = 0 := by
    intro a; funext m; simp [chartCoord]
  refine Prod.ext ?_ ?_
  · funext a
    by_cases h : a.val < 4
    · simp [vertexChart, h, hc, cayley_zero]
    · simp [vertexChart, h]
  · funext e
    simp [vertexChart]

/-- The chart coordinates are smooth (linear) functions of `x`. -/
theorem contDiff_chartCoord (a : Fin 4) : ContDiff ℝ ∞ (fun x : Fin 44 → ℝ => chartCoord x a) := by
  rw [contDiff_pi]
  intro m
  simp only [chartCoord]
  have h1 : ContDiff ℝ ∞ (fun x : Fin 44 → ℝ => (x ⟨6 * a + 3 + m, by omega⟩ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 44 => ℝ) _).contDiff
  have h2 : ContDiff ℝ ∞ (fun x : Fin 44 → ℝ => (x ⟨6 * a + m, by omega⟩ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 44 => ℝ) _).contDiff
  exact h1.add (contDiff_const.mul h2)

/-- The open set on which all four Cayley denominators are nonzero. -/
def cayleyDomain : Set (Fin 44 → ℝ) := {x | ∀ a : Fin 4, cayleyS (chartCoord x a) ≠ 1}

theorem isOpen_cayleyDomain : IsOpen cayleyDomain := by
  have : cayleyDomain = ⋂ a : Fin 4, (fun x => chartCoord x a) ⁻¹' {c | cayleyS c ≠ 1} := by
    ext x; simp [cayleyDomain]
  rw [this]
  exact isOpen_iInter_of_finite fun a => isOpen_cayley_domain.preimage (contDiff_chartCoord a).continuous

/-- The matrix entries of the group elements of the chart are smooth on `cayleyDomain`. -/
theorem vertexChart_group_contDiffOn (X₀ : Fin 5 → SL2C) (w₀ : Fin 10 → ℂ) (a : Fin 5)
    (i k : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => ((vertexChart X₀ w₀ x).1 a : Matrix (Fin 2) (Fin 2) ℂ) i k) cayleyDomain := by
  by_cases h : a.val < 4
  · have hf : ∀ x ∈ cayleyDomain, ((vertexChart X₀ w₀ x).1 a : Matrix (Fin 2) (Fin 2) ℂ) i k =
        ∑ l, (X₀ a : Matrix (Fin 2) (Fin 2) ℂ) i l * cayleyMat (chartCoord x ⟨a.val, h⟩) l k := by
      intro x hx
      simp only [vertexChart, h, ↓reduceDIte, Matrix.SpecialLinearGroup.coe_mul]
      rw [coe_cayley (hx ⟨a.val, h⟩), Matrix.mul_apply]
    refine ContDiffOn.congr ?_ hf
    refine ContDiffOn.sum fun l _ => contDiffOn_const.mul ?_
    exact (contDiffOn_cayleyMat l k).comp (contDiff_chartCoord ⟨a.val, h⟩).contDiffOn
      (fun x hx => hx ⟨a.val, h⟩)
  · simp only [vertexChart, h, ↓reduceDIte]
    exact contDiffOn_const

/-- The spinors of the chart are smooth (affine) functions of `x`. -/
theorem vertexChart_spinor_contDiff (X₀ : Fin 5 → SL2C) (w₀ : Fin 10 → ℂ) (e : Fin 10) :
    ContDiff ℝ ∞ (fun x => (vertexChart X₀ w₀ x).2 e) := by
  have hiff : ∀ {w : (Fin 44 → ℝ) → Spinor}, (∀ i, ContDiff ℝ ∞ (fun x => w x i)) → ContDiff ℝ ∞ w := by
    intro w h
    let L : (Fin 2 → ℂ) →L[ℝ] Spinor :=
      ((EuclideanSpace.equiv (Fin 2) ℂ).symm.toContinuousLinearMap).restrictScalars ℝ
    exact L.contDiff.comp (contDiff_pi.2 h)
  refine hiff fun i => ?_
  have h1 : ContDiff ℝ ∞ (fun x : Fin 44 → ℝ => (x ⟨24 + 2 * e, by omega⟩ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 44 => ℝ) _).contDiff
  have h2 : ContDiff ℝ ∞ (fun x : Fin 44 → ℝ => (x ⟨25 + 2 * e, by omega⟩ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 44 => ℝ) _).contDiff
  fin_cases i
  · simpa [vertexChart] using (contDiff_const.add h1).add (contDiff_const.mul h2)
  · simpa [vertexChart] using contDiff_const

/-- **The pulled-back action of the vertex chart is smooth** on the open set where the four Cayley
denominators are nonzero and, on every edge, the product of the overlaps is off the cut. -/
theorem lorChartAction_vertexChart_contDiffOn (j p : Fin 10 → ℝ) (g : BdryData) (X₀ : Fin 5 → SL2C)
    (w₀ : Fin 10 → ℂ) {U : Set (Fin 44 → ℝ)} (hU : IsOpen U) (hUc : U ⊆ cayleyDomain)
    (hP : ∀ x ∈ U, ∀ e,
      inner ℂ (spinAct ((vertexChart X₀ w₀ x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((vertexChart X₀ w₀ x).2 e)) (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1)))
          (spinAct ((vertexChart X₀ w₀ x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((vertexChart X₀ w₀ x).2 e)) ∈ Complex.slitPlane) :
    ContDiffOn ℝ ∞ (lorChartAction j p g (vertexChart X₀ w₀)) U :=
  lorChartAction_contDiffOn j p g hU
    (fun a i k => (vertexChart_group_contDiffOn X₀ w₀ a i k).mono hUc)
    (fun e => (vertexChart_spinor_contDiff X₀ w₀ e).contDiffOn) hP

open Filter MeasureTheory Lightlike.Oscillatory in
open _root_.Asymptotics in
/-- **The vertex asymptotics in the 44-variable chart**: `lorVertex_asymptotics_local` for
`vertexChart X₀ w₀`, with its smoothness hypothesis replaced by the conditions that make it true:
`U ⊆ cayleyDomain` open, containing the support of the localised amplitude, with the overlap product
off the cut on every edge at every point of `U`. The Haar density and the identification of the
vertex integral with `∫ (aLoc + aFar) e^{λS}` over the chart remain named hypotheses (`aLoc`,
`aFar`); the chart is smooth, equal to the base point at `0`, with tangent map the generators of BDFHP
Appendix A. -/
theorem lorVertex_asymptotics_vertexChart {j p : Fin 10 → ℝ} (hj : ∀ e, 0 ≤ j e) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (X₀ : Fin 5 → SL2C) (w₀ : Fin 10 → ℂ) {U : Set (Fin 44 → ℝ)} (hU : IsOpen U)
    (hUc : U ⊆ cayleyDomain)
    (hP : ∀ x ∈ U, ∀ e,
      inner ℂ (spinAct ((vertexChart X₀ w₀ x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((vertexChart X₀ w₀ x).2 e)) (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1)))
          (spinAct ((vertexChart X₀ w₀ x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((vertexChart X₀ w₀ x).2 e)) ∈ Complex.slitPlane)
    {aLoc aFar : (Fin 44 → ℝ) → ℂ} (hsU : tsupport aLoc ⊆ U)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (K : Finset (Fin 44 → ℝ))
    (hK : ∀ x ∈ tsupport aLoc,
      ((lorChartAction j p g (vertexChart X₀ w₀) x).re = 0 ∧
        fderiv ℝ (lorChartAction j p g (vertexChart X₀ w₀)) x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport aLoc)
    (hdet : ∀ x ∈ K, (-lorHessian j p g (vertexChart X₀ w₀) x).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x =>
      aFar x * cexp (τ * lorChartAction j p g (vertexChart X₀ w₀) x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x *
        cexp ((lam : ℝ) * lorChartAction j p g (vertexChart X₀ w₀) x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (-((44 : ℝ) / 2) - 1)))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) :
    (fun lam : ℕ => w lam * (∫ x, (aLoc x + aFar x) *
        cexp ((lam : ℝ) * lorChartAction j p g (vertexChart X₀ w₀) x)) -
      w lam * ∑ x₀ ∈ K, cexp ((lam : ℝ) * lorChartAction j p g (vertexChart X₀ w₀) x₀) *
        ((2 * Real.pi / (lam : ℝ)) ^ ((44 : ℝ) / 2) : ℝ) *
          invSqrtDet (-lorHessian j p g (vertexChart X₀ w₀) x₀) * aLoc x₀)
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (44 : ℝ) / 2 - 1)) := by
  have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
  have hne : ∀ x ∈ tsupport aLoc, ∀ e,
      inner ℂ (spinAct ((vertexChart X₀ w₀ x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((vertexChart X₀ w₀ x).2 e)) (firstCol (g e 0)) *
        inner ℂ (jMap (firstCol (g e 1)))
          (spinAct ((vertexChart X₀ w₀ x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((vertexChart X₀ w₀ x).2 e)) ≠ 0 :=
    fun x hx e h => h0 (h ▸ hP x (hsU hx) e)
  exact lorVertex_asymptotics_local (n := 44) hj hξ hξ' hU
    (lorChartAction_vertexChart_contDiffOn j p g X₀ w₀ hU hUc hP) hsU ha hc
    (fun x hx e h => (left_ne_zero_of_mul (hne x hx e)) (by rw [h]; simp))
    (fun x hx e h => (right_ne_zero_of_mul (hne x hx e)) (by rw [h]; simp))
    (fun x hx e => left_ne_zero_of_mul (hne x hx e))
    (fun x hx e => right_ne_zero_of_mul (hne x hx e)) K hK hKs hdet hint hfar w m hw

end Lightlike.Asymptotics.Lorentzian
