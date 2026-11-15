import Lightlike.Asymptotics.Lorentzian.VertexFormula
import Lightlike.Asymptotics.Lorentzian.Parity

/-!
# The Lorentzian vertex action on `SL(2,ℂ)^5 × (ℂ²)^10` and its asymptotics in a chart

The action of the coherent Lorentzian EPRL vertex (BDFHP eq. (17)) is the sum over the ten
triangles of the one-triangle action `triAction`, evaluated at the spinors `Z = X_a† z_ab` and
`Z' = X_b† z_ab`, with the boundary spinors `ξ_ab` and `ξ_ba` the first columns of the boundary
group elements. This file defines it, proves `Re S ≤ 0` where no spinor or overlap vanishes, and
combines it with `weighted_asymptotics` for a chart of dimension `n`.

What is **assumed**, not constructed: (i) the chart `chart : ℝⁿ → SL(2,ℂ)^5 × (ℂ²)^10` onto a
neighbourhood of the critical points and its smoothness of the pulled-back action; (ii) the
amplitude `aLoc + aFar` is the pullback of the Haar density of `SL(2,ℂ)^4` and of the spinor
measure times the coherent amplitude, with `aLoc` compactly supported near the critical points
(the library has no Haar measure of `SL(2,ℂ)`); (iii) the finiteness and nondegeneracy of the
critical set `K` (the critical set classification outside SU(2) is not proved); (iv) `hfar` and
`hint`. The weight `w` stands for the dimension factors.

Open gaps, listed here so that no result reads stronger than it is: there is no closed form of the
`44 × 44` Hessian (`lorHessian` is the Hessian of the pulled-back action), no Haar measure of
`SL(2,ℂ)` in the library, and the explicit constants of the source are not computed.
-/

open Complex Filter Asymptotics MeasureTheory Lightlike.Oscillatory Lightlike.Asymptotics.EPRL
open scoped Real ContDiff Topology Matrix
open Lightlike.Lorentz (SL2C)

namespace Lightlike.Asymptotics.Lorentzian

/-- The action (17) of the Lorentzian vertex: the sum over the ten triangles `e` of
`triAction (j e) (p e)` at `Z = X_{src e}† z_e`, `Z' = X_{tgt e}† z_e` and the boundary spinors
`ξ = firstCol (g e 0)`, `ξ' = firstCol (g e 1)`. Here `j e` is the spin parameter of
`triAction` and `p e` the parameter multiplying the imaginary part (`p = γ j` in the model). -/
noncomputable def lorAction (j p : Fin 10 → ℝ) (g : BdryData) (X : Fin 5 → SL2C)
    (z : Fin 10 → Spinor) : ℂ :=
  ∑ e : Fin 10, triAction (j e) (p e)
    (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 0))
    (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) (firstCol (g e 1))

/-- The real part of the one-triangle action is nonpositive when the spinors are nonzero, the
boundary spinors have norm one and neither overlap vanishes (where `log` has no junk value). -/
theorem re_triAction_le_zero {k p : ℝ} (hk : 0 ≤ k) {Z ξ Z' ξ' : Spinor} (hZ : Z ≠ 0)
    (hZ' : Z' ≠ 0) (hξ : ‖ξ‖ = 1) (hξ' : ‖ξ'‖ = 1) (h1 : inner ℂ Z ξ ≠ 0)
    (h2 : inner ℂ (jMap ξ') Z' ≠ 0) : (triAction k p Z ξ Z' ξ').re ≤ 0 := by
  have h := norm_exp_triAction (k := k) (p := p) hZ hZ' h1 h2
  rw [Complex.norm_exp] at h
  have hle := triWeight_le_one hk hZ hZ' hξ hξ'
  rw [← h] at hle
  exact Real.exp_le_one_iff.mp hle

/-- `Re S ≤ 0` for the vertex action, under the edgewise hypotheses of `re_triAction_le_zero`. -/
theorem re_lorAction_le_zero {j p : Fin 10 → ℝ} (hj : ∀ e, 0 ≤ j e) {g : BdryData}
    {X : Fin 5 → SL2C} {z : Fin 10 → Spinor}
    (hZ : ∀ e, spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (hZ' : ∀ e, spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e) ≠ 0)
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (h1 : ∀ e, inner ℂ (spinAct (X (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e))
      (firstCol (g e 0)) ≠ 0)
    (h2 : ∀ e, inner ℂ (jMap (firstCol (g e 1)))
      (spinAct (X (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ (z e)) ≠ 0) :
    (lorAction j p g X z).re ≤ 0 := by
  unfold lorAction
  rw [Complex.re_sum]
  exact Finset.sum_nonpos fun e _ =>
    re_triAction_le_zero (hj e) (hZ e) (hZ' e) (hξ e) (hξ' e) (h1 e) (h2 e)

/-- The action pulled back to a chart `chart : ℝⁿ → SL(2,ℂ)^5 × (ℂ²)^10`. -/
noncomputable def lorChartAction {n : ℕ} (j p : Fin 10 → ℝ) (g : BdryData)
    (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)) : (Fin n → ℝ) → ℂ :=
  fun x => lorAction j p g (chart x).1 (chart x).2

/-- The Hessian of the chart action at a point, an `n × n` complex matrix (`44 × 44` for the
vertex: 24 real dimensions for four `SL(2,ℂ)` elements and 20 for ten spinor directions). It is
defined as the Hessian of the pulled-back action; no closed form is claimed. -/
noncomputable def lorHessian {n : ℕ} (j p : Fin 10 → ℝ) (g : BdryData)
    (chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  hessMat (lorChartAction j p g chart) x

/-- **The asymptotic formula of the vertex in a chart, under named hypotheses.** For a chart
of dimension `n` on which the pulled-back action is smooth, an amplitude `aLoc + aFar` with `aLoc`
smooth and compactly supported, nonvanishing spinors and overlaps on the support of `aLoc`
(so `Re S ≤ 0`), a finite critical set `K` in the support with `hdet` (the Hessian of
`-S` invertible at each point), the remainder bound `hfar` and integrability `hint`, and a
weight `w = O(λ^m)`:
`w(λ) ∫ (aLoc + aFar) e^{λ S}` is `w(λ) Σ_{x₀ ∈ K} e^{λ S(x₀)} (2π/λ)^{n/2}
(det(-H(x₀)))^{-1/2} aLoc(x₀)` up to `O(λ^{m-n/2-1})`, with `H = lorHessian`. The explicit
constants of eq. (57) (the weight's leading coefficient, the Haar density, the sign) are not
computed. -/
theorem lorVertex_asymptotics {n : ℕ} {j p : Fin 10 → ℝ} (hj : ∀ e, 0 ≤ j e) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    {chart : (Fin n → ℝ) → (Fin 5 → SL2C) × (Fin 10 → Spinor)}
    (hS : ContDiff ℝ ∞ (lorChartAction j p g chart)) {aLoc aFar : (Fin n → ℝ) → ℂ}
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hZ : ∀ x ∈ tsupport aLoc, ∀ e,
      spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e) ≠ 0)
    (hZ' : ∀ x ∈ tsupport aLoc, ∀ e,
      spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e) ≠ 0)
    (h1 : ∀ x ∈ tsupport aLoc, ∀ e,
      inner ℂ (spinAct ((chart x).1 (edgeSrc e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e))
        (firstCol (g e 0)) ≠ 0)
    (h2 : ∀ x ∈ tsupport aLoc, ∀ e,
      inner ℂ (jMap (firstCol (g e 1)))
        (spinAct ((chart x).1 (edgeTgt e) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((chart x).2 e)) ≠ 0)
    (K : Finset (Fin n → ℝ))
    (hK : ∀ x ∈ tsupport aLoc,
      ((lorChartAction j p g chart x).re = 0 ∧
        fderiv ℝ (lorChartAction j p g chart) x = 0) ↔ x ∈ K)
    (hKs : ∀ x ∈ K, x ∈ tsupport aLoc)
    (hdet : ∀ x ∈ K, (-lorHessian j p g chart x).det ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * lorChartAction j p g chart x))
    (hfar : (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * lorChartAction j p g chart x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (-((n : ℝ) / 2) - 1)))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) :
    (fun lam : ℕ => w lam * (∫ x, (aLoc x + aFar x) *
        cexp ((lam : ℝ) * lorChartAction j p g chart x)) -
      w lam * ∑ x₀ ∈ K, cexp ((lam : ℝ) * lorChartAction j p g chart x₀) *
        ((2 * π / (lam : ℝ)) ^ ((n : ℝ) / 2) : ℝ) *
          invSqrtDet (-lorHessian j p g chart x₀) * aLoc x₀)
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (n : ℝ) / 2 - 1)) :=
  weighted_asymptotics hS ha hc
    (fun x hx => re_lorAction_le_zero hj (hZ x hx) (hZ' x hx) hξ hξ' (h1 x hx) (h2 x hx))
    K hK hKs hdet hint hfar w m hw

/-! ### Trust checks -/

/-- With all spin parameters zero the action vanishes for every configuration (a degenerate
check of the definition: the action is linear in the parameters `j` and `p`). -/
theorem lorAction_zero (g : BdryData) (X : Fin 5 → SL2C) (z : Fin 10 → Spinor) :
    lorAction 0 0 g X z = 0 := by
  simp [lorAction, triAction]

end Lightlike.Asymptotics.Lorentzian
