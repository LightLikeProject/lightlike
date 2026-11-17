import Lightlike.Asymptotics.Lorentzian.ClosureFromCritical
import Lightlike.Asymptotics.Lorentzian.VertexHaarChart
import Lightlike.Asymptotics.Lorentzian.VertexFixChart
import Lightlike.Asymptotics.Lorentzian.VertexLocal
import Lightlike.Asymptotics.Lorentzian.Suppression

/-!
# Non-closing suppression of the vertex in the fixed charts

BDFHP Sec. 6.4, eq. (56): for boundary data with no critical point the vertex amplitude is `o(λ^{-K})` for
every `K`. Here the sub-case in which the normals of a tetrahedron do not close, in the chart of the vertex
formula (`fixVertexChart`), with the hypotheses of `NonClosing.lean` proved instead of assumed.

* `fixPre`, `hasDerivAt_fixMat_line`: the differential of the chart `g_0(b, w, λ)` of `SL(2, ℂ)` is onto the
  tangent space: along `y + t δ` with `δ = fixPre y u` the entries of `g_0` have the derivative of the entries
  of `g_0(y) · genMat u`.
* `fixVertexChart_curve`: at a point of the chart domain, for a node `a < 4` and a direction `u`, a coordinate
  vector `v` moving only that node such that the chart at `x + t v` is the configuration of `x` with `X_a`
  replaced by `X_a Y(t)`, `Y' = genMat u`.
* `hasDerivAt_chartAction_aligned`: with `hasDerivAt_lorAction_aligned`, the derivative of the pulled-back action
  along `v` at an aligned point is the sum of the logarithmic derivatives of the ends at the node.
* `weighted_suppressed_local`: the weighted suppression for an action smooth only on an open set.
* `lorVertex_suppressed_fixChart`: the weighted vertex integral is `O(λ^{m-N})` for every `N` when the
  normals do not close at a node `a < 4`; `Re S ≤ 0`, the absence of critical points (`Re S = 0` gives an
  aligned point, `aligned_of_re_lorAction_eq_zero`) and the smoothness of the action are proved.

Not claimed: the far remainder (`hint`, `hfar`, assumed as in `NonClosing.lean`), the node `a = 4` of the gauge
(its closure follows from the other four by the Lorentz invariance of the action, not formalised), and the case
of data with closure.
-/

open Complex
open Lightlike.Lorentz (SL2C fixMat fixChart)
open Lightlike.Asymptotics.EPRL
open Filter MeasureTheory Lightlike.Oscillatory
open _root_.Asymptotics
open scoped ComplexConjugate Matrix ContDiff

namespace Lightlike.Asymptotics.Lorentzian

/-- The direction `δ` in the coordinates `(b, w, λ)` of the fixed chart `g_0` whose image under the differential
is the left translate of `genMat u`: `δb = b (w (u₀ - i u₁) - u₂)/2 + (u₀ - i u₁)/(2λ)`,
`δw = (u₀ (1 - w²) + i u₁ (1 + w²))/2 + u₂ w`, `δλ = λ (w (u₀ - i u₁) - u₂)/2`. -/
noncomputable def fixPre (y u : Fin 3 → ℂ) : Fin 3 → ℂ := fun m =>
  match m with
  | 0 => y 0 * (y 1 * (u 0 - Complex.I * u 1) - u 2) / 2 + (u 0 - Complex.I * u 1) / (2 * y 2)
  | 1 => (u 0 * (1 - y 1 ^ 2) + Complex.I * u 1 * (1 + y 1 ^ 2)) / 2 + u 2 * y 1
  | 2 => y 2 * (y 1 * (u 0 - Complex.I * u 1) - u 2) / 2

/-- **The differential of the fixed chart `g_0` is onto the tangent space**: along the line `y + t δ`,
`δ = fixPre y u`, the entries of `fixMat 0` have the derivative of the entries of `fixMat 0 y * genMat u`. -/
theorem hasDerivAt_fixMat_line (y u : Fin 3 → ℂ) (hy : y 2 ≠ 0) (i k : Fin 2) :
    HasDerivAt (fun t : ℝ => (fixMat 0 (fun m => y m + (t : ℂ) * fixPre y u m) : Matrix (Fin 2) (Fin 2) ℂ) i k)
      ((fixMat 0 y * genMat u) i k) 0 := by
  have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have hl : ∀ m, HasDerivAt (fun t : ℝ => y m + (t : ℂ) * fixPre y u m) (fixPre y u m) 0 := fun m => by
    simpa using (ht.mul_const (fixPre y u m)).const_add (y m)
  have hev : ∀ᶠ t : ℝ in nhds 0, y 2 + (t : ℂ) * fixPre y u 2 ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ => y 2 + (t : ℂ) * fixPre y u 2) 0 := (hl 2).continuousAt
    exact hc.eventually_ne (by simpa using hy)
  have hf : (fun t : ℝ => (fixMat 0 (fun m => y m + (t : ℂ) * fixPre y u m) : Matrix (Fin 2) (Fin 2) ℂ) i k)
      =ᶠ[nhds 0] fun t : ℝ => (!![(y 0 + (t : ℂ) * fixPre y u 0) * (y 1 + (t : ℂ) * fixPre y u 1) +
        (y 2 + (t : ℂ) * fixPre y u 2)⁻¹, y 0 + (t : ℂ) * fixPre y u 0;
        (y 2 + (t : ℂ) * fixPre y u 2) * (y 1 + (t : ℂ) * fixPre y u 1), y 2 + (t : ℂ) * fixPre y u 2] :
          Matrix (Fin 2) (Fin 2) ℂ) i k := by
    filter_upwards [hev] with t ht
    simp [fixMat, ht]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hf
  have hinv := (hl 2).inv (by simpa using hy)
  have h00 : HasDerivAt (fun t : ℝ => (y 0 + (t : ℂ) * fixPre y u 0) * (y 1 + (t : ℂ) * fixPre y u 1) +
      (y 2 + (t : ℂ) * fixPre y u 2)⁻¹) (fixPre y u 0 * y 1 + y 0 * fixPre y u 1 + -fixPre y u 2 / y 2 ^ 2) 0 := by
    exact (((hl 0).mul (hl 1)).add hinv).congr_deriv (by simp)
  have h01 : HasDerivAt (fun t : ℝ => y 0 + (t : ℂ) * fixPre y u 0) (fixPre y u 0) 0 := hl 0
  have h10 : HasDerivAt (fun t : ℝ => (y 2 + (t : ℂ) * fixPre y u 2) * (y 1 + (t : ℂ) * fixPre y u 1))
      (fixPre y u 2 * y 1 + y 2 * fixPre y u 1) 0 := by
    exact ((hl 2).mul (hl 1)).congr_deriv (by simp)
  have h11 : HasDerivAt (fun t : ℝ => y 2 + (t : ℂ) * fixPre y u 2) (fixPre y u 2) 0 := hl 2
  fin_cases i <;> fin_cases k
  · refine h00.congr_deriv ?_
    simp [fixMat, hy, fixPre, genMat, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · refine h01.congr_deriv ?_
    simp [fixMat, hy, fixPre, genMat, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · refine h10.congr_deriv ?_
    simp [fixMat, hy, fixPre, genMat, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  · refine h11.congr_deriv ?_
    simp [fixMat, hy, fixPre, genMat, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

/-- **A curve of the fixed chart with prescribed velocity at one node**: at a point `x` of the chart domain,
for the node `a < 4` and every `u`, a coordinate vector `v` (moving only the node `a`) and a curve `Y` in
`SL(2, ℂ)` with `Y 0 = 1`, entrywise derivative `genMat u` at `0`, such that the chart at `x + t v` is the
configuration of `x` with `X_a` replaced by `X_a Y(t)` (the spinors do not change). -/
theorem fixVertexChart_curve (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ)))
    (hl : IsLinearMap ℝ e) (a : Fin 4) (x : Fin 44 → ℝ) (hx : (e x).1 a 2 ≠ 0) (u : Fin 3 → ℂ) :
    ∃ (v : Fin 44 → ℝ) (Y : ℝ → SL2C), Y 0 = 1 ∧
      (∀ i k, HasDerivAt (fun s => (Y s : Matrix (Fin 2) (Fin 2) ℂ) i k)
        (((Y 0 : Matrix (Fin 2) (Fin 2) ℂ) * genMat u) i k) 0) ∧
      ∀ t : ℝ, fixVertexChart e (x + t • v) =
        (Function.update (fixVertexChart e x).1 a.castSucc
          ((fixVertexChart e x).1 a.castSucc * Y t), (fixVertexChart e x).2) := by
  set y : Fin 3 → ℂ := (e x).1 a with hy
  set δ : Fin 3 → ℂ := fixPre y u with hδ
  refine ⟨e.symm (fun b => if b = a then δ else 0, fun _ => 0),
    fun t => (fixChart 0 y)⁻¹ * fixChart 0 (fun m => y m + (t : ℂ) * δ m), ?_, ?_, ?_⟩
  · have : fixChart 0 (fun m => y m + ((0 : ℝ) : ℂ) * δ m) = fixChart 0 y := by simp
    simp only [this, inv_mul_cancel]
  · intro i k
    have h0 : fixChart 0 (fun m => y m + ((0 : ℝ) : ℂ) * δ m) = fixChart 0 y := by simp
    have hf : ∀ t : ℝ, (((fixChart 0 y)⁻¹ * fixChart 0 (fun m => y m + (t : ℂ) * δ m) : SL2C) :
        Matrix (Fin 2) (Fin 2) ℂ) i k = ∑ l, ((fixChart 0 y)⁻¹ : SL2C) i l *
          (fixMat 0 (fun m => y m + (t : ℂ) * δ m)) l k := fun t => by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      rfl
    simp only [hf]
    have hd := HasDerivAt.sum (u := Finset.univ) (fun l _ =>
      (hasDerivAt_fixMat_line y u hx l k).const_mul (((fixChart 0 y)⁻¹ : SL2C) i l))
    refine hd.congr_deriv ?_
    simp only [h0, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]
    have hm : (((fixChart 0 y)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * (fixChart 0 y : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hG : (fixChart 0 y : Matrix (Fin 2) (Fin 2) ℂ) = fixMat 0 y := rfl
    rw [← Matrix.mul_apply, ← Matrix.mul_assoc, ← hG, hm, one_mul]
  · intro t
    have hev : e (e.symm (fun b => if b = a then δ else 0, fun _ => 0)) =
        (fun b => if b = a then δ else 0, fun _ => (0 : ℂ)) := e.apply_symm_apply _
    have hadd : e (x + t • e.symm (fun b => if b = a then δ else 0, fun _ => 0)) =
        e x + t • (fun b => if b = a then δ else 0, fun _ => (0 : ℂ)) := by
      rw [hl.map_add, hl.map_smul, hev]
    refine Prod.ext ?_ ?_
    · funext b
      refine Fin.lastCases ?_ (fun c => ?_) b
      · have hne : (Fin.last 4) ≠ a.castSucc := (Fin.castSucc_lt_last a).ne'
        simp only [fixVertexChart, Lightlike.Lorentz.gauge_last, Function.update_of_ne hne]
      · simp only [fixVertexChart, Lightlike.Lorentz.gauge_castSucc, hadd]
        by_cases hc : c = a
        · subst hc
          simp only [Function.update_self, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
            ↓reduceIte]
          rw [← hy, mul_inv_cancel_left]
          rfl
        · have hne : c.castSucc ≠ a.castSucc := fun h => hc (Fin.castSucc_injective _ h)
          simp only [Function.update_of_ne hne, Lightlike.Lorentz.gauge_castSucc, Prod.fst_add,
            Prod.smul_fst, Pi.add_apply, Pi.smul_apply, hc, ↓reduceIte, smul_zero, add_zero]
    · funext k
      simp [fixVertexChart, hadd]

/-- **The derivative of the pulled-back action along a chart direction at an aligned point**: at a point `x` of
the chart domain whose configuration is aligned (`X_a† z_e = λ_e ξ_ab` at every source end, `X_b† z_e = μ_e J ξ_ba`
at every target end, overlap products off the cut), for the node `a < 4` and every `u` there is a coordinate
vector `v` with `d/dt S(x + t v) = Σ_e (if the source of e is a then logDeriv … u ξ) + (if the target is a …)`. -/
theorem hasDerivAt_chartAction_aligned {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ}
    (hj : ∀ e, j e = (n e : ℝ) / 2) {g : BdryData}
    (hξ : ∀ e, ‖firstCol (g e 0)‖ = 1) (hξ' : ∀ e, ‖firstCol (g e 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (hl : IsLinearMap ℝ e)
    (a : Fin 4) (x : Fin 44 → ℝ) (hx : (e x).1 a 2 ≠ 0) (lam mu : Fin 10 → ℂ)
    (hlam : ∀ k, lam k ≠ 0) (hmu : ∀ k, mu k ≠ 0)
    (hsrc : ∀ k, spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      ((fixVertexChart e x).2 k) = lam k • firstCol (g k 0))
    (htgt : ∀ k, spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      ((fixVertexChart e x).2 k) = mu k • jMap (firstCol (g k 1)))
    (hslit : ∀ k, inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
      inner ℂ (jMap (firstCol (g k 1))) (spinAct ((fixVertexChart e x).1 (edgeTgt k) :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((fixVertexChart e x).2 k)) ∈ Complex.slitPlane)
    (u : Fin 3 → ℂ) :
    ∃ v : Fin 44 → ℝ, HasDerivAt (fun t : ℝ => lorChartAction j p g (fixVertexChart e) (x + t • v))
      (∑ k, ((if edgeSrc k = a.castSucc then logDeriv (n k) (p k) u (firstCol (g k 0)) else 0) +
        (if edgeTgt k = a.castSucc then logDeriv (n k) (p k) u (firstCol (g k 1)) else 0))) 0 := by
  obtain ⟨v, Y, hY0, hY, hcurve⟩ := fixVertexChart_curve e hl a x hx u
  refine ⟨v, ?_⟩
  have h := hasDerivAt_lorAction_aligned (p := p) hj hξ hξ' lam mu hlam hmu hsrc htgt hslit a.castSucc u Y hY0
    (fun i k => by simpa using hY i k)
  have hfun : (fun t : ℝ => lorChartAction j p g (fixVertexChart e) (x + t • v)) =
      fun t : ℝ => lorAction j p g (Function.update (fixVertexChart e x).1 a.castSucc
        ((fixVertexChart e x).1 a.castSucc * Y t)) (fixVertexChart e x).2 := by
    funext t
    simp only [lorChartAction, hcurve]
  rw [hfun]
  exact h

/-- The sum of the logarithmic derivatives over the ends at a node, for the direction `i · e_i` of the
rotations, is `i/2` times the sum of the spin vectors (closure at the node). -/
theorem sum_logDeriv_imag {n : Fin 10 → ℕ} {p : Fin 10 → ℝ} (g : BdryData) (a : Fin 5) (i : Fin 3) :
    ∑ k, ((if edgeSrc k = a then logDeriv (n k) (p k) (fun m => if m = i then Complex.I else 0)
        (firstCol (g k 0)) else 0) +
      (if edgeTgt k = a then logDeriv (n k) (p k) (fun m => if m = i then Complex.I else 0)
        (firstCol (g k 1)) else 0)) =
      Complex.I * (((1 / 2 * ∑ k, ((if edgeSrc k = a then (n k : ℝ) * spinVec (firstCol (g k 0)) i else 0) +
        (if edgeTgt k = a then (n k : ℝ) * spinVec (firstCol (g k 1)) i else 0)) : ℝ)) : ℂ) := by
  set c : Fin 3 → ℂ := fun m => if m = i then Complex.I else 0 with hc
  have key : ∀ (k : Fin 10) (ξ : Spinor), logDeriv (n k) (p k) c ξ =
      Complex.I * ((((n k : ℝ) / 2 * spinVec ξ i : ℝ)) : ℂ) := by
    intro k ξ
    have him : ∀ x : Fin 3, (c x).im = if x = i then 1 else 0 := fun x => by
      simp only [hc]; split_ifs <;> simp
    have hre : ∀ x : Fin 3, (c x).re = 0 := fun x => by
      simp only [hc]; split_ifs <;> simp
    rw [logDeriv_eq]
    simp only [him, hre, zero_mul, Finset.sum_const_zero]
    simp [Finset.sum_ite_eq']
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [key]
  split_ifs <;> push_cast <;> ring

/-- **The weighted suppression for an action smooth only on an open set `U`** containing the support of
`aLoc` (`weighted_suppressed` with `ContDiffOn ℝ ∞ S U`): a smooth cutoff of the action
(`exists_smooth_extension`) reduces the local part to the global statement, and the far part stays under its
hypotheses `hint` and `hfar` for `S` itself. -/
theorem weighted_suppressed_local {S aLoc aFar : (Fin 44 → ℝ) → ℂ} {U : Set (Fin 44 → ℝ)}
    (hU : IsOpen U) (hS : ContDiffOn ℝ ∞ S U) (hsU : tsupport aLoc ⊆ U)
    (ha : ContDiff ℝ ∞ aLoc) (hc : HasCompactSupport aLoc)
    (hRe : ∀ x ∈ tsupport aLoc, (S x).re ≤ 0)
    (hnc : ∀ x ∈ tsupport aLoc, (S x).re < 0 ∨ fderiv ℝ S x ≠ 0)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * S x))
    (hfar : ∀ N : ℕ, (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) (N : ℕ) :
    (fun lam : ℕ => w lam * ∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) * S x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (N : ℝ))) := by
  obtain ⟨S', hS', W, hW, hKW, hSW⟩ := exists_smooth_extension hU hS hc.isCompact hsU
  have hpt : ∀ x, aLoc x ≠ 0 → S' x = S x := fun x hx =>
    hSW x (hKW (subset_tsupport _ (Function.mem_support.mpr hx)))
  have hder : ∀ x ∈ tsupport aLoc, fderiv ℝ S' x = fderiv ℝ S x := fun x hx =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hW.mem_nhds (hKW hx)) fun y hy => hSW y hy)
  have hRe' : ∀ x ∈ tsupport aLoc, (S' x).re ≤ 0 := fun x hx => by
    rw [hSW x (hKW hx)]; exact hRe x hx
  have hnc' : ∀ x ∈ tsupport aLoc, (S' x).re < 0 ∨ fderiv ℝ S' x ≠ 0 := fun x hx => by
    rw [hSW x (hKW hx), hder x hx]; exact hnc x hx
  have heq : ∀ τ : ℝ, ∫ x, aLoc x * cexp (τ * S x) = ∫ x, aLoc x * cexp (τ * S' x) := fun τ => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases h : aLoc x = 0
    · simp [h]
    · simp only [hpt x h]
  obtain ⟨C, hC⟩ := expPhase_suppressed hS' ha hc hRe' hnc' N
  have hloc : (fun lam : ℕ => ∫ x, aLoc x * cexp ((lam : ℝ) * S x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with lam hlam
    have h1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
    have := hC lam h1
    have hpos : (0 : ℝ) < lam := by linarith
    rw [heq, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _), Real.rpow_neg hpos.le,
      Real.rpow_natCast]
    simpa [div_eq_mul_inv, mul_comm] using this
  have hsplit : ∀ τ : ℝ, ∫ x, (aLoc x + aFar x) * cexp (τ * S x) =
      (∫ x, aLoc x * cexp (τ * S x)) + ∫ x, aFar x * cexp (τ * S x) := fun τ => by
    have h1 : Integrable fun x => aLoc x * cexp (τ * S x) := by
      have h2 : Integrable fun x => aLoc x * cexp (τ * S' x) := by
        refine Continuous.integrable_of_hasCompactSupport ?_ (hc.mul_right)
        exact ha.continuous.mul (Complex.continuous_exp.comp
          (continuous_const.mul hS'.continuous))
      refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
      by_cases h : aLoc x = 0
      · simp [h]
      · simp only [hpt x h]
    simp only [add_mul]
    exact integral_add h1 (hint τ)
  have hsum := (hloc.add (hfar N)).congr_left fun lam => (hsplit lam).symm
  have hprod := hw.mul hsum
  refine hprod.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have : (0 : ℝ) < lam := by exact_mod_cast hlam
  rw [← Real.rpow_add this]
  ring_nf

/-- **Non-closing suppression in the fixed charts** (BDFHP Sec. 6.4, eq. (56), the sub-case in which the normals
of a tetrahedron do not close): for positive spins `j = n/2`, unit boundary spinors whose spin vectors do not
close at some node `a < 4`, a smooth compactly supported amplitude `aLoc` supported in an open set `U` of the
chart domain on which the overlap products are off the cut, and the far remainder under `hint`, `hfar`, the
weighted vertex integral is `O(λ^{m - N})` for every `N`. The condition `Re S ≤ 0`, the absence of critical
points and the smoothness of the action are proved, not assumed. -/
theorem lorVertex_suppressed_fixChart {j p : Fin 10 → ℝ} {n : Fin 10 → ℕ}
    (hj : ∀ k, j k = (n k : ℝ) / 2) (hjpos : ∀ k, 0 < j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (hnc : ∃ (a : Fin 4) (i : Fin 3), ∑ k, ((if edgeSrc k = a.castSucc then (n k : ℝ) * spinVec (firstCol (g k 0)) i
        else 0) + (if edgeTgt k = a.castSucc then (n k : ℝ) * spinVec (firstCol (g k 1)) i else 0)) ≠ 0)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (hl : IsLinearMap ℝ e)
    {U : Set (Fin 44 → ℝ)} (hU : IsOpen U) (hUc : U ⊆ fixDomain e)
    (hP : ∀ x ∈ U, ∀ k,
      inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((fixVertexChart e x).2 k)) ∈ Complex.slitPlane)
    {aLoc aFar : (Fin 44 → ℝ) → ℂ} (hsU : tsupport aLoc ⊆ U) (ha : ContDiff ℝ ∞ aLoc)
    (hc : HasCompactSupport aLoc)
    (hint : ∀ τ : ℝ, Integrable fun x => aFar x * cexp (τ * lorChartAction j p g (fixVertexChart e) x))
    (hfar : ∀ N : ℕ, (fun lam : ℕ => ∫ x, aFar x * cexp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))))
    (w : ℕ → ℂ) (m : ℝ) (hw : w =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ m)) (N : ℕ) :
    (fun lam : ℕ => w lam * ∫ x, (aLoc x + aFar x) * cexp ((lam : ℝ) *
        lorChartAction j p g (fixVertexChart e) x))
      =O[atTop] fun lam : ℕ => ((lam : ℝ) ^ (m - (N : ℝ))) := by
  have hS := lorChartAction_fixVertexChart_contDiffOn e hl j p g hU hUc hP
  have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
  -- overlaps and spinors at a point of `U`
  have hov : ∀ x ∈ U, (∀ k, inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((fixVertexChart e x).2 k)) (firstCol (g k 0)) ≠ 0) ∧
      (∀ k, inner ℂ (jMap (firstCol (g k 1))) (spinAct ((fixVertexChart e x).1 (edgeTgt k) :
        Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((fixVertexChart e x).2 k)) ≠ 0) := by
    intro x hx
    have hne : ∀ k, inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1))) (spinAct ((fixVertexChart e x).1 (edgeTgt k) :
          Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((fixVertexChart e x).2 k)) ≠ 0 := fun k h => h0 (h ▸ hP x hx k)
    exact ⟨fun k => left_ne_zero_of_mul (hne k), fun k => right_ne_zero_of_mul (hne k)⟩
  have hZ : ∀ x ∈ U, (∀ k, spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      ((fixVertexChart e x).2 k) ≠ 0) ∧ (∀ k, spinAct ((fixVertexChart e x).1 (edgeTgt k) :
      Matrix (Fin 2) (Fin 2) ℂ)ᴴ ((fixVertexChart e x).2 k) ≠ 0) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hov x hx
    exact ⟨fun k h => h1 k (by rw [h]; simp), fun k h => h2 k (by rw [h]; simp)⟩
  have hRe : ∀ x ∈ tsupport aLoc, (lorChartAction j p g (fixVertexChart e) x).re ≤ 0 := fun x hx =>
    re_lorAction_le_zero (fun k => (hjpos k).le) (hZ x (hsU hx)).1 (hZ x (hsU hx)).2 hξ hξ'
      (hov x (hsU hx)).1 (hov x (hsU hx)).2
  have hncx : ∀ x ∈ tsupport aLoc, (lorChartAction j p g (fixVertexChart e) x).re < 0 ∨
      fderiv ℝ (lorChartAction j p g (fixVertexChart e)) x ≠ 0 := by
    intro x hx
    by_cases hre : (lorChartAction j p g (fixVertexChart e) x).re = 0
    · right
      intro hd
      have hxU := hsU hx
      have hal := aligned_of_re_lorAction_eq_zero hjpos (hZ x hxU).1 (hZ x hxU).2 hξ hξ'
        (hov x hxU).1 (hov x hxU).2 hre
      choose lam mu hlam hmu hsrc htgt using hal
      obtain ⟨a, i, hne⟩ := hnc
      obtain ⟨v, hv⟩ := hasDerivAt_chartAction_aligned (p := p) hj hξ hξ' e hl a x (hUc hxU a) lam mu hlam hmu
        hsrc htgt (hP x hxU) (fun m => if m = i then Complex.I else 0)
      have hdiff : DifferentiableAt ℝ (lorChartAction j p g (fixVertexChart e)) x :=
        ((hS.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp))
      have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      have hdiff' : DifferentiableAt ℝ (lorChartAction j p g (fixVertexChart e)) (x + (0 : ℝ) • v) := by
        simpa using hdiff
      have hh := hdiff'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
      have h2 := hh.unique hv
      simp only [zero_smul, add_zero, hd, zero_apply] at h2
      rw [sum_logDeriv_imag] at h2
      have h3 := (mul_eq_zero.mp h2.symm).resolve_left Complex.I_ne_zero
      have h4 : (1 / 2 * ∑ k, ((if edgeSrc k = a.castSucc then (n k : ℝ) * spinVec (firstCol (g k 0)) i else 0) +
          (if edgeTgt k = a.castSucc then (n k : ℝ) * spinVec (firstCol (g k 1)) i else 0)) : ℝ) = 0 := by
        exact_mod_cast h3
      exact hne (by linarith)
    · left
      exact lt_of_le_of_ne (hRe x hx) hre
  exact weighted_suppressed_local hU hS hsU ha hc hRe hncx hint hfar w m hw N

end Lightlike.Asymptotics.Lorentzian
