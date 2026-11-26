import Lightlike.Spacetime.PenroseSingularity.ExpTheta
import Lightlike.Spacetime.PenroseSingularity.SecondVariation

/-!
# The jets of the exponential variation in a chart (G1-012, step D4)

For a curve `γ_c` and fields `W`, `Z` along it in the chart at `p₀`, the variation
`A (s, t) = Θ (γ_c t, s W t + s² Z t)` is smooth, and its `s`-jets `c, c1, c2, Y, Y1, Y2` (as functions of
`(s, t)`) satisfy the hypotheses of `uniform_neg_local` and `hasDerivAt_E_gpair`; at `s = 0`,
`c = γ_c`, `c1 = W` and `c2 = 2 Z - Γ (W, W)`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ}

/-- The variation in the chart. -/
def varA (Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ) (γc W Z : ℝ → Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ :=
  Θ (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2)

/-- The `s`-jets of a function `A : ℝ × ℝ → ℝⁿ`: `A_s`, `A_ss`, `A_t`, `A_ts`, `A_tss`. -/
def jetC1 (A : ℝ × ℝ → Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ := fderiv ℝ A p (1, 0)
/-- `A_ss`. -/
def jetC2 (A : ℝ × ℝ → Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ := fderiv ℝ (fderiv ℝ A) p (1, 0) (1, 0)
/-- `A_t`. -/
def jetY (A : ℝ × ℝ → Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ := fderiv ℝ A p (0, 1)
/-- `A_ts`. -/
def jetY1 (A : ℝ × ℝ → Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ := fderiv ℝ (fderiv ℝ A) p (1, 0) (0, 1)
/-- `A_tss`. -/
def jetY2 (A : ℝ × ℝ → Fin n → ℝ) (p : ℝ × ℝ) : Fin n → ℝ :=
  fderiv ℝ (jetY1 A) p (1, 0)

variable {A : ℝ × ℝ → Fin n → ℝ} {V : Set (ℝ × ℝ)}

/-- The jets of a `C³` function are `C¹` or better. -/
theorem contDiffOn_jetY1 (hV : IsOpen V) (hA : ContDiffOn ℝ 3 A V) : ContDiffOn ℝ 1 (jetY1 A) V := by
  have hA1 : ContDiffOn ℝ 2 (fderiv ℝ A) V := hA.fderiv_of_isOpen hV (by norm_num)
  have hA2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ A)) V := hA1.fderiv_of_isOpen hV (by norm_num)
  exact (hA2.clm_apply contDiffOn_const).clm_apply contDiffOn_const

/-- The `s`-derivative relations of the jets of a `C³` function. -/
theorem hasDerivAt_jets (hV : IsOpen V) (hA : ContDiffOn ℝ 3 A V) {p : ℝ × ℝ} (hp : p ∈ V) :
    HasDerivAt (fun r => A (r, p.2)) (jetC1 A p) p.1 ∧
    HasDerivAt (fun r => jetC1 A (r, p.2)) (jetC2 A p) p.1 ∧
    HasDerivAt (fun r => jetY A (r, p.2)) (jetY1 A p) p.1 ∧
    HasDerivAt (fun r => jetY1 A (r, p.2)) (jetY2 A p) p.1 := by
  have hcurve : HasDerivAt (fun r : ℝ => ((r, p.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hAC : ∀ q ∈ V, ContDiffAt ℝ 3 A q := fun q hq => hA.contDiffAt (hV.mem_nhds hq)
  have hd0 : DifferentiableAt ℝ A p := (hAC p hp).differentiableAt (by simp)
  have hd1 : DifferentiableAt ℝ (fderiv ℝ A) p :=
    ((hAC p hp).fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have hdY : DifferentiableAt ℝ (jetY1 A) p :=
    ((contDiffOn_jetY1 hV hA).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hd0.hasFDerivAt.comp_hasDerivAt p.1 hcurve
  · exact hasDerivAt_fderiv_comp' hd1 hcurve (1, 0)
  · exact hasDerivAt_fderiv_comp' hd1 hcurve (0, 1)
  · exact hdY.hasFDerivAt.comp_hasDerivAt p.1 hcurve

/-- The jets of a `C³` function are continuous. -/
theorem continuousAt_jets (hV : IsOpen V) (hA : ContDiffOn ℝ 3 A V) {p : ℝ × ℝ} (hp : p ∈ V) :
    ContinuousAt A p ∧ ContinuousAt (jetC1 A) p ∧ ContinuousAt (jetC2 A) p ∧ ContinuousAt (jetY A) p ∧
      ContinuousAt (jetY1 A) p ∧ ContinuousAt (jetY2 A) p := by
  have hA1 : ContDiffOn ℝ 2 (fderiv ℝ A) V := hA.fderiv_of_isOpen hV (by norm_num)
  have hA2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ A)) V := hA1.fderiv_of_isOpen hV (by norm_num)
  have hY1 := contDiffOn_jetY1 hV hA
  have hY1d : ContinuousOn (fderiv ℝ (jetY1 A)) V := hY1.continuousOn_fderiv_of_isOpen hV le_rfl
  have c0 : ContinuousAt A p := hA.continuousOn.continuousAt (hV.mem_nhds hp)
  have c1 : ContinuousAt (fderiv ℝ A) p := hA1.continuousOn.continuousAt (hV.mem_nhds hp)
  have c2 : ContinuousAt (fderiv ℝ (fderiv ℝ A)) p := hA2.continuousOn.continuousAt (hV.mem_nhds hp)
  refine ⟨c0, c1.clm_apply continuousAt_const, (c2.clm_apply continuousAt_const).clm_apply continuousAt_const,
    c1.clm_apply continuousAt_const, (c2.clm_apply continuousAt_const).clm_apply continuousAt_const,
    (hY1d.continuousAt (hV.mem_nhds hp)).clm_apply continuousAt_const⟩

/-- Symmetry of the second derivative of a `C²` function. -/
theorem fderiv2_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : ℝ × ℝ → E} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (hφ : ContDiffOn ℝ 2 φ V) {p : ℝ × ℝ} (hp : p ∈ V) (u v : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ φ) p u v = fderiv ℝ (fderiv ℝ φ) p v u :=
  ((hφ.contDiffAt (hV.mem_nhds hp)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])) u v

/-- The mixed derivative: the `t`-derivative of `A_s` is `A_ts`. -/
theorem hasDerivAt_jetC1_t (hV : IsOpen V) (hA : ContDiffOn ℝ 3 A V) {t : ℝ} (hp : ((0 : ℝ), t) ∈ V) :
    HasDerivAt (fun r => jetC1 A (0, r)) (jetY1 A (0, t)) t := by
  have hcurve : HasDerivAt (fun r : ℝ => (((0 : ℝ), r) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
  have hAC : ∀ q ∈ V, ContDiffAt ℝ 3 A q := fun q hq => hA.contDiffAt (hV.mem_nhds hq)
  have hd1 : DifferentiableAt ℝ (fderiv ℝ A) ((0 : ℝ), t) :=
    ((hAC _ hp).fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have h := hasDerivAt_fderiv_comp' hd1 hcurve (1, 0)
  have hA2 : ContDiffOn ℝ 2 A V := hA.of_le (by norm_num)
  have e := fderiv2_symm hV hA2 hp (0, 1) (1, 0)
  simpa [jetC1, jetY1, e] using h

/-- The mixed third derivative: the `t`-derivative of `A_ss` is `A_tss`. -/
theorem hasDerivAt_jetC2_t (hV : IsOpen V) (hA : ContDiffOn ℝ 3 A V) {t : ℝ} (hp : ((0 : ℝ), t) ∈ V) :
    HasDerivAt (fun r => jetC2 A (0, r)) (jetY2 A (0, t)) t := by
  have hcurve : HasDerivAt (fun r : ℝ => (((0 : ℝ), r) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
  have hcurve' : ∀ q : ℝ × ℝ, HasDerivAt (fun r : ℝ => ((r, q.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q.1 := fun q =>
    (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
  have hA1 : ContDiffOn ℝ 2 (fderiv ℝ A) V := hA.fderiv_of_isOpen hV (by norm_num)
  have hφ : ContDiffOn ℝ 2 (jetC1 A) V := hA1.clm_apply contDiffOn_const
  have hφ1 : ContDiffOn ℝ 1 (fderiv ℝ (jetC1 A)) V := hφ.fderiv_of_isOpen hV (by norm_num)
  have hφd : ∀ q ∈ V, DifferentiableAt ℝ (jetC1 A) q := fun q hq =>
    ((hφ.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp))
  have hφ1d : ∀ q ∈ V, DifferentiableAt ℝ (fderiv ℝ (jetC1 A)) q := fun q hq =>
    (hφ1.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)
  -- `A_ss` is the `s`-derivative of `A_s`
  have hC2 : ∀ q ∈ V, jetC2 A q = fderiv ℝ (jetC1 A) q (1, 0) := fun q hq => by
    have h : HasDerivAt (fun r : ℝ => jetC1 A ((r, q.2) : ℝ × ℝ)) (fderiv ℝ (jetC1 A) q (1, 0)) q.1 :=
      HasFDerivAt.comp_hasDerivAt (l := jetC1 A) (f := fun r : ℝ => ((r, q.2) : ℝ × ℝ)) (l' := fderiv ℝ (jetC1 A) q) q.1
        (hφd q hq).hasFDerivAt (hcurve' q)
    exact (hasDerivAt_jets hV hA hq).2.1.unique h
  -- `A_ts` is the `t`-derivative of `A_s`
  have hY1 : ∀ q ∈ V, jetY1 A q = fderiv ℝ (jetC1 A) q (0, 1) := fun q hq => by
    have hA2 : ContDiffOn ℝ 2 A V := hA.of_le (by norm_num)
    have e := fderiv2_symm hV hA2 hq (0, 1) (1, 0)
    have hc : HasDerivAt (fun r : ℝ => (((q.1 : ℝ), r) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    have h1 := (hφd q hq).hasFDerivAt.comp_hasDerivAt q.2 hc
    have hAC : ∀ r ∈ V, ContDiffAt ℝ 3 A r := fun r hr => hA.contDiffAt (hV.mem_nhds hr)
    have hd1 : DifferentiableAt ℝ (fderiv ℝ A) q :=
      ((hAC _ hq).fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
    have h2 := hasDerivAt_fderiv_comp' hd1 hc (1, 0)
    have h3 : HasDerivAt (fun r => jetC1 A (q.1, r)) (jetY1 A q) q.2 := by
      simpa [jetC1, jetY1, e] using h2
    have := h3.unique h1
    simpa using this
  -- the third derivative
  have hY2 : jetY2 A ((0 : ℝ), t) = fderiv ℝ (fderiv ℝ (jetC1 A)) (0, t) (1, 0) (0, 1) := by
    have h1 := hasDerivAt_fderiv_comp' (q := fun r : ℝ => ((r, t) : ℝ × ℝ)) (r := 0) (hφ1d _ hp)
      (hcurve' ((0 : ℝ), t)) (0, 1)
    have h2 := (hasDerivAt_jets hV hA hp).2.2.2
    have h3 : HasDerivAt (fun r => fderiv ℝ (jetC1 A) (r, t) (0, 1)) (jetY2 A ((0 : ℝ), t)) 0 := by
      refine h2.congr_of_eventuallyEq ?_
      have : ∀ᶠ r in 𝓝 (0 : ℝ), ((r, t) : ℝ × ℝ) ∈ V :=
        (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
      filter_upwards [this] with r hr using (hY1 _ hr).symm
    simpa using h3.unique h1
  have hsym := fderiv2_symm hV hφ hp (1, 0) (0, 1)
  have h4 := hasDerivAt_fderiv_comp' (hφ1d _ hp) hcurve (1, 0)
  have h5 : HasDerivAt (fun r => jetC2 A (0, r)) (fderiv ℝ (fderiv ℝ (jetC1 A)) (0, t) (0, 1) (1, 0)) t := by
    refine h4.congr_of_eventuallyEq ?_
    have : ∀ᶠ r in 𝓝 t, (((0 : ℝ), r) : ℝ × ℝ) ∈ V :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
    filter_upwards [this] with r hr using hC2 _ hr
  rw [hY2, hsym]
  exact h5

section Values

variable {Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ} {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}

/-- The `s`-curve in the domain of `Θ`: `q s = (q₀, s w₀ + s² z₀)`. -/
theorem hasDerivAt_sCurve (q₀ w₀ z₀ : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ((q₀, r • w₀ + r ^ 2 • z₀) : (Fin n → ℝ) × (Fin n → ℝ)))
      ((0 : Fin n → ℝ), w₀ + (2 * s) • z₀) s := by
  refine (hasDerivAt_const s q₀).prodMk ?_
  have h1 : HasDerivAt (fun r : ℝ => r • w₀) w₀ s := by simpa using (hasDerivAt_id s).smul_const w₀
  have h2 : HasDerivAt (fun r : ℝ => r ^ 2 • z₀) ((2 * s) • z₀) s := by
    simpa using (hasDerivAt_pow 2 s).smul_const z₀
  exact h1.fun_add h2

/-- The first `s`-derivative of the variation along the fibre: `d/ds Θ (q₀, s w₀ + s² z₀) = D_wΘ (…) (w₀ + 2 s z₀)`. -/
theorem hasDerivAt_theta_s (hD : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D) {q₀ w₀ z₀ : Fin n → ℝ} {s : ℝ}
    (hs : (q₀, s • w₀ + s ^ 2 • z₀) ∈ D) :
    HasDerivAt (fun r : ℝ => Θ (q₀, r • w₀ + r ^ 2 • z₀))
      (fderiv ℝ Θ (q₀, s • w₀ + s ^ 2 • z₀) (0, w₀ + (2 * s) • z₀)) s := by
  have hd : DifferentiableAt ℝ Θ (q₀, s • w₀ + s ^ 2 • z₀) :=
    (hΘ.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hs)
  exact hd.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_sCurve q₀ w₀ z₀ s)

/-- The second `s`-derivative of the variation at `s = 0`: `D²_wΘ (w₀, w₀) + D_wΘ (2 z₀)`. -/
theorem hasDerivAt_theta_ss (hD : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D) {q₀ w₀ z₀ : Fin n → ℝ}
    (h0 : (q₀, (0 : Fin n → ℝ)) ∈ D) :
    HasDerivAt (fun r : ℝ => fderiv ℝ Θ (q₀, r • w₀ + r ^ 2 • z₀) (0, w₀ + (2 * r) • z₀))
      (fderiv ℝ (fderiv ℝ Θ) (q₀, 0) (0, w₀) (0, w₀) + fderiv ℝ Θ (q₀, 0) (0, (2 : ℝ) • z₀)) 0 := by
  have hΘ2 : ContDiffOn ℝ ∞ (fderiv ℝ Θ) D := hΘ.fderiv_of_isOpen hD (by simp)
  have h0' : (q₀, (0 : ℝ) • w₀ + (0 : ℝ) ^ 2 • z₀) ∈ D := by simpa using h0
  have hd2 : DifferentiableAt ℝ (fderiv ℝ Θ) (q₀, (0 : ℝ) • w₀ + (0 : ℝ) ^ 2 • z₀) :=
    (hΘ2.differentiableOn (by simp)).differentiableAt (hD.mem_nhds h0')
  have hq := hasDerivAt_sCurve q₀ w₀ z₀ 0
  have hL := hd2.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  have hqv : HasDerivAt (fun r : ℝ => ((0 : Fin n → ℝ), w₀ + (2 * r) • z₀)) ((0 : Fin n → ℝ), (2 : ℝ) • z₀) 0 := by
    refine (hasDerivAt_const 0 (0 : Fin n → ℝ)).prodMk ?_
    have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).smul_const z₀
    simpa using (hasDerivAt_const (0 : ℝ) w₀).fun_add this
  have h := hL.clm_apply hqv
  refine h.congr_deriv ?_
  simp

variable {γc W Z : ℝ → Fin n → ℝ} {V : Set (ℝ × ℝ)}

/-- `jetC1` of the variation, at any point of its domain. -/
theorem jetC1_varA (hV : IsOpen V) (hD : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D)
    (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V) {p : ℝ × ℝ} (hp : p ∈ V)
    (hpD : (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D) :
    jetC1 (varA Θ γc W Z) p = fderiv ℝ Θ (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) (0, W p.2 + (2 * p.1) • Z p.2) :=
  (hasDerivAt_jets hV hA hp).1.unique (hasDerivAt_theta_s hD hΘ hpD)

/-- **The values of the jets of the variation at `s = 0`.** -/
theorem varA_values (hV : IsOpen V) (hD : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D)
    (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V) {gc : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (h0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (j2 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) =
      Lightlike.Geodesic.accel gc q w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D)
    {t : ℝ} (hp : ((0 : ℝ), t) ∈ V) (hpD : (γc t, (0 : Fin n → ℝ)) ∈ D) :
    varA Θ γc W Z (0, t) = γc t ∧ jetC1 (varA Θ γc W Z) (0, t) = W t ∧
      jetC2 (varA Θ γc W Z) (0, t) = (2 : ℝ) • Z t + Lightlike.Geodesic.accel gc (γc t) (W t) := by
  refine ⟨?_, ?_, ?_⟩
  · show Θ (γc t, (0 : ℝ) • W t + (0 : ℝ) ^ 2 • Z t) = γc t
    simpa using h0 _ hpD
  · rw [jetC1_varA hV hD hΘ hA hp (by simpa using hpD)]
    simpa using j1 _ hpD (W t)
  · have hmem : ∀ᶠ r in 𝓝 (0 : ℝ), ((r, t) : ℝ × ℝ) ∈ V :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
    have h1 := (hasDerivAt_jets hV hA hp).2.1
    have h2 := hasDerivAt_theta_ss hD hΘ (q₀ := γc t) (w₀ := W t) (z₀ := Z t) hpD
    have h3 : HasDerivAt (fun r : ℝ => jetC1 (varA Θ γc W Z) (r, t))
        (fderiv ℝ (fderiv ℝ Θ) (γc t, 0) (0, W t) (0, W t) + fderiv ℝ Θ (γc t, 0) (0, (2 : ℝ) • Z t)) 0 := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [hmem] with r hr
      exact jetC1_varA hV hD hΘ hA hr (hVD _ hr)
    have := h1.unique h3
    rw [this, j2 _ hpD, j1 _ hpD]
    abel

end Values

section Package

variable {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ} {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}

/-- The domain of the variation: `t ∈ I` and the initial vector lies in the domain of `Θ`. -/
def varV (D : Set ((Fin n → ℝ) × (Fin n → ℝ))) (I : Set ℝ) (γc W Z : ℝ → Fin n → ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ I} ∩ (fun p : ℝ × ℝ => (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2)) ⁻¹' D

/-- The variation is `C³` on its domain, which is open. -/
theorem varA_smooth (hD : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D) {I : Set ℝ} (hI : IsOpen I)
    {γc W Z : ℝ → Fin n → ℝ} (hγ : ContDiffOn ℝ 3 γc I) (hW : ContDiffOn ℝ 3 W I) (hZ : ContDiffOn ℝ 3 Z I) :
    IsOpen (varV D I γc W Z) ∧ ContDiffOn ℝ 3 (varA Θ γc W Z) (varV D I γc W Z) := by
  have hsnd : ContinuousOn (fun p : ℝ × ℝ => p.2) {p : ℝ × ℝ | p.2 ∈ I} := continuous_snd.continuousOn
  have hIo : IsOpen {p : ℝ × ℝ | p.2 ∈ I} := hI.preimage continuous_snd
  have hγ' : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => γc p.2) {p : ℝ × ℝ | p.2 ∈ I} :=
    hγ.comp contDiff_snd.contDiffOn (fun p hp => hp)
  have hW' : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => W p.2) {p : ℝ × ℝ | p.2 ∈ I} :=
    hW.comp contDiff_snd.contDiffOn (fun p hp => hp)
  have hZ' : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => Z p.2) {p : ℝ × ℝ | p.2 ∈ I} :=
    hZ.comp contDiff_snd.contDiffOn (fun p hp => hp)
  have hmap : ContDiffOn ℝ 3 (fun p : ℝ × ℝ => (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) :
      ℝ × ℝ → (Fin n → ℝ) × (Fin n → ℝ)) {p : ℝ × ℝ | p.2 ∈ I} := by
    refine hγ'.prodMk ?_
    exact ((contDiff_fst.contDiffOn).smul hW').add (((contDiff_fst.pow 2).contDiffOn).smul hZ')
  refine ⟨hmap.continuousOn.isOpen_inter_preimage hIo hD, ?_⟩
  exact (hΘ.of_le (by norm_num)).comp (hmap.mono inter_subset_left) (fun p hp => hp.2)

variable {γc W Z : ℝ → Fin n → ℝ} {V : Set (ℝ × ℝ)}

/-- On the zero section of the variation, `A (0, r) = γc r` as long as `(0, r)` stays in the domain. -/
theorem varA_zero_section (hD : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D) {r : ℝ} (hr : ((0 : ℝ), r) ∈ V) :
    varA Θ γc W Z (0, r) = γc r := by
  have := hVD _ hr
  simp only [zero_smul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at this
  simpa [varA] using hD _ this

/-- `Y (0, t) = γc' (t)`: the `t`-jet of the variation along the zero section. -/
theorem hasDerivAt_curve_of_jetY (hV : IsOpen V) (hΘ : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (hD : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D) {t : ℝ} (hp : ((0 : ℝ), t) ∈ V) :
    HasDerivAt γc (jetY (varA Θ γc W Z) (0, t)) t := by
  have hcurve : HasDerivAt (fun r : ℝ => (((0 : ℝ), r) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
  have hd : DifferentiableAt ℝ (varA Θ γc W Z) ((0 : ℝ), t) :=
    ((hΘ.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp))
  have h := hd.hasFDerivAt.comp_hasDerivAt t hcurve
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by simp [jetY])
  have : ∀ᶠ r in 𝓝 t, (((0 : ℝ), r) : ℝ × ℝ) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
  filter_upwards [this] with r hr
  exact (varA_zero_section hD hVD hr).symm

/-- `Y1 (0, t) = W' (t)`: the mixed jet along the zero section is the derivative of `W`. -/
theorem hasDerivAt_W_of_jetY1 (hV : IsOpen V) (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (hD0 : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D) (j0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D) {t : ℝ} (hp : ((0 : ℝ), t) ∈ V) :
    HasDerivAt W (jetY1 (varA Θ γc W Z) (0, t)) t := by
  have h := hasDerivAt_jetC1_t hV hA hp
  refine h.congr_of_eventuallyEq ?_
  have : ∀ᶠ r in 𝓝 t, (((0 : ℝ), r) : ℝ × ℝ) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
  filter_upwards [this] with r hr
  have hrD : (γc r, (0 : Fin n → ℝ)) ∈ D := by simpa using hVD _ hr
  rw [jetC1_varA hV hD0 hΘ hA hr (hVD _ hr)]
  simpa using (j1 _ hrD (W r)).symm

/-- **Uniform negativity for the variation.** Along a null curve `γc` with a field `W` such that
`g(γc', γc') = 0` and `g(D_t W, γc') = 0`, if the second-order coefficient of the variation is negative at
`t₀`, then the variation `s ↦ A (s, t)` has timelike `t`-velocity for small `s ≠ 0` and `t` near `t₀`. -/
theorem varA_uniform_neg (hg : Lightlike.IsCoordMetric g U) (hV : IsOpen V) (hD0 : IsOpen D)
    (hΘ : ContDiffOn ℝ ∞ Θ D) (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (j0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D)
    (hcU : ∀ p ∈ V, varA Θ γc W Z p ∈ U) {t₀ : ℝ} (hp : ((0 : ℝ), t₀) ∈ V)
    (h0 : ∀ᶠ t in 𝓝 t₀, gpairAt g (γc t) (deriv γc t) (deriv γc t) = 0)
    (h0' : ∀ᶠ t in 𝓝 t₀, gpairAt g (γc t) (deriv W t + Lightlike.Geodesic.gammaApply g (γc t) (W t) (deriv γc t))
      (deriv γc t) = 0)
    (hneg : coeffK g (fun s t => varA Θ γc W Z (s, t)) (fun s t => jetC1 (varA Θ γc W Z) (s, t))
      (fun s t => jetC2 (varA Θ γc W Z) (s, t)) (fun s t => jetY (varA Θ γc W Z) (s, t))
      (fun s t => jetY1 (varA Θ γc W Z) (s, t)) (fun s t => jetY2 (varA Θ γc W Z) (s, t)) 0 t₀ < 0) :
    ∃ δ > 0, ∃ ε > 0, ∀ t, |t - t₀| < ε → ∀ s, |s| < δ → s ≠ 0 →
      gpairAt g (varA Θ γc W Z (s, t)) (jetY (varA Θ γc W Z) (s, t)) (jetY (varA Θ γc W Z) (s, t)) < 0 := by
  have hVn : V ∈ 𝓝 ((0 : ℝ), t₀) := hV.mem_nhds hp
  have hcj := continuousAt_jets hV hA hp
  have hmem : ∀ᶠ t in 𝓝 t₀, (((0 : ℝ), t) : ℝ × ℝ) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hVn
  have hY0 : ∀ t, (((0 : ℝ), t) : ℝ × ℝ) ∈ V → jetY (varA Θ γc W Z) (0, t) = deriv γc t := fun t ht =>
    (hasDerivAt_curve_of_jetY hV hA j0 hVD ht).deriv.symm
  refine uniform_neg_local hg (c := fun s t => varA Θ γc W Z (s, t)) (hVt := hVn) ?_ ?_ ?_ ?_ hcU ?_ ?_ ?_ ?_ hneg
  · exact fun q hq => (hasDerivAt_jets hV hA hq).1
  · exact fun q hq => (hasDerivAt_jets hV hA hq).2.1
  · exact fun q hq => (hasDerivAt_jets hV hA hq).2.2.1
  · exact fun q hq => (hasDerivAt_jets hV hA hq).2.2.2
  · exact hcj.1.prodMk (hcj.2.1.prodMk (hcj.2.2.2.1.prodMk hcj.2.2.2.2.1))
  · exact hcj.2.2.1.prodMk hcj.2.2.2.2.2
  · filter_upwards [h0, hmem] with t ht hm
    show gpairAt g (varA Θ γc W Z (0, t)) (jetY (varA Θ γc W Z) (0, t)) (jetY (varA Θ γc W Z) (0, t)) = 0
    rw [hY0 t hm, varA_zero_section j0 hVD hm]
    exact ht
  · filter_upwards [h0', hmem] with t ht hm
    have hrD : (γc t, (0 : Fin n → ℝ)) ∈ D := by simpa using hVD _ hm
    have hc1 : jetC1 (varA Θ γc W Z) (0, t) = W t := by
      rw [jetC1_varA hV hD0 hΘ hA hm (hVD _ hm)]
      simpa using j1 _ hrD (W t)
    have hW := (hasDerivAt_W_of_jetY1 hV hA hD0 hΘ j0 j1 hVD hm).deriv
    show gpairAt g (varA Θ γc W Z (0, t)) (jetY1 (varA Θ γc W Z) (0, t) +
      Lightlike.Geodesic.gammaApply g (varA Θ γc W Z (0, t)) (jetC1 (varA Θ γc W Z) (0, t))
        (jetY (varA Θ γc W Z) (0, t))) (jetY (varA Θ γc W Z) (0, t)) = 0
    rw [hY0 t hm, varA_zero_section j0 hVD hm, hc1, ← hW]
    exact ht

/-- **The `t`-derivative of the pairing of `E = A_ss + Γ(A_s, A_s)` with `w = γc'` along the zero section**
for the variation: it equals the second-order coefficient minus `|D_t W|²` plus the tidal term. -/
theorem varA_hasDerivAt_E (hg : Lightlike.IsCoordMetric g U) (hV : IsOpen V) (hD0 : IsOpen D)
    (hΘ : ContDiffOn ℝ ∞ Θ D) (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (j0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D)
    (hcU : ∀ p ∈ V, varA Θ γc W Z p ∈ U) {t : ℝ} (hp : ((0 : ℝ), t) ∈ V)
    (hγ : HasDerivAt (deriv γc) (Lightlike.Geodesic.accel g (γc t) (deriv γc t)) t) :
    HasDerivAt (fun r => gpairAt g (γc r) (jetC2 (varA Θ γc W Z) (0, r) +
        Lightlike.Geodesic.gammaApply g (γc r) (W r) (W r)) (deriv γc r))
      (coeffK g (fun s t => varA Θ γc W Z (s, t)) (fun s t => jetC1 (varA Θ γc W Z) (s, t))
        (fun s t => jetC2 (varA Θ γc W Z) (s, t)) (fun s t => jetY (varA Θ γc W Z) (s, t))
        (fun s t => jetY1 (varA Θ γc W Z) (s, t)) (fun s t => jetY2 (varA Θ γc W Z) (s, t)) 0 t -
      gpairAt g (γc t) (deriv W t + Lightlike.Geodesic.gammaApply g (γc t) (W t) (deriv γc t))
        (deriv W t + Lightlike.Geodesic.gammaApply g (γc t) (W t) (deriv γc t)) +
      gpairAt g (γc t) (Lightlike.Geodesic.riemannApply g (γc t) (W t) (deriv γc t)) (deriv γc t)) t := by
  have hmem : ∀ᶠ r in 𝓝 t, (((0 : ℝ), r) : ℝ × ℝ) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
  have hc1 : ∀ r, (((0 : ℝ), r) : ℝ × ℝ) ∈ V → jetC1 (varA Θ γc W Z) (0, r) = W r := fun r hr => by
    have hrD : (γc r, (0 : Fin n → ℝ)) ∈ D := by simpa using hVD _ hr
    rw [jetC1_varA hV hD0 hΘ hA hr (hVD _ hr)]
    simpa using j1 _ hrD (W r)
  have hY0 : ∀ r, (((0 : ℝ), r) : ℝ × ℝ) ∈ V → jetY (varA Θ γc W Z) (0, r) = deriv γc r := fun r hr =>
    (hasDerivAt_curve_of_jetY hV hA j0 hVD hr).deriv.symm
  have hcγ : HasDerivAt (fun r => varA Θ γc W Z (0, r)) (jetY (varA Θ γc W Z) (0, t)) t :=
    (hasDerivAt_curve_of_jetY hV hA j0 hVD hp).congr_of_eventuallyEq (by
      filter_upwards [hmem] with r hr using varA_zero_section j0 hVD hr)
  have hW := hasDerivAt_W_of_jetY1 hV hA hD0 hΘ j0 j1 hVD hp
  have hc1d : HasDerivAt (fun r => jetC1 (varA Θ γc W Z) (0, r)) (jetY1 (varA Θ γc W Z) (0, t)) t :=
    hW.congr_of_eventuallyEq (by filter_upwards [hmem] with r hr using hc1 r hr)
  have hc2d := hasDerivAt_jetC2_t hV hA hp
  have hw : HasDerivAt (fun r => jetY (varA Θ γc W Z) (0, r))
      (Lightlike.Geodesic.accel g (varA Θ γc W Z (0, t)) (jetY (varA Θ γc W Z) (0, t))) t := by
    rw [hY0 t hp, varA_zero_section j0 hVD hp]
    exact hγ.congr_of_eventuallyEq (by filter_upwards [hmem] with r hr using hY0 r hr)
  have hx : varA Θ γc W Z (0, t) ∈ U := hcU _ hp
  have h := hasDerivAt_E_gpair hg (c := fun s t => varA Θ γc W Z (s, t))
    (c1 := fun s t => jetC1 (varA Θ γc W Z) (s, t)) (c2 := fun s t => jetC2 (varA Θ γc W Z) (s, t))
    (Y := fun s t => jetY (varA Θ γc W Z) (s, t)) (Y1 := fun s t => jetY1 (varA Θ γc W Z) (s, t))
    (Y2 := fun s t => jetY2 (varA Θ γc W Z) (s, t)) hx hcγ hc1d hc2d hw
  have hWd := hW.deriv
  have e0 : varA Θ γc W Z (0, t) = γc t := varA_zero_section j0 hVD hp
  have e1 := hc1 t hp
  have e2 := hY0 t hp
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hmem] with r hr
    simp only [varA_zero_section j0 hVD hr, hc1 r hr, hY0 r hr]
  · simp only [e0, e1, e2, ← hWd]

/-- `g(2 Z, w) = 2 g(Z, w)`. -/
theorem gpairAt_two_smul_left (x z w : Fin n → ℝ) :
    gpairAt g x ((2 : ℝ) • z) w = 2 * gpairAt g x z w := by
  simp only [gpairAt, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **The second-order coefficient of the variation** with the null curve `γc`, the field `W` and the correction
`Z`: it is `d/dt (2 g(Z, γc'))` plus `g(D_t W, D_t W)` minus the tidal term. -/
theorem varA_hasDerivAt_pair {δ : ℝ} (hg : Lightlike.IsCoordMetric g U) (hV : IsOpen V) (hD0 : IsOpen D)
    (hΘ : ContDiffOn ℝ ∞ Θ D) (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (j0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (j2 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) =
      Lightlike.Geodesic.accel g q w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D)
    (hcU : ∀ p ∈ V, varA Θ γc W Z p ∈ U) {t : ℝ} (hp : ((0 : ℝ), t) ∈ V)
    (hγ : HasDerivAt (deriv γc) (Lightlike.Geodesic.accel g (γc t) (deriv γc t)) t)
    (hZ : HasDerivAt (fun r => 2 * gpairAt g (γc r) (Z r) (deriv γc r)) (δ : ℝ) t) :
    coeffK g (fun s t => varA Θ γc W Z (s, t)) (fun s t => jetC1 (varA Θ γc W Z) (s, t))
        (fun s t => jetC2 (varA Θ γc W Z) (s, t)) (fun s t => jetY (varA Θ γc W Z) (s, t))
        (fun s t => jetY1 (varA Θ γc W Z) (s, t)) (fun s t => jetY2 (varA Θ γc W Z) (s, t)) 0 t =
      δ + gpairAt g (γc t) (deriv W t + Lightlike.Geodesic.gammaApply g (γc t) (W t) (deriv γc t))
        (deriv W t + Lightlike.Geodesic.gammaApply g (γc t) (W t) (deriv γc t)) -
      gpairAt g (γc t) (Lightlike.Geodesic.riemannApply g (γc t) (W t) (deriv γc t)) (deriv γc t) := by
  have h := varA_hasDerivAt_E hg hV hD0 hΘ hA j0 j1 hVD hcU hp hγ
  have hmem : ∀ᶠ r in 𝓝 t, (((0 : ℝ), r) : ℝ × ℝ) ∈ V :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
  have hfun : (fun r => gpairAt g (γc r) (jetC2 (varA Θ γc W Z) (0, r) +
        Lightlike.Geodesic.gammaApply g (γc r) (W r) (W r)) (deriv γc r)) =ᶠ[𝓝 t]
      fun r => 2 * gpairAt g (γc r) (Z r) (deriv γc r) := by
    filter_upwards [hmem] with r hr
    have hrD : (γc r, (0 : Fin n → ℝ)) ∈ D := by simpa using hVD _ hr
    have hc2 : jetC2 (varA Θ γc W Z) (0, r) = (2 : ℝ) • Z r + Lightlike.Geodesic.accel g (γc r) (W r) := by
      exact (varA_values hV hD0 hΘ hA j0 j1 (gc := g) j2 hVD hr hrD).2.2
    rw [hc2, Lightlike.Geodesic.accel_eq_neg_gammaApply]
    have : (2 : ℝ) • Z r + -Lightlike.Geodesic.gammaApply g (γc r) (W r) (W r) +
        Lightlike.Geodesic.gammaApply g (γc r) (W r) (W r) = (2 : ℝ) • Z r := by abel
    rw [this, gpairAt_two_smul_left]
  have h2 := h.unique ((hZ.congr_of_eventuallyEq hfun))
  linarith

/-- With `Z = φ N + Z⊥`, `g(N, γc') = -1` and `g(Z⊥, γc') = 0` near `t`, the pairing derivative is `-2 φ'`. -/
theorem hasDerivAt_two_pair_of_phi {φ : ℝ → ℝ} {N Zp : ℝ → Fin n → ℝ} {φ' : ℝ} {t : ℝ}
    (hg : Lightlike.IsCoordMetric g U) (hN : ∀ᶠ r in 𝓝 t, gpairAt g (γc r) (N r) (deriv γc r) = -1)
    (hZp : ∀ᶠ r in 𝓝 t, gpairAt g (γc r) (Zp r) (deriv γc r) = 0)
    (hφ : HasDerivAt (fun r => φ r) φ' t) (hZ : ∀ᶠ r in 𝓝 t, Z r = φ r • N r + Zp r) :
    HasDerivAt (fun r => 2 * gpairAt g (γc r) (Z r) (deriv γc r)) (-2 * φ') t := by
  have h := (hφ.neg).const_mul 2
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards [hN, hZp, hZ] with r hNr hZpr hZr
  have hs : gpairAt g (γc r) (Z r) (deriv γc r) = -φ r := by
    rw [hZr]
    simp only [gpairAt, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    have := hNr
    have h2 := hZpr
    simp only [gpairAt] at this h2
    calc ∑ a, ∑ b, g (γc r) a b * (φ r * N r a + Zp r a) * deriv γc r b
        = φ r * (∑ a, ∑ b, g (γc r) a b * N r a * deriv γc r b) +
            ∑ a, ∑ b, g (γc r) a b * Zp r a * deriv γc r b := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
      _ = -φ r := by rw [this, h2]; ring
  simp [hs]

end Package

end Lightlike.Penrose
