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

end Package

end Lightlike.Penrose
