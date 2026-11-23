import Mathlib
import Lightlike.Spacetime.GreenOperators.RiemannKernel

/-!
# The Riemann solution `u = K ⋆ h` satisfies the integral equation `u = Q (h + c u)`

Supporting file for G1-021 (SC6; Bär–Ginoux–Pfäffle 2007, source key `bgp-2007`).
For `h` continuous with compact support and `K = riemannKernel c` let `u = K ⋆ h` (`riemannSol`).
Then `u` is `Cⁿ` if `h` is, it vanishes when `a ≤ -R` or `b ≤ -R` (`R` a box size for `h`), and,
by associativity of convolution and `K = 1_Q + c (1_Q ⋆ K)` (`riemannKernel_eq`),
`u = quadPrim (h + c u)` (`riemannSol_eq_quadPrim`): the integral form of `u_{ab} = h + c u`.

This is a supporting result; no catalogue entry.
-/

open Set MeasureTheory
open scoped Convolution

namespace Lightlike.GreenOperators

lemma norm_quadKernel (t : ℝ × ℝ) : ‖quadKernel t‖ = quadKernel t := by
  by_cases h : (0 : ℝ × ℝ) ≤ t <;> simp [quadKernel, h]

/-- A compactly supported function vanishes when a coordinate is `≤ -R`. -/
lemma exists_vanishing {g : ℝ × ℝ → ℝ} (hcg : HasCompactSupport g) :
    ∃ R : ℝ, ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → g q = 0 := by
  obtain ⟨R, hR⟩ := exists_box hcg
  refine ⟨R, fun q hq => ?_⟩
  by_contra hne
  have hb := hR q hne
  rcases hq with hq | hq
  · have h1 := hb.1
    rw [abs_lt] at h1
    linarith [h1.1]
  · have h1 := hb.2
    rw [abs_lt] at h1
    linarith [h1.1]

/-- `t ↦ 1_Q(t) w(p - t)` is integrable for locally integrable `w` vanishing when a coordinate
is `≤ -R`. -/
lemma integrable_quadKernel_mul {w : ℝ × ℝ → ℝ} (hw : LocallyIntegrable w (volume : Measure (ℝ × ℝ)))
    {R : ℝ} (hz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → w q = 0) (p : ℝ × ℝ) :
    Integrable (fun t => quadKernel t * w (p - t)) (volume : Measure (ℝ × ℝ)) := by
  have h1 : Integrable ((Icc ((-R, -R) : ℝ × ℝ) p).indicator w) (volume : Measure (ℝ × ℝ)) :=
    (hw.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc
  refine (h1.comp_sub_left p).congr (ae_of_all _ fun t => ?_)
  by_cases h0 : (0 : ℝ × ℝ) ≤ t
  · have hq : quadKernel t = 1 := by simp [quadKernel, h0]
    by_cases hm : ((-R, -R) : ℝ × ℝ) ≤ p - t
    · have : p - t ∈ Icc ((-R, -R) : ℝ × ℝ) p := ⟨hm, sub_le_self _ h0⟩
      simp only [indicator_of_mem this, hq, one_mul]
    · have : p - t ∉ Icc ((-R, -R) : ℝ × ℝ) p := fun hm' => hm hm'.1
      simp only [indicator_of_notMem this, hq, one_mul]
      refine (hz _ ?_).symm
      simp only [Prod.le_def, not_and_or, not_le] at hm
      rcases hm with hm | hm
      · exact Or.inl hm.le
      · exact Or.inr hm.le
  · have hq : quadKernel t = 0 := by simp [quadKernel, h0]
    have : p - t ∉ Icc ((-R, -R) : ℝ × ℝ) p := fun hm => h0 (by simpa using hm.2)
    simp only [indicator_of_notMem this, hq, zero_mul]

lemma convolutionExistsAt_quadKernel {w : ℝ × ℝ → ℝ}
    (hw : LocallyIntegrable w (volume : Measure (ℝ × ℝ))) {R : ℝ}
    (hz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → w q = 0) (p : ℝ × ℝ) :
    ConvolutionExistsAt quadKernel w p (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  unfold ConvolutionExistsAt
  simpa using integrable_quadKernel_mul hw hz p

/-- A convolution with a kernel supported in `t ≥ 0` vanishes when a coordinate is `≤ -R`. -/
lemma convolution_eq_zero_of_forward {f h : ℝ × ℝ → ℝ} (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    (hf : ∀ t : ℝ × ℝ, ¬ (0 : ℝ × ℝ) ≤ t → f t = 0) {R : ℝ}
    (hz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → h q = 0) (p : ℝ × ℝ)
    (hp : p.1 ≤ -R ∨ p.2 ≤ -R) : (f ⋆[L, volume] h) p = 0 := by
  rw [convolution_def]
  have : (fun t => L (f t) (h (p - t))) = fun _ => 0 := by
    funext t
    by_cases ht : (0 : ℝ × ℝ) ≤ t
    · have ht1 : (0 : ℝ) ≤ t.1 := ht.1
      have ht2 : (0 : ℝ) ≤ t.2 := ht.2
      rw [hz (p - t) (by
        rcases hp with hp | hp
        · left; simp only [Prod.fst_sub]; linarith
        · right; simp only [Prod.snd_sub]; linarith)]
      simp
    · rw [hf t ht]; simp
  rw [this, integral_zero]

lemma riemannKernel_norm_locallyIntegrable (c : ℝ) :
    LocallyIntegrable (fun x => ‖riemannKernel c x‖) (volume : Measure (ℝ × ℝ)) := by
  have hc : Continuous fun q : ℝ × ℝ => ‖besselPhi c (q.1 * q.2)‖ :=
    ((contDiff_besselPhi c).continuous.comp (continuous_fst.mul continuous_snd)).norm
  have := (hc.locallyIntegrable (μ := (volume : Measure (ℝ × ℝ)))).indicator
    (measurableSet_Ici (a := (0 : ℝ × ℝ)))
  convert this using 1
  funext q
  by_cases h : (0 : ℝ × ℝ) ≤ q <;> simp [riemannKernel, h]

/-- The Riemann solution `K ⋆ h`. -/
noncomputable def riemannSol (c : ℝ) (h : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  riemannKernel c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h

lemma riemannSol_contDiff (c : ℝ) {n : ℕ∞} {h : ℝ × ℝ → ℝ} (hcg : HasCompactSupport h)
    (hh : ContDiff ℝ n h) : ContDiff ℝ n (riemannSol c h) :=
  hcg.contDiff_convolution_right _ (riemannKernel_locallyIntegrable c) hh

lemma riemannSol_eq_zero (c : ℝ) {h : ℝ × ℝ → ℝ} {R : ℝ}
    (hz : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → h q = 0) (p : ℝ × ℝ)
    (hp : p.1 ≤ -R ∨ p.2 ≤ -R) : riemannSol c h p = 0 :=
  convolution_eq_zero_of_forward _ (fun t ht => by simp [riemannKernel, ht]) hz p hp

/-- **Integral equation** `u = Q (h + c u)` for `u = K ⋆ h`. -/
theorem riemannSol_eq_quadPrim (c : ℝ) {h : ℝ × ℝ → ℝ} (hh : Continuous h)
    (hcg : HasCompactSupport h) :
    riemannSol c h = quadPrim (h + c • riemannSol c h) := by
  obtain ⟨R, hz⟩ := exists_vanishing hcg
  funext p
  have hKli := riemannKernel_locallyIntegrable c
  have hKh : ConvolutionExists (riemannKernel c) h (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hcg.convolutionExists_right _ hKli hh
  have hQh : ConvolutionExistsAt quadKernel h p (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    convolutionExistsAt_quadKernel hh.locallyIntegrable hz p
  have hW : (c • (quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] riemannKernel c))
      = riemannKernel c - quadKernel := by
    funext q
    have := riemannKernel_eq c q
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  have h1 : ((c • (quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] riemannKernel c))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) p
      = c * ((quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] riemannKernel c)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) p := by
    rw [smul_convolution]; rfl
  have h2 : ((riemannKernel c - quadKernel) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) p
      = (riemannKernel c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) p
        - (quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) p := by
    simp only [convolution_def, Pi.sub_apply, map_sub, sub_apply]
    exact integral_sub (hKh p) hQh
  rw [hW] at h1
  -- associativity
  have hL : ∀ (x y z : ℝ), (ContinuousLinearMap.lsmul ℝ ℝ) ((ContinuousLinearMap.lsmul ℝ ℝ) x y) z
      = (ContinuousLinearMap.lsmul ℝ ℝ) x ((ContinuousLinearMap.lsmul ℝ ℝ) y z) := by
    intro x y z; simp [mul_assoc]
  have hfg : ∀ᵐ y ∂(volume : Measure (ℝ × ℝ)),
      ConvolutionExistsAt quadKernel (riemannKernel c) y (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ae_of_all _ fun y => convolutionExistsAt_quadKernel (R := 1) hKli
      (fun q hq => by
        have : ¬ (0 : ℝ × ℝ) ≤ q := by
          rintro ⟨h1, h2⟩
          rcases hq with hq | hq <;> simp at h1 h2 hq <;> linarith
        simp [riemannKernel, this]) y
  have hgk : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)),
      ConvolutionExistsAt (fun x => ‖riemannKernel c x‖) (fun x => ‖h x‖) x
        (ContinuousLinearMap.mul ℝ ℝ) volume :=
    ae_of_all _ fun x => hcg.norm.convolutionExists_right _
      (riemannKernel_norm_locallyIntegrable c) hh.norm x
  have hGc : Continuous ((fun x => ‖riemannKernel c x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      fun x => ‖h x‖) :=
    hcg.norm.continuous_convolution_right _ (riemannKernel_norm_locallyIntegrable c) hh.norm
  have hfgk : ConvolutionExistsAt (fun x => ‖quadKernel x‖)
      ((fun x => ‖riemannKernel c x‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] fun x => ‖h x‖) p
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    unfold ConvolutionExistsAt
    simp only [norm_quadKernel, ContinuousLinearMap.mul_apply']
    refine integrable_quadKernel_mul (R := R) hGc.locallyIntegrable (fun q hq => ?_) p
    exact convolution_eq_zero_of_forward _ (fun t ht => by simp [riemannKernel, ht])
      (fun q hq => by simp [hz q hq]) q hq
  have h3 := convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ) hL (x₀ := p)
    (f := quadKernel) (g := riemannKernel c) (k := h) (μ := volume) (ν := volume)
    quadKernel_locallyIntegrable.aestronglyMeasurable hKli.aestronglyMeasurable
    hh.aestronglyMeasurable hfg hgk hfgk
  have h3' : ((quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] riemannKernel c)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) p
      = (quadKernel ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] riemannSol c h) p := h3
  have hu0 : ∀ q : ℝ × ℝ, (q.1 ≤ -R ∨ q.2 ≤ -R) → (c • riemannSol c h) q = 0 := by
    intro q hq
    simp [riemannSol_eq_zero c hz q hq]
  have h4 : ConvolutionExistsAt quadKernel (c • riemannSol c h) p
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    convolutionExistsAt_quadKernel
      (((contDiff_zero.mp (riemannSol_contDiff c hcg (n := 0) (contDiff_zero.mpr hh))).const_smul
        c).locallyIntegrable)
      hu0 p
  rw [quadPrim_eq_convolution, hQh.distrib_add h4, convolution_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h5 : riemannSol c h p = (riemannKernel c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) p := rfl
  rw [h3'] at h1
  linarith

end Lightlike.GreenOperators
