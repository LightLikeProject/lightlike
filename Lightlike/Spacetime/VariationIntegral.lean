import Lightlike.Spacetime.PalatiniCoord

/-!
# The first variation of the Einstein-Hilbert action (GE15, stage S3)

For a smooth metric `g` of any signature on `ℝⁿ` (`det g ≠ 0` everywhere), a smooth symmetric perturbation `h` whose support lies in a
compact set `T`, and `g_t = g + t h`: `eh_first_variation`,
`d/dt ∫_T √|g_t| (R(g_t) - 2Λ) = -∫_T √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at `t = 0`, with no boundary term.

* `contDiffAt_lagDensity`: the density `√|g_t| (R(g_t) - 2Λ)` is `C¹` in `(t, x)`;
* `hasDerivAt_integral_family`: differentiation under the integral over a compact set;
* `integral_pd_eq_zero`: a divergence of a `C¹` field of compact support integrates to zero;
* `contDiff_flux`, `dChristoffel_eq_zero`: the flux `√|g| W^ρ` is smooth and vanishes where `h` does.

**Limits.** Coordinates on `ℝⁿ`; the metric is `C^∞`, nondegenerate everywhere. That the critical points are the vacuum Einstein
equations (the fundamental lemma of the calculus of variations), the manifold statement, and the trust checks (in two dimensions the
variation vanishes, the sign of `Λ`) are later stages.
-/

open Matrix Filter Topology MeasureTheory Set Metric
open scoped ContDiff

noncomputable section

namespace Lightlike

variable {n : ℕ}

section
variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))

/-- The Einstein-Hilbert density of `g + t h` at `x`: `√|det g_t| (R(g_t) - 2Λ)`. -/
def lagDensity (Λ : ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  √|(g x + t • h x).det| * (scalarCurvature (fun z => g z + t • h z) x - 2 * Λ)

include hg hh

/-- The Christoffel family is smooth near every point where the perturbed metric is invertible. -/
theorem eventually_contDiffAt_christoffel (t₀ : ℝ) (x : Fin n → ℝ) (hx : (g x + t₀ • h x).det ≠ 0) (i j k : Fin n) :
    ∀ᶠ p in 𝓝 ((t₀, x) : ℝ × (Fin n → ℝ)),
      ContDiffAt ℝ ∞ (fun q : ℝ × (Fin n → ℝ) => christoffel (fun y => g y + q.1 • h y) i j k q.2) p := by
  have hdetc : Continuous (fun p : ℝ × (Fin n → ℝ) => (g p.2 + p.1 • h p.2).det) :=
    (contDiff_det_of (f := fun p : ℝ × (Fin n → ℝ) => g p.2 + p.1 • h p.2) (m := ⊤) (by
      intro a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact ((hg a b).comp contDiff_snd).add (contDiff_fst.mul ((hh a b).comp contDiff_snd)))).continuous
  have : ∀ᶠ p in 𝓝 ((t₀, x) : ℝ × (Fin n → ℝ)), (g p.2 + p.1 • h p.2).det ≠ 0 :=
    hdetc.continuousAt.eventually_ne hx
  filter_upwards [this] with p hp
  exact contDiffAt_christoffel_family_at g h hg hh p.1 p.2 hp i j k |>.congr_of_eventuallyEq (by rfl) |> fun h => by simpa using h


/-- **The Einstein-Hilbert density family is `C¹`** in `(t, x)` near a point where the perturbed metric is invertible. -/
theorem contDiffAt_lagDensity (Λ : ℝ) (t₀ : ℝ) (x : Fin n → ℝ) (hx : (g x + t₀ • h x).det ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ℝ × (Fin n → ℝ) => lagDensity g h Λ p.1 p.2) (t₀, x) := by
  set p₀ : ℝ × (Fin n → ℝ) := (t₀, x) with hp₀
  set Γf : Fin n → Fin n → Fin n → ℝ × (Fin n → ℝ) → ℝ :=
    fun i j k q => christoffel (fun y => g y + q.1 • h y) i j k q.2 with hΓf
  have hΓ : ∀ i j k, ContDiffAt ℝ ∞ (Γf i j k) p₀ := fun i j k => contDiffAt_christoffel_family_at g h hg hh t₀ x hx i j k
  have hψ : ∀ i j k μ, ContDiffAt ℝ 1 (fun q => fderiv ℝ (Γf i j k) q ((0 : ℝ), (Pi.single μ (1 : ℝ) : Fin n → ℝ))) p₀ :=
    fun i j k μ => ((hΓ i j k).fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const
  have hΓ1 : ∀ i j k, ContDiffAt ℝ 1 (Γf i j k) p₀ := fun i j k => (hΓ i j k).of_le (by simp)
  have hev : ∀ i j k μ, ∀ᶠ q in 𝓝 p₀, pd μ (fun y => christoffel (fun z => g z + q.1 • h z) i j k y) q.2 =
      fderiv ℝ (Γf i j k) q ((0 : ℝ), (Pi.single μ (1 : ℝ) : Fin n → ℝ)) := by
    intro i j k μ
    filter_upwards [eventually_contDiffAt_christoffel g h hg hh t₀ x hx i j k] with q hq
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => (q.1, y)) (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) q.2 :=
      hasFDerivAt_prodMk_right q.1 q.2
    have h2 := (hq.differentiableAt (by simp)).hasFDerivAt.comp q.2 (show HasFDerivAt (fun y : Fin n → ℝ => (q.1, y)) _ q.2 from h1)
    unfold pd
    have : fderiv ℝ (fun y => Γf i j k (q.1, y)) q.2 = (fderiv ℝ (Γf i j k) (q.1, q.2)).comp (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) := h2.fderiv
    simp only [hΓf] at this ⊢
    rw [show (fun y => christoffel (fun z => g z + q.1 • h z) i j k y) = fun y => christoffel (fun z => g z + (q.1, y).1 • h z) i j k (q.1, y).2 from rfl, this]
    simp
  -- the Riemann tensor
  have hRf : ∀ ρ σ μ ν, ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) =>
      fderiv ℝ (Γf ρ ν σ) q ((0 : ℝ), (Pi.single μ (1 : ℝ) : Fin n → ℝ)) -
        fderiv ℝ (Γf ρ μ σ) q ((0 : ℝ), (Pi.single ν (1 : ℝ) : Fin n → ℝ)) +
        ∑ l, (Γf ρ μ l q * Γf l ν σ q - Γf ρ ν l q * Γf l μ σ q)) p₀ := by
    intro ρ σ μ ν
    refine ((hψ ρ ν σ μ).sub (hψ ρ μ σ ν)).add (ContDiffAt.sum fun l _ => ?_)
    exact ((hΓ1 ρ μ l).mul (hΓ1 l ν σ)).sub ((hΓ1 ρ ν l).mul (hΓ1 l μ σ))
  have hriem : ∀ ρ σ μ ν, ∀ᶠ q in 𝓝 p₀, riemann (fun z => g z + q.1 • h z) ρ σ μ ν q.2 =
      fderiv ℝ (Γf ρ ν σ) q ((0 : ℝ), (Pi.single μ (1 : ℝ) : Fin n → ℝ)) -
        fderiv ℝ (Γf ρ μ σ) q ((0 : ℝ), (Pi.single ν (1 : ℝ) : Fin n → ℝ)) +
        ∑ l, (Γf ρ μ l q * Γf l ν σ q - Γf ρ ν l q * Γf l μ σ q) := by
    intro ρ σ μ ν
    filter_upwards [hev ρ ν σ μ, hev ρ μ σ ν] with q h1 h2
    unfold riemann
    rw [h1, h2]
  -- the scalar curvature
  have hinv : ∀ a b, ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) => (g q.2 + q.1 • h q.2)⁻¹ a b) p₀ := by
    intro a b
    have := contDiffAt_inv_entry (f := fun q : ℝ × (Fin n → ℝ) => g q.2 + q.1 • h q.2) (m := ⊤) (x := p₀) (by
      intro a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact ((hg a b).comp contDiff_snd).add (contDiff_fst.mul ((hh a b).comp contDiff_snd))) hx a b
    exact this.of_le (by simp)
  have hscal1 : ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) => ∑ σ, ∑ ν, (g q.2 + q.1 • h q.2)⁻¹ σ ν *
      ∑ ρ, (fderiv ℝ (Γf ρ ν σ) q ((0 : ℝ), (Pi.single ρ (1 : ℝ) : Fin n → ℝ)) -
        fderiv ℝ (Γf ρ ρ σ) q ((0 : ℝ), (Pi.single ν (1 : ℝ) : Fin n → ℝ)) +
        ∑ l, (Γf ρ ρ l q * Γf l ν σ q - Γf ρ ν l q * Γf l ρ σ q))) p₀ :=
    ContDiffAt.sum fun σ _ => ContDiffAt.sum fun ν _ => (hinv σ ν).mul (ContDiffAt.sum fun ρ _ => hRf ρ σ ρ ν)
  have hscal : (fun q : ℝ × (Fin n → ℝ) => scalarCurvature (fun z => g z + q.1 • h z) q.2) =ᶠ[𝓝 p₀]
      fun q => ∑ σ, ∑ ν, (g q.2 + q.1 • h q.2)⁻¹ σ ν *
      ∑ ρ, (fderiv ℝ (Γf ρ ν σ) q ((0 : ℝ), (Pi.single ρ (1 : ℝ) : Fin n → ℝ)) -
        fderiv ℝ (Γf ρ ρ σ) q ((0 : ℝ), (Pi.single ν (1 : ℝ) : Fin n → ℝ)) +
        ∑ l, (Γf ρ ρ l q * Γf l ν σ q - Γf ρ ν l q * Γf l ρ σ q)) := by
    have hall : ∀ᶠ q in 𝓝 p₀, ∀ ρ σ ν, riemann (fun z => g z + q.1 • h z) ρ σ ρ ν q.2 =
        fderiv ℝ (Γf ρ ν σ) q ((0 : ℝ), (Pi.single ρ (1 : ℝ) : Fin n → ℝ)) -
          fderiv ℝ (Γf ρ ρ σ) q ((0 : ℝ), (Pi.single ν (1 : ℝ) : Fin n → ℝ)) +
          ∑ l, (Γf ρ ρ l q * Γf l ν σ q - Γf ρ ν l q * Γf l ρ σ q) := by
      rw [eventually_all]; intro ρ; rw [eventually_all]; intro σ; rw [eventually_all]; intro ν
      exact hriem ρ σ ρ ν
    filter_upwards [hall] with q hq
    unfold scalarCurvature ricci
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
    congr 1
    exact Finset.sum_congr rfl fun ρ _ => hq ρ σ ν
  have hscalC : ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) => scalarCurvature (fun z => g z + q.1 • h z) q.2) p₀ :=
    hscal1.congr_of_eventuallyEq hscal
  have hDC : ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) => (g q.2 + q.1 • h q.2).det) p₀ := by
    have := (contDiff_det_of (f := fun q : ℝ × (Fin n → ℝ) => g q.2 + q.1 • h q.2) (m := ⊤) (by
      intro a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact ((hg a b).comp contDiff_snd).add (contDiff_fst.mul ((hh a b).comp contDiff_snd)))).contDiffAt (x := p₀)
    exact this.of_le (by simp)
  have hsqrt : ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) => √|(g q.2 + q.1 • h q.2).det|) p₀ := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · have h1 : ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) => √(-(g q.2 + q.1 • h q.2).det)) p₀ :=
        (hDC.neg).sqrt (by simpa using hneg.ne)
      refine h1.congr_of_eventuallyEq ?_
      have hc : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => (g q.2 + q.1 • h q.2).det) p₀ := hDC.continuousAt
      filter_upwards [hc.eventually (gt_mem_nhds hneg)] with q hq
      show √|(g q.2 + q.1 • h q.2).det| = √(-(g q.2 + q.1 • h q.2).det)
      rw [abs_of_neg hq]
    · have h1 : ContDiffAt ℝ 1 (fun q : ℝ × (Fin n → ℝ) => √((g q.2 + q.1 • h q.2).det)) p₀ :=
        hDC.sqrt hpos.ne'
      refine h1.congr_of_eventuallyEq ?_
      have hc : ContinuousAt (fun q : ℝ × (Fin n → ℝ) => (g q.2 + q.1 • h q.2).det) p₀ := hDC.continuousAt
      filter_upwards [hc.eventually (lt_mem_nhds hpos)] with q hq
      show √|(g q.2 + q.1 • h q.2).det| = √((g q.2 + q.1 • h q.2).det)
      rw [abs_of_pos hq]
  exact hsqrt.mul (hscalC.sub contDiffAt_const)

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- **Differentiation under the integral over a compact set** of a function that is `C¹` near `{0} × T`. -/
theorem hasDerivAt_integral_family {T : Set E} (hT : IsCompact T) (Φ : ℝ × E → ℝ)
    (hΦ : ∀ x ∈ T, ContDiffAt ℝ 1 Φ (0, x)) :
    HasDerivAt (fun t : ℝ => ∫ x in T, Φ (t, x) ∂μ) (∫ x in T, fderiv ℝ Φ (0, x) (1, 0) ∂μ) 0 := by
  set U : Set (ℝ × E) := {p | ContDiffAt ℝ 1 Φ p} with hU
  have hint : ∀ x ∈ T, ((0 : ℝ), x) ∈ interior U := by
    intro x hx
    exact mem_interior_iff_mem_nhds.2 ((hΦ x hx).eventually (by simp))
  have hsub : ({(0 : ℝ)} : Set ℝ) ×ˢ T ⊆ interior U := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    rw [mem_singleton_iff] at ha
    subst ha
    exact hint x hx
  obtain ⟨u, v, hu, hv, h0u, hTv, huv⟩ := generalized_tube_lemma isCompact_singleton hT isOpen_interior hsub
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hu 0 (h0u rfl)
  set ε : ℝ := ε₀ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hclosed : closedBall (0 : ℝ) ε ⊆ u := fun t ht => hball (by
    rw [mem_ball]; have := mem_closedBall.1 ht; rw [hε] at this; simp only [dist_zero_right, Real.norm_eq_abs] at this ⊢; linarith)
  have hU' : ∀ t ∈ closedBall (0 : ℝ) ε, ∀ x ∈ T, ContDiffAt ℝ 1 Φ (t, x) := fun t ht x hx =>
    interior_subset (huv (mk_mem_prod (hclosed ht) (hTv hx)))
  have hcont : ∀ t ∈ closedBall (0 : ℝ) ε, ∀ x ∈ T, ContinuousAt (fun p => fderiv ℝ Φ p (1, 0)) (t, x) := by
    intro t ht x hx
    have := ((hU' t ht x hx).fderiv_right (m := 0) (by simp)).continuousAt
    exact this.clm_apply continuousAt_const
  have hK : IsCompact (closedBall (0 : ℝ) ε ×ˢ T) := (isCompact_closedBall 0 ε).prod hT
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun p => fderiv ℝ Φ p (1, 0)) (fun p hp =>
    (hcont p.1 hp.1 p.2 hp.2).continuousWithinAt)
  have hmeasT : MeasurableSet T := hT.isClosed.measurableSet
  have hcontx : ∀ t ∈ closedBall (0 : ℝ) ε, ContinuousOn (fun x => Φ (t, x)) T := by
    intro t ht x hx
    have : ContinuousAt Φ (t, x) := (hU' t ht x hx).continuousAt
    exact (this.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hcontx' : ContinuousOn (fun x => fderiv ℝ Φ (0, x) (1, 0)) T := by
    intro x hx
    have := hcont 0 (by simp [hεpos.le]) x hx
    exact (this.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict T) (F := fun t x => Φ (t, x))
    (F' := fun t x => fderiv ℝ Φ (t, x) (1, 0)) (x₀ := (0 : ℝ)) (bound := fun _ => B) (s := ball (0 : ℝ) ε) (Metric.ball_mem_nhds (0 : ℝ) hεpos)
    (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hεpos] with t ht
      exact (hcontx t (ball_subset_closedBall ht)).aestronglyMeasurable hmeasT)
    ((hcontx 0 (by simp [hεpos.le])).integrableOn_compact hT)
    (hcontx'.aestronglyMeasurable hmeasT)
    (by
      filter_upwards [ae_restrict_mem hmeasT] with x hx t ht
      exact hB (t, x) ⟨ball_subset_closedBall ht, hx⟩)
    (integrableOn_const (hT.measure_lt_top.ne))
    (by
      filter_upwards [ae_restrict_mem hmeasT] with x hx t ht
      have hd := ((hU' t (ball_subset_closedBall ht) x hx).differentiableAt (by simp)).hasFDerivAt
      have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : E)) t := (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
      exact hd.comp_hasDerivAt t hl)
  exact this.2


/-- **A divergence integrates to zero**: `∫ ∂_ρ F = 0` for a `C¹` function of compact support. -/
theorem integral_pd_eq_zero (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (ρ : Fin n) :
    ∫ y, pd ρ F y = 0 := by
  have hcF : Continuous F := hF.continuous
  have hd : Continuous (fun x => fderiv ℝ F x (Pi.single ρ (1 : ℝ) : Fin n → ℝ)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := fun _ : Fin n → ℝ => (1 : ℝ)) (g := F)
    (v := (Pi.single ρ (1 : ℝ) : Fin n → ℝ))
    (by simp) (by simpa using hd.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ _))
    (by simpa using hcF.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hF.differentiable (by simp)) x)
  simpa [pd] using h1


section
variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
include hg hh

theorem dChristoffel_eq_zero (y : Fin n → ℝ) (hz : ∀ a b, (fun z => h z a b) =ᶠ[𝓝 y] fun _ => (0 : ℝ)) (i j k : Fin n) :
    dChristoffel g h i j k y = 0 := by
  have hpd : ∀ a b c, pd c (fun z => h z a b) y = 0 := by
    intro a b c
    unfold pd
    rw [(hz a b).fderiv_eq]
    simp
  have hy : ∀ a b, h y a b = 0 := fun a b => (hz a b).self_of_nhds
  have hhy : h y = 0 := by ext a b; exact hy a b
  unfold dChristoffel
  simp [hpd, hhy]

end


theorem contDiffAt_sqrt_abs {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {m : ℕ∞ω}
    (hf : ContDiffAt ℝ m f x) (hx : f x ≠ 0) : ContDiffAt ℝ m (fun y => √|f y|) x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have h1 : ContDiffAt ℝ m (fun y => √(-f y)) x := (hf.neg).sqrt (by simpa using hneg.ne)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hf.continuousAt.eventually (gt_mem_nhds hneg)] with q hq
    show √|f q| = √(-f q)
    rw [abs_of_neg hq]
  · have h1 : ContDiffAt ℝ m (fun y => √(f y)) x := hf.sqrt hpos.ne'
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hpos)] with q hq
    show √|f q| = √(f q)
    rw [abs_of_pos hq]

section
variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hdet : ∀ x, (g x).det ≠ 0)
include hg hh hdet

/-- The flux `√|g| W^ρ` of the Palatini identity is smooth. -/
theorem contDiff_flux (ρ : Fin n) : ContDiff ℝ ∞ (fun y => √|(g y).det| * Wvec g h ρ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hinv : ∀ a b, ContDiffAt ℝ ∞ (fun y => (g y)⁻¹ a b) x := fun a b => contDiffAt_inv_entry hg (hdet x) a b
  have hd : ∀ i j k, ContDiffAt ℝ ∞ (dChristoffel g h i j k) x := fun i j k => contDiffAt_dChristoffel g h x hg hh (hdet x) i j k
  have hW : ContDiffAt ℝ ∞ (Wvec g h ρ) x := by
    unfold Wvec
    exact (ContDiffAt.sum fun σ _ => ContDiffAt.sum fun ν _ => (hinv σ ν).mul (hd ρ σ ν)).sub
      (ContDiffAt.sum fun σ _ => (hinv ρ σ).mul (ContDiffAt.sum fun κ _ => hd κ κ σ))
  exact (contDiffAt_sqrt_abs ((contDiff_det_of (f := g) (m := ⊤) hg).contDiffAt) (hdet x)).mul hW

end


section
variable (g h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hg : ∀ a b, ContDiff ℝ ∞ (fun y => g y a b)) (hh : ∀ a b, ContDiff ℝ ∞ (fun y => h y a b))
    (hgs : ∀ y a b, g y a b = g y b a) (hhs : ∀ y a b, h y a b = h y b a)
    (hdet : ∀ x, (g x).det ≠ 0) {T : Set (Fin n → ℝ)} (hT : IsCompact T)
    (hsupp : ∀ a b, tsupport (fun y => h y a b) ⊆ T)
include hg hh hgs hhs hdet hT hsupp

/-- **The first variation of the Einstein-Hilbert action** on a compact region `T` containing the support of the perturbation:
`d/dt ∫_T √|g_t| (R(g_t) - 2Λ) = -∫_T √|g| (R^{αβ} - ½ R g^{αβ} + Λ g^{αβ}) h_{αβ}` at `t = 0`, with no boundary term. -/
theorem eh_first_variation (Λ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in T, lagDensity g h Λ t x)
      (-∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
          (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β)) 0 := by
  set Φ : ℝ × (Fin n → ℝ) → ℝ := fun p => lagDensity g h Λ p.1 p.2 with hΦ
  have hΦc : ∀ x, ContDiffAt ℝ 1 Φ (0, x) := fun x =>
    contDiffAt_lagDensity g h hg hh Λ 0 x (by simpa using hdet x)
  have hmain := hasDerivAt_integral_family (μ := volume) hT Φ (fun x _ => hΦc x)
  -- the integrand of the derivative
  set F : Fin n → (Fin n → ℝ) → ℝ := fun ρ y => √|(g y).det| * Wvec g h ρ y with hF
  have hFs : ∀ ρ, ContDiff ℝ ∞ (F ρ) := fun ρ => contDiff_flux g h hg hh hdet ρ
  set A : (Fin n → ℝ) → ℝ := fun x => -√|(g x).det| * ∑ α, ∑ β, h x α β *
      (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) with hA
  set B : (Fin n → ℝ) → ℝ := fun x => ∑ ρ, pd ρ (F ρ) x with hB
  have hder : ∀ x, fderiv ℝ Φ (0, x) (1, 0) = A x + B x := by
    intro x
    have h1 := hasDerivAt_lagrangian g h hg hh hgs hhs x (hdet x) Λ
    have h2 : HasDerivAt (fun t : ℝ => Φ (t, x)) (fderiv ℝ Φ (0, x) (1, 0)) 0 := by
      have hd := ((hΦc x).differentiableAt (by simp)).hasFDerivAt
      have hl : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : Fin n → ℝ)) 0 := (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 x)
      exact hd.comp_hasDerivAt (0 : ℝ) hl
    exact h2.unique h1
  have hmeasT : MeasurableSet T := hT.isClosed.measurableSet
  have hzero : ∀ x, x ∉ T → ∀ ρ, F ρ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    intro x hx ρ
    have hopen : IsOpen Tᶜ := hT.isClosed.isOpen_compl
    filter_upwards [hopen.mem_nhds hx] with y hy
    have hyz : ∀ a b, (fun z => h z a b) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := fun a b =>
      notMem_tsupport_iff_eventuallyEq.1 (fun hmem => hy (hsupp a b hmem))
    have : Wvec g h ρ y = 0 := by
      unfold Wvec
      simp [dChristoffel_eq_zero g h hg hh y hyz]
    simp [hF, this]
  have hBzero : ∀ ρ, ∫ x in T, pd ρ (F ρ) x = 0 := by
    intro ρ
    have hsupport : HasCompactSupport (F ρ) :=
      HasCompactSupport.intro hT (fun x hx => (hzero x hx ρ).self_of_nhds)
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_pd_eq_zero (F ρ) ((hFs ρ).of_le (by simp)) hsupport ρ
    · intro x hx
      unfold pd
      rw [(hzero x hx ρ).fderiv_eq]
      simp
  have hBc : Continuous B := continuous_finset_sum _ fun ρ _ => (contDiff_pd (hFs ρ) ρ).continuous
  have hBint : IntegrableOn B T volume := hBc.continuousOn.integrableOn_compact hT
  have hcontx : ContinuousOn (fun x => fderiv ℝ Φ (0, x) (1, 0)) T := by
    intro x hx
    have : ContinuousAt (fun p : ℝ × (Fin n → ℝ) => fderiv ℝ Φ p ((1 : ℝ), (0 : Fin n → ℝ))) (0, x) :=
      ((hΦc x).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply (continuousAt_const (y := ((1 : ℝ), (0 : Fin n → ℝ))))
    exact (this.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hABint : IntegrableOn (fun x => fderiv ℝ Φ (0, x) (1, 0)) T volume := hcontx.integrableOn_compact hT
  have hAint : IntegrableOn A T volume := by
    have := hABint.sub hBint
    refine this.congr_fun (fun x _ => ?_) hmeasT
    show fderiv ℝ Φ (0, x) (1, 0) - B x = A x
    rw [hder x]; ring
  have hint : ∫ x in T, fderiv ℝ Φ (0, x) (1, 0) = ∫ x in T, A x := by
    have : ∫ x in T, fderiv ℝ Φ (0, x) (1, 0) = ∫ x in T, (A x + B x) := by
      refine setIntegral_congr_fun hmeasT fun x _ => hder x
    rw [this, integral_add hAint hBint]
    have hB0 : ∫ x in T, B x = 0 := by
      simp only [hB]
      rw [integral_finsetSum _ fun ρ _ => ((contDiff_pd (hFs ρ) ρ).continuous.continuousOn.integrableOn_compact hT)]
      exact Finset.sum_eq_zero fun ρ _ => hBzero ρ
    rw [hB0, add_zero]
  rw [hint] at hmain
  have hA' : ∫ x in T, A x = -∫ x in T, √|(g x).det| * ∑ α, ∑ β, h x α β *
      (ricciUp g x α β - (1 / 2) * scalarCurvature g x * (g x)⁻¹ α β + Λ * (g x)⁻¹ α β) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun hmeasT fun x _ => ?_
    simp only [hA, neg_mul]
  rw [hA'] at hmain
  exact hmain

end

end Lightlike
