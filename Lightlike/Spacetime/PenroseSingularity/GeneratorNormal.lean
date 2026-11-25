import Lightlike.Spacetime.PenroseSingularity.FocalLength
import Lightlike.Spacetime.PenroseSingularity.NullGeodCausal
import Lightlike.Spacetime.PenroseSingularity.Orthogonality

/-!
# The initial velocity of a generator is a future null normal (G1-012)

A future null geodesic from a point `x` of a level set `f⁻¹(0)` to a point outside `I⁺(S)` has initial
velocity that is non-zero, null, future directed and `g`-orthogonal to `ker df_x`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The phase of a null geodesic is a non-zero null vector. -/
theorem IsNullGeodesicOn.phase_null {γ : ℝ → M} {J : Set ℝ} (h : IsNullGeodesicOn g γ J) {t : ℝ} (ht : t ∈ J) :
    (phase (n := n) γ t).snd ≠ 0 ∧ g.g (γ t) (phase (n := n) γ t).snd (phase (n := n) γ t).snd = 0 := by
  obtain ⟨w, O, hO, hsrc, hgeo, hw0, hnull⟩ := h t ht
  set O' : Set ℝ := interior O with hO'
  have ht' : t ∈ O' := mem_interior_iff_mem_nhds.2 hO
  have hgeo' : Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ t))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) w O' :=
    ⟨fun r hr => hgeo.pos r (interior_subset hr), fun r hr => hgeo.vel r (interior_subset hr)⟩
  obtain ⟨-, hphase⟩ := phase_coord g (γ t) isOpen_interior (fun s hs => hsrc s (interior_subset hs)) hgeo' ht'
  have hsrc0 : γ t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).source := mem_extChartAt_source _
  have hb : γ t ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t)).baseSet := mem_baseSet_trivializationAt _ _ _
  refine ⟨fun h0 => hw0 ?_, ?_⟩
  · rw [← hphase]
    have : (phase (n := n) γ t) = ⟨γ t, 0⟩ := by unfold phase at h0 ⊢; congr 1
    rw [this]
    exact ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t)).linear ℝ hb).map_zero
  · have := g_eq_gpair g (γ t) (γ t) hsrc0 (phase (n := n) γ t).snd (phase (n := n) γ t).snd
    rw [this]
    have e1 : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ t) ⟨γ t, (phase (n := n) γ t).snd⟩).2 = w t := hphase
    rw [e1, gpairAt_eq_bil]
    exact hnull

/-- On a closed interval of positive length the velocity at `0` is the phase velocity. -/
theorem velocity_eq_phase {γ : ℝ → M} {L : ℝ} (hL : 0 < L) (h : IsNullGeodesicOn g γ (Icc 0 L)) :
    Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 L) 0 = (phase (n := n) γ 0).snd := by
  obtain ⟨ε, hε, hgeo⟩ := h.exists_open_interval g hL.le
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (L + ε) := ⟨by linarith, by linarith⟩
  have hmd := hgeo.mdifferentiableAt isOpen_Ioo h0
  unfold Causal.velocity phase
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc (0 : ℝ) L) 0 := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffOn_Icc hL 0 ⟨le_rfl, hL.le⟩
  rw [mfderivWithin_eq_mfderiv hu hmd]

/-- **The initial velocity of a future null geodesic is a future null vector.** -/
theorem generator_future_null (T : Causal.TimeOrientation g) {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (h : IsFutureNullGeodesicOn T γ (Icc 0 L)) :
    (phase (n := n) γ 0).snd ≠ 0 ∧ g.g (γ 0) (phase (n := n) γ 0).snd (phase (n := n) γ 0).snd = 0 ∧
      g.g (γ 0) (phase (n := n) γ 0).snd (T.X (γ 0)) < 0 := by
  obtain ⟨h1, h2⟩ := h.1.phase_null g ⟨le_rfl, hL.le⟩
  refine ⟨h1, h2, ?_⟩
  have := h.2 0 ⟨le_rfl, hL.le⟩
  rwa [velocity_eq_phase g hL h.1] at this

/-- **A generator is orthogonal to the tangent directions of the surface.** -/
theorem generator_orthogonal (T : Causal.TimeOrientation g) {S : Set M} {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ : IsFutureNullGeodesicOn T γ (Icc 0 L)) (hfar : γ L ∉ Causal.chronFutureSet T S)
    {m : ℕ} {xS : (Fin m → ℝ) → M} {Sg₀ : Set (Fin m → ℝ)} (hSo : IsOpen Sg₀) (h0 : (0 : Fin m → ℝ) ∈ Sg₀)
    (hsm : ContMDiffOn 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ xS Sg₀) (hx0 : xS 0 = γ 0)
    (hSS : ∀ σ ∈ Sg₀, xS σ ∈ S) (e : Fin m → ℝ) :
    g.g (γ 0) (phase (n := n) γ 0).snd (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 e) = 0 := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo 0 h0
  set c : ℝ := r / (2 * (‖e‖ + 1)) with hc
  have hcpos : 0 < c := by positivity
  set ρ : ℝ → ℝ := fun ε => c * Real.arctan (ε / c) with hρ
  have hρ0 : ρ 0 = 0 := by simp [hρ]
  have hρd : HasDerivAt ρ 1 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => ε / c) (1 / c) 0 := (hasDerivAt_id (0 : ℝ)).div_const c
    have h2 := (Real.hasDerivAt_arctan (0 / c)).comp 0 h1
    have h3 := h2.const_mul c
    refine h3.congr_deriv ?_
    field_simp
    simp
  have hρb : ∀ ε, |ρ ε| < 2 * c := by
    intro ε
    have h1 := Real.arctan_lt_pi_div_two (ε / c)
    have h2 := Real.neg_pi_div_two_lt_arctan (ε / c)
    have h3 := Real.pi_lt_four
    simp only [hρ, abs_mul, abs_of_pos hcpos]
    have : |Real.arctan (ε / c)| < 2 := by rw [abs_lt]; constructor <;> linarith
    nlinarith
  set σ : ℝ → M := fun ε => xS (ρ ε • e) with hσ
  have hmem : ∀ ε, ρ ε • e ∈ Sg₀ := by
    intro ε
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc |ρ ε| * ‖e‖ ≤ 2 * c * ‖e‖ := by
          exact mul_le_mul_of_nonneg_right (hρb ε).le (norm_nonneg _)
      _ < r := by
          rw [hc]
          have hpos : 0 < ‖e‖ + 1 := by positivity
          rw [show 2 * (r / (2 * (‖e‖ + 1))) * ‖e‖ = r * (‖e‖ / (‖e‖ + 1)) by field_simp]
          have : ‖e‖ / (‖e‖ + 1) < 1 := by rw [div_lt_one hpos]; linarith
          nlinarith
  have hσ0 : σ 0 = γ 0 := by simp [hσ, hρ0, hx0]
  have hσS : ∀ ε, σ ε ∈ S := fun ε => hSS _ (hmem ε)
  have hxc : ContMDiffAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ xS 0 := hsm.contMDiffAt (hSo.mem_nhds h0)
  have hρc : Continuous ρ := by
    simp only [hρ]; fun_prop
  have hσc : ContinuousAt σ 0 := by
    have : ContinuousAt (fun ε : ℝ => ρ ε • e) 0 := (hρc.smul continuous_const).continuousAt
    have h2 : ContinuousAt xS ((fun ε : ℝ => ρ ε • e) 0) := by
      simp only [hρ0, zero_smul]; exact hxc.continuousAt
    exact ContinuousAt.comp (f := fun ε : ℝ => ρ ε • e) h2 this
  have hsrc : ∀ᶠ ε in 𝓝 (0 : ℝ), σ ε ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0)).source := by
    refine hσc.eventually ?_
    rw [hσ0]; exact extChartAt_source_mem_nhds (γ 0)
  have hb : γ 0 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ 0)).baseSet := mem_baseSet_trivializationAt _ _ _
  have hψ : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0)) (xS 0) := by
    rw [hx0]; exact mdifferentiableAt_extChartAt (by simpa [extChartAt_source] using hb)
  have hxd : MDifferentiableAt 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 := hxc.mdifferentiableAt (by simp)
  set D : Fin n → ℝ := mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0)) (xS 0)
    (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 e) with hD
  have hdiff : DifferentiableAt ℝ (fun σ' => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0) (xS σ')) 0 :=
    mdifferentiableAt_iff_differentiableAt.1 (hψ.comp 0 hxd)
  have hline : HasDerivAt (fun ε : ℝ => ρ ε • e) e 0 := by
    simpa using hρd.smul_const e
  have hσd : HasDerivAt (fun ε => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0) (σ ε)) D 0 := by
    have h3 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp [hρ0])
    have h4 := fderiv_comp_mfderiv hψ hxd e
    rw [← hD] at h4
    rw [h4] at h3
    exact h3
  have key := null_geodesic_orthogonal T hL hγ hfar hσ0 hσS hsrc hσd
  rw [velocity_eq_phase g hL hγ.1] at key
  have hxb : xS 0 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ 0)).baseSet := by rw [hx0]; exact hb
  have hDv : D = hv (E := Fin n → ℝ) (γ 0) (xS 0) (mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 e) :=
    (hv_eq_mfderiv (γ 0) hxb _).symm
  have hpt : ∀ y : M, y = γ 0 → ∀ w : Fin n → ℝ,
      ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ 0)).symmL ℝ y w : Fin n → ℝ) =
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ 0)).symmL ℝ (γ 0) w := by
    rintro y rfl w; rfl
  have hsy : ((chartTriv n (γ 0)).symmL ℝ (γ 0) D : Fin n → ℝ) =
      mfderiv 𝓘(ℝ, Fin m → ℝ) 𝓘(ℝ, Fin n → ℝ) xS 0 e := by
    refine (hpt (xS 0) hx0 D).symm.trans ?_
    rw [hDv]
    exact symmL_hv (γ 0) hxb _
  rw [hsy] at key
  exact key

/-- **The initial velocity of a generator of the boundary of the future of a level set is a future null
normal.** -/
theorem generator_isFutureNullNormal (T : Causal.TimeOrientation g) (hn : 2 ≤ n) {S : Set M}
    {f : M → Fin 2 → ℝ} (hf : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f) (hS : S = f ⁻¹' {0})
    (hsurj : ∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x))
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L) (hγ : IsFutureNullGeodesicOn T γ (Icc 0 L)) (hx : γ 0 ∈ S)
    (hfar : γ L ∉ Causal.chronFutureSet T S) :
    IsFutureNullNormalAt g T f (γ 0) (phase (n := n) γ 0).snd := by
  obtain ⟨h1, h2, h3⟩ := generator_future_null g T hL hγ
  have hfγ0 : f (γ 0) = 0 := by rw [hS] at hx; exact hx
  obtain ⟨xS, Sg₀, hSo, hS0, hsm, hx0, hfx, hinj, hker, -⟩ := exists_surface_param hn hf hfγ0 (hsurj _ hx)
  refine ⟨h1, h2, ?_, h3⟩
  intro v hv
  obtain ⟨u, hu⟩ := (hker v).1 hv
  rw [← hu]
  exact generator_orthogonal g T hL hγ hfar hSo hS0 hsm hx0 (fun σ hσ => by rw [hS]; exact hfx σ hσ) u

end Lightlike.Penrose
