import Lightlike.Rows.G1_012.NullGeodCausal
import Lightlike.Rows.G1_012.NullVariation
import Lightlike.Rows.G1_012.AchronalBoundary
import Lightlike.Spacetime.CausalLadder.ChartCurve

/-!
# Generators of `∂J⁺(S)` leave `S` orthogonally (G1-012)

Manifold-level step: a future null geodesic from a point of `S` to a point outside `I⁺(S)` is
`g`-orthogonal to every curve in `S` through its start point
(`Lightlike.Penrose.null_geodesic_orthogonal`). The proof moves the start point along the curve in
the chart at the start point by the timelike variation of `Lightlike.Geodesic.exists_null_variation`
and pushes up with the end of the geodesic.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- A tangent vector at `p` whose coordinates in the trivialization at `x` are `D` is
`(chartTriv n x).symmL p D`. -/
theorem eq_symmL_of_tTriv (x p : M) (hp : p ∈ (chartTriv n x).baseSet)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) {D : Fin n → ℝ}
    (h : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨p, v⟩).2 = D) :
    v = (chartTriv n x).symmL ℝ p D := by
  have hlin : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨p, v⟩).2 =
      (chartTriv n x).linearEquivAt ℝ p hp v := by
    rw [Trivialization.linearEquivAt_apply]
  rw [hlin, Trivialization.linearEquivAt_apply] at h
  rw [Trivialization.symmL_apply (chartTriv n x) hp, ← h]
  exact ((chartTriv n x).symm_apply_apply_mk hp v).symm


/-- The metric of two vectors at `p` given by their coordinates in the chart at `x` is the coordinate
bilinear form of the chart at `x`, evaluated at `p`. -/
theorem metric_eq_bil_at (g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M) (x p : M)
    (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) (D₁ D₂ : Fin n → ℝ) :
    g.g p ((chartTriv n x).symmL ℝ p D₁) ((chartTriv n x).symmL ℝ p D₂) =
      bil (g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x p)) D₁ D₂ := by
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hp
  have e : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x p) = p :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hp
  have hb : ∀ i j, g.coordMetric x (extChartAt 𝓘(ℝ, Fin n → ℝ) x p) i j =
      g.g p ((chartTriv n x).symmL ℝ p (Pi.single i 1)) ((chartTriv n x).symmL ℝ p (Pi.single j 1)) := by
    intro i j
    have := g.coordMetric_eq x hy i j
    rw [coordBasis_apply, coordBasis_apply] at this
    rw [e] at this
    exact this
  have hD : ∀ D : Fin n → ℝ, (chartTriv n x).symmL ℝ p D =
      ∑ i, D i • (chartTriv n x).symmL ℝ p (Pi.single i 1) := by
    intro D
    conv_lhs => rw [pi_eq_sum_univ D]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hD D₁, hD D₂]
  unfold bil
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hb]
  ring


variable {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- The coordinates, in the chart at `x`, of the time orientation field at the point with chart
coordinates `y`. -/
def timeCoord (T : Causal.TimeOrientation g) (x : M) (y : Fin n → ℝ) : Fin n → ℝ :=
  (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x ⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y,
    T.X ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)⟩).2

/-- The time orientation field in chart coordinates is continuous on the chart target. -/
theorem continuousOn_timeCoord (T : Causal.TimeOrientation g) (x : M) :
    ContinuousOn (timeCoord T x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target := by
  have hsec : Continuous (fun p : M => (⟨p, T.X p⟩ : TotalSpace (Fin n → ℝ)
      (TangentSpace 𝓘(ℝ, Fin n → ℝ)))) := T.contMDiff.continuous
  have hsymm : ContinuousOn (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target := continuousOn_extChartAt_symm x
  have h1 : ContinuousOn (fun y => (⟨(extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y,
      T.X ((extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm y)⟩ : TotalSpace (Fin n → ℝ)
      (TangentSpace 𝓘(ℝ, Fin n → ℝ)))) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    hsec.comp_continuousOn hsymm
  have h2 := (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x).continuousOn.comp h1 fun y hy => by
    rw [Trivialization.mem_source]
    exact symm_mem_chartTriv_baseSet x hy
  exact continuous_snd.comp_continuousOn h2

/-- The time orientation field at `p` is the vector with coordinates `timeCoord` at `p`. -/
theorem timeOrientation_eq_symmL (T : Causal.TimeOrientation g) (x p : M)
    (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) :
    T.X p = (chartTriv n x).symmL ℝ p
      (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x p)) := by
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hp
  have e : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x p) = p :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hp
  have hb : p ∈ (chartTriv n x).baseSet := by
    have := symm_mem_chartTriv_baseSet x hy
    rwa [e] at this
  refine eq_symmL_of_tTriv x p hb (T.X p) ?_
  unfold timeCoord
  rw [e]


/-- `pairing` is the bilinear contraction `bil`. -/
theorem pairing_eq_bil (G : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (y a b : Fin n → ℝ) :
    Lightlike.Geodesic.pairing G y a b = bil (G y) a b := by
  unfold Lightlike.Geodesic.pairing bil
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A point in the source of the chart at `x` lies in the base set of the chart trivialization. -/
theorem mem_baseSet_of_mem_source (x p : M) (hp : p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) :
    p ∈ (chartTriv n x).baseSet := by
  have hy : extChartAt 𝓘(ℝ, Fin n → ℝ) x p ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).map_source hp
  have e : (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm (extChartAt 𝓘(ℝ, Fin n → ℝ) x p) = p :=
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x).left_inv hp
  have := symm_mem_chartTriv_baseSet x hy
  rwa [e] at this

/-- **Moving the start of a future null geodesic along a transversal curve gives a timelike curve to
a later point of the geodesic.** If `D` (the chart velocity at `γ a` of the curve `σ` through `γ a`)
satisfies `g(γ', D) > 0`, then for all small `ε > 0` the point `γ b` is in `I⁺(σ ε)`. -/
theorem null_geodesic_chronFuture (T : Causal.TimeOrientation g) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsFutureNullGeodesicOn T γ (Icc a b)) {σ : ℝ → M} (hσ0 : σ 0 = γ a)
    (hσsrc : ∀ᶠ ε in 𝓝 (0 : ℝ), σ ε ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a)).source)
    {D : Fin n → ℝ}
    (hσd : HasDerivAt (fun ε => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a) (σ ε)) D 0)
    (hpos : 0 < g.g (γ a) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) a)
      ((chartTriv n (γ a)).symmL ℝ (γ a) D)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ b ∈ Causal.chronFuture T (σ ε) := by
  obtain ⟨hnull, hfut⟩ := id hγ
  obtain ⟨w, O, hO, hsrc, hgeo, hw0, hbil⟩ := hnull a ⟨le_rfl, hab.le⟩
  have hq : γ a ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a)).source := mem_extChartAt_source (γ a)
  have hbq := mem_baseSet_of_mem_source (γ a) (γ a) hq
  -- velocity in chart coordinates
  obtain ⟨-, hvel⟩ := geodesic_local_velocity hab ⟨le_rfl, hab.le⟩ hO hsrc hgeo.pos
  have hvq := eq_symmL_of_tTriv (γ a) (γ a) hbq _ hvel
  have hXq := timeOrientation_eq_symmL T (γ a) (γ a) hq
  have hmet : ∀ D₁ D₂ : Fin n → ℝ, g.g (γ a) ((chartTriv n (γ a)).symmL ℝ (γ a) D₁)
      ((chartTriv n (γ a)).symmL ℝ (γ a) D₂) =
      bil (g.coordMetric (γ a) (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a) (γ a))) D₁ D₂ :=
    fun D₁ D₂ => metric_eq_bil_at g.toNondegMetric (γ a) (γ a) hq D₁ D₂
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a) with hψ
  set gc := g.coordMetric (γ a) with hgc
  have hgcM : IsCoordMetric gc ψ.target := g.isCoordMetric_coordMetric (γ a)
  set J : Set ℝ := O ∩ Iio b with hJ
  have hJn : J ∈ 𝓝 a := inter_mem hO (Iio_mem_nhds hab)
  have hUJ : ∀ t ∈ J, ψ (γ t) ∈ ψ.target := fun t ht => ψ.map_source (hsrc t ht.1)
  have hgeoJ : Lightlike.Geodesic.IsGeodesicOn gc (fun s => ψ (γ s)) w J :=
    ⟨fun t ht => hgeo.pos t ht.1, fun t ht => hgeo.vel t ht.1⟩
  have hnull0 : Lightlike.Geodesic.normSq gc (ψ (γ a)) (w a) = 0 := by
    rw [← Lightlike.Geodesic.pairing_self, pairing_eq_bil]; exact hbil
  have hG : 0 < Lightlike.Geodesic.pairing gc (ψ (γ a)) (w a) D := by
    rw [pairing_eq_bil]
    rw [hvq, hmet] at hpos
    exact hpos
  have hXneg : Lightlike.Geodesic.pairing gc (ψ (γ a)) (w a) (timeCoord T (γ a) (ψ (γ a))) < 0 := by
    have := hfut a ⟨le_rfl, hab.le⟩
    rw [hvq, hXq, hmet] at this
    rw [pairing_eq_bil]
    exact this
  obtain ⟨δ, hδ, h, h', O', hO'o, hIcc, hO'J, hhd, hh'c, hh₀, hhδ, ε₀, ν, hε₀, hν, hvar⟩ :=
    Lightlike.Geodesic.exists_null_variation hgcM hJn hgeoJ hUJ hnull0 hG
      (continuousOn_timeCoord T (γ a)) hXneg
  have hslope := hσd.tendsto_slope_zero_right
  filter_upwards [hslope.eventually (Metric.ball_mem_nhds D hν), Ioo_mem_nhdsGT hε₀,
    nhdsWithin_le_nhds hσsrc] with ε hsl hε hsε
  set d : Fin n → ℝ := ψ (σ ε) - ψ (γ a) with hd
  set v : Fin n → ℝ := ε⁻¹ • d with hv
  have hv' : v ∈ Metric.ball D ν := by simpa [hv, hd, hσ0] using hsl
  have hεv : ε • v = d := by rw [hv, smul_inv_smul₀ hε.1.ne']
  have hvar' := fun t ht => hvar ε hε v hv' t ht
  simp only [hεv] at hvar'
  set c : ℝ → Fin n → ℝ := fun t => ψ (γ t) + h t • d with hcdef
  set c' : ℝ → Fin n → ℝ := fun t => w t + h' t • d with hc'def
  have hIJ : ∀ t ∈ Icc a (a + δ), t ∈ J := fun t ht => hO'J (hIcc ht)
  have hcd : ∀ t ∈ O', HasDerivAt c (c' t) t := fun t ht =>
    (hgeo.pos t (hO'J ht).1).add ((hhd t ht).smul_const d)
  have hc'c : ∀ t ∈ O', ContinuousAt c' t := fun t ht =>
    (hgeo.vel t (hO'J ht).1).continuousAt.add ((hh'c t ht).smul continuousAt_const)
  have hcC1 : ContDiffOn ℝ 1 c O' := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hO'o]
    refine ⟨fun t ht => (hcd t ht).differentiableAt.differentiableWithinAt,
      fun h0 => absurd h0 (by simp), ?_⟩
    rw [contDiffOn_zero]
    exact (continuousOn_of_forall_continuousAt hc'c).congr fun t ht => (hcd t ht).deriv
  have hctarget : ∀ t ∈ Icc a (a + δ), c t ∈ ψ.target := fun t ht => (hvar' t ht).1
  set C : ℝ → M := fun t => ψ.symm (c t) with hC
  have hCsm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) 1 C (Icc a (a + δ)) :=
    (contMDiffOn_extChartAt_symm (γ a)).comp (hcC1.contMDiffOn.mono hIcc) hctarget
  have hδ' : a < a + δ := by linarith
  have hCvel : ∀ t ∈ Icc a (a + δ), (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M (γ a)
      ⟨C t, Causal.velocity 𝓘(ℝ, Fin n → ℝ) C (Icc a (a + δ)) t⟩).2 = c' t := fun t ht =>
    (Causal.mdifferentiableWithinAt_chart_symm (I := 𝓘(ℝ, Fin n → ℝ)) (γ a)
      (uniqueDiffOn_Icc hδ' t ht) ht (hcd t (hIcc ht)).hasDerivWithinAt hctarget).2
  have hCsrc : ∀ t ∈ Icc a (a + δ), C t ∈ ψ.source := fun t ht => ψ.map_target (hctarget t ht)
  have hψC : ∀ t ∈ Icc a (a + δ), ψ (C t) = c t := fun t ht => ψ.right_inv (hctarget t ht)
  have hTL : ∀ t ∈ Icc a (a + δ),
      T.IsFutureTimelike (Causal.velocity 𝓘(ℝ, Fin n → ℝ) C (Icc a (a + δ)) t) := by
    intro t ht
    have hvq' := eq_symmL_of_tTriv (γ a) (C t) (mem_baseSet_of_mem_source _ _ (hCsrc t ht)) _
      (hCvel t ht)
    have hXC := timeOrientation_eq_symmL T (γ a) (C t) (hCsrc t ht)
    rw [hψC t ht] at hXC
    obtain ⟨-, h2, h3⟩ := hvar' t ht
    unfold Causal.TimeOrientation.IsFutureTimelike
    rw [hvq', hXC, metric_eq_bil_at g.toNondegMetric (γ a) (C t) (hCsrc t ht),
      metric_eq_bil_at g.toNondegMetric (γ a) (C t) (hCsrc t ht), hψC t ht]
    rw [pairing_eq_bil] at h2 h3
    exact ⟨h2, h3⟩
  have hcurve : Causal.IsFutureTimelikeCurve T C (Icc a (a + δ)) :=
    Causal.isFutureTimelikeCurve_of_contMDiffOn T hδ' hCsm hTL
  have hCa : C a = σ ε := by
    simp only [hC, hcdef, hh₀, one_smul, hd]
    rw [add_sub_cancel]
    exact ψ.left_inv hsε
  have haδJ : a + δ ∈ J := hIJ _ ⟨by linarith, le_rfl⟩
  have hCb : C (a + δ) = γ (a + δ) := by
    simp only [hC, hcdef, hhδ, zero_smul, add_zero]
    exact ψ.left_inv (hsrc _ haδJ.1)
  have hmem1 : γ (a + δ) ∈ Causal.chronFuture T (σ ε) :=
    ⟨C, a, a + δ, hδ', hcurve, hCa, hCb⟩
  have hcaus := (hγ.isFutureCausalCurve T hab)
  have hcaus' : Causal.IsFutureCausalCurve T γ (Icc (a + δ) b) :=
    Causal.IsCurveWith.mono hcaus (by linarith) le_rfl haδJ.2
  have hmem2 : γ b ∈ Causal.causalFuture T (γ (a + δ)) :=
    ⟨γ, a + δ, b, haδJ.2.le, hcaus', rfl, rfl⟩
  exact Causal.chronFuture_causalFuture_trans_of_isOpen T (Causal.isOpen_chronFuture_of_reach T)
    hmem1 hmem2


/-- **A future null geodesic from `S` to a point outside `I⁺(S)` is orthogonal to `S`.** Let `γ` be a
future null geodesic on `[a, b]` with `γ b ∉ I⁺(S)`, and `σ` a curve in `S` through `γ a`, with chart
velocity `D` at `γ a`. Then `g(γ'(a), D) = 0`. (Hawking–Ellis, section 4.5; the proof is the
timelike variation `Lightlike.Geodesic.exists_null_variation`. Difference: the tangent vector to `S`
is given as the chart velocity of a curve in `S`, not as an element of the tangent space of a
submanifold.) -/
theorem null_geodesic_orthogonal (T : Causal.TimeOrientation g) {S : Set M} {γ : ℝ → M} {a b : ℝ}
    (hab : a < b) (hγ : IsFutureNullGeodesicOn T γ (Icc a b))
    (hr : γ b ∉ Causal.chronFutureSet T S) {σ : ℝ → M} (hσ0 : σ 0 = γ a) (hσS : ∀ ε, σ ε ∈ S)
    (hσsrc : ∀ᶠ ε in 𝓝 (0 : ℝ), σ ε ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a)).source)
    {D : Fin n → ℝ}
    (hσd : HasDerivAt (fun ε => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a) (σ ε)) D 0) :
    g.g (γ a) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) a)
      ((chartTriv n (γ a)).symmL ℝ (γ a) D) = 0 := by
  by_contra hne
  have hmem : ∀ {σ' : ℝ → M}, (∀ ε, σ' ε ∈ S) →
      (∃ ε, γ b ∈ Causal.chronFuture T (σ' ε)) → False := by
    rintro σ' hS ⟨ε, hε⟩
    exact hr (mem_iUnion₂.2 ⟨σ' ε, hS ε, hε⟩)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hneg : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0 : ℝ))
    have hd' : HasDerivAt (fun ε => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a) (σ (-ε))) (-D) 0 := by
      have h0 : HasDerivAt (fun ε => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ a) (σ ε)) D (-0) := by
        simpa using hσd
      have h1 := h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
      simp only [neg_smul, one_smul] at h1
      convert h1 using 1
      rfl
    have hpos : 0 < g.g (γ a) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc a b) a)
        ((chartTriv n (γ a)).symmL ℝ (γ a) (-D)) := by
      rw [map_neg, map_neg]
      linarith
    obtain ⟨ε, hε⟩ := (null_geodesic_chronFuture T hab hγ (σ := fun ε => σ (-ε))
      (by simpa using hσ0) (hneg.eventually hσsrc) hd' hpos).exists
    exact hmem (σ' := fun ε => σ (-ε)) (fun ε => hσS _) ⟨ε, hε⟩
  · obtain ⟨ε, hε⟩ := (null_geodesic_chronFuture T hab hγ hσ0 hσsrc hσd hgt).exists
    exact hmem hσS ⟨ε, hε⟩

end Lightlike.Penrose
