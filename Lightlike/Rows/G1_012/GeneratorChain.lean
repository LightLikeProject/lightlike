import Lightlike.Rows.G1_012.RadialNull
import Lightlike.Rows.G1_012.FutureNull
import Lightlike.Geodesic.RadialUnique
import Lightlike.Rows.G1_012.GeodesicChartConverse

/-!
# Chaining local radial pieces into one null geodesic (G1-012)

A future causal curve `β` which never enters `I⁺` of one of its own earlier points
(`hno`, the situation of a curve in `J⁺(S) \ I⁺(S)`) is, on short windows in a chart, a monotone
reparametrisation of a radial null geodesic (`window_radial`). Overlapping windows have matching
tangents (`geodesic_eq_radial`), so they glue to one null geodesic (`IsNullGeodesicOn.union`).
-/

open Bundle Manifold Set Filter Topology MeasureTheory Metric Matrix
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- **Uniform future time balls over a set `S` of chart points**: fixed radii `ρ`, `r`, `η` such
that every `p ∈ S` has a future time ball of radius `r` whose image contains the `η`-ball about `p`. -/
def UniformFutureBall (T : Causal.TimeOrientation g) (x : M) (S : Set (Fin n → ℝ)) (ρ r η : ℝ) :
    Prop :=
  0 < r ∧ r < ρ ∧ 0 < η ∧ ∀ p ∈ S, ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ))
    (N : (Fin n → ℝ) → Fin n → ℝ), Lightlike.Geodesic.IsTimeBall (g.coordMetric x)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target p ρ φ (timeCoord T x p) r N ∧
    (∀ v ∈ ball (0 : Fin n → ℝ) r, Lightlike.Geodesic.pairing (g.coordMetric x) (φ v) (N v)
      (timeCoord T x (φ v)) < 0) ∧
    ∀ y : Fin n → ℝ, Dist.dist y p < η → ∃ v ∈ ball (0 : Fin n → ℝ) r, φ v = y

/-- **A future causal curve is not constant on a nondegenerate interval.** -/
theorem Causal_not_const {T : Causal.TimeOrientation g} {β : ℝ → M} {a b t₀ t₂ : ℝ}
    (hβ : Causal.IsFutureCausalCurve T β (Icc a b)) (hsub : Icc t₀ t₂ ⊆ Icc a b) (h : t₀ < t₂) :
    ¬ ∀ t ∈ Icc t₀ t₂, β t = β t₀ := by
  intro hc
  have hae := hβ.ae_velocity
  have hae' := (ae_restrict_iff' measurableSet_Icc).1 hae
  have hex : ∃ t ∈ Ioo t₀ t₂, MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Fin n → ℝ) β (Icc a b) t ∧
      T.IsFutureCausal (Causal.velocity 𝓘(ℝ, Fin n → ℝ) β (Icc a b) t) := by
    by_contra hcon
    push_neg at hcon
    have hnull0 := ae_iff.1 hae'
    have : volume (Ioo t₀ t₂) = 0 := by
      refine measure_mono_null ?_ hnull0
      intro t ht hQ
      exact hcon t ht (hQ (hsub ⟨ht.1.le, ht.2.le⟩)).1 (hQ (hsub ⟨ht.1.le, ht.2.le⟩)).2
    rw [Real.volume_Ioo] at this
    simp at this
    linarith
  obtain ⟨t, ht, -, hP⟩ := hex
  have hev : β =ᶠ[𝓝[Icc a b] t] fun _ => β t₀ := by
    refine Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)) ?_
    intro s hs
    exact hc s hs
  have hv : Causal.velocity 𝓘(ℝ, Fin n → ℝ) β (Icc a b) t = 0 := by
    unfold Causal.velocity
    rw [hev.mfderivWithin_eq (hc t ⟨ht.1.le, ht.2.le⟩), mfderivWithin_const]
    rfl
  exact hP.1 hv

/-- **A short window of a no-shortcut causal curve is a radial null geodesic.** -/
theorem window_radial (T : Causal.TimeOrientation g) (x : M) {β : ℝ → M} {a b : ℝ}
    (hβ : Causal.IsFutureCausalCurve T β (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, β t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source)
    (hno : ∀ t' ∈ Icc a b, ∀ t'' ∈ Icc a b, t' ≤ t'' → β t'' ∉ Causal.chronFuture T (β t'))
    {ρ r η : ℝ} {L : NNReal}
    (hL : LipschitzOnWith L (extChartAt 𝓘(ℝ, Fin n → ℝ) x ∘ β) (Icc a b))
    (hU : UniformFutureBall T x ((extChartAt 𝓘(ℝ, Fin n → ℝ) x) '' (β '' Icc a b)) ρ r η)
    {t₀ t₂ : ℝ} (ht₀ : t₀ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) (h02 : t₀ < t₂)
    (hd : (L : ℝ) * (t₂ - t₀) < η) :
    ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)) (N : (Fin n → ℝ) → Fin n → ℝ)
      (vb : Fin n → ℝ) (lam : ℝ → ℝ),
      Lightlike.Geodesic.IsTimeBall (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target
        (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀)) ρ φ
        (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀))) r N ∧
      (∀ v ∈ ball (0 : Fin n → ℝ) r, Lightlike.Geodesic.pairing (g.coordMetric x) (φ v) (N v)
        (timeCoord T x (φ v)) < 0) ∧
      (∀ y : Fin n → ℝ, Dist.dist y (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀)) < η →
        ∃ v ∈ ball (0 : Fin n → ℝ) r, φ v = y) ∧
      vb ∈ ball (0 : Fin n → ℝ) r ∧ vb ≠ 0 ∧
      Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀)) vb vb = 0 ∧
      Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀))
        (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀))) vb < 0 ∧
      lam t₀ = 0 ∧ lam t₂ = 1 ∧ MonotoneOn lam (Icc t₀ t₂) ∧ ContinuousOn lam (Icc t₀ t₂) ∧
      ∀ t ∈ Icc t₀ t₂, extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t) = φ (lam t • vb) := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  have hsub : Icc t₀ t₂ ⊆ Icc a b := Icc_subset_Icc ht₀.1 ht₂.2
  have hp : ψ (β t₀) ∈ ψ '' (β '' Icc a b) := ⟨β t₀, ⟨t₀, ht₀, rfl⟩, rfl⟩
  obtain ⟨φ, N, hTB, hfut, hcov⟩ := hU.2.2.2 _ hp
  have hβ' : Causal.IsFutureCausalCurve T β (Icc t₀ t₂) :=
    Causal.IsCurveWith.mono hβ ht₀.1 ht₂.2 h02
  have hin : ∀ t ∈ Icc t₀ t₂, ψ (β t) ∈ φ '' ball (0 : Fin n → ℝ) r := by
    intro t ht
    have h1 := hL.dist_le_mul t (hsub ht) t₀ ht₀
    have h2 : Dist.dist (ψ (β t)) (ψ (β t₀)) < η := by
      refine lt_of_le_of_lt h1 (lt_of_le_of_lt ?_ hd)
      have : Dist.dist t t₀ ≤ t₂ - t₀ := by
        rw [Real.dist_eq, abs_le]; constructor <;> linarith [ht.1, ht.2]
      exact mul_le_mul_of_nonneg_left this L.2
    obtain ⟨v, hv, hvy⟩ := hcov _ h2
    exact ⟨v, hv, hvy⟩
  obtain ⟨lam, vb, hvb, hnull, hx0w, hl0, hl1, hmono, hcont, hlam⟩ :=
    local_null_rigidity T x h02 hβ' (fun t ht => hsrc t (hsub ht)) hTB hfut hin
      (hno t₀ ht₀ t₂ ht₂ h02.le)
  -- nonconstancy
  have hvb0 : vb ≠ 0 := by
    intro h0
    obtain ⟨K, -, hae⟩ := chart_curve_data T x hβ' (fun t ht => hsrc t (hsub ht))
    have hconst : ∀ t ∈ Icc t₀ t₂, ψ (β t) = ψ (β t₀) := by
      intro t ht
      rw [hlam t ht, hlam t₀ ⟨le_rfl, h02.le⟩, h0, smul_zero, smul_zero]
    have hex : ∃ t ∈ Ioo t₀ t₂, ∃ u' : Fin n → ℝ, HasDerivAt (ψ ∘ β) u' t ∧ u' ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hnull0 := ae_iff.1 hae
      have : volume (Ioo t₀ t₂) = 0 := by
        refine measure_mono_null ?_ hnull0
        intro t ht hQ
        obtain ⟨u', hu', hne, -⟩ := hQ ht
        exact hne (hcon t ht u' hu')
      rw [Real.volume_Ioo] at this
      simp at this
      linarith
    obtain ⟨t, ht, u', hu', hne⟩ := hex
    apply hne
    have hev : (ψ ∘ β) =ᶠ[𝓝 t] fun _ => ψ (β t₀) := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs using hconst s hs
    exact hu'.unique ((hasDerivAt_const t (ψ (β t₀))).congr_of_eventuallyEq hev)
  have hx0 : Lightlike.Geodesic.pairing (g.coordMetric x) (ψ (β t₀)) (timeCoord T x (ψ (β t₀)))
      vb < 0 := by
    refine lt_of_le_of_ne hx0w fun h0 => hvb0 ?_
    have hy : ψ (β t₀) ∈ ψ.target := ψ.map_source (hsrc t₀ ht₀)
    have hL' := g.isLorentzianCoordMetric_coordMetric x
    have hLf := Lightlike.Geodesic.isLorentzianForm_matForm hL' hy
    have hq : ∀ a b, Lightlike.Geodesic.pairing (g.coordMetric x) (ψ (β t₀)) a b =
        matForm (g.coordMetric x (ψ (β t₀))) a b := fun a b =>
      Lightlike.Geodesic.pairing_eq_matForm _ _ a b
    refine hLf.eq_zero_of_orthogonal_timelike (X := timeCoord T x (ψ (β t₀)))
      (by rw [← hq]; exact timeCoord_timelike T x hy) ?_ (by rw [← hq]; exact hnull.le)
    rw [← hq, Lightlike.Geodesic.pairing_comm hL'.1 hy]; exact h0
  exact ⟨φ, N, vb, lam, hTB, hfut, hcov, hvb, hvb0, hnull, hx0, hl0, hl1, hmono, hcont, hlam⟩

/-- The velocity at `0` within `[0, S]` is the velocity within `[0, ∞)`. -/
theorem velocity_Icc_zero {γ : ℝ → M} {S : ℝ} (hS : 0 < S) :
    Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Icc 0 S) 0 = Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Ici 0) 0 := by
  unfold Causal.velocity
  rw [← Ici_inter_Iic, mfderivWithin_inter (Iic_mem_nhds hS)]

/-- **Reachability by a null geodesic**: `β t` is the end of a null geodesic from `β a`, which
covers `β [a, t]` monotonically and has a future-directed start. -/
def GenReach (T : Causal.TimeOrientation g) (β : ℝ → M) (a t : ℝ) : Prop :=
  ∃ (γ : ℝ → M) (S : ℝ) (lam : ℝ → ℝ) (e : ℝ), 0 < S ∧ 0 < e ∧
    IsNullGeodesicOn g γ (Ioo (-e) (S + e)) ∧ γ 0 = β a ∧ γ S = β t ∧ lam a = 0 ∧ lam t = S ∧
    MonotoneOn lam (Icc a t) ∧ ContinuousOn lam (Icc a t) ∧ (∀ s ∈ Icc a t, β s = γ (lam s)) ∧
    g.g (γ 0) (Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Ici 0) 0) (T.X (γ 0)) < 0

/-- **The first step: a window starting at `β a` gives a null geodesic from `β a`.** -/
theorem genReach_of_window (T : Causal.TimeOrientation g) (x : M) {β : ℝ → M} {a t₂ : ℝ}
    (hsrc : ∀ t ∈ Icc a t₂, β t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) (h02 : a < t₂)
    {ρ r : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {N : (Fin n → ℝ) → Fin n → ℝ}
    {vb : Fin n → ℝ} {lam : ℝ → ℝ}
    (hTB : Lightlike.Geodesic.IsTimeBall (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a)) ρ φ
      (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a))) r N)
    (hfutN : ∀ v ∈ ball (0 : Fin n → ℝ) r, Lightlike.Geodesic.pairing (g.coordMetric x) (φ v) (N v)
      (timeCoord T x (φ v)) < 0)
    (hvb : vb ∈ ball (0 : Fin n → ℝ) r) (hvb0 : vb ≠ 0)
    (hnull : Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a))
      vb vb = 0)
    (hx0 : Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a))
      (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β a))) vb < 0)
    (hl0 : lam a = 0) (hl1 : lam t₂ = 1) (hmono : MonotoneOn lam (Icc a t₂))
    (hcont : ContinuousOn lam (Icc a t₂))
    (hlam : ∀ t ∈ Icc a t₂, extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t) = φ (lam t • vb)) :
    GenReach T β a t₂ := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  obtain ⟨lamb, hlamb1, hnullg⟩ := radial_isNullGeodesicOn T x hTB hvb hvb0 hnull
  have hfut := radial_isFutureNullGeodesicOn T x hTB hfutN hvb hvb0 hnull hx0
  have haI : a ∈ Icc a t₂ := ⟨le_rfl, h02.le⟩
  have hβs : ∀ t ∈ Icc a t₂, ψ.symm (φ (lam t • vb)) = β t := fun t ht => by
    rw [← hlam t ht]; exact ψ.left_inv (hsrc t ht)
  refine ⟨fun s => ψ.symm (φ (s • vb)), 1, lam, lamb - 1, one_pos, by linarith, ?_, ?_, ?_, hl0,
    hl1, hmono, hcont, fun s hs => (hβs s hs).symm, ?_⟩
  · refine hnullg.mono ?_
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  · simp only [zero_smul]
    rw [hTB.chart.map_zero]
    exact ψ.left_inv (hsrc a haI)
  · simp only [one_smul]
    have := hβs t₂ ⟨h02.le, le_rfl⟩
    rw [hl1, one_smul] at this
    exact this
  · have h1 := hfut.2 0 ⟨le_rfl, zero_le_one⟩
    rw [velocity_Icc_zero one_pos] at h1
    exact h1

end Lightlike.Penrose
