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

/-- The preimage of `(-L, L)` under `σ ↦ c σ + d`, `c > 0`, is an open interval. -/
theorem preimage_affine_Ioo {c d L : ℝ} (hc : 0 < c) :
    (fun σ : ℝ => c * σ + d) ⁻¹' Ioo (-L) L = Ioo ((-L - d) / c) ((L - d) / c) := by
  ext σ
  simp only [mem_preimage, mem_Ioo]
  rw [div_lt_iff₀ hc, lt_div_iff₀ hc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

set_option maxHeartbeats 1600000 in
/-- **Extending a null geodesic along an overlapping window** (the inductive step of the chain). -/
theorem genReach_extend (T : Causal.TimeOrientation g) (x : M) {β : ℝ → M} {a b t₀ t₁ t₂ : ℝ}
    (hβ : Causal.IsFutureCausalCurve T β (Icc a b)) (hat₀ : a ≤ t₀) (h01 : t₀ < t₁)
    (h12 : t₁ < t₂) (ht₂ : t₂ ≤ b)
    (hsrc : ∀ t ∈ Icc t₀ t₂, β t ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source)
    {ρ r : ℝ} (hrρ : r < ρ)
    {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)} {N : (Fin n → ℝ) → Fin n → ℝ}
    {vb : Fin n → ℝ} {lam : ℝ → ℝ}
    (hTB : Lightlike.Geodesic.IsTimeBall (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀)) ρ φ
      (timeCoord T x (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀))) r N)
    (hvb : vb ∈ ball (0 : Fin n → ℝ) r) (hvb0 : vb ≠ 0)
    (hnull : Lightlike.Geodesic.pairing (g.coordMetric x) (extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t₀))
      vb vb = 0)
    (hl0 : lam t₀ = 0) (hl1 : lam t₂ = 1) (hmono : MonotoneOn lam (Icc t₀ t₂))
    (hcont : ContinuousOn lam (Icc t₀ t₂))
    (hlam : ∀ t ∈ Icc t₀ t₂, extChartAt 𝓘(ℝ, Fin n → ℝ) x (β t) = φ (lam t • vb))
    (hreach : GenReach T β a t₁) : GenReach T β a t₂ := by
  obtain ⟨γ, S, lamγ, e, hS, he, hnullγ, hγ0, hγS, hl0γ, hlSγ, hmonoγ, hcontγ, hβγ, hfut0⟩ := hreach
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  have hb₁ : t₁ ≤ b := h12.le.trans ht₂
  have hsubab : ∀ {u v : ℝ}, a ≤ u → v ≤ b → Icc u v ⊆ Icc a b := fun hu hv =>
    Icc_subset_Icc hu hv
  have hsrc1 : ∀ t ∈ Icc t₀ t₁, β t ∈ ψ.source := fun t ht =>
    hsrc t ⟨ht.1, ht.2.trans h12.le⟩
  have ht₀a : t₀ ∈ Icc a t₁ := ⟨hat₀, h01.le⟩
  have ht₁a : t₁ ∈ Icc a t₁ := ⟨(hat₀.trans h01.le), le_rfl⟩
  have hτ0 : 0 ≤ lamγ t₀ := by
    have := hmonoγ ⟨le_rfl, hat₀.trans h01.le⟩ ht₀a hat₀
    rwa [hl0γ] at this
  have hτS : lamγ t₀ ≤ S := by
    have := hmonoγ ht₀a ht₁a h01.le
    rwa [hlSγ] at this
  have hnc : ¬ ∀ t ∈ Icc t₀ t₁, β t = β t₀ :=
    Causal_not_const hβ (hsubab hat₀ hb₁) h01
  have hτlt : lamγ t₀ < S := by
    by_contra hcon
    have hτ : lamγ t₀ = S := le_antisymm hτS (not_lt.1 hcon)
    refine hnc fun s hs => ?_
    have hs1 : lamγ s = S := by
      have h1 := hmonoγ ht₀a ⟨hat₀.trans hs.1, hs.2⟩ hs.1
      have h2 := hmonoγ ⟨hat₀.trans hs.1, hs.2⟩ ht₁a hs.2
      linarith
    rw [hβγ s ⟨hat₀.trans hs.1, hs.2⟩, hβγ t₀ ht₀a, hs1, hτ]
  have hS₁0 : 0 ≤ lam t₁ := by
    have := hmono ⟨le_rfl, h01.le.trans h12.le⟩ ⟨h01.le, h12.le⟩ h01.le
    rwa [hl0] at this
  have hS₁le : lam t₁ ≤ 1 := by
    have := hmono ⟨h01.le, h12.le⟩ ⟨h01.le.trans h12.le, le_rfl⟩ h12.le
    rwa [hl1] at this
  have hS₁pos : 0 < lam t₁ := by
    refine lt_of_le_of_ne hS₁0 fun h0 => hnc fun s hs => ?_
    have hs0 : lam s = 0 := by
      have h1 := hmono ⟨le_rfl, h01.le.trans h12.le⟩ ⟨hs.1, hs.2.trans h12.le⟩ hs.1
      have h2 := hmono ⟨hs.1, hs.2.trans h12.le⟩ ⟨h01.le, h12.le⟩ hs.2
      linarith
    have e1 := hlam s ⟨hs.1, hs.2.trans h12.le⟩
    have e0 := hlam t₀ ⟨le_rfl, h01.le.trans h12.le⟩
    rw [hs0, zero_smul] at e1
    rw [hl0, zero_smul] at e0
    exact ψ.injOn (hsrc1 s hs) (hsrc1 t₀ ⟨le_rfl, h01.le⟩) (by rw [e1, e0])
  set τ : ℝ := lamγ t₀ with hτdef
  set S₁ : ℝ := lam t₁ with hS₁def
  set dS : ℝ := S - τ with hdS
  have hdSpos : 0 < dS := by rw [hdS]; linarith
  have hsub01 : Icc t₀ t₁ ⊆ Icc a t₁ := Icc_subset_Icc hat₀ le_rfl
  have hivt : ∀ σ ∈ Icc τ S, ∃ s ∈ Icc t₀ t₁, lamγ s = σ := by
    intro σ hσ
    have := intermediate_value_Icc h01.le (hcontγ.mono hsub01)
    rw [hlSγ] at this
    obtain ⟨s, hs, hsσ⟩ := this hσ
    exact ⟨s, hs, hsσ⟩
  -- arc points: in the chart source and in the radial image
  have harc : ∀ σ ∈ Icc τ S, γ σ ∈ ψ.source ∧ ψ (γ σ) ∈ φ '' ball (0 : Fin n → ℝ) r := by
    intro σ hσ
    obtain ⟨s, hs, hsσ⟩ := hivt σ hσ
    have hβs : β s = γ σ := by rw [hβγ s (hsub01 hs), hsσ]
    have hsrc_s : β s ∈ ψ.source := hsrc1 s hs
    refine ⟨hβs ▸ hsrc_s, ?_⟩
    rw [← hβs, hlam s ⟨hs.1, hs.2.trans h12.le⟩]
    refine ⟨lam s • vb, ?_, rfl⟩
    have h0 : 0 ≤ lam s := by
      have := hmono ⟨le_rfl, h01.le.trans h12.le⟩ ⟨hs.1, hs.2.trans h12.le⟩ hs.1
      rwa [hl0] at this
    have h1 : lam s ≤ 1 := by
      have := hmono ⟨hs.1, hs.2.trans h12.le⟩ ⟨h01.le.trans h12.le, le_rfl⟩
        (hs.2.trans h12.le)
      rwa [hl1] at this
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
    have := mem_ball_zero_iff.1 hvb
    nlinarith [norm_nonneg vb]
  -- the chart expression of `γ` along the arc is a geodesic of the chart at `x`
  set J₁ : Set ℝ := Ioo (-e) (S + e) with hJ₁
  have hJ₁o : IsOpen J₁ := isOpen_Ioo
  have hγgeo : IsGeodesicCurveOn g γ J₁ := hnullγ.isGeodesicCurveOn
  have hγc : ContinuousOn γ J₁ := fun σ hσ =>
    (IsGeodesicCurveOn.continuousAt g hγgeo hσ).continuousWithinAt
  set Y : Set ℝ := J₁ ∩ γ ⁻¹' ψ.source with hY
  have hYo : IsOpen Y := hγc.isOpen_inter_preimage hJ₁o (isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x)
  have hτJ : ∀ σ ∈ Icc τ S, σ ∈ J₁ := fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hY' : ∀ σ ∈ Icc τ S, σ ∈ Y := fun σ hσ => ⟨hτJ σ hσ, (harc σ hσ).1⟩
  set aff : ℝ → ℝ := fun y => dS * y + τ with haff
  have haffc : Continuous aff := by fun_prop
  set Oarc : Set ℝ := aff ⁻¹' Y with hOarc
  have hOarco : IsOpen Oarc := hYo.preimage haffc
  have hIcc01 : Icc (0 : ℝ) 1 ⊆ Oarc := fun y hy => hY' (aff y) ⟨by simp only [haff]; nlinarith [hy.1],
    by simp only [haff, hdS]; nlinarith [hy.2]⟩
  have hγ'null := hnullγ.comp_affine hdSpos.ne' τ
  have hγ'geo : IsGeodesicCurveOn g (fun y => γ (dS * y + τ)) Oarc :=
    (hγ'null.isGeodesicCurveOn).mono (fun y hy => hy.1)
  obtain ⟨w, hwgeo⟩ := geodesicOn_chart_of_curve g x hOarco (fun y hy => hy.2) hγ'geo
  have hg1 := (g.isLorentzianCoordMetric_coordMetric x).1
  have hγτ : γ τ = β t₀ := (hβγ t₀ ht₀a).symm
  have hΛ0 : ψ (γ (dS * 0 + τ)) = ψ (β t₀) := by rw [mul_zero, zero_add, hγτ]
  have hrad := hTB.chart.geodesic_eq_radial hg1 hTB.pos hrρ hOarco hIcc01 hwgeo hΛ0 (fun y hy => by
    have := harc (aff y) ⟨by simp only [haff]; nlinarith [hy.1],
      by simp only [haff, hdS]; nlinarith [hy.2]⟩
    exact this.2)
  set ξ : Fin n → ℝ := w 0 with hξ
  have hξS : ξ = S₁ • vb := by
    obtain ⟨hb1, h1, -⟩ := hrad 1 ⟨zero_le_one, le_rfl⟩
    have e1 : ψ (γ (dS * 1 + τ)) = φ (S₁ • vb) := by
      have : dS * 1 + τ = S := by rw [hdS]; ring
      rw [this, hγS, hlam t₁ ⟨h01.le, h12.le⟩]
    rw [e1, one_smul] at h1
    have hSb : S₁ • vb ∈ ball (0 : Fin n → ℝ) ρ := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hS₁0]
      have := mem_ball_zero_iff.1 hvb
      nlinarith [norm_nonneg vb]
    have hξb : ξ ∈ ball (0 : Fin n → ℝ) ρ := by
      have := ball_subset_ball hrρ.le (one_smul ℝ ξ ▸ hb1)
      exact this
    exact (φ.injOn (by rw [hTB.chart.source_eq]; exact hξb) (by rw [hTB.chart.source_eq]; exact hSb)
      h1.symm)
  have hΛ : ∀ y ∈ Icc (0 : ℝ) 1, ψ (γ (dS * y + τ)) = φ ((y * S₁) • vb) := by
    intro y hy
    obtain ⟨-, h1, -⟩ := hrad y hy
    rw [h1, hξS, smul_smul]
  -- the radial continuation
  obtain ⟨lamb, hlamb1, hΓnull⟩ := radial_isNullGeodesicOn T x hTB hvb hvb0 hnull
  set Γ : ℝ → M := fun s => ψ.symm (φ (s • vb)) with hΓ
  set c : ℝ := S₁ / dS with hc
  have hcpos : 0 < c := div_pos hS₁pos hdSpos
  set d : ℝ := -c * τ with hd
  set γ₂ : ℝ → M := fun σ => Γ (c * σ + d) with hγ₂
  have hγ₂null := hΓnull.comp_affine hcpos.ne' d
  rw [preimage_affine_Ioo hcpos] at hγ₂null
  set lo : ℝ := (-lamb - d) / c with hlo
  set hi : ℝ := (lamb - d) / c with hhi
  have hJ₂o : IsOpen (Ioo lo hi) := isOpen_Ioo
  have hcσ : ∀ σ, c * σ + d = c * (σ - τ) := fun σ => by rw [hd]; ring
  -- agreement on the arc
  have hag_arc : ∀ σ ∈ Icc τ S, γ σ = γ₂ σ := by
    intro σ hσ
    set y : ℝ := (σ - τ) / dS with hy
    have hy01 : y ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [hσ.1]) hdSpos.le
      · rw [hy, div_le_one hdSpos]; rw [hdS]; linarith [hσ.2]
    have hσy : dS * y + τ = σ := by rw [hy]; field_simp; ring
    have h1 := hΛ y hy01
    rw [hσy] at h1
    have hcy : c * σ + d = y * S₁ := by
      rw [hcσ, hc, hy]; field_simp
    have hsrcσ := (harc σ hσ).1
    calc γ σ = ψ.symm (ψ (γ σ)) := (ψ.left_inv hsrcσ).symm
      _ = ψ.symm (φ ((y * S₁) • vb)) := by rw [h1]
      _ = γ₂ σ := by simp only [hγ₂, hΓ, hcy]
  -- agreement on the whole overlap, by uniqueness of geodesic curves
  have hγ₂geo : IsGeodesicCurveOn g γ₂ (Ioo lo hi) := hγ₂null.isGeodesicCurveOn
  set σ₀ : ℝ := (τ + S) / 2 with hσ₀
  have hσ₀I : σ₀ ∈ Ioo τ S := ⟨by rw [hσ₀]; linarith, by rw [hσ₀]; linarith⟩
  have hσ₀J₁ : σ₀ ∈ J₁ := hτJ σ₀ ⟨hσ₀I.1.le, hσ₀I.2.le⟩
  have hlo' : lo = τ - lamb * dS / S₁ := by
    rw [hlo, hd, hc]; field_simp; ring
  have hhi' : hi = τ + lamb * dS / S₁ := by
    rw [hhi, hd, hc]; field_simp; ring
  have hdS1 : dS ≤ dS / S₁ := by
    rw [le_div_iff₀ hS₁pos]; nlinarith
  have hlt1 : dS < lamb * dS / S₁ := by
    have : lamb * dS / S₁ = lamb * (dS / S₁) := by ring
    rw [this]
    nlinarith
  have hlop : lamb * dS / S₁ > 0 := by positivity
  have hloτ : lo < τ := by rw [hlo']; linarith
  have hSh : S < hi := by rw [hhi']; rw [hdS] at hlt1; linarith
  have hσ₀J₂ : σ₀ ∈ Ioo lo hi := ⟨by linarith [hσ₀I.1], by linarith [hσ₀I.2]⟩
  have hJ₁₂c : IsPreconnected (J₁ ∩ Ioo lo hi) :=
    (ordConnected_Ioo.inter ordConnected_Ioo).isPreconnected
  have hJ₁₂o : IsOpen (J₁ ∩ Ioo lo hi) := hJ₁o.inter hJ₂o
  have hag : EqOn γ γ₂ (J₁ ∩ Ioo lo hi) := by
    refine IsGeodesicCurveOn.eqOn g hJ₁₂o hJ₁₂c (hγgeo.mono inter_subset_left)
      (hγ₂geo.mono inter_subset_right) ⟨hσ₀J₁, hσ₀J₂⟩ (hag_arc σ₀ ⟨hσ₀I.1.le, hσ₀I.2.le⟩) ?_
    have hev : γ =ᶠ[𝓝 σ₀] γ₂ := by
      filter_upwards [Ioo_mem_nhds hσ₀I.1 hσ₀I.2] with σ hσ using hag_arc σ ⟨hσ.1.le, hσ.2.le⟩
    exact Filter.EventuallyEq.deriv_eq (hev.mono fun σ hσ => by simp only [hσ])
  obtain ⟨γN, hglue, hγN₁, hγN₂⟩ := hnullγ.exists_union hγ₂null hJ₁o hJ₂o hag
  set S' : ℝ := τ + dS / S₁ with hS'
  have hdSS : 0 < dS / S₁ := div_pos hdSpos hS₁pos
  have hS'pos : 0 < S' := by rw [hS']; linarith
  have hSS' : S ≤ S' := by rw [hS', hdS] at *; linarith
  have hS'hi : S' < hi := by
    rw [hhi', hS']
    have : lamb * dS / S₁ = lamb * (dS / S₁) := by ring
    rw [this]; nlinarith
  set e' : ℝ := min e (hi - S') with he'
  have he'pos : 0 < e' := lt_min he (by linarith)
  have hsubJ : Ioo (-e') (S' + e') ⊆ J₁ ∪ Ioo lo hi := by
    intro σ hσ
    by_cases h1 : σ < S + e
    · exact Or.inl ⟨by linarith [hσ.1, min_le_left e (hi - S')], h1⟩
    · refine Or.inr ⟨by linarith [not_lt.1 h1], by linarith [hσ.2, min_le_right e (hi - S')]⟩
  have hnew : IsNullGeodesicOn g γN (Ioo (-e') (S' + e')) := hglue.mono hsubJ
  have hS'J₂ : S' ∈ Ioo lo hi := ⟨by linarith, hS'hi⟩
  -- the new reparametrisation
  have hJ0S : ∀ σ ∈ Icc 0 S, σ ∈ J₁ := fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  set lamN : ℝ → ℝ := fun s => if s ≤ t₁ then lamγ s else τ + dS * lam s / S₁ with hlamN
  have hlamγb : ∀ s ∈ Icc a t₁, lamγ s ∈ Icc 0 S := fun s hs =>
    ⟨by have := hmonoγ ⟨le_rfl, hat₀.trans h01.le⟩ hs hs.1; rwa [hl0γ] at this,
     by have := hmonoγ hs ht₁a hs.2; rwa [hlSγ] at this⟩
  have hlamb2 : ∀ s ∈ Icc t₁ t₂, S ≤ τ + dS * lam s / S₁ ∧ τ + dS * lam s / S₁ ≤ S' := by
    intro s hs
    have h1 : S₁ ≤ lam s := by
      have := hmono ⟨h01.le, h12.le⟩ ⟨h01.le.trans hs.1, hs.2⟩ hs.1
      exact this
    have h2 : lam s ≤ 1 := by
      have := hmono ⟨h01.le.trans hs.1, hs.2⟩ ⟨h01.le.trans h12.le, le_rfl⟩ hs.2
      rwa [hl1] at this
    constructor
    · have : dS ≤ dS * lam s / S₁ := by rw [le_div_iff₀ hS₁pos]; nlinarith
      rw [hdS] at this ⊢; linarith
    · have : dS * lam s / S₁ ≤ dS / S₁ := by
        rw [div_le_div_iff_of_pos_right hS₁pos]; nlinarith
      rw [hS']; linarith
  refine ⟨γN, S', lamN, e', hS'pos, he'pos, hnew, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hγN₁ 0 ⟨by linarith, by linarith⟩, hγ0]
  · rw [hγN₂ S' hS'J₂]
    simp only [hγ₂, hΓ]
    have h1 : c * S' + d = 1 := by
      rw [hcσ, hS', hc]; field_simp; ring
    rw [h1, one_smul]
    have := hlam t₂ ⟨h01.le.trans h12.le, le_rfl⟩
    rw [hl1, one_smul] at this
    rw [← this]
    exact ψ.left_inv (hsrc t₂ ⟨h01.le.trans h12.le, le_rfl⟩)
  · have ha1 : a ≤ t₁ := hat₀.trans h01.le
    simp only [hlamN, ha1, ite_true]
    exact hl0γ
  · simp only [hlamN, not_le.2 h12, ite_false, hl1, hS']
    field_simp
  · intro s hs t ht hst
    simp only [hlamN]
    by_cases hs1 : s ≤ t₁
    · by_cases ht1 : t ≤ t₁
      · simp only [hs1, ht1, ite_true]
        exact hmonoγ ⟨hs.1, hs1⟩ ⟨ht.1, ht1⟩ hst
      · simp only [hs1, ht1, ite_true, ite_false]
        have h1 : lamγ s ≤ S := (hlamγb s ⟨hs.1, hs1⟩).2
        have h2 := (hlamb2 t ⟨(not_le.1 ht1).le, ht.2⟩).1
        linarith
    · have ht1 : ¬ t ≤ t₁ := fun h => hs1 (hst.trans h)
      simp only [hs1, ht1, ite_false]
      have hs' : s ∈ Icc t₀ t₂ := ⟨(h01.le.trans (not_le.1 hs1).le), hs.2⟩
      have ht' : t ∈ Icc t₀ t₂ := ⟨(h01.le.trans (not_le.1 ht1).le), ht.2⟩
      have := hmono hs' ht' hst
      have : dS * lam s / S₁ ≤ dS * lam t / S₁ := by
        rw [div_le_div_iff_of_pos_right hS₁pos]
        exact mul_le_mul_of_nonneg_left this hdSpos.le
      linarith
  · have hsplit : Icc a t₂ = Icc a t₁ ∪ Icc t₁ t₂ :=
      (Icc_union_Icc_eq_Icc (hat₀.trans h01.le) h12.le).symm
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine hcontγ.congr fun s hs => ?_
      simp only [hlamN, hs.2, ite_true]
    · have hc2 : ContinuousOn (fun s => τ + dS * lam s / S₁) (Icc t₁ t₂) :=
        continuousOn_const.add ((continuousOn_const.mul
          (hcont.mono (Icc_subset_Icc h01.le le_rfl))).div_const _)
      refine hc2.congr fun s hs => ?_
      simp only [hlamN]
      by_cases hs1 : s ≤ t₁
      · have hst : s = t₁ := le_antisymm hs1 hs.1
        subst hst
        simp only [hs1, ite_true]
        have : lamγ s = S := hlSγ
        rw [this, show lam s = S₁ from rfl, mul_div_assoc, div_self hS₁pos.ne', mul_one, hdS]
        ring
      · simp only [hs1, ite_false]
  · intro s hs
    by_cases hs1 : s ≤ t₁
    · have hsm : lamN s = lamγ s := by simp only [hlamN, hs1, ite_true]
      rw [hsm, hγN₁ _ (hJ0S _ (hlamγb s ⟨hs.1, hs1⟩))]
      exact hβγ s ⟨hs.1, hs1⟩
    · have hs1' : t₁ < s := not_le.1 hs1
      have hsm : lamN s = τ + dS * lam s / S₁ := by simp only [hlamN, hs1, ite_false]
      have hb := hlamb2 s ⟨hs1'.le, hs.2⟩
      have hmem : lamN s ∈ Ioo lo hi := by
        rw [hsm]
        exact ⟨by linarith [hb.1, hSh, hloτ, hτS], by linarith [hb.2, hS'hi]⟩
      rw [hγN₂ _ hmem]
      simp only [hγ₂, hΓ]
      have h1 : c * lamN s + d = lam s := by
        rw [hcσ, hsm, hc]; field_simp; ring
      rw [h1]
      have := hlam s ⟨h01.le.trans hs1'.le, hs.2⟩
      rw [← this]
      exact (ψ.left_inv (hsrc s ⟨h01.le.trans hs1'.le, hs.2⟩)).symm ▸ rfl
  · -- the start stays future directed
    have hγN0 : γN 0 = γ 0 := hγN₁ 0 ⟨by linarith, by linarith⟩
    have hev : γN =ᶠ[𝓝[Ici 0] 0] γ := by
      refine mem_nhdsWithin_of_mem_nhds ?_
      filter_upwards [Ioo_mem_nhds (by linarith : -e < 0) (by linarith : (0 : ℝ) < S + e)] with σ hσ
      exact hγN₁ σ hσ
    have hvel : Causal.velocity 𝓘(ℝ, Fin n → ℝ) γN (Ici 0) 0 =
        Causal.velocity 𝓘(ℝ, Fin n → ℝ) γ (Ici 0) 0 := by
      unfold Causal.velocity
      rw [hev.mfderivWithin_eq hγN0]
      rfl
    have key : ∀ (p q : M) (h : p = q) (v : Fin n → ℝ), g.g p v (T.X p) = g.g q v (T.X q) := by
      intro p q h v; subst h; rfl
    refine (key _ _ hγN0 _).trans_lt ?_
    rw [hvel]
    exact hfut0

end Lightlike.Penrose
