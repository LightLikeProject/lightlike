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
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}

/-- **Uniform future time balls over a set `S` of chart points**: fixed radii `ρ`, `r`, `η` such
that every `p ∈ S` has a future time ball of radius `r` whose image contains the `η`-ball about `p`. -/
def UniformFutureBall (T : Causal.TimeOrientation g) (x : M) (S : Set (Fin n → ℝ)) (ρ r η : ℝ) :
    Prop :=
  0 < r ∧ r ≤ ρ ∧ 0 < η ∧ ∀ p ∈ S, ∃ (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ))
    (N : (Fin n → ℝ) → Fin n → ℝ), Lightlike.Geodesic.IsTimeBall (g.coordMetric x)
      (extChartAt 𝓘(ℝ, Fin n → ℝ) x).target p ρ φ (timeCoord T x p) r N ∧
    (∀ v ∈ ball (0 : Fin n → ℝ) r, Lightlike.Geodesic.pairing (g.coordMetric x) (φ v) (N v)
      (timeCoord T x (φ v)) < 0) ∧
    ∀ y : Fin n → ℝ, Dist.dist y p < η → ∃ v ∈ ball (0 : Fin n → ℝ) r, φ v = y

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

end Lightlike.Penrose
