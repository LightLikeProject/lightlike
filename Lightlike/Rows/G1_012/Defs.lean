import Lightlike.Spacetime.Curvature
import Lightlike.Spacetime.GeodesicChartChange
import Lightlike.Spacetime.Lorentzian

/-!
# Geodesic curves and null geodesic completeness on a manifold (G1-012)

The library has geodesics only in coordinates (`Lightlike.Geodesic.IsGeodesicOn g γ w I` for a coordinate metric
`g : ℝⁿ → Matrix`). Penrose's theorem is a statement about null geodesics of a spacetime, so this file lifts the
chart notion to a manifold `M` modelled on `ℝⁿ` with a Lorentzian metric `g`, by the preferred chart at each point
of the curve (`NondegMetric.coordMetric`).

* `IsGeodesicCurveOn g γ J`: near every `t ∈ J`, the chart expression of `γ` in the chart at `γ t` is a geodesic of
  the coordinate metric `g.coordMetric (γ t)`. (By `IsGeodesicOn.lift_chartChange` / `map_chartChange` the choice of
  chart does not matter; that independence is not reproved here.)
* `IsNullGeodesicOn g γ J`: moreover the velocity is a non-zero null vector.
* `NullGeodesicallyComplete g`: every null geodesic defined on a bounded open interval extends to a null geodesic
  on all of `ℝ` (affine parameter).

Source: Senovilla–Garfinkle 2015 (Theorem 2 statement uses "null geodesically incomplete"); Hawking–Ellis 1973,
section 8.1.
-/

open Set Filter Topology Manifold
open scoped ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- A curve `γ : ℝ → M` is a **geodesic on `J`** if near each `t ∈ J` its expression in the chart at `γ t` is a
geodesic (with some velocity `w`) of the coordinate metric of `g` in that chart. -/
def IsGeodesicCurveOn (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ (w : ℝ → Fin n → ℝ) (O : Set ℝ), O ∈ 𝓝 t ∧
    (∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).source) ∧
    Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ t))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) w O

/-- A curve is a **null geodesic on `J`** if it is a geodesic on `J` whose velocity (in the chart at each `γ t`)
is a non-zero null vector. (The metric speed is constant along a geodesic, so this holds along the whole curve.) -/
def IsNullGeodesicOn (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∃ (w : ℝ → Fin n → ℝ) (O : Set ℝ), O ∈ 𝓝 t ∧
    (∀ s ∈ O, γ s ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t)).source) ∧
    Lightlike.Geodesic.IsGeodesicOn (g.coordMetric (γ t))
      (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ s)) w O ∧
    w t ≠ 0 ∧ Lightlike.bil (g.coordMetric (γ t) (extChartAt 𝓘(ℝ, Fin n → ℝ) (γ t) (γ t))) (w t) (w t) = 0

/-- **Null geodesic completeness**: every null geodesic on a bounded open interval `(a, b)` extends to a null
geodesic on `ℝ`. -/
def NullGeodesicallyComplete (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) : Prop :=
  ∀ (γ : ℝ → M) (a b : ℝ), a < b → IsNullGeodesicOn g γ (Ioo a b) →
    ∃ γ' : ℝ → M, IsNullGeodesicOn g γ' univ ∧ EqOn γ γ' (Ioo a b)

/-- **Null geodesic incompleteness** (as in Penrose's theorem): some null geodesic does not extend. -/
def NullGeodesicallyIncomplete (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) : Prop :=
  ¬ NullGeodesicallyComplete g

variable {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} {γ : ℝ → M} {J J' : Set ℝ}

/-- A null geodesic is a geodesic. -/
theorem IsNullGeodesicOn.isGeodesicCurveOn (h : IsNullGeodesicOn g γ J) : IsGeodesicCurveOn g γ J :=
  fun t ht => by
    obtain ⟨w, O, hO, hs, hg, -⟩ := h t ht
    exact ⟨w, O, hO, hs, hg⟩

/-- Restriction of a geodesic to a smaller set. -/
theorem IsGeodesicCurveOn.mono (h : IsGeodesicCurveOn g γ J) (hJ : J' ⊆ J) : IsGeodesicCurveOn g γ J' :=
  fun t ht => h t (hJ ht)

/-- Restriction of a null geodesic to a smaller set. -/
theorem IsNullGeodesicOn.mono (h : IsNullGeodesicOn g γ J) (hJ : J' ⊆ J) : IsNullGeodesicOn g γ J' :=
  fun t ht => h t (hJ ht)

/-- If `g` is null geodesically complete and `γ` is a null geodesic on a bounded open interval, then `γ` is the
restriction of a null geodesic on `ℝ`. -/
theorem NullGeodesicallyComplete.extend (hc : NullGeodesicallyComplete g) {a b : ℝ} (hab : a < b)
    (h : IsNullGeodesicOn g γ (Ioo a b)) :
    ∃ γ' : ℝ → M, IsNullGeodesicOn g γ' univ ∧ EqOn γ γ' (Ioo a b) :=
  hc γ a b hab h

end Lightlike.Penrose
