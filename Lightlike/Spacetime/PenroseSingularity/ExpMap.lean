import Lightlike.Spacetime.PenroseSingularity.GeodesicUnique

/-!
# The exponential map of a manifold (G1-012, G1-006 manifold lift)

A tangent vector at `p` is given by its coordinates `v` in the preferred chart at `p` (`extChartAt p`); this is the
convention of `IsGeodesicCurveOn`, which reads a curve in the chart at each of its points.

* `ExpDomain g`: the pairs `(p, v)` for which there is a geodesic curve `γ` on an open interval `(a, b) ∋ 0, 1` with
  `γ 0 = p` and chart velocity `v` at `0`.
* `expMap g (p, v)`: `γ 1` for such a `γ`; well defined by `IsGeodesicCurveOn.eqOn` (needs `[T2Space M]`), and `p`
  outside the domain.
* `expMap_eq`: any such `γ` gives `expMap g (p, v) = γ 1`. `expMap_zero`: `exp_p(0) = p`.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The domain of the exponential map. -/
def ExpDomain : Set (M × (Fin n → ℝ)) :=
  {q | ∃ (a b : ℝ) (γ : ℝ → M), a < 0 ∧ 1 < b ∧ IsGeodesicCurveOn g γ (Ioo a b) ∧ γ 0 = q.1 ∧
    deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) q.1 (γ s)) 0 = q.2}

/-- The exponential map: the value at `1` of the geodesic curve with initial data `q`, and the base point outside the
domain. -/
def expMap (q : M × (Fin n → ℝ)) : M := by
  classical
  exact if h : q ∈ ExpDomain g then (Classical.choose (Classical.choose_spec (Classical.choose_spec h))) 1 else q.1

/-- **The exponential map is the value at `1` of any geodesic curve with the given initial data.** -/
theorem expMap_eq_of [T2Space M] {q : M × (Fin n → ℝ)} {a b : ℝ} {γ : ℝ → M} (ha : a < 0) (hb : 1 < b)
    (hγ : IsGeodesicCurveOn g γ (Ioo a b)) (h0 : γ 0 = q.1)
    (h1 : deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) q.1 (γ s)) 0 = q.2) :
    expMap g q = γ 1 := by
  have hq : q ∈ ExpDomain g := ⟨a, b, γ, ha, hb, hγ, h0, h1⟩
  unfold expMap
  rw [dite_eq_left_of_eq_true (eq_true hq)]
  obtain ⟨ha₀, hb₀, hγ₀, h00, h10⟩ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hq))
  set a₀ := Classical.choose hq
  set b₀ := Classical.choose (Classical.choose_spec hq)
  set γ₀ := Classical.choose (Classical.choose_spec (Classical.choose_spec hq))
  have hsub : Ioo (max a a₀) (min b b₀) ⊆ Ioo a b := Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hsub₀ : Ioo (max a a₀) (min b b₀) ⊆ Ioo a₀ b₀ := Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have h0mem : (0 : ℝ) ∈ Ioo (max a a₀) (min b b₀) := ⟨max_lt ha ha₀, lt_min (by linarith) (by linarith)⟩
  have h1mem : (1 : ℝ) ∈ Ioo (max a a₀) (min b b₀) := ⟨max_lt (by linarith) (by linarith), lt_min hb hb₀⟩
  have heq := IsGeodesicCurveOn.eqOn g isOpen_Ioo isPreconnected_Ioo (hγ₀.mono hsub₀) (hγ.mono hsub) h0mem
    (by rw [h00, h0]) (by rw [h00, h10]; simpa [h00, h0] using h1.symm)
  exact heq h1mem

/-- A constant curve is a geodesic curve. -/
theorem isGeodesicCurveOn_const (p : M) (J : Set ℝ) : IsGeodesicCurveOn g (fun _ => p) J := by
  intro t ht
  refine ⟨fun _ => 0, univ, univ_mem, fun s _ => mem_extChartAt_source p, ?_, ?_⟩
  · intro s _
    exact hasDerivAt_const s _
  · intro s _
    have h0 : Lightlike.Geodesic.accel (g.coordMetric p) (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) 0 = 0 := by
      have := Lightlike.Geodesic.accel_smul (g.coordMetric p) (extChartAt 𝓘(ℝ, Fin n → ℝ) p p) 0 0
      simpa using this
    show HasDerivAt (fun _ => (0 : Fin n → ℝ)) (Lightlike.Geodesic.accel (g.coordMetric p) _ 0) s
    rw [h0]
    exact hasDerivAt_const s _

/-- **Rescaling a geodesic curve**: `s ↦ γ (c s)` is a geodesic curve on `{s | c s ∈ J}`. -/
theorem IsGeodesicCurveOn.scale {γ : ℝ → M} {J : Set ℝ} (h : IsGeodesicCurveOn g γ J) (c : ℝ) :
    IsGeodesicCurveOn g (fun s => γ (c * s)) ((fun s => c * s) ⁻¹' J) := by
  intro t ht
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := h (c * t) ht
  refine ⟨fun s => c • w (c * s), (fun s => c * s) ⁻¹' O, ?_, fun s hs => hsrc _ hs, hgeo.scale c⟩
  exact (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hO

/-- `exp_p(0) = p`. -/
theorem expMap_zero [T2Space M] (p : M) : expMap g (p, 0) = p := by
  have := expMap_eq_of g (q := (p, 0)) (a := -1) (b := 2) (γ := fun _ => p) (by norm_num) (by norm_num)
    (isGeodesicCurveOn_const g p _) rfl (by simp)
  simpa using this

/-- **Homogeneity of the exponential map**: along a geodesic curve `γ` on `(a, b) ∋ 0, 1`, `exp(γ 0, c v) = γ c` for
`0 < c ≤ 1`, with `v` the chart velocity at `0`. -/
theorem expMap_smul_of [T2Space M] {a b : ℝ} {γ : ℝ → M} (ha : a < 0) (hb : 1 < b)
    (hγ : IsGeodesicCurveOn g γ (Ioo a b)) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    expMap g (γ 0, c • deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0) (γ s)) 0) = γ c := by
  obtain ⟨w, O, hO, hsrc, hgeo⟩ := hγ 0 ⟨ha, by linarith⟩
  have hd : HasDerivAt (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0) (γ s)) (w 0) 0 :=
    hgeo.pos 0 (mem_of_mem_nhds hO)
  have hd' : HasDerivAt (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0) (γ (c * s))) (c • w 0) 0 := by
    have := HasDerivAt.scomp (0 : ℝ) (by simpa using hd) ((hasDerivAt_id' (0 : ℝ)).const_mul c)
    rw [mul_one] at this
    exact this
  have hsub : Ioo (a / c) (b / c) ⊆ (fun s => c * s) ⁻¹' Ioo a b := by
    intro s hs
    constructor
    · have := (div_lt_iff₀ hc0).1 hs.1
      linarith
    · have := (lt_div_iff₀ hc0).1 hs.2
      linarith
  have ha' : a / c < 0 := div_neg_of_neg_of_pos ha hc0
  have hb' : 1 < b / c := by
    rw [lt_div_iff₀ hc0]; linarith
  have := expMap_eq_of g (q := (γ 0, c • deriv (fun s => extChartAt 𝓘(ℝ, Fin n → ℝ) (γ 0) (γ s)) 0))
    (a := a / c) (b := b / c) (γ := fun s => γ (c * s)) ha' hb'
    ((hγ.scale g c).mono hsub) (by simp) (by rw [hd'.deriv, hd.deriv])
  simpa using this

end Lightlike.Penrose
