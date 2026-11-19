import Lightlike.Geodesic.GaussMaximal

/-!
# The exponential map on its maximal domain

For a coordinate metric `g` on `U`, the domain `expDomain g U` of the exponential map is the set
of pairs `(p, v)` such that the geodesic from `p` with initial velocity `v` exists on an open set
containing `[0, 1]` and stays in `U` on `[0, 1]`; `expMap g U (p, v)` is its point at time `1`.
This is the map `exp : D → M` of the source, in a chart.

## Main results

* `expMap_eq`: `expMap g U (γ 0, w 0) = γ 1` for every geodesic `γ` on `[0, 1]` in `U`.
* `zero_mem_expDomain`, `expMap_zero`: the zero section lies in the domain, and `exp_p 0 = p`.
* `smul_mem_expDomain`, `expMap_smul`: the domain is star shaped in the velocity, and
  `exp_p (t v) = c_v (t)`.
* `isOpen_expDomain`, `contDiffOn_expMap`: the domain is open and `exp` is smooth on it.
* `gauss_expMap`: the Gauss lemma on the whole domain.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025): Definition 2.1.13 (page 37) and
  (2.2.5)–(2.2.6) (page 46) for `D` and `exp`; Proposition 2.2.3 (page 46): `D` is open and
  `D_p` is open and star shaped; (2.1.13): `exp_p (t v) = c_v (t)`; Theorem 2.1.21 (page 43):
  the Gauss lemma. Difference: a coordinate metric on an open subset of `ℝⁿ`, so the geodesics
  are those that stay in the chart domain `U` on `[0, 1]`.
-/

open Set Metric Filter Topology Matrix
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The domain of the exponential map: the pairs `(p, v)` such that there is a geodesic from `p`
with initial velocity `v`, defined on an open set containing `[0, 1]`, with values in `U` on
`[0, 1]`. -/
def expDomain (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ)) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {q | ∃ (I : Set ℝ) (γ w : ℝ → Fin n → ℝ), IsOpen I ∧ Icc (0 : ℝ) 1 ⊆ I ∧
    IsGeodesicOn g γ w I ∧ γ 0 = q.1 ∧ w 0 = q.2 ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U}

open Classical in
/-- The exponential map: `expMap g U (p, v)` is the point at time `1` of the geodesic from `p`
with initial velocity `v`, for `(p, v)` in `expDomain g U` (and `p` outside the domain). -/
def expMap (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (U : Set (Fin n → ℝ))
    (q : (Fin n → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  if h : q ∈ expDomain g U then (Classical.choose (Classical.choose_spec h)) 1 else q.1

/-- **The exponential map is the endpoint of the geodesic**: for every geodesic `γ` with velocity
`w`, defined on an open set containing `[0, 1]`, with values in `U` on `[0, 1]`,
`expMap g U (γ 0, w 0) = γ 1`. -/
theorem expMap_eq (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (h01 : Icc (0 : ℝ) 1 ⊆ I) (hgeo : IsGeodesicOn g γ w I)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) : expMap g U (γ 0, w 0) = γ 1 := by
  have hmem : ((γ 0, w 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ expDomain g U :=
    ⟨I, γ, w, hI, h01, hgeo, rfl, rfl, hU⟩
  simp only [expMap, hmem, ↓reduceDIte]
  obtain ⟨w', hI', h01', hgeo', h0', hw0', hU'⟩ :=
    Classical.choose_spec (Classical.choose_spec hmem)
  exact (IsGeodesicOn.eqOn_Icc hg hI' hI h01' h01 hgeo' hgeo hU' h0' hw0' 1
    ⟨zero_le_one, le_rfl⟩).1

/-- A pair in the domain, in terms of a geodesic. -/
theorem mem_expDomain_of_geodesic {γ w : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (h01 : Icc (0 : ℝ) 1 ⊆ I) (hgeo : IsGeodesicOn g γ w I)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) :
    ((γ 0, w 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ expDomain g U :=
  ⟨I, γ, w, hI, h01, hgeo, rfl, rfl, hU⟩

/-- The zero section lies in the domain of `exp`. -/
theorem zero_mem_expDomain {p : Fin n → ℝ} (hp : p ∈ U) :
    ((p, 0) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ expDomain g U := by
  refine ⟨univ, fun _ => p, fun _ => 0, isOpen_univ, subset_univ _,
    ⟨fun t _ => hasDerivAt_const t p, fun t _ => ?_⟩, rfl, rfl, fun _ _ => hp⟩
  rw [accel_zero]
  exact hasDerivAt_const t (0 : Fin n → ℝ)

/-- `exp_p 0 = p`. -/
theorem expMap_zero (hg : Lightlike.IsCoordMetric g U) {p : Fin n → ℝ} (hp : p ∈ U) :
    expMap g U (p, 0) = p := by
  have hgeo : IsGeodesicOn g (fun _ : ℝ => p) (fun _ : ℝ => (0 : Fin n → ℝ)) univ :=
    ⟨fun t _ => hasDerivAt_const t p, fun t _ => by
      rw [accel_zero]; exact hasDerivAt_const t (0 : Fin n → ℝ)⟩
  exact expMap_eq hg isOpen_univ (subset_univ _) hgeo (fun _ _ => hp)

/-- **The domain of `exp` is star shaped in the velocity** (Kunzinger–Steinbauer,
Proposition 2.2.3). -/
theorem smul_mem_expDomain {p v : Fin n → ℝ}
    (h : ((p, v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ expDomain g U) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ((p, t • v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ expDomain g U := by
  obtain ⟨I, γ, w, hI, h01, hgeo, h0, hw0, hU⟩ := h
  have hmul : ∀ s ∈ Icc (0 : ℝ) 1, t * s ∈ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨mul_nonneg ht.1 hs.1, by
      calc t * s ≤ 1 * 1 := mul_le_mul ht.2 hs.2 hs.1 zero_le_one
        _ = 1 := one_mul 1⟩
  refine ⟨(fun s => t * s) ⁻¹' I, fun s => γ (t * s), fun s => t • w (t * s),
    hI.preimage (continuous_const.mul continuous_id), fun s hs => h01 (hmul s hs),
    hgeo.scale t, ?_, ?_, fun s hs => hU _ (hmul s hs)⟩
  · simpa using h0
  · simp only [mul_zero, hw0]

/-- **`exp_p (t v) = c_v (t)`** (Kunzinger–Steinbauer, (2.1.13)): for a geodesic `γ` on `[0, 1]`
in `U` with velocity `w`, `expMap g U (γ 0, t • w 0) = γ t` for `t ∈ [0, 1]`. -/
theorem expMap_smul (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (h01 : Icc (0 : ℝ) 1 ⊆ I) (hgeo : IsGeodesicOn g γ w I)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    expMap g U (γ 0, t • w 0) = γ t := by
  have hmul : ∀ s ∈ Icc (0 : ℝ) 1, t * s ∈ Icc (0 : ℝ) 1 := fun s hs =>
    ⟨mul_nonneg ht.1 hs.1, by
      calc t * s ≤ 1 * 1 := mul_le_mul ht.2 hs.2 hs.1 zero_le_one
        _ = 1 := one_mul 1⟩
  have h1 := expMap_eq hg (γ := fun s => γ (t * s)) (w := fun s => t • w (t * s))
    (hI.preimage (continuous_const.mul continuous_id)) (fun s hs => h01 (hmul s hs))
    (hgeo.scale t) (fun s hs => hU _ (hmul s hs))
  simpa using h1

/-- Near every point of its domain, the exponential map is defined and smooth. -/
theorem exists_ball_subset_expDomain (hg : Lightlike.IsCoordMetric g U)
    {q₀ : (Fin n → ℝ) × (Fin n → ℝ)} (hq₀ : q₀ ∈ expDomain g U) :
    ∃ r > 0, ball q₀ r ⊆ expDomain g U ∧ ContDiffOn ℝ ∞ (expMap g U) (ball q₀ r) := by
  obtain ⟨I, γ, w, hI, h01, hgeo, h0, hw0, hU⟩ := hq₀
  have hO : IsOpen (U ×ˢ (univ : Set (Fin n → ℝ))) := hg.isOpen.prod isOpen_univ
  set c : ℝ → (Fin n → ℝ) × (Fin n → ℝ) := fun t => (γ t, w t) with hc
  have hcs : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt c (geodField g (c t)) (Icc 0 1) t ∧
      c t ∈ U ×ˢ (univ : Set (Fin n → ℝ)) := fun t ht =>
    ⟨(hgeo.hasDerivAt_phase (h01 ht)).hasDerivWithinAt, ⟨hU t ht, mem_univ _⟩⟩
  obtain ⟨r, η, Φ, hr, hη, hΦ, hΦs, -⟩ :=
    Lightlike.ODE.exists_flow_along hO (contDiffOn_geodField hg) zero_le_one hcs
  have hc0 : c 0 = q₀ := Prod.ext h0 hw0
  rw [hc0] at hΦ hΦs
  have h1J : (1 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have hsubJ : Icc (0 : ℝ) 1 ⊆ Ioo (-η) (1 + η) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hgeoy : ∀ y ∈ ball q₀ r, IsGeodesicOn g (fun t => (Φ t y).1) (fun t => (Φ t y).2)
      (Ioo (-η) (1 + η)) := fun y hy =>
    isGeodesicOn_of_phase fun t ht => ((hΦ y hy).2 t ht).1
  have hUy : ∀ y ∈ ball q₀ r, ∀ t ∈ Icc (0 : ℝ) 1, (Φ t y).1 ∈ U := fun y hy t ht =>
    (((hΦ y hy).2 t (hsubJ ht)).2).1
  have hval : ∀ y ∈ ball q₀ r, y ∈ expDomain g U ∧ expMap g U y = (Φ 1 y).1 := by
    intro y hy
    have h1 := mem_expDomain_of_geodesic isOpen_Ioo hsubJ (hgeoy y hy) (hUy y hy)
    have h2 := expMap_eq hg isOpen_Ioo hsubJ (hgeoy y hy) (hUy y hy)
    simp only [(hΦ y hy).1] at h1 h2
    exact ⟨h1, h2⟩
  refine ⟨r, hr, fun y hy => (hval y hy).1, ?_⟩
  have hι : ContDiff ℝ ∞ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => ((1 : ℝ), y)) :=
    contDiff_const.prodMk contDiff_id
  have hs : ContDiffOn ℝ ∞ (fun y : (Fin n → ℝ) × (Fin n → ℝ) => (Φ 1 y).1) (ball q₀ r) :=
    contDiff_fst.comp_contDiffOn (hΦs.comp hι.contDiffOn fun y hy => ⟨h1J, hy⟩)
  exact hs.congr fun y hy => (hval y hy).2

/-- **The domain of the exponential map is open** (Kunzinger–Steinbauer, Proposition 2.2.3). -/
theorem isOpen_expDomain (hg : Lightlike.IsCoordMetric g U) : IsOpen (expDomain g U) := by
  rw [Metric.isOpen_iff]
  intro q hq
  obtain ⟨r, hr, hsub, -⟩ := exists_ball_subset_expDomain hg hq
  exact ⟨r, hr, hsub⟩

/-- **The exponential map is smooth on its domain.** -/
theorem contDiffOn_expMap (hg : Lightlike.IsCoordMetric g U) :
    ContDiffOn ℝ ∞ (expMap g U) (expDomain g U) := by
  intro q hq
  obtain ⟨r, hr, -, hs⟩ := exists_ball_subset_expDomain hg hq
  exact (hs.contDiffAt (ball_mem_nhds q hr)).contDiffWithinAt

/-- **The Gauss lemma on the whole domain of the exponential map** (Kunzinger–Steinbauer,
Theorem 2.1.21): for `(x, v)` in the domain of `exp` and every `w₁`,
`g (exp_x v) (D exp_x (v) v, D exp_x (v) w₁) = g x (v, w₁)`. -/
theorem gauss_expMap (hg : Lightlike.IsCoordMetric g U) {x v : Fin n → ℝ}
    (h : ((x, v) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ expDomain g U) (w₁ : Fin n → ℝ) :
    pairing g (expMap g U (x, v)) (fderiv ℝ (fun u => expMap g U (x, u)) v v)
        (fderiv ℝ (fun u => expMap g U (x, u)) v w₁) = pairing g x v w₁ := by
  obtain ⟨I, γ, w, hI, h01, hgeo, h0, hw0, hU⟩ := h
  simp only at h0 hw0
  obtain ⟨δ, E, hδ, -, hE1, hEg, hgauss⟩ := exists_expMap_along_gauss hg h01 hgeo hU
  rw [h0, hw0] at hEg hgauss
  rw [hw0] at hE1
  have hEq : ∀ u ∈ ball v δ, expMap g U (x, u) = E u := by
    intro u hu
    obtain ⟨η, γ', w', hη, h0', hw0', h1', hgeo', hU'⟩ := hEg u hu
    have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-η) (1 + η) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := expMap_eq hg isOpen_Ioo hsub hgeo' hU'
    rw [h0', hw0', h1'] at this
    exact this
  have hev : (fun u => expMap g U (x, u)) =ᶠ[𝓝 v] E := by
    filter_upwards [ball_mem_nhds v hδ] with u hu using hEq u hu
  rw [hev.fderiv_eq, hEq v (mem_ball_self hδ)]
  exact hgauss w₁

end Lightlike.Geodesic
