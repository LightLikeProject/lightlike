import Lightlike.Geodesic.ExpDiffeo

/-!
# Radial geodesics in a normal neighbourhood

In a normal neighbourhood `φ (B(0, ρ))` of `x`, with `φ` the exponential map on the ball
(`Lightlike.Geodesic.exists_expMap_diffeo`), the curve `t ↦ φ (t • v)` is a geodesic from `x` to
`φ v` in the neighbourhood, and it is the only one: every geodesic `τ` on `[0, 1]` from `x` that
stays in the neighbourhood is `t ↦ φ (t • τ'(0))`, and `τ'(0) = φ⁻¹ (τ 1)`
(`Lightlike.Geodesic.exists_normal_neighbourhood`).

Uniqueness uses that two geodesics in `U` with the same position and velocity at one time agree
on every interval on which both are defined (`IsGeodesicOn.eqOn_Icc`).

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Proposition 2.1.15 (radial
  geodesics), page 39. Differences: a coordinate metric on an open subset of `ℝⁿ` instead of a
  semi-Riemannian manifold; the normal neighbourhood is the image of a ball.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **Geodesics are unique on intervals**: two geodesics, defined on open sets containing
`[a, b]`, the first with values in `U` on `[a, b]`, that have the same position and velocity at
`a`, have the same position and velocity on `[a, b]`. -/
theorem IsGeodesicOn.eqOn_Icc (hg : Lightlike.IsCoordMetric g U) {γ w γ' w' : ℝ → Fin n → ℝ}
    {I I' : Set ℝ} {a b : ℝ} (hI : IsOpen I) (hI' : IsOpen I') (hab : Icc a b ⊆ I)
    (hab' : Icc a b ⊆ I') (h : IsGeodesicOn g γ w I) (h' : IsGeodesicOn g γ' w' I')
    (hU : ∀ t ∈ Icc a b, γ t ∈ U) (h0 : γ a = γ' a) (h1 : w a = w' a) :
    ∀ t ∈ Icc a b, γ t = γ' t ∧ w t = w' t := by
  set s : Set ℝ := {t | (γ t, w t) = (γ' t, w' t)} with hs
  have hc : ContinuousOn (fun t => (γ t, w t)) (Icc a b) := fun t ht =>
    (((h.pos t (hab ht)).continuousAt).prodMk ((h.vel t (hab ht)).continuousAt)).continuousWithinAt
  have hc' : ContinuousOn (fun t => (γ' t, w' t)) (Icc a b) := fun t ht =>
    (((h'.pos t (hab' ht)).continuousAt).prodMk
      ((h'.vel t (hab' ht)).continuousAt)).continuousWithinAt
  have hclosed : IsClosed (s ∩ Icc a b) := by
    have h2 : s ∩ Icc a b = {t ∈ Icc a b | (γ t, w t) = (γ' t, w' t)} := by
      ext t; simp [hs, and_comm]
    rw [h2]
    exact isClosed_Icc.isClosed_eq hc hc'
  have hsub : Icc a b ⊆ s := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hclosed (Prod.ext h0 h1) fun t ht => ?_
    obtain ⟨hts, htI⟩ := ht
    have htI' : t ∈ Icc a b := ⟨htI.1, htI.2.le⟩
    have hev := IsGeodesicOn.eventuallyEq hg (hI.mem_nhds (hab htI')) (hI'.mem_nhds (hab' htI'))
      h h' (hU t htI') (congrArg Prod.fst hts) (congrArg Prod.snd hts)
    exact mem_nhdsWithin_of_mem_nhds hev
  intro t ht
  have := hsub ht
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- **Normal neighbourhoods and their radial geodesics** (Kunzinger–Steinbauer, Theorem 2.1.14
and Proposition 2.1.15, for a coordinate metric of any signature).

For `x ∈ U` there are `ρ > 0` and an open partial homeomorphism `φ` of `ℝⁿ`, with source the ball
of radius `ρ` about `0` and target in `U`, smooth with smooth inverse, with `φ 0 = x` and
derivative the identity at `0`, such that:

* for every `v` in the ball, `t ↦ φ (t • v)` on `[0, 1]` is a geodesic from `x` to `φ v` with
  initial velocity `v` (the radial geodesic);
* every geodesic `τ` with velocity `ν`, defined on an open set containing `[0, 1]`, with
  `τ 0 = x` and `τ t` in the target of `φ` for `t ∈ [0, 1]`, is radial: `ν 0` lies in the ball,
  `τ t = φ (t • ν 0)` on `[0, 1]`, and `ν 0 = φ⁻¹ (τ 1)`. -/
theorem exists_normal_neighbourhood (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) :
    ∃ (ρ : ℝ) (φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)), 0 < ρ ∧
      φ.source = ball 0 ρ ∧ φ 0 = x ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target ∧
      HasFDerivAt φ (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 ∧ φ.target ⊆ U ∧
      (∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ, γ 0 = x ∧ w 0 = v ∧ γ 1 = φ v ∧
        IsGeodesicOn g γ w (Ioo (-1) 2) ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ t = φ (t • v)) ∧
      ∀ (τ ν : ℝ → Fin n → ℝ) (I : Set ℝ), IsOpen I → Icc (0 : ℝ) 1 ⊆ I →
        IsGeodesicOn g τ ν I → τ 0 = x → (∀ t ∈ Icc (0 : ℝ) 1, τ t ∈ φ.target) →
        ν 0 ∈ ball (0 : Fin n → ℝ) ρ ∧ (∀ t ∈ Icc (0 : ℝ) 1, τ t = φ (t • ν 0)) ∧
          ν 0 = φ.symm (τ 1) := by
  obtain ⟨ρ, φ, hρ, hsrc, hφ0, hφs, hφi, hφd, hφU, hrad⟩ := exists_expMap_diffeo hg hx
  refine ⟨ρ, φ, hρ, hsrc, hφ0, hφs, hφi, hφd, hφU, hrad, ?_⟩
  intro τ ν I hI h01 hτ hτ0 hτU
  set w₀ : Fin n → ℝ := ν 0 with hw₀
  -- Step A: `τ (c t) = φ (t • (c • w₀))` when `c • w₀` is in the ball
  have hA : ∀ c ∈ Ioc (0 : ℝ) 1, c • w₀ ∈ ball (0 : Fin n → ℝ) ρ →
      ∀ t ∈ Icc (0 : ℝ) 1, τ (c * t) = φ (t • (c • w₀)) := by
    intro c hc hcw t ht
    obtain ⟨γ, w, hγ0, hw0, -, hγ, hγφ⟩ := hrad (c • w₀) hcw
    have hsc := hτ.scale c
    have hpre : IsOpen ((fun t => c * t) ⁻¹' I) := hI.preimage (continuous_const.mul continuous_id)
    have hsub : Icc (0 : ℝ) 1 ⊆ (fun t => c * t) ⁻¹' I := by
      intro u hu
      refine h01 ⟨mul_nonneg hc.1.le hu.1, ?_⟩
      calc c * u ≤ 1 * 1 := mul_le_mul hc.2 hu.2 hu.1 zero_le_one
        _ = 1 := one_mul 1
    have hUc : ∀ u ∈ Icc (0 : ℝ) 1, (fun t => τ (c * t)) u ∈ U := fun u hu =>
      hφU (hτU (c * u) ⟨mul_nonneg hc.1.le hu.1, by
        calc c * u ≤ 1 * 1 := mul_le_mul hc.2 hu.2 hu.1 zero_le_one
          _ = 1 := one_mul 1⟩)
    have heq := IsGeodesicOn.eqOn_Icc hg hpre isOpen_Ioo hsub
      (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩) hsc hγ hUc
      (by simp [hτ0, hγ0]) (by simp [hw0, hw₀]) t ht
    rw [← hγφ t ht]
    exact heq.1
  have hτc : ContinuousOn τ (Icc (0 : ℝ) 1) := fun t ht =>
    ((hτ.pos t (h01 ht)).continuousAt).continuousWithinAt
  -- Step B: `w₀` is in the ball
  have hball : w₀ ∈ ball (0 : Fin n → ℝ) ρ := by
    rw [mem_ball_zero_iff]
    by_contra hnot
    push Not at hnot
    have hm : 0 < ‖w₀‖ := lt_of_lt_of_le hρ hnot
    set us : ℝ := ρ / ‖w₀‖ with hus
    have hus0 : 0 < us := div_pos hρ hm
    have hus1 : us ≤ 1 := (div_le_one hm).2 hnot
    have husI : us ∈ Icc (0 : ℝ) 1 := ⟨hus0.le, hus1⟩
    -- for `u < us` the vector `u • w₀` is in the ball and `τ u = φ (u • w₀)`
    have hlt : ∀ u ∈ Ioo (0 : ℝ) us, u • w₀ ∈ ball (0 : Fin n → ℝ) ρ ∧ τ u = φ (u • w₀) := by
      intro u hu
      have hin : u • w₀ ∈ ball (0 : Fin n → ℝ) ρ := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hu.1]
        calc u * ‖w₀‖ < us * ‖w₀‖ := mul_lt_mul_of_pos_right hu.2 hm
          _ = ρ := div_mul_cancel₀ ρ hm.ne'
      have := hA u ⟨hu.1, hu.2.le.trans hus1⟩ hin 1 ⟨zero_le_one, le_rfl⟩
      simp only [mul_one, one_smul] at this
      exact ⟨hin, this⟩
    -- the limit of `φ⁻¹ (τ u)` as `u ↑ us`, computed in two ways
    have hgc : ContinuousWithinAt (fun u => φ.symm (τ u)) (Icc (0 : ℝ) 1) us :=
      (φ.continuousOn_symm.comp hτc (fun u hu => hτU u hu)) us husI
    have hsubI : Ioo (0 : ℝ) us ⊆ Icc (0 : ℝ) 1 := fun u hu =>
      ⟨hu.1.le, hu.2.le.trans hus1⟩
    have hne : (𝓝[Ioo (0 : ℝ) us] us).NeBot := right_nhdsWithin_Ioo_neBot hus0
    have h1 : Tendsto (fun u => φ.symm (τ u)) (𝓝[Ioo (0 : ℝ) us] us)
        (𝓝 (φ.symm (τ us))) := hgc.mono hsubI
    have h2 : Tendsto (fun u => φ.symm (τ u)) (𝓝[Ioo (0 : ℝ) us] us) (𝓝 (us • w₀)) := by
      have hlin : Tendsto (fun u : ℝ => u • w₀) (𝓝[Ioo (0 : ℝ) us] us) (𝓝 (us • w₀)) :=
        ((continuous_id.smul continuous_const).tendsto us).mono_left nhdsWithin_le_nhds
      refine hlin.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      rw [(hlt u hu).2]
      exact (φ.left_inv (by rw [hsrc]; exact (hlt u hu).1)).symm
    have h3 := tendsto_nhds_unique h1 h2
    have h4 : φ.symm (τ us) ∈ ball (0 : Fin n → ℝ) ρ := by
      rw [← hsrc]; exact φ.map_target (hτU us husI)
    rw [h3, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hus0, hus,
      div_mul_cancel₀ ρ hm.ne'] at h4
    exact lt_irrefl _ h4
  have hrad' : ∀ t ∈ Icc (0 : ℝ) 1, τ t = φ (t • w₀) := by
    intro t ht
    have := hA 1 ⟨zero_lt_one, le_rfl⟩ (by rwa [one_smul]) t ht
    simpa using this
  refine ⟨hball, hrad', ?_⟩
  rw [hrad' 1 ⟨zero_le_one, le_rfl⟩, one_smul]
  exact (φ.left_inv (by rw [hsrc]; exact hball)).symm

end Lightlike.Geodesic
