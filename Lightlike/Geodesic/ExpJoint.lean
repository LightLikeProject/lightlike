import Lightlike.Geodesic.ExpSmooth

/-!
# The exponential map in the base point and the velocity

For a coordinate metric `g` on `U` and `x ∈ U`, the map `(p, v) ↦ exp_p (v)` is smooth for `p`
near `x` and `v` near `0`, with derivative `(ξ, η) ↦ ξ + η` at `(x, 0)`
(`Lightlike.Geodesic.exists_expMap_joint`). This is the second component of the map
`E (v) = (π (v), exp_{π (v)} v)` of the source, near the zero vector at `x`; it is the input for
the theorem that `E` is a diffeomorphism near the zero section and for convex neighbourhoods.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), equations (2.2.4) and (2.2.6),
  page 46, and the first step of the proof of Theorem 2.2.6, pages 47–48.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The exponential map is smooth in the base point and the velocity.** For `x ∈ U` there are
`ρ > 0` and a map `E` of `(p, v)`, smooth for `‖p - x‖ < ρ` and `‖v‖ < ρ`, with values in `U`,
such that `E (p, 0) = p`, the derivative of `E` at `(x, 0)` is `(ξ, η) ↦ ξ + η`, and for such
`p`, `v` there is a geodesic `γ` on `(-1, 2)` with `γ 0 = p`, initial velocity `v`, and
`γ t = E (p, t • v)` for `t ∈ [-1, 1]`. So `E (p, v) = exp_p (v)`. -/
theorem exists_expMap_joint (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (ρ : ℝ) (E : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ)), 0 < ρ ∧
      (∀ p ∈ ball x ρ, E (p, 0) = p) ∧
      ContDiffOn ℝ ∞ E (ball x ρ ×ˢ ball (0 : Fin n → ℝ) ρ) ∧
      HasFDerivAt E (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ) +
        ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)) (x, 0) ∧
      (∀ p ∈ ball x ρ, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, E (p, v) ∈ U) ∧
      ∀ p ∈ ball x ρ, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ,
        γ 0 = p ∧ w 0 = v ∧ IsGeodesicOn g γ w (Ioo (-1) 2) ∧
        ∀ t ∈ Icc (-1 : ℝ) 1, γ t = E (p, t • v) := by
  set p₀ : (Fin n → ℝ) × (Fin n → ℝ) := (x, 0) with hp₀
  have hopen : IsOpen (U ×ˢ (univ : Set (Fin n → ℝ))) := hg.isOpen.prod isOpen_univ
  obtain ⟨aU, haU, hballU⟩ := Metric.isOpen_iff.mp hopen p₀ (mk_mem_prod hx (mem_univ _))
  obtain ⟨A, hA, H⟩ := Lightlike.ODE.exists_isFlowBox (contDiffAt_geodField hg hx 0)
  set a : ℝ := min A aU with ha
  have ha0 : 0 < a := lt_min hA haU
  obtain ⟨r, T, K, Ψ, h⟩ := H a ha0 (min_le_left _ _)
  have hsm : ContDiffOn ℝ ∞ (fun q : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => Ψ q.1 q.2)
      (Ioo (-T) T ×ˢ ball p₀ r) :=
    h.contDiffOn_uncurry_infty ((contDiffOn_geodField hg).mono
      ((ball_subset_ball (min_le_right _ _)).trans hballU))
  have hT := h.T_pos
  have hr := h.r_pos
  set s : ℝ := T / 2 with hs
  have hs0 : 0 < s := half_pos hT
  have hsI : s ∈ Ioo (-T) T := ⟨by linarith, by linarith⟩
  have hsI' : s ∈ Icc (-T) T := Ioo_subset_Icc_self hsI
  have hp₀r : p₀ ∈ ball p₀ r := mem_ball_self h.r_pos
  -- membership in the ball of initial points, in terms of the two components
  have hmk : ∀ (p u : Fin n → ℝ), Dist.dist p x < r → ‖u‖ < r → (p, u) ∈ ball p₀ r := by
    intro p u hp hu
    rw [mem_ball, Prod.dist_eq]
    refine max_lt hp ?_
    show Dist.dist u (0 : Fin n → ℝ) < r
    rwa [dist_zero_right]
  have hsplit : ∀ (p u : Fin n → ℝ), (p, u) ∈ ball p₀ r → Dist.dist p x < r ∧ ‖u‖ < r := by
    intro p u hpu
    have := mem_ball.1 hpu
    rw [Prod.dist_eq, max_lt_iff] at this
    have h2 : Dist.dist u (0 : Fin n → ℝ) < r := this.2
    rw [dist_zero_right] at h2
    exact ⟨this.1, h2⟩
  set ρ : ℝ := min r (s * r) with hρ
  have hρ0 : 0 < ρ := lt_min hr (mul_pos hs0 hr)
  have hmem : ∀ p ∈ ball x ρ, ∀ v ∈ ball (0 : Fin n → ℝ) ρ, (p, s⁻¹ • v) ∈ ball p₀ r := by
    intro p hp v hv
    rw [mem_ball_zero_iff] at hv
    refine hmk p _ (lt_of_lt_of_le (mem_ball.1 hp) (min_le_left _ _)) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0), inv_mul_lt_iff₀ hs0]
    exact lt_of_lt_of_le hv (min_le_right _ _)
  -- constant geodesics
  have hconst : ∀ p : Fin n → ℝ, (p, (0 : Fin n → ℝ)) ∈ ball p₀ r → ∀ t ∈ Icc (-T) T,
      Ψ t (p, 0) = (p, 0) := by
    intro p hp t ht
    have hc : ∀ u ∈ Icc (-T) T, HasDerivWithinAt
        (fun _ : ℝ => ((p, 0) : (Fin n → ℝ) × (Fin n → ℝ))) (geodField g (p, 0))
        (Icc (-T) T) u := fun u _ => by
      rw [geodField_zero]; exact hasDerivWithinAt_const u _ _
    exact Lightlike.ODE.eqOn_of_trajectories h.lipschitzOnWith (h.hasDerivWithinAt hp)
      (h.flow_mem _ hp) hc (fun _ _ => h.initial_mem hp) (h.flow_zero _ hp) ht
  -- homogeneity of the geodesic flow
  have hhom : ∀ p u : Fin n → ℝ, (p, u) ∈ ball p₀ r → ∀ c ∈ Icc (-1 : ℝ) 1, ∀ τ ∈ Icc (-T) T,
      Ψ τ (p, c • u) = ((Ψ (c * τ) (p, u)).1, c • (Ψ (c * τ) (p, u)).2) := by
    intro p u hu c hc τ hτ
    have hc1 : |c| ≤ 1 := abs_le.2 hc
    have hcI : ∀ τ ∈ Icc (-T) T, c * τ ∈ Icc (-T) T := by
      intro τ hτ
      have h1 : |c * τ| ≤ T := by
        rw [abs_mul]
        calc |c| * |τ| ≤ 1 * T := mul_le_mul hc1 (abs_le.2 hτ) (abs_nonneg _) zero_le_one
          _ = T := one_mul T
      exact abs_le.1 h1
    have hgeo : IsGeodesicOn g (fun t => (Ψ t (p, u)).1) (fun t => (Ψ t (p, u)).2)
        (Icc (-T) T) :=
      isGeodesicOn_of_phase fun t ht => h.hasDerivAt _ hu t ht
    have hsc := hgeo.scale c
    obtain ⟨hpx, hur⟩ := hsplit p u hu
    have hcu : (p, c • u) ∈ ball p₀ r := by
      refine hmk p _ hpx ?_
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg u, abs_nonneg c]
    have hβ : ∀ τ ∈ Icc (-T) T, HasDerivWithinAt
        (fun τ => ((Ψ (c * τ) (p, u)).1, c • (Ψ (c * τ) (p, u)).2))
        (geodField g ((Ψ (c * τ) (p, u)).1, c • (Ψ (c * τ) (p, u)).2)) (Icc (-T) T) τ :=
      fun τ hτ => (hsc.hasDerivAt_phase (t := τ) (hcI τ hτ)).hasDerivWithinAt
    have hβs : ∀ τ ∈ Icc (-T) T,
        ((Ψ (c * τ) (p, u)).1, c • (Ψ (c * τ) (p, u)).2) ∈ ball p₀ a := by
      intro τ hτ
      have h1 := mem_ball.1 (h.flow_mem _ hu (c * τ) (hcI τ hτ))
      rw [Prod.dist_eq, max_lt_iff] at h1
      have h2 : Dist.dist (Ψ (c * τ) (p, u)).2 (0 : Fin n → ℝ) < a := h1.2
      rw [dist_zero_right] at h2
      rw [mem_ball, Prod.dist_eq]
      refine max_lt h1.1 ?_
      show Dist.dist (c • (Ψ (c * τ) (p, u)).2) (0 : Fin n → ℝ) < a
      rw [dist_zero_right, norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg (Ψ (c * τ) (p, u)).2, abs_nonneg c]
    have h0 : (fun τ => Ψ τ (p, c • u)) 0 =
        (fun τ => ((Ψ (c * τ) (p, u)).1, c • (Ψ (c * τ) (p, u)).2)) 0 := by
      simp only [mul_zero, h.flow_zero _ hu, h.flow_zero _ hcu]
    exact Lightlike.ODE.eqOn_of_trajectories h.lipschitzOnWith (h.hasDerivWithinAt hcu)
      (h.flow_mem _ hcu) hβ hβs h0 hτ
  refine ⟨ρ, fun q => (Ψ s (q.1, s⁻¹ • q.2)).1, hρ0, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp0 := hmem p hp 0 (mem_ball_self hρ0)
    simp only [smul_zero] at hp0 ⊢
    rw [hconst p hp0 s hsI']
  · have hι : ContDiff ℝ ∞ (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        (s, ((q.1, s⁻¹ • q.2) : (Fin n → ℝ) × (Fin n → ℝ)))) :=
      contDiff_const.prodMk (contDiff_fst.prodMk (contDiff_snd.const_smul s⁻¹))
    exact contDiff_fst.comp_contDiffOn
      (hsm.comp hι.contDiffOn fun q hq => ⟨hsI, hmem q.1 hq.1 q.2 hq.2⟩)
  · -- the derivative at `(x, 0)`
    have hA' : ∀ t ∈ Icc (-T) T, fderiv ℝ (geodField g) (Ψ t p₀) =
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
          (0 : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := fun t ht => by
      rw [hp₀, hconst x hp₀r t ht]; exact (hasFDerivAt_geodField_zero hg hx).fderiv
    have hDΨ : ∀ ξ η : Fin n → ℝ, fderiv ℝ (Ψ s) p₀ (ξ, η) = (ξ + s • η, η) := by
      intro ξ η
      have hu : ∀ t ∈ Icc (-T) T, HasDerivWithinAt
          (fun t => fderiv ℝ (Ψ t) p₀ (ξ, η))
          (fderiv ℝ (geodField g) (Ψ t p₀) (fderiv ℝ (Ψ t) p₀ (ξ, η)))
          (Icc (-T) T) t := by
        intro t ht
        have h1 := (h.hasDerivWithinAt_fderiv_flow hp₀r ht).clm_apply
          (hasDerivWithinAt_const t (Icc (-T) T) (ξ, η))
        simpa using h1
      have hv : ∀ t ∈ Icc (-T) T, HasDerivWithinAt (fun t : ℝ => (ξ + t • η, η))
          (fderiv ℝ (geodField g) (Ψ t p₀) (ξ + t • η, η)) (Icc (-T) T) t := by
        intro t ht
        rw [hA' t ht]
        have h1 : HasDerivWithinAt (fun t : ℝ => (ξ + t • η, η)) ((1 : ℝ) • η, (0 : Fin n → ℝ))
            (Icc (-T) T) t :=
          (((hasDerivWithinAt_id t _).smul_const η).const_add ξ).prodMk
            (hasDerivWithinAt_const t _ η)
        simpa using h1
      have h0 : (fun t => fderiv ℝ (Ψ t) p₀ (ξ, η)) 0 = (fun t : ℝ => (ξ + t • η, η)) 0 := by
        simp [h.fderiv_flow_zero hp₀r]
      exact Lightlike.ODE.eqOn_of_linear (A := fun t => fderiv ℝ (geodField g) (Ψ t p₀))
        (K := K) (fun t ht => h.norm_fderiv_le _ (h.flow_mem _ hp₀r t ht)) hu hv h0 hsI'
    have hinner : HasFDerivAt (fun q : (Fin n → ℝ) × (Fin n → ℝ) =>
        ((q.1, s⁻¹ • q.2) : (Fin n → ℝ) × (Fin n → ℝ)))
        ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
          (s⁻¹ • ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ))) (x, 0) :=
      hasFDerivAt_fst.prodMk (hasFDerivAt_snd.const_smul s⁻¹)
    have hΨd : HasFDerivAt (Ψ s) (fderiv ℝ (Ψ s) p₀) ((x, s⁻¹ • (0 : Fin n → ℝ))) := by
      rw [smul_zero]; exact (h.differentiableAt_flow hp₀r hsI').hasFDerivAt
    have hcomp := (hasFDerivAt_fst (𝕜 := ℝ) (p := Ψ s (x, s⁻¹ • (0 : Fin n → ℝ)))).comp
      ((x, 0) : (Fin n → ℝ) × (Fin n → ℝ)) (HasFDerivAt.comp (x, 0) hΨd hinner)
    refine hcomp.congr_fderiv (ContinuousLinearMap.ext fun ζ => ?_)
    show (fderiv ℝ (Ψ s) p₀ (ζ.1, s⁻¹ • ζ.2)).1 = ζ.1 + ζ.2
    rw [hDΨ ζ.1 (s⁻¹ • ζ.2), smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  · intro p hp v hv
    exact (hballU (ball_subset_ball (min_le_right _ _)
      (h.flow_mem _ (hmem p hp v hv) s hsI'))).1
  · intro p hp v hv
    have hpv := hmem p hp v hv
    have hgeo : IsGeodesicOn g (fun t => (Ψ t (p, s⁻¹ • v)).1) (fun t => (Ψ t (p, s⁻¹ • v)).2)
        (Ioo (-T) T) :=
      isGeodesicOn_of_phase fun t ht => h.hasDerivAt _ hpv t (Ioo_subset_Icc_self ht)
    have hsc := hgeo.scale s
    have hsub : Ioo (-1 : ℝ) 2 ⊆ (fun t => s * t) ⁻¹' Ioo (-T) T := by
      intro t ht
      constructor
      · have : s * t > s * (-1) := mul_lt_mul_of_pos_left ht.1 hs0
        show -T < s * t
        nlinarith
      · have : s * t < s * 2 := mul_lt_mul_of_pos_left ht.2 hs0
        show s * t < T
        nlinarith
    refine ⟨fun t => (Ψ (s * t) (p, s⁻¹ • v)).1, fun t => s • (Ψ (s * t) (p, s⁻¹ • v)).2,
      ?_, ?_, ⟨fun t ht => hsc.pos t (hsub ht), fun t ht => hsc.vel t (hsub ht)⟩, ?_⟩
    · simp [h.flow_zero _ hpv]
    · simp [h.flow_zero _ hpv, smul_smul, mul_inv_cancel₀ hs0.ne']
    · intro t ht
      show (Ψ (s * t) (p, s⁻¹ • v)).1 = (Ψ s (p, s⁻¹ • (t • v))).1
      rw [smul_comm s⁻¹ t v, hhom p (s⁻¹ • v) hpv t ht s hsI', mul_comm t s]

end Lightlike.Geodesic
