import Lightlike.ODE.FlowBoxSmooth
import Lightlike.Regge.Geodesic.Exp

/-!
# The exponential map is smooth near the origin, with derivative the identity

For a coordinate metric `g` on an open set `U ⊆ ℝⁿ` of any signature and a point `x ∈ U`, there
is a smooth map `E` on a ball about `0` such that `E v` is the endpoint at time `1` of the
geodesic from `x` with initial velocity `v`, `E 0 = x`, and the derivative of `E` at `0` is the
identity (`Lightlike.Geodesic.exists_expMap_smooth`). This is the exponential map `exp_x` near
`0`, and the two facts are the two steps of the proof of the theorem that `exp_x` is a local
diffeomorphism.

`Lightlike.Geodesic.exists_expMap` (in `Lightlike.Regge.Geodesic.Exp`) has a map with the
estimate `E v = x + v + O(|v|²)` but no regularity; the regularity comes from the smooth
dependence of the geodesic flow on its initial data (`Lightlike.ODE.IsFlowBox.contDiffOn_uncurry_infty`).

The derivative at `0` is computed from the variational equation along the constant geodesic at
`x`: the derivative of the geodesic vector field at `(x, 0)` is `(ξ, ω) ↦ (ω, 0)`, because the
acceleration is quadratic in the velocity, so the derivative of the flow in the direction `(0, ω)`
is `(t ω, ω)`.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Definition 2.1.13 (page 37) and the
  proof of Theorem 2.1.14 (pages 38–39): `exp_p` is smooth near `0` and `T_0 exp_p = id`,
  equation (2.1.14). The notes treat semi-Riemannian manifolds and follow O'Neill,
  *Semi-Riemannian Geometry*, chapter 3.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The acceleration vanishes at zero velocity. -/
theorem accel_zero (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    accel g x 0 = 0 := by
  funext i; simp [accel]

/-- The geodesic vector field vanishes at a point with zero velocity. -/
theorem geodField_zero (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    geodField g (x, 0) = 0 := by
  simp [geodField, accel_zero]

/-- **The derivative of the geodesic vector field at zero velocity** is `(ξ, ω) ↦ (ω, 0)`: the
acceleration is quadratic in the velocity. -/
theorem hasFDerivAt_geodField_zero (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ}
    (hx : x ∈ U) :
    HasFDerivAt (geodField g)
      ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
        (0 : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))) (x, 0) := by
  obtain ⟨R, hR, hRU⟩ : ∃ R > 0, closedBall x R ⊆ U := by
    obtain ⟨R, hR, hb⟩ := Metric.isOpen_iff.mp hg.isOpen x hx
    exact ⟨R / 2, half_pos hR, (closedBall_subset_ball (half_lt_self hR)).trans hb⟩
  obtain ⟨A, hA, hB⟩ := exists_accel_bound hg (isCompact_closedBall x R) hRU
  have hacc : HasFDerivAt (fun p : (Fin n → ℝ) × (Fin n → ℝ) => accel g p.1 p.2)
      (0 : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (x, 0) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    have hpos : 0 < min R (c / (A + 1)) := lt_min hR (div_pos hc (by linarith))
    filter_upwards [Metric.ball_mem_nhds (0 : (Fin n → ℝ) × (Fin n → ℝ)) hpos] with q hq
    rw [mem_ball_zero_iff] at hq
    have hq1 : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
    have hq2 : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
    have hmem : x + q.1 ∈ closedBall x R := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hq1.trans (hq.le.trans (min_le_left _ _))
    have h1 := hB (x + q.1) hmem (0 + q.2)
    rw [zero_add] at h1
    have h2 : ‖q‖ * (A + 1) ≤ c := by
      have := (lt_of_lt_of_le hq (min_le_right _ _)).le
      rwa [le_div_iff₀ (by linarith)] at this
    simp only [Prod.fst_add, Prod.snd_add, accel_zero, sub_zero, zero_apply,
      zero_add]
    calc ‖accel g (x + q.1) q.2‖ ≤ A * ‖q.2‖ ^ 2 := h1
      _ ≤ A * ‖q‖ ^ 2 := by
        have : ‖q.2‖ ^ 2 ≤ ‖q‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq2 2
        exact mul_le_mul_of_nonneg_left this hA
      _ ≤ c * ‖q‖ := by nlinarith [norm_nonneg q, mul_nonneg hA (norm_nonneg q)]
  exact hasFDerivAt_snd.prodMk hacc

/-- **The exponential map is smooth near the origin and its derivative there is the identity**
(Kunzinger–Steinbauer, proof of Theorem 2.1.14, for a coordinate metric of any signature).

For `x ∈ U` there are `ρ > 0` and a map `E`, smooth on the ball of radius `ρ` about `0`, with
`E 0 = x` and derivative the identity at `0`, such that every `v` in that ball is the initial
velocity of a geodesic from `x`, defined on `(-1, 2)`, which reaches `E v` at time `1`. -/
theorem exists_expMap_smooth (hg : Lightlike.IsCoordMetric g U) {x : Fin n → ℝ} (hx : x ∈ U) :
    ∃ (ρ : ℝ) (E : (Fin n → ℝ) → (Fin n → ℝ)), 0 < ρ ∧ E 0 = x ∧
      ContDiffOn ℝ ∞ E (ball 0 ρ) ∧
      HasFDerivAt E (ContinuousLinearMap.id ℝ (Fin n → ℝ)) 0 ∧
      ∀ v ∈ ball (0 : Fin n → ℝ) ρ, ∃ γ w : ℝ → Fin n → ℝ, γ 0 = x ∧ w 0 = v ∧ γ 1 = E v ∧
        IsGeodesicOn g γ w (Ioo (-1) 2) := by
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
  set s : ℝ := T / 2 with hs
  have hs0 : 0 < s := half_pos hT
  have hsI : s ∈ Ioo (-T) T := ⟨by linarith, by linarith⟩
  have hsI' : s ∈ Icc (-T) T := Ioo_subset_Icc_self hsI
  have hp₀r : p₀ ∈ ball p₀ r := mem_ball_self h.r_pos
  -- the constant geodesic at `x`
  have hconst : ∀ t ∈ Icc (-T) T, Ψ t p₀ = p₀ := by
    intro t ht
    have hc : ∀ u ∈ Icc (-T) T, HasDerivWithinAt (fun _ : ℝ => p₀) (geodField g p₀)
        (Icc (-T) T) u := fun u _ => by
      rw [hp₀, geodField_zero]; exact hasDerivWithinAt_const u _ _
    exact Lightlike.ODE.eqOn_of_trajectories h.lipschitzOnWith (h.hasDerivWithinAt hp₀r)
      (h.flow_mem _ hp₀r) hc (fun _ _ => h.initial_mem hp₀r) (h.flow_zero _ hp₀r) ht
  -- points `(x, s⁻¹ v)` of the ball of initial points
  have hmem : ∀ v ∈ ball (0 : Fin n → ℝ) (s * r), (x, s⁻¹ • v) ∈ ball p₀ r := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    rw [mem_ball, Prod.dist_eq]
    refine max_lt (by simpa [hp₀] using h.r_pos) ?_
    show Dist.dist (s⁻¹ • v) (0 : Fin n → ℝ) < r
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs0),
      inv_mul_lt_iff₀ hs0]
    exact hv
  refine ⟨s * r, fun v => (Ψ s (x, s⁻¹ • v)).1, mul_pos hs0 h.r_pos, ?_, ?_, ?_, ?_⟩
  · simp only [smul_zero]
    rw [← hp₀, hconst s hsI']
  · have hι : ContDiff ℝ ∞ (fun v : Fin n → ℝ => (s, ((x, s⁻¹ • v) : (Fin n → ℝ) × (Fin n → ℝ)))) :=
      contDiff_const.prodMk (contDiff_const.prodMk (contDiff_id.const_smul s⁻¹))
    exact contDiff_fst.comp_contDiffOn (hsm.comp hι.contDiffOn fun v hv => ⟨hsI, hmem v hv⟩)
  · -- the derivative at `0`, from the variational equation along the constant geodesic
    have hA' : ∀ t ∈ Icc (-T) T, fderiv ℝ (geodField g) (Ψ t p₀) =
        (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin n → ℝ)).prod
          (0 : (Fin n → ℝ) × (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := fun t ht => by
      rw [hconst t ht]; exact (hasFDerivAt_geodField_zero hg hx).fderiv
    have hDΨ : ∀ η : Fin n → ℝ, fderiv ℝ (Ψ s) p₀ ((0 : Fin n → ℝ), η) = (s • η, η) := by
      intro η
      have hu : ∀ t ∈ Icc (-T) T, HasDerivWithinAt
          (fun t => fderiv ℝ (Ψ t) p₀ ((0 : Fin n → ℝ), η))
          (fderiv ℝ (geodField g) (Ψ t p₀) (fderiv ℝ (Ψ t) p₀ ((0 : Fin n → ℝ), η)))
          (Icc (-T) T) t := by
        intro t ht
        have h1 := (h.hasDerivWithinAt_fderiv_flow hp₀r ht).clm_apply
          (hasDerivWithinAt_const t (Icc (-T) T) ((0 : Fin n → ℝ), η))
        simpa using h1
      have hv : ∀ t ∈ Icc (-T) T, HasDerivWithinAt (fun t : ℝ => (t • η, η))
          (fderiv ℝ (geodField g) (Ψ t p₀) (t • η, η)) (Icc (-T) T) t := by
        intro t ht
        rw [hA' t ht]
        have h1 : HasDerivWithinAt (fun t : ℝ => (t • η, η)) ((1 : ℝ) • η, (0 : Fin n → ℝ))
            (Icc (-T) T) t :=
          ((hasDerivWithinAt_id t _).smul_const η).prodMk (hasDerivWithinAt_const t _ η)
        simpa using h1
      have h0 : (fun t => fderiv ℝ (Ψ t) p₀ ((0 : Fin n → ℝ), η)) 0 =
          (fun t : ℝ => (t • η, η)) 0 := by
        simp [h.fderiv_flow_zero hp₀r]
      exact Lightlike.ODE.eqOn_of_linear (A := fun t => fderiv ℝ (geodField g) (Ψ t p₀))
        (K := K) (fun t ht => h.norm_fderiv_le _ (h.flow_mem _ hp₀r t ht)) hu hv h0 hsI'
    have hinner : HasFDerivAt (fun v : Fin n → ℝ => ((x, s⁻¹ • v) : (Fin n → ℝ) × (Fin n → ℝ)))
        ((0 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod
          (s⁻¹ • ContinuousLinearMap.id ℝ (Fin n → ℝ))) 0 :=
      (hasFDerivAt_const x (0 : Fin n → ℝ)).prodMk ((hasFDerivAt_id (0 : Fin n → ℝ)).const_smul s⁻¹)
    have hΨd : HasFDerivAt (Ψ s) (fderiv ℝ (Ψ s) p₀) ((x, s⁻¹ • (0 : Fin n → ℝ))) := by
      rw [smul_zero]; exact (h.differentiableAt_flow hp₀r hsI').hasFDerivAt
    have hcomp := (hasFDerivAt_fst (𝕜 := ℝ) (p := Ψ s (x, s⁻¹ • (0 : Fin n → ℝ)))).comp
      (0 : Fin n → ℝ) (HasFDerivAt.comp (0 : Fin n → ℝ) hΨd hinner)
    refine hcomp.congr_fderiv (ContinuousLinearMap.ext fun ξ => ?_)
    show (fderiv ℝ (Ψ s) p₀ ((0 : Fin n → ℝ), s⁻¹ • ξ)).1 = ξ
    rw [hDΨ (s⁻¹ • ξ), smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  · intro v hv
    have hpv := hmem v hv
    have hgeo : IsGeodesicOn g (fun t => (Ψ t (x, s⁻¹ • v)).1) (fun t => (Ψ t (x, s⁻¹ • v)).2)
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
    refine ⟨fun t => (Ψ (s * t) (x, s⁻¹ • v)).1, fun t => s • (Ψ (s * t) (x, s⁻¹ • v)).2,
      ?_, ?_, ?_, ⟨fun t ht => hsc.pos t (hsub ht), fun t ht => hsc.vel t (hsub ht)⟩⟩
    · simp [h.flow_zero _ hpv]
    · simp [h.flow_zero _ hpv, smul_smul, mul_inv_cancel₀ hs0.ne']
    · simp

end Lightlike.Geodesic
