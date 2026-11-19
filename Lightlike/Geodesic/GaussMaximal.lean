import Lightlike.Geodesic.Variation
import Lightlike.ODE.FlowVariational

/-!
# The exponential map and the Gauss lemma on the whole domain of `exp`

Let `γ` be a geodesic of a coordinate metric `g` on `U`, defined on an open set containing
`[0, 1]`, with `γ 0 = x` and initial velocity `v`: in the language of the source, `v` lies in the
domain `D_x` of `exp_x`. Then (`Lightlike.Geodesic.exists_expMap_along_gauss`):

* the geodesics from `x` with initial velocity `u` near `v` are also defined on an open interval
  containing `[0, 1]`, and their endpoints `E u` depend smoothly on `u` (the domain of `exp_x` is
  open and `exp_x` is smooth on it: the source's Proposition 2.2.3 and the smoothness of the
  geodesic flow);
* the Gauss lemma holds at `v`: `g (E v) (DE(v) v, DE(v) w₁) = g x (v, w₁)` for every `w₁`.

Unlike `IsNormalChart.gauss`, there is no restriction to a normal neighbourhood: `v` may be any
vector whose geodesic reaches time `1`.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), Theorem 2.1.21 (Gauss lemma),
  page 43, with `0 ≠ x ∈ D_p`, and Proposition 2.2.3 (the domain of `exp`), page 46.
-/

open Set Metric Filter Topology Matrix
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The exponential map near a vector of its domain, and the Gauss lemma there**
(Kunzinger–Steinbauer, Proposition 2.2.3 and Theorem 2.1.21, for a coordinate metric of any
signature).

Let `γ` be a geodesic with velocity `w`, defined on an open set containing `[0, 1]`, with values
in `U` on `[0, 1]`. Then there are `δ > 0` and a map `E`, smooth on the ball of radius `δ` about
`w 0`, with `E (w 0) = γ 1`, such that every `u` in that ball is the initial velocity of a
geodesic from `γ 0`, defined on an open interval containing `[0, 1]` and with values in `U` on
`[0, 1]`, which reaches `E u` at time `1`; and for every `w₁`,
`g (E (w 0)) (DE(w 0) (w 0), DE(w 0) w₁) = g (γ 0) (w 0, w₁)`. -/
theorem exists_expMap_along_gauss (hg : Lightlike.IsCoordMetric g U) {γ w : ℝ → Fin n → ℝ}
    {I : Set ℝ} (h01 : Icc (0 : ℝ) 1 ⊆ I) (hgeo : IsGeodesicOn g γ w I)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) :
    ∃ (δ : ℝ) (E : (Fin n → ℝ) → (Fin n → ℝ)), 0 < δ ∧ ContDiffOn ℝ ∞ E (ball (w 0) δ) ∧
      E (w 0) = γ 1 ∧
      (∀ u ∈ ball (w 0) δ, ∃ (η : ℝ) (γ' w' : ℝ → Fin n → ℝ), 0 < η ∧ γ' 0 = γ 0 ∧ w' 0 = u ∧
        γ' 1 = E u ∧ IsGeodesicOn g γ' w' (Ioo (-η) (1 + η)) ∧ ∀ t ∈ Icc (0 : ℝ) 1, γ' t ∈ U) ∧
      ∀ w₁ : Fin n → ℝ,
        pairing g (E (w 0)) (fderiv ℝ E (w 0) (w 0)) (fderiv ℝ E (w 0) w₁) =
          pairing g (γ 0) (w 0) w₁ := by
  set x : Fin n → ℝ := γ 0 with hx
  set v : Fin n → ℝ := w 0 with hv
  have hO : IsOpen (U ×ˢ (univ : Set (Fin n → ℝ))) := hg.isOpen.prod isOpen_univ
  have hGs := contDiffOn_geodField hg
  set c : ℝ → (Fin n → ℝ) × (Fin n → ℝ) := fun t => (γ t, w t) with hc
  have hcs : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt c (geodField g (c t)) (Icc 0 1) t ∧
      c t ∈ U ×ˢ (univ : Set (Fin n → ℝ)) := fun t ht =>
    ⟨(hgeo.hasDerivAt_phase (h01 ht)).hasDerivWithinAt, ⟨hU t ht, mem_univ _⟩⟩
  obtain ⟨r, η, Φ, hr, hη, hΦ, hΦs, hΦc⟩ :=
    Lightlike.ODE.exists_flow_along hO hGs zero_le_one hcs
  have hc0 : c 0 = (x, v) := rfl
  rw [hc0] at hΦ hΦs hΦc
  set y₀ : (Fin n → ℝ) × (Fin n → ℝ) := (x, v) with hy₀
  have hS : IsOpen (Ioo (-η) (1 + η) ×ˢ ball y₀ r) := isOpen_Ioo.prod isOpen_ball
  have h0J : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have h1J : (1 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have hymem : ∀ u ∈ ball v r, ((x, u) : (Fin n → ℝ) × (Fin n → ℝ)) ∈ ball y₀ r := by
    intro u hu
    rw [mem_ball, Prod.dist_eq]
    refine max_lt ?_ (mem_ball.1 hu)
    show Dist.dist x x < r
    rw [dist_self]; exact hr
  have hy₀r : y₀ ∈ ball y₀ r := mem_ball_self hr
  have hxU : x ∈ U := hU 0 ⟨le_rfl, zero_le_one⟩
  have hsol : ∀ q ∈ Ioo (-η) (1 + η) ×ˢ ball y₀ r,
      HasDerivAt (fun τ => Φ τ q.2) (geodField g (Φ q.1 q.2)) q.1 := fun q hq =>
    ((hΦ q.2 hq.2).2 q.1 hq.1).1
  have hmemO : ∀ q ∈ Ioo (-η) (1 + η) ×ˢ ball y₀ r, (Φ q.1 q.2).1 ∈ U := fun q hq =>
    (((hΦ q.2 hq.2).2 q.1 hq.1).2).1
  -- the geodesic with initial velocity `u`
  have hgeou : ∀ u ∈ ball v r, IsGeodesicOn g (fun t => (Φ t (x, u)).1)
      (fun t => (Φ t (x, u)).2) (Ioo (-η) (1 + η)) := fun u hu =>
    isGeodesicOn_of_phase fun t ht => hsol (t, (x, u)) ⟨ht, hymem u hu⟩
  have hΦ0 : ∀ u ∈ ball v r, Φ 0 (x, u) = (x, u) := fun u hu => (hΦ _ (hymem u hu)).1
  have hιE : ContDiff ℝ ∞ (fun u : Fin n → ℝ =>
      ((1 : ℝ), ((x, u) : (Fin n → ℝ) × (Fin n → ℝ)))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hEs : ContDiffOn ℝ ∞ (fun u : Fin n → ℝ => (Φ 1 (x, u)).1) (ball v r) :=
    contDiff_fst.comp_contDiffOn (hΦs.comp hιE.contDiffOn fun u hu => ⟨h1J, hymem u hu⟩)
  have hvr : v ∈ ball v r := mem_ball_self hr
  refine ⟨r, fun u => (Φ 1 (x, u)).1, hr, hEs, ?_, fun u hu => ?_, fun w₁ => ?_⟩
  · show (Φ 1 y₀).1 = γ 1
    rw [hΦc 1 ⟨zero_le_one, le_rfl⟩]
  · refine ⟨η, fun t => (Φ t (x, u)).1, fun t => (Φ t (x, u)).2, hη, ?_, ?_, rfl, hgeou u hu,
      fun t ht => hmemO (t, (x, u)) ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hymem u hu⟩⟩
    · show (Φ 0 (x, u)).1 = x
      rw [hΦ0 u hu]
    · show (Φ 0 (x, u)).2 = u
      rw [hΦ0 u hu]
  · -- the Gauss lemma at `v`
    set ζ : (Fin n → ℝ) × (Fin n → ℝ) := ((0 : Fin n → ℝ), w₁) with hζ
    have e0 : v + (0 : ℝ) • w₁ = v := by simp
    obtain ⟨δ₁, hδ₁, hδ₁b⟩ : ∃ δ₁ > 0, ∀ s ∈ ball (0 : ℝ) δ₁, v + s • w₁ ∈ ball v r := by
      have hcont : Continuous fun s : ℝ => v + s • w₁ := by fun_prop
      have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), v + s • w₁ ∈ ball v r :=
        (hcont.tendsto 0).eventually (isOpen_ball.mem_nhds (by simpa using hvr))
      exact Metric.eventually_nhds_iff_ball.1 h1
    set F : ℝ → ℝ → Fin n → ℝ := fun t s => (Φ t (x, v + s • w₁)).1 with hF
    set a : ℝ → ℝ → Fin n → ℝ := fun t s => (Φ t (x, v + s • w₁)).2 with ha
    have hΦty : ∀ t ∈ Ioo (-η) (1 + η), HasFDerivAt (Φ t) (fderiv ℝ (Φ t) y₀) y₀ := by
      intro t ht
      have h1 : ContDiffAt ℝ ∞ (Φ t) y₀ :=
        ContDiffAt.comp (g := fun p : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => Φ p.1 p.2)
          (f := fun y' : (Fin n → ℝ) × (Fin n → ℝ) => (t, y')) y₀
          (hΦs.contDiffAt (hS.mem_nhds ⟨ht, hy₀r⟩)) (contDiffAt_const.prodMk contDiffAt_id)
      exact (h1.differentiableAt (by simp)).hasFDerivAt
    have h3 : HasDerivAt (fun s : ℝ => v + s • w₁) w₁ 0 := by
      have h0 := ((hasDerivAt_id (0 : ℝ)).smul_const w₁).const_add v
      rw [one_smul] at h0
      exact h0
    have hscurve : HasDerivAt (fun s : ℝ => ((x, v + s • w₁) : (Fin n → ℝ) × (Fin n → ℝ)))
        ζ 0 := (hasDerivAt_const (0 : ℝ) x).prodMk h3
    set ψ : ℝ → ℝ := fun τ => pairing g (F τ 0) (a τ 0) (fderiv ℝ (Φ τ) y₀ ζ).1 with hψ
    have key : ∀ t ∈ Ioo (-η) (1 + η), HasDerivAt ψ (pairing g x v w₁) t := by
      intro t ht
      have hq0 : ((t, (x, v + (0 : ℝ) • w₁)) : ℝ × ((Fin n → ℝ) × (Fin n → ℝ))) ∈
          Ioo (-η) (1 + η) ×ˢ ball y₀ r := by rw [e0]; exact ⟨ht, hy₀r⟩
      have hUF : F t 0 ∈ U := hmemO _ hq0
      have hph := hsol _ hq0
      have hFt : HasDerivAt (fun τ => F τ 0) (a t 0) t := hph.fst
      have hat : HasDerivAt (fun τ => a τ 0) (accel g (F t 0) (a t 0)) t := hph.snd
      have hΦty' : HasFDerivAt (Φ t) (fderiv ℝ (Φ t) y₀) (x, v + (0 : ℝ) • w₁) := by
        rw [e0]; exact hΦty t ht
      have hpairs : HasDerivAt (fun s : ℝ => Φ t (x, v + s • w₁)) (fderiv ℝ (Φ t) y₀ ζ) 0 :=
        hΦty'.comp_hasDerivAt (0 : ℝ) hscurve
      have hFs : HasDerivAt (fun s => F t s) (fderiv ℝ (Φ t) y₀ ζ).1 0 := hpairs.fst
      have has : HasDerivAt (fun s => a t s) (fderiv ℝ (Φ t) y₀ ζ).2 0 := hpairs.snd
      have hVd : DifferentiableAt ℝ (geodField g) (Φ t y₀) :=
        (hGs.contDiffAt (hO.mem_nhds ⟨hmemO (t, y₀) ⟨ht, hy₀r⟩, mem_univ _⟩)).differentiableAt
          (by simp)
      have hvar := Lightlike.ODE.hasDerivAt_fderiv_flow_of_contDiffOn hS hΦs hsol
        (t := t) (y := y₀) ⟨ht, hy₀r⟩ hVd ζ
      have hbt : HasDerivAt (fun τ => (fderiv ℝ (Φ τ) y₀ ζ).1) (fderiv ℝ (Φ t) y₀ ζ).2 t := by
        have h4 : HasDerivAt (fun τ => (fderiv ℝ (Φ τ) y₀ ζ).1)
            (fderiv ℝ (geodField g) (Φ t y₀) (fderiv ℝ (Φ t) y₀ ζ)).1 t := hvar.fst
        have h5 : (fderiv ℝ (geodField g) (Φ t y₀) (fderiv ℝ (Φ t) y₀ ζ)).1 =
            (fderiv ℝ (Φ t) y₀ ζ).2 :=
          fderiv_geodField_fst hg (hmemO (t, y₀) ⟨ht, hy₀r⟩) _
        rw [h5] at h4
        exact h4
      have hN : ∀ᶠ s in 𝓝 (0 : ℝ), normSq g (F t s) (a t s) = normSq g x (v + s • w₁) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ₁] with s hs
        have hu := hδ₁b s hs
        have hsp : ∀ σ ∈ Ioo (-η) (1 + η),
            HasDerivAt (fun σ => normSq g (F σ s) (a σ s)) 0 σ := fun σ hσ =>
          (hgeou _ hu).hasDerivAt_speed hg hσ (hmemO (σ, (x, v + s • w₁)) ⟨hσ, hymem _ hu⟩)
        have h5 := eq_of_hasDerivAt_zero_Ioo hsp ht h0J
        simp only [hF, ha, hΦ0 _ hu] at h5
        exact h5
      have h6 := hasDerivAt_pairing_variation hg (F := F) (a := a)
        (b := fun τ => (fderiv ℝ (Φ τ) y₀ ζ).1) hUF hFt hat hFs hbt has hN
        (hasDerivAt_normSq_line hg hxU v w₁)
      have h7 : 2 * pairing g x v w₁ / 2 = pairing g x v w₁ := by ring
      rw [h7] at h6
      exact h6
    have hconst : ∀ τ ∈ Ioo (-η) (1 + η),
        HasDerivAt (fun τ => ψ τ - τ * pairing g x v w₁) 0 τ := fun τ hτ => by
      have h1 : HasDerivAt (fun τ => ψ τ - τ * pairing g x v w₁)
          (pairing g x v w₁ - 1 * pairing g x v w₁) τ :=
        (key τ hτ).sub ((hasDerivAt_id τ).mul_const (pairing g x v w₁))
      have h2 : pairing g x v w₁ - 1 * pairing g x v w₁ = 0 := by ring
      rw [h2] at h1
      exact h1
    have h8 := eq_of_hasDerivAt_zero_Ioo hconst h1J h0J
    -- at time `0` the flow is the identity
    have hD0 : fderiv ℝ (Φ 0) y₀ = ContinuousLinearMap.id ℝ _ := by
      have hev : Φ 0 =ᶠ[𝓝 y₀] id := by
        filter_upwards [isOpen_ball.mem_nhds hy₀r] with y hy using (hΦ y hy).1
      rw [hev.fderiv_eq]
      exact fderiv_id
    have hψ0 : ψ 0 = 0 := by
      simp only [hψ, hD0, ContinuousLinearMap.id_apply, hζ]
      exact pairing_zero_right g _ _
    simp only [hψ0, zero_mul, sub_zero, one_mul] at h8
    -- the derivative of `E` in the direction `w₁`
    have hEd : HasFDerivAt (fun u : Fin n → ℝ => (Φ 1 (x, u)).1)
        ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin n → ℝ)).comp
          ((fderiv ℝ (Φ 1) y₀).comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin n → ℝ)))) v :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := Φ 1 (x, v))).comp v
        (HasFDerivAt.comp v (hΦty 1 h1J) (hasFDerivAt_prodMk_right x v))
    have hEw : fderiv ℝ (fun u : Fin n → ℝ => (Φ 1 (x, u)).1) v w₁ =
        (fderiv ℝ (Φ 1) y₀ ζ).1 := by
      rw [hEd.fderiv]; rfl
    -- the radial derivative of `E` is the velocity of the geodesic at time `1`
    have hEv : fderiv ℝ (fun u : Fin n → ℝ => (Φ 1 (x, u)).1) v v = (Φ 1 y₀).2 := by
      have hchain : HasDerivAt (fun τ : ℝ => (Φ 1 (x, τ • v)).1)
          (fderiv ℝ (fun u : Fin n → ℝ => (Φ 1 (x, u)).1) v v) 1 := by
        have h9 : HasDerivAt (fun τ : ℝ => τ • v) v 1 := by
          have h0 := (hasDerivAt_id (1 : ℝ)).smul_const v
          rw [one_smul] at h0
          exact h0
        have hEd' : HasFDerivAt (fun u : Fin n → ℝ => (Φ 1 (x, u)).1)
            (fderiv ℝ (fun u : Fin n → ℝ => (Φ 1 (x, u)).1) v) ((1 : ℝ) • v) := by
          rw [one_smul]; exact hEd.differentiableAt.hasFDerivAt
        exact hEd'.comp_hasDerivAt (1 : ℝ) h9
      have hgeo1 : HasDerivAt (fun τ : ℝ => (Φ τ y₀).1) (Φ 1 y₀).2 1 :=
        (hsol (1, y₀) ⟨h1J, hy₀r⟩).fst
      -- homogeneity: for `τ` near `1`, the geodesic with velocity `τ v` at time `1` is `γ_v (τ)`
      have hhomev : (fun τ : ℝ => (Φ 1 (x, τ • v)).1) =ᶠ[𝓝 (1 : ℝ)] fun τ => (Φ τ y₀).1 := by
        have hcτ : Continuous fun τ : ℝ => τ • v := by fun_prop
        have h10 : ∀ᶠ τ in 𝓝 (1 : ℝ), τ • v ∈ ball v r :=
          (hcτ.tendsto 1).eventually (isOpen_ball.mem_nhds (by simpa using hvr))
        have h11 : ∀ᶠ τ in 𝓝 (1 : ℝ), τ ∈ Ioo (1 / 2 : ℝ) (1 + η) :=
          Ioo_mem_nhds (by norm_num) (by linarith)
        filter_upwards [h10, h11] with τ hτb hτI
        have hτ0 : 0 < τ := by linarith [hτI.1]
        have hsc := (hgeou v hvr).scale τ
        have hpre : IsOpen ((fun t => τ * t) ⁻¹' Ioo (-η) (1 + η)) :=
          isOpen_Ioo.preimage (continuous_const.mul continuous_id)
        have hsubA : Icc (0 : ℝ) 1 ⊆ (fun t => τ * t) ⁻¹' Ioo (-η) (1 + η) := by
          intro t ht
          constructor
          · have : 0 ≤ τ * t := mul_nonneg hτ0.le ht.1
            show -η < τ * t
            linarith
          · have : τ * t ≤ τ * 1 := mul_le_mul_of_nonneg_left ht.2 hτ0.le
            show τ * t < 1 + η
            linarith [hτI.2]
        have hsubB : Icc (0 : ℝ) 1 ⊆ Ioo (-η) (1 + η) := fun t ht =>
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hUA : ∀ t ∈ Icc (0 : ℝ) 1, (fun t => (Φ (τ * t) (x, v)).1) t ∈ U := fun t ht =>
          hmemO (τ * t, y₀) ⟨hsubA ht, hy₀r⟩
        have heq := IsGeodesicOn.eqOn_Icc hg hpre isOpen_Ioo hsubA hsubB hsc (hgeou _ hτb) hUA
          (by simp [hΦ0 v hvr, hΦ0 _ hτb]) (by simp [hΦ0 v hvr, hΦ0 _ hτb]) 1
          ⟨zero_le_one, le_rfl⟩
        have h12 := heq.1
        simp only [mul_one] at h12
        exact h12.symm
      exact (hgeo1.congr_of_eventuallyEq hhomev).unique hchain |>.symm
    show pairing g ((Φ 1 (x, v)).1) (fderiv ℝ (fun u : Fin n → ℝ => (Φ 1 (x, u)).1) v v)
      (fderiv ℝ (fun u : Fin n → ℝ => (Φ 1 (x, u)).1) v w₁) = pairing g x v w₁
    have h13 : ψ 1 = pairing g x v w₁ := by linarith
    rw [hEv, hEw, ← h13]
    show pairing g (Φ 1 y₀).1 (Φ 1 y₀).2 (fderiv ℝ (Φ 1) y₀ ζ).1 =
      pairing g (Φ 1 (x, v + (0 : ℝ) • w₁)).1 (Φ 1 (x, v + (0 : ℝ) • w₁)).2
        (fderiv ℝ (Φ 1) y₀ ζ).1
    rw [e0]

end Lightlike.Geodesic
