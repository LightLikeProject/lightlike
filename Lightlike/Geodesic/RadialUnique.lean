import Lightlike.Geodesic.ExpDiffeo
import Lightlike.Geodesic.Radial
import Lightlike.Geodesic.Gauss

/-!
# A geodesic from the centre of a normal chart which stays in the chart is radial

In a normal chart `φ` at `p` on the ball of radius `ρ`, a geodesic `Λ` from `p` with initial
velocity `ξ` whose points on `[0, S]` lie in `φ (B(0, r))`, `r < ρ`, is the radial geodesic
`s ↦ φ (s ξ)`, with `s ξ ∈ B(0, r)` (`IsNormalChart.geodesic_eq_radial`). It is the uniqueness half
of "geodesics from the centre of a normal chart are the radial lines".
-/

open Set Metric Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Geodesic

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

namespace IsNormalChart

variable {p : Fin n → ℝ} {ρ : ℝ} {φ : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ)}

/-- **The radial line is a geodesic near each time at which it is in the normal ball.** -/
theorem exists_radial_geodesic (h : IsNormalChart g U p ρ φ) {ξ : Fin n → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hxξ : x • ξ ∈ ball (0 : Fin n → ℝ) ρ) :
    ∃ (R wR : ℝ → Fin n → ℝ) (I : Set ℝ), I ∈ 𝓝 x ∧ IsGeodesicOn g R wR I ∧
      ∀ᶠ t in 𝓝 x, R t = φ (t • ξ) ∧ wR t = fderiv ℝ φ (t • ξ) ξ := by
  have hopen : IsOpen ((fun t : ℝ => t • ξ) ⁻¹' ball (0 : Fin n → ℝ) ρ) :=
    isOpen_ball.preimage (by fun_prop)
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 hopen x hxξ
  set c : ℝ := x + δ / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hcξ : c • ξ ∈ ball (0 : Fin n → ℝ) ρ := hsub (by
    rw [Metric.mem_ball, Real.dist_eq, hc, show x + δ / 2 - x = δ / 2 by ring,
      abs_of_pos (by linarith)]; linarith)
  obtain ⟨γ', w', -, -, -, hgeo', hγ'⟩ := h.geodesic (c • ξ) hcξ
  have hgeoS := hgeo'.scale c⁻¹
  refine ⟨fun t => γ' (c⁻¹ * t), fun t => c⁻¹ • w' (c⁻¹ * t),
    (fun t => c⁻¹ * t) ⁻¹' Ioo (-1 : ℝ) 2, ?_, hgeoS, ?_⟩
  · refine (isOpen_Ioo.preimage (by fun_prop)).mem_nhds ?_
    show c⁻¹ * x ∈ Ioo (-1 : ℝ) 2
    have : c⁻¹ * x < 1 := by rw [inv_mul_lt_iff₀ hcpos]; rw [hc]; linarith
    constructor
    · have : 0 ≤ c⁻¹ * x := mul_nonneg (inv_nonneg.2 hcpos.le) hx
      linarith
    · linarith
  · -- near `x` the rescaled geodesic is the radial line
    have hnear : ∀ᶠ t in 𝓝 x, |c⁻¹ * t| < 1 ∧ t • ξ ∈ ball (0 : Fin n → ℝ) ρ := by
      have h1 : ∀ᶠ t in 𝓝 x, |c⁻¹ * t| < 1 := by
        have : ContinuousAt (fun t : ℝ => |c⁻¹ * t|) x := by fun_prop
        refine this.eventually (gt_mem_nhds ?_)
        show |c⁻¹ * x| < 1
        rw [abs_mul, abs_of_pos (inv_pos.2 hcpos), abs_of_nonneg hx, inv_mul_lt_iff₀ hcpos]
        rw [hc]; linarith
      exact h1.and (hopen.mem_nhds hxξ)
    have hR : ∀ᶠ t in 𝓝 x, γ' (c⁻¹ * t) = φ (t • ξ) := by
      filter_upwards [hnear] with t ht
      rw [hγ' _ ⟨(abs_lt.1 ht.1).1.le, (abs_lt.1 ht.1).2.le⟩, smul_smul]
      congr 2
      field_simp
    filter_upwards [hnear.eventually_nhds, hR.eventually_nhds, hR] with t ht hRn hRt
    refine ⟨hRt, ?_⟩
    have ht0 : |c⁻¹ * t| < 1 ∧ t • ξ ∈ ball (0 : Fin n → ℝ) ρ := ht.self_of_nhds
    have hmem : t ∈ (fun t => c⁻¹ * t) ⁻¹' Ioo (-1 : ℝ) 2 := by
      have := abs_lt.1 ht0.1
      exact ⟨this.1, by linarith [this.2]⟩
    have h1 := hgeoS.pos t hmem
    have hsrc : t • ξ ∈ φ.source := by rw [h.source_eq]; exact ht0.2
    have hdφ : HasFDerivAt φ (fderiv ℝ φ (t • ξ)) (t • ξ) :=
      ((h.contDiffOn.contDiffAt (φ.open_source.mem_nhds hsrc)).differentiableAt (by simp)).hasFDerivAt
    have hin : HasDerivAt (fun s : ℝ => s • ξ) ξ t := by
      simpa using (hasDerivAt_id t).smul_const ξ
    have h2 := hdφ.comp_hasDerivAt t hin
    exact h1.unique (h2.congr_of_eventuallyEq hRn)

/-- **A geodesic from the centre that stays in the chart is radial.** Let `Λ` be a geodesic on an
open set containing `[0, S]` with `Λ 0 = p` and `Λ s ∈ φ (B(0, r))` for `s ∈ [0, S]`, `r < ρ`. Then
for `ξ = Λ'(0)` and `s ∈ [0, S]`: `s ξ ∈ B(0, r)`, `Λ s = φ (s ξ)` and `Λ'(s) = Dφ(s ξ) ξ`. -/
theorem geodesic_eq_radial (hg : Lightlike.IsCoordMetric g U) (h : IsNormalChart g U p ρ φ)
    {r : ℝ} (hr : 0 < r) (hrρ : r < ρ) {Λ ξ' : ℝ → Fin n → ℝ} {O : Set ℝ} (hO : IsOpen O)
    {S : ℝ} (hOS : Icc 0 S ⊆ O) (hΛ : IsGeodesicOn g Λ ξ' O) (hΛ0 : Λ 0 = p)
    (hΛmem : ∀ s ∈ Icc (0 : ℝ) S, Λ s ∈ φ '' ball (0 : Fin n → ℝ) r) :
    ∀ s ∈ Icc (0 : ℝ) S, s • ξ' 0 ∈ ball (0 : Fin n → ℝ) r ∧ Λ s = φ (s • ξ' 0) ∧
      ξ' s = fderiv ℝ φ (s • ξ' 0) (ξ' 0) := by
  set ξ := ξ' 0 with hξ
  have hbρ : ball (0 : Fin n → ℝ) r ⊆ ball 0 ρ := ball_subset_ball hrρ.le
  have hcb : closedBall (0 : Fin n → ℝ) r ⊆ ball 0 ρ := closedBall_subset_ball hrρ
  have hφcd : ContDiffOn ℝ ∞ φ (ball 0 ρ) := h.source_eq ▸ h.contDiffOn
  have hφc : ContinuousOn φ (ball 0 ρ) := hφcd.continuousOn
  have hDφc : ContinuousOn (fun v => fderiv ℝ φ v) (ball 0 ρ) :=
    hφcd.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  -- the closed set
  set T : Set ℝ := {s | s • ξ ∈ closedBall (0 : Fin n → ℝ) r ∧ Λ s = φ (s • ξ) ∧
    ξ' s = fderiv ℝ φ (s • ξ) ξ} with hT
  have hΛc : ∀ s ∈ Icc (0 : ℝ) S, ContinuousAt Λ s := fun s hs => (hΛ.pos s (hOS hs)).continuousAt
  have hξc : ∀ s ∈ Icc (0 : ℝ) S, ContinuousAt ξ' s := fun s hs => (hΛ.vel s (hOS hs)).continuousAt
  have hclosed : IsClosed (T ∩ Icc 0 S) := by
    set C : Set ℝ := {s | s • ξ ∈ closedBall (0 : Fin n → ℝ) r} ∩ Icc 0 S with hC
    have hCc : IsClosed C :=
      (isClosed_closedBall.preimage (by fun_prop)).inter isClosed_Icc
    have hmapC : ∀ s ∈ C, s • ξ ∈ ball (0 : Fin n → ℝ) ρ := fun s hs => hcb hs.1
    have hf1 : ContinuousOn (fun s => Λ s - φ (s • ξ)) C := by
      refine ContinuousOn.sub (fun s hs => (hΛc s hs.2).continuousWithinAt) ?_
      exact hφc.comp (by fun_prop : Continuous fun s : ℝ => s • ξ).continuousOn hmapC
    have hf2 : ContinuousOn (fun s => ξ' s - fderiv ℝ φ (s • ξ) ξ) C := by
      refine ContinuousOn.sub (fun s hs => (hξc s hs.2).continuousWithinAt) ?_
      exact (hDφc.comp (by fun_prop : Continuous fun s : ℝ => s • ξ).continuousOn hmapC).clm_apply
        continuousOn_const
    have e : T ∩ Icc 0 S = C ∩ (fun s => Λ s - φ (s • ξ)) ⁻¹' {0} ∩
        (fun s => ξ' s - fderiv ℝ φ (s • ξ) ξ) ⁻¹' {0} := by
      ext s
      simp only [hT, hC, mem_inter_iff, mem_setOf_eq, mem_preimage, mem_singleton_iff, sub_eq_zero]
      tauto
    rw [e]
    have h1c := hf1.preimage_isClosed_of_isClosed hCc (isClosed_singleton (x := (0 : Fin n → ℝ)))
    exact (hf2.mono inter_subset_left).preimage_isClosed_of_isClosed h1c
      (isClosed_singleton (x := (0 : Fin n → ℝ)))
  -- on `Icc 0 S`, `s ξ ∈ closedBall` and `Λ s = φ (s ξ)` give `s ξ ∈ ball`
  have hball : ∀ s : ℝ, 0 ≤ s → s ∈ Icc (0 : ℝ) S → s ∈ T → s • ξ ∈ ball (0 : Fin n → ℝ) r := by
    intro s _ hs hsT
    obtain ⟨v, hv, hvs⟩ := hΛmem s hs
    have hinj := φ.injOn
    have : v = s • ξ := hinj (by rw [h.source_eq]; exact hbρ hv) (by rw [h.source_eq]; exact hcb hsT.1)
      (by rw [hvs, hsT.2.1])
    rw [← this]; exact hv
  have hmain : Icc (0 : ℝ) S ⊆ T := by
    refine hclosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_
    · refine ⟨by simp [hr.le], ?_, ?_⟩
      · rw [zero_smul, hΛ0, h.map_zero]
      · rw [zero_smul, h.hasFDerivAt_zero.fderiv]; rfl
    · rintro x ⟨hxT, hx0, hxS⟩
      have hxI : x ∈ Icc (0 : ℝ) S := ⟨hx0, hxS.le⟩
      have hxb := hball x hx0 hxI hxT
      obtain ⟨R, wR, I, hI, hgeoR, hev⟩ := h.exists_radial_geodesic hx0 (hbρ hxb)
      have hΛU : Λ x ∈ U := by
        rw [hxT.2.1]
        exact h.target_subset (φ.map_source (by rw [h.source_eq]; exact hbρ hxb))
      have hR0 : R x = φ (x • ξ) := hev.self_of_nhds.1
      have hw0 : wR x = fderiv ℝ φ (x • ξ) ξ := hev.self_of_nhds.2
      have hph := IsGeodesicOn.eventuallyEq hg (hO.mem_nhds (hOS hxI)) hI hΛ hgeoR hΛU
        (by rw [hxT.2.1, hR0]) (by rw [hxT.2.2, hw0])
      have hopenb : ∀ᶠ t in 𝓝 x, t • ξ ∈ ball (0 : Fin n → ℝ) r :=
        (isOpen_ball.preimage (by fun_prop : Continuous fun t : ℝ => t • ξ)).mem_nhds hxb
      refine mem_nhdsWithin_of_mem_nhds ?_
      filter_upwards [hph, hev, hopenb] with t h1 h2 h3
      have h1' : Λ t = R t ∧ ξ' t = wR t := ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
      exact ⟨ball_subset_closedBall h3, by rw [h1'.1, h2.1], by rw [h1'.2, h2.2]⟩
  intro s hs
  exact ⟨hball s hs.1 hs (hmain hs), (hmain hs).2.1, (hmain hs).2.2⟩

end IsNormalChart

end Lightlike.Geodesic
