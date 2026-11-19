import Lightlike.ODE.FlowBoxSmooth

/-!
# The flow along a whole trajectory

Let `V` be a smooth vector field on an open set `O` of a real Banach space and `c` an integral
curve of `V` in `O` on `[0, T]`. Then the solutions that start near `c 0` exist on an open
interval containing `[0, T]`, stay in `O`, and depend smoothly on the time and the initial point
(`Lightlike.ODE.exists_flow_along`). In the language of flows: the domain of the flow is open,
and the flow is smooth on it.

The proof continues a flow in the time, one flow box at a time: if a smooth flow near `c 0` is
known up to a time `t₁` close to `t*`, the flow box at `c t*` extends it to all times close to
`t*`. The interval `[0, T]` is connected.

## References

* `kunzinger-steinbauer-2020`: M. Kunzinger and R. Steinbauer, *Riemannian Geometry*, lecture
  notes, University of Vienna (version of 11 December 2025), proof of Proposition 2.2.3,
  page 46: "the maximal domain of the flow is open", quoted there from the authors' analysis on
  manifolds notes ([12, 2.3.3(iii)]), which were not opened.
* `teschl-2012`: G. Teschl, *Ordinary Differential Equations and Dynamical Systems*, Theorem 2.10,
  page 46 of the author's version, for the regularity.
-/

open Set Metric Filter Topology
open scoped NNReal ContDiff

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A smooth flow of `V` in `O` for initial points near `p`, for the times in an open interval
around `[0, T']`, which follows the curve `c` from `p`. -/
def HasFlowUpTo (V : E → E) (O : Set E) (c : ℝ → E) (T' : ℝ) : Prop :=
  ∃ (r η : ℝ) (Φ : ℝ → E → E), 0 < r ∧ 0 < η ∧
    (∀ y ∈ ball (c 0) r, Φ 0 y = y ∧ ∀ t ∈ Ioo (-η) (T' + η),
      HasDerivAt (fun t => Φ t y) (V (Φ t y)) t ∧ Φ t y ∈ O) ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) (Ioo (-η) (T' + η) ×ˢ ball (c 0) r) ∧
    ∀ t ∈ Icc 0 T', Φ t (c 0) = c t

omit [CompleteSpace E] in
/-- A flow up to a time is a flow up to every earlier time. -/
lemma HasFlowUpTo.mono {V : E → E} {O : Set E} {c : ℝ → E} {T₁ T₂ : ℝ}
    (h : HasFlowUpTo V O c T₁) (h21 : T₂ ≤ T₁) : HasFlowUpTo V O c T₂ := by
  obtain ⟨r, η, Φ, hr, hη, h1, h2, h3⟩ := h
  have hsub : Ioo (-η) (T₂ + η) ⊆ Ioo (-η) (T₁ + η) := Ioo_subset_Ioo_right (by linarith)
  exact ⟨r, η, Φ, hr, hη, fun y hy => ⟨(h1 y hy).1, fun t ht => (h1 y hy).2 t (hsub ht)⟩,
    h2.mono (prod_mono hsub subset_rfl), fun t ht => h3 t ⟨ht.1, ht.2.trans h21⟩⟩

set_option maxHeartbeats 400000 in
/-- The extension step: near a time `t*`, a flow up to one time `t₁` extends to a flow up to
every time `t₂`. -/
theorem exists_extension_step {V : E → E} {O : Set E} (hO : IsOpen O)
    (hV : ContDiffOn ℝ ∞ V O) {c : ℝ → E} {T : ℝ}
    (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (V (c t)) (Icc 0 T) t ∧ c t ∈ O) {ts : ℝ}
    (hts : ts ∈ Icc 0 T) :
    ∃ ε > 0, ∀ t₁ ∈ Icc 0 T, |t₁ - ts| < ε → HasFlowUpTo V O c t₁ →
      ∀ t₂ ∈ Icc 0 T, |t₂ - ts| < ε → HasFlowUpTo V O c t₂ := by
  set ps : E := c ts with hps
  have hpsO : ps ∈ O := (hc ts hts).2
  have hV1 : ContDiffAt ℝ 1 V ps :=
    (hV.contDiffAt (hO.mem_nhds hpsO)).of_le (by exact_mod_cast le_top)
  obtain ⟨A, hA, H⟩ := exists_isFlowBox hV1
  obtain ⟨aO, haO, hballO⟩ := Metric.isOpen_iff.1 hO ps hpsO
  set a' : ℝ := min A aO with ha'
  have ha'0 : 0 < a' := lt_min hA haO
  obtain ⟨r', T', K', Ψ, hΨ⟩ := H a' ha'0 (min_le_left _ _)
  have hballa : ball ps a' ⊆ O := (ball_subset_ball (min_le_right _ _)).trans hballO
  have hΨs : ContDiffOn ℝ ∞ (fun p : ℝ × E => Ψ p.1 p.2) (Ioo (-T') T' ×ˢ ball ps r') :=
    hΨ.contDiffOn_uncurry_infty (hV.mono hballa)
  have hT' := hΨ.T_pos
  have hr' := hΨ.r_pos
  set ρ' : ℝ := min r' a' with hρ'
  have hρ'0 : 0 < ρ' := lt_min hr' ha'0
  -- continuity of `c` at `ts`
  have hcc : ContinuousWithinAt c (Icc 0 T) ts := (hc ts hts).1.continuousWithinAt
  obtain ⟨ε₁, hε₁, Hε₁⟩ := Metric.continuousWithinAt_iff.1 hcc (ρ' / 2) (half_pos hρ'0)
  have hcnear : ∀ t ∈ Icc 0 T, |t - ts| < ε₁ → c t ∈ ball ps (ρ' / 2) := fun t ht h1 =>
    mem_ball.2 (Hε₁ ht (by rw [Real.dist_eq]; exact h1))
  refine ⟨min ε₁ (T' / 4), lt_min hε₁ (by linarith), ?_⟩
  intro t₁ ht₁ h1ε hP t₂ ht₂ h2ε
  rcases le_or_gt t₂ t₁ with h21 | h12
  · exact hP.mono h21
  obtain ⟨r, η, Φ, hr, hη, hΦ, hΦs, hΦc⟩ := hP
  have h1abs := abs_lt.1 h1ε
  have h2abs := abs_lt.1 h2ε
  have hεT : min ε₁ (T' / 4) ≤ T' / 4 := min_le_right _ _
  have hεε : min ε₁ (T' / 4) ≤ ε₁ := min_le_left _ _
  have hdt : t₂ - t₁ < T' / 2 := by linarith [h1abs.1, h2abs.2]
  have ht₁I : t₁ ∈ Ioo (-η) (t₁ + η) := ⟨by linarith [ht₁.1], by linarith⟩
  have hp₀ : c 0 ∈ ball (c 0) r := mem_ball_self hr
  have hopenΦ : IsOpen (Ioo (-η) (t₁ + η) ×ˢ ball (c 0) r) := isOpen_Ioo.prod isOpen_ball
  -- near `(t₁, c 0)` the flow `Φ` takes values near `ps`
  have hΦt₁ : Φ t₁ (c 0) ∈ ball ps (ρ' / 2) := by
    rw [hΦc t₁ ⟨ht₁.1, le_rfl⟩]
    exact hcnear t₁ ht₁ (lt_of_lt_of_le h1ε hεε)
  have hΦcont : ContinuousAt (fun p : ℝ × E => Φ p.1 p.2) (t₁, c 0) :=
    (hΦs.contDiffAt (hopenΦ.mem_nhds ⟨ht₁I, hp₀⟩)).continuousAt
  have hpre : (fun p : ℝ × E => Φ p.1 p.2) ⁻¹' ball ps (ρ' / 2) ∈ 𝓝 ((t₁, c 0) : ℝ × E) :=
    hΦcont.preimage_mem_nhds (isOpen_ball.mem_nhds hΦt₁)
  obtain ⟨τ₀, hτ₀, hτ₀sub⟩ := Metric.mem_nhds_iff.1 hpre
  set τ : ℝ := min (min (τ₀ / 2) (η / 2)) (T' / 4) with hτ
  have hτ0 : 0 < τ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hττ₀ : τ < τ₀ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hτη : τ < η := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  have hτT : τ ≤ T' / 4 := min_le_right _ _
  set r₂ : ℝ := min r τ₀ with hr₂
  have hr₂0 : 0 < r₂ := lt_min hr hτ₀
  have hr₂r : ball (c 0) r₂ ⊆ ball (c 0) r := ball_subset_ball (min_le_left _ _)
  have hnear : ∀ t : ℝ, |t - t₁| < τ₀ → ∀ y ∈ ball (c 0) r₂, Φ t y ∈ ball ps (ρ' / 2) := by
    intro t ht y hy
    have hmem : ((t, y) : ℝ × E) ∈ ball ((t₁, c 0) : ℝ × E) τ₀ := by
      rw [mem_ball, Prod.dist_eq]
      exact max_lt (by rw [Real.dist_eq]; exact ht)
        (lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _))
    exact hτ₀sub hmem
  have hρr : ball ps (ρ' / 2) ⊆ ball ps r' :=
    ball_subset_ball (by have : ρ' ≤ r' := min_le_left _ _; linarith)
  have hρa : ball ps (ρ' / 2) ⊆ ball ps a' :=
    ball_subset_ball (by have : ρ' ≤ a' := min_le_right _ _; linarith)
  have hΨτ : IsFlowBox V ps a' r' τ K' Ψ := hΨ.mono hr' le_rfl hτ0 (by linarith)
  -- `Φ (t₁ + u) y = Ψ u (Φ t₁ y)` for small `u`
  have hglue : ∀ y ∈ ball (c 0) r₂, ∀ u ∈ Icc (-τ) τ, Φ (t₁ + u) y = Ψ u (Φ t₁ y) := by
    intro y hy u hu
    have hz : Φ t₁ y ∈ ball ps r' := hρr (hnear t₁ (by simpa using hτ₀) y hy)
    have hcu : ∀ v ∈ Icc (-τ) τ, HasDerivWithinAt (fun v => Φ (t₁ + v) y)
        (V (Φ (t₁ + v) y)) (Icc (-τ) τ) v := by
      intro v hv
      have hmem : t₁ + v ∈ Ioo (-η) (t₁ + η) :=
        ⟨by linarith [hv.1, ht₁.1], by linarith [hv.2]⟩
      have h1 := ((hΦ y (hr₂r hy)).2 (t₁ + v) hmem).1.scomp v ((hasDerivAt_id v).const_add t₁)
      have h2 : HasDerivAt (fun v => Φ (t₁ + v) y) (V (Φ (t₁ + v) y)) v := by
        simpa [Function.comp_def] using h1
      exact h2.hasDerivWithinAt
    have hcs : ∀ v ∈ Icc (-τ) τ, Φ (t₁ + v) y ∈ ball ps a' := fun v hv =>
      hρa (hnear (t₁ + v) (by
        rw [add_sub_cancel_left]
        exact lt_of_le_of_lt (abs_le.2 hv) hττ₀) y hy)
    have h0 : (fun v => Φ (t₁ + v) y) 0 = (fun v => Ψ v (Φ t₁ y)) 0 := by
      simp only [add_zero, hΨτ.flow_zero _ hz]
    exact eqOn_of_trajectories hΨτ.lipschitzOnWith hcu hcs (hΨτ.hasDerivWithinAt hz)
      (hΨτ.flow_mem _ hz) h0 hu
  -- the extended flow
  set Φ' : ℝ → E → E := fun t y => if t < t₁ then Φ t y else Ψ (t - t₁) (Φ t₁ y) with hΦ'
  have hΦ'lo : ∀ y ∈ ball (c 0) r₂, ∀ t : ℝ, t < t₁ + τ → Φ' t y = Φ t y := by
    intro y hy t ht
    by_cases h : t < t₁
    · simp only [hΦ', h, ↓reduceIte]
    · simp only [hΦ', h, ↓reduceIte]
      push Not at h
      have := hglue y hy (t - t₁) ⟨by linarith, by linarith⟩
      rw [add_sub_cancel] at this
      exact this.symm
  have hΦ'hi : ∀ y ∈ ball (c 0) r₂, ∀ t : ℝ, t₁ - τ < t → Φ' t y = Ψ (t - t₁) (Φ t₁ y) := by
    intro y hy t ht
    by_cases h : t < t₁
    · simp only [hΦ', h, ↓reduceIte]
      have := hglue y hy (t - t₁) ⟨by linarith, by linarith⟩
      rw [add_sub_cancel] at this
      exact this
    · simp only [hΦ', h, ↓reduceIte]
  set η' : ℝ := min η (T' / 4) with hη'
  have hη'0 : 0 < η' := lt_min hη (by linarith)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'T : η' ≤ T' / 4 := min_le_right _ _
  have hΨmem : ∀ t ∈ Ioo (-η') (t₂ + η'), t₁ - τ < t → t - t₁ ∈ Ioo (-T') T' := fun t ht h =>
    ⟨by linarith, by linarith [ht.2]⟩
  refine ⟨r₂, η', Φ', hr₂0, hη'0, fun y hy => ⟨?_, fun t ht => ?_⟩, ?_, ?_⟩
  · -- the initial condition
    have h0 : (0 : ℝ) < t₁ + τ := by linarith [ht₁.1]
    rw [hΦ'lo y hy 0 h0]
    exact (hΦ y (hr₂r hy)).1
  · -- the equation
    have hz : Φ t₁ y ∈ ball ps r' := hρr (hnear t₁ (by simpa using hτ₀) y hy)
    by_cases hcase : t < t₁ + τ
    · have htΦ : t ∈ Ioo (-η) (t₁ + η) := ⟨by linarith [ht.1], by linarith⟩
      have hev : (fun t => Φ' t y) =ᶠ[𝓝 t] fun t => Φ t y := by
        filter_upwards [Iio_mem_nhds hcase] with s hs using hΦ'lo y hy s hs
      rw [hΦ'lo y hy t hcase]
      exact ⟨((hΦ y (hr₂r hy)).2 t htΦ).1.congr_of_eventuallyEq hev,
        ((hΦ y (hr₂r hy)).2 t htΦ).2⟩
    · push Not at hcase
      have hlt : t₁ - τ < t := by linarith
      have hmem := hΨmem t ht hlt
      have hev : (fun t => Φ' t y) =ᶠ[𝓝 t] fun t => Ψ (t - t₁) (Φ t₁ y) := by
        filter_upwards [Ioi_mem_nhds hlt] with s hs using hΦ'hi y hy s hs
      rw [hΦ'hi y hy t hlt]
      have h1 := (hΨ.hasDerivAt _ hz (t - t₁) (Ioo_subset_Icc_self hmem)).scomp t
        ((hasDerivAt_id t).sub_const t₁)
      have h2 : HasDerivAt (fun t => Ψ (t - t₁) (Φ t₁ y)) (V (Ψ (t - t₁) (Φ t₁ y))) t := by
        simpa [Function.comp_def] using h1
      exact ⟨h2.congr_of_eventuallyEq hev,
        hballa (hΨ.flow_mem _ hz (t - t₁) (Ioo_subset_Icc_self hmem))⟩
  · -- smoothness
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    refine ContDiffAt.contDiffWithinAt ?_
    have hz : Φ t₁ y ∈ ball ps r' := hρr (hnear t₁ (by simpa using hτ₀) y hy)
    by_cases hcase : t < t₁ + τ
    · have htΦ : t ∈ Ioo (-η) (t₁ + η) := ⟨by linarith [ht.1], by linarith⟩
      have hev : (fun p : ℝ × E => Φ' p.1 p.2) =ᶠ[𝓝 (t, y)] fun p : ℝ × E => Φ p.1 p.2 := by
        have h1 : ∀ᶠ p : ℝ × E in 𝓝 (t, y), p.1 < t₁ + τ :=
          continuous_fst.continuousAt.eventually (Iio_mem_nhds hcase)
        have h2 : ∀ᶠ p : ℝ × E in 𝓝 (t, y), p.2 ∈ ball (c 0) r₂ :=
          continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds hy)
        filter_upwards [h1, h2] with p hp1 hp2 using hΦ'lo p.2 hp2 p.1 hp1
      exact (hΦs.contDiffAt (hopenΦ.mem_nhds ⟨htΦ, hr₂r hy⟩)).congr_of_eventuallyEq hev
    · push Not at hcase
      have hlt : t₁ - τ < t := by linarith
      have hmem := hΨmem t ht hlt
      have hev : (fun p : ℝ × E => Φ' p.1 p.2) =ᶠ[𝓝 (t, y)]
          fun p : ℝ × E => Ψ (p.1 - t₁) (Φ t₁ p.2) := by
        have h1 : ∀ᶠ p : ℝ × E in 𝓝 (t, y), t₁ - τ < p.1 :=
          continuous_fst.continuousAt.eventually (Ioi_mem_nhds hlt)
        have h2 : ∀ᶠ p : ℝ × E in 𝓝 (t, y), p.2 ∈ ball (c 0) r₂ :=
          continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds hy)
        filter_upwards [h1, h2] with p hp1 hp2 using hΦ'hi p.2 hp2 p.1 hp1
      have hΦt₁s : ContDiffAt ℝ ∞ (Φ t₁) y :=
        ContDiffAt.comp (g := fun p : ℝ × E => Φ p.1 p.2) (f := fun y' : E => (t₁, y')) y
          (hΦs.contDiffAt (hopenΦ.mem_nhds ⟨ht₁I, hr₂r hy⟩))
          (contDiffAt_const.prodMk contDiffAt_id)
      have hinner : ContDiffAt ℝ ∞ (fun p : ℝ × E => (p.1 - t₁, Φ t₁ p.2)) (t, y) :=
        (contDiffAt_fst.sub contDiffAt_const).prodMk (hΦt₁s.comp (t, y) contDiffAt_snd)
      have hΨat : ContDiffAt ℝ ∞ (fun q : ℝ × E => Ψ q.1 q.2) (t - t₁, Φ t₁ y) :=
        hΨs.contDiffAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨hmem, hz⟩)
      have hcomp : ContDiffAt ℝ ∞ (fun p : ℝ × E => Ψ (p.1 - t₁) (Φ t₁ p.2)) (t, y) :=
        ContDiffAt.comp (g := fun q : ℝ × E => Ψ q.1 q.2) (t, y) hΨat hinner
      exact hcomp.congr_of_eventuallyEq hev
  · -- the flow follows `c`
    intro t ht
    have hy0 : c 0 ∈ ball (c 0) r₂ := mem_ball_self hr₂0
    by_cases hcase : t < t₁
    · rw [hΦ'lo (c 0) hy0 t (by linarith)]
      exact hΦc t ⟨ht.1, hcase.le⟩
    · push Not at hcase
      rw [hΦ'hi (c 0) hy0 t (by linarith), hΦc t₁ ⟨ht₁.1, le_rfl⟩]
      -- uniqueness of the solution from `c t₁` in the flow box at `ps`
      have hct₁ : c t₁ ∈ ball ps r' := hρr (hcnear t₁ ht₁ (lt_of_lt_of_le h1ε hεε))
      set b : ℝ := t - t₁ with hb
      have hb0 : 0 ≤ b := by linarith
      have hbT : b ≤ T' / 2 := by linarith [ht.2]
      have hrange : ∀ u ∈ Icc 0 b, t₁ + u ∈ Icc 0 T ∧ |t₁ + u - ts| < ε₁ := by
        intro u hu
        have h3 : t₁ + u ≤ t₂ := by linarith [hu.2, ht.2]
        refine ⟨⟨by linarith [ht₁.1, hu.1], h3.trans ht₂.2⟩, ?_⟩
        rw [abs_lt]
        constructor <;> linarith [h1abs.1, h2abs.2, hu.1]
      have hΨc : ContinuousOn (fun u => Ψ u (c t₁)) (Icc 0 b) := fun u hu =>
        (hΨ.hasDerivAt _ hct₁ u ⟨by linarith [hu.1], by linarith [hu.2]⟩).continuousAt.continuousWithinAt
      have hΨd : ∀ u ∈ Ico 0 b, HasDerivWithinAt (fun u => Ψ u (c t₁))
          (V (Ψ u (c t₁))) (Ici u) u := fun u hu =>
        (hΨ.hasDerivAt _ hct₁ u ⟨by linarith [hu.1], by linarith [hu.2]⟩).hasDerivWithinAt
      have hΨm : ∀ u ∈ Ico 0 b, Ψ u (c t₁) ∈ ball ps a' := fun u hu =>
        hΨ.flow_mem _ hct₁ u ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hshift : MapsTo (fun u : ℝ => t₁ + u) (Icc 0 b) (Icc 0 T) := fun u hu =>
        (hrange u hu).1
      have hcd : ∀ u ∈ Icc 0 b, HasDerivWithinAt (fun u => c (t₁ + u)) (V (c (t₁ + u)))
          (Icc 0 b) u := by
        intro u hu
        have h1 := HasDerivWithinAt.scomp u (hc (t₁ + u) (hrange u hu).1).1
          ((hasDerivAt_id u).const_add t₁).hasDerivWithinAt hshift
        simpa [Function.comp_def] using h1
      have hcc' : ContinuousOn (fun u => c (t₁ + u)) (Icc 0 b) := fun u hu =>
        (hcd u hu).continuousWithinAt
      have hcd' : ∀ u ∈ Ico 0 b, HasDerivWithinAt (fun u => c (t₁ + u)) (V (c (t₁ + u)))
          (Ici u) u := fun u hu =>
        (hcd u ⟨hu.1, hu.2.le⟩).mono_of_mem_nhdsWithin
          (Filter.mem_of_superset (Icc_mem_nhdsGE_of_mem ⟨le_rfl, hu.2⟩)
            (fun v hv => ⟨hu.1.trans hv.1, hv.2⟩))
      have hcm : ∀ u ∈ Ico 0 b, c (t₁ + u) ∈ ball ps a' := fun u hu =>
        hρa (hcnear _ (hrange u ⟨hu.1, hu.2.le⟩).1 (hrange u ⟨hu.1, hu.2.le⟩).2)
      have huniq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => V)
        (s := fun _ => ball ps a') (K := K') (fun _ _ => hΨ.lipschitzOnWith)
        hΨc hΨd hΨm hcc' hcd' hcm
        (by simp only [add_zero]; exact hΨ.flow_zero _ hct₁)
      have := huniq ⟨hb0, le_rfl⟩
      simp only [hb, add_sub_cancel] at this
      exact this

/-- **The flow along a whole trajectory.** Let `V` be smooth on the open set `O` and let `c` be
an integral curve of `V` in `O` on `[0, T]`. Then there are `r > 0`, `η > 0` and a map `Φ` such
that for every `y` within `r` of `c 0`: `Φ 0 y = y`, the curve `t ↦ Φ t y` solves `ẋ = V x` in
`O` on `(-η, T + η)`; `Φ` is smooth on `(-η, T + η) × B(c 0, r)`; and `Φ t (c 0) = c t` on
`[0, T]`. So solutions starting near `c 0` exist as long as `c` does, and depend smoothly on
their initial point. -/
theorem exists_flow_along {V : E → E} {O : Set E} (hO : IsOpen O) (hV : ContDiffOn ℝ ∞ V O)
    {c : ℝ → E} {T : ℝ} (hT : 0 ≤ T)
    (hc : ∀ t ∈ Icc 0 T, HasDerivWithinAt c (V (c t)) (Icc 0 T) t ∧ c t ∈ O) :
    HasFlowUpTo V O c T := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  -- a flow box at `c 0`
  have hP0 : HasFlowUpTo V O c 0 := by
    have hpO : c 0 ∈ O := (hc 0 h0T).2
    have hV1 : ContDiffAt ℝ 1 V (c 0) :=
      (hV.contDiffAt (hO.mem_nhds hpO)).of_le (by exact_mod_cast le_top)
    obtain ⟨A, hA, H⟩ := exists_isFlowBox hV1
    obtain ⟨aO, haO, hballO⟩ := Metric.isOpen_iff.1 hO (c 0) hpO
    obtain ⟨r', T', K', Ψ, hΨ⟩ := H (min A aO) (lt_min hA haO) (min_le_left _ _)
    have hballa : ball (c 0) (min A aO) ⊆ O :=
      (ball_subset_ball (min_le_right _ _)).trans hballO
    refine ⟨r', T', Ψ, hΨ.r_pos, hΨ.T_pos, fun y hy => ⟨hΨ.flow_zero y hy, fun t ht => ?_⟩,
      ?_, ?_⟩
    · rw [zero_add] at ht
      exact ⟨hΨ.hasDerivAt y hy t (Ioo_subset_Icc_self ht),
        hballa (hΨ.flow_mem y hy t (Ioo_subset_Icc_self ht))⟩
    · rw [zero_add]
      exact hΨ.contDiffOn_uncurry_infty (hV.mono hballa)
    · intro t ht
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      rw [ht0]
      exact hΨ.flow_zero _ (mem_ball_self hΨ.r_pos)
  choose ε hε hstep using fun ts : Icc (0 : ℝ) T => exists_extension_step hO hV hc ts.2
  by_contra hnot
  set u : Set ℝ := ⋃ (ts : Icc (0 : ℝ) T)
    (_ : ∃ t₁ ∈ Icc (0 : ℝ) T, |t₁ - ts| < ε ts ∧ HasFlowUpTo V O c t₁), ball (ts : ℝ) (ε ts)
    with hu
  set v : Set ℝ := ⋃ (ts : Icc (0 : ℝ) T)
    (_ : ¬ ∃ t₁ ∈ Icc (0 : ℝ) T, |t₁ - ts| < ε ts ∧ HasFlowUpTo V O c t₁), ball (ts : ℝ) (ε ts)
    with hv
  have huo : IsOpen u := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hvo : IsOpen v := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  have hcover : Icc (0 : ℝ) T ⊆ u ∪ v := by
    intro t ht
    by_cases hex : ∃ t₁ ∈ Icc (0 : ℝ) T, |t₁ - t| < ε ⟨t, ht⟩ ∧ HasFlowUpTo V O c t₁
    · exact Or.inl (mem_iUnion₂.2 ⟨⟨t, ht⟩, hex, mem_ball_self (hε ⟨t, ht⟩)⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨⟨t, ht⟩, hex, mem_ball_self (hε ⟨t, ht⟩)⟩)
  have h0u : (Icc (0 : ℝ) T ∩ u).Nonempty :=
    ⟨0, h0T, mem_iUnion₂.2 ⟨⟨0, h0T⟩, ⟨0, h0T, by simpa using hε ⟨0, h0T⟩, hP0⟩,
      mem_ball_self (hε ⟨0, h0T⟩)⟩⟩
  have hTT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hTv : (Icc (0 : ℝ) T ∩ v).Nonempty := by
    refine ⟨T, hTT, mem_iUnion₂.2 ⟨⟨T, hTT⟩, ?_, mem_ball_self (hε ⟨T, hTT⟩)⟩⟩
    rintro ⟨t₁, ht₁, h1, hP⟩
    exact hnot (hstep ⟨T, hTT⟩ t₁ ht₁ h1 hP T hTT (by simpa using hε ⟨T, hTT⟩))
  obtain ⟨s, hs, hsu, hsv⟩ := isPreconnected_Icc u v huo hvo hcover h0u hTv
  obtain ⟨ts₁, ⟨t₁, ht₁, h1, hP⟩, hb₁⟩ := mem_iUnion₂.1 hsu
  obtain ⟨ts₂, hno, hb₂⟩ := mem_iUnion₂.1 hsv
  rw [mem_ball, Real.dist_eq] at hb₁ hb₂
  have hPs : HasFlowUpTo V O c s := hstep ts₁ t₁ ht₁ h1 hP s hs hb₁
  exact hno ⟨s, hs, hb₂, hPs⟩

end Lightlike.ODE
