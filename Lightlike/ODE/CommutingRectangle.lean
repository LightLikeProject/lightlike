import Lightlike.ODE.CommutingConverse
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Commuting flows along a rectangle of times

Michor's Corollary 3.15, (1) ⇒ (3), in its non-local form: if `[V, W] = 0` and
`β τ σ = Fl^V_τ (Fl^W_σ x)` is defined for all `(τ, σ)` in a rectangle `[0, T] × N`, then
`σ ↦ β τ σ` is an integral curve of `W` for every `τ ∈ [0, T]`, so that
`Fl^V_τ (Fl^W_σ x) = Fl^W_σ (Fl^V_τ x)` along the rectangle.

Here `β` is any map such that `τ ↦ β τ σ` solves `ẋ = V x` on `[0, T]` for each `σ` near `σ₀`,
and `σ ↦ β 0 σ` has derivative `W (β 0 σ₀)` at `σ₀`; the conclusion is that `σ ↦ β τ σ` has
derivative `W (β τ σ₀)` at `σ₀` (`Lightlike.ODE.hasDerivAt_of_lieBracket_eq_zero_rectangle`).
There is no smallness condition on `T`.

The proof estimates `z τ = β τ σ - β τ σ₀ - (σ - σ₀) • W (β τ σ₀)` by Grönwall's inequality:
`ż = DV (z) + R` because `DW (V) = DV (W)`, with `R` small by the uniform continuity of `DV` near
the compact trajectory. The trajectories of nearby `σ` stay near that of `σ₀` by a continuity
argument (`norm_sub_le_of_trajectories_near`).

## References

* `michor-2008`: P. W. Michor, *Topics in Differential Geometry*, Corollary 3.15, page 28 of the
  author's version: "for all `(t, s, x)` such that one side is defined even along
  `[0, t] × [0, s]` for `t, s > 0`, similarly for other cases".
-/

open Set Metric Filter Topology
open scoped NNReal

noncomputable section

namespace Lightlike.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Grönwall's bound is at most `δ e^{K x} + ε x e^{K x}`. -/
theorem gronwallBound_le {δ K ε x : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε x ≤ δ * Real.exp (K * x) + ε * x * Real.exp (K * x) := by
  have h0 := gronwallBound_zero_le (x := x) hK hε
  have hsplit : gronwallBound δ K ε x = δ * Real.exp (K * x) + gronwallBound 0 K ε x := by
    rcases eq_or_lt_of_le hK with rfl | hK'
    · simp [gronwallBound_K0]
    · rw [gronwallBound_of_K_ne_0 hK'.ne', gronwallBound_of_K_ne_0 hK'.ne']
      ring
  linarith

/-- Grönwall's inequality on `[a, b]` for a curve differentiable within `[a, b]`. -/
theorem norm_le_gronwallBound_Icc {f f' : ℝ → E} {δ K ε a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t) (ha : ‖f a‖ ≤ δ)
    (bound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ gronwallBound δ K ε (t - a) := by
  have hcont : ContinuousOn f (Icc a b) := fun s hs => (hf s hs).continuousWithinAt
  have hder : ∀ s ∈ Ico a b, HasDerivWithinAt f (f' s) (Ici s) s := by
    intro s hs
    refine (hf s ⟨hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (Icc_mem_nhdsGE_of_mem ⟨le_rfl, hs.2⟩)
      (fun u hu => ⟨hs.1.trans hu.1, hu.2⟩)
  exact norm_le_gronwallBound_of_norm_deriv_right_le hcont hder ha
    (fun s hs => bound s ⟨hs.1, hs.2.le⟩)

/-- **Continuous dependence on the initial point for an arbitrary time.** Let `γ` and `γ'` solve
`ẋ = V x` on `[0, T]`, and let `V` be `K`-Lipschitz at the points of `γ` in the sense that
`‖V y - V (γ t)‖ ≤ K ‖y - γ t‖` for `‖y - γ t‖ < ρ`. If `‖γ' 0 - γ 0‖ e^{K T} < ρ`, then
`‖γ' t - γ t‖ ≤ ‖γ' 0 - γ 0‖ e^{K t}` on `[0, T]`: the second solution cannot leave the tube
where the estimate holds. -/
theorem norm_sub_le_of_trajectories_near {V : E → E} {γ γ' : ℝ → E} {K ρ T : ℝ} (hK : 0 ≤ K)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (V (γ t)) (Icc 0 T) t)
    (hγ' : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ' (V (γ' t)) (Icc 0 T) t)
    (hLip : ∀ t ∈ Icc 0 T, ∀ y, ‖y - γ t‖ < ρ → ‖V y - V (γ t)‖ ≤ K * ‖y - γ t‖)
    (hsmall : ‖γ' 0 - γ 0‖ * Real.exp (K * T) < ρ) :
    ∀ t ∈ Icc 0 T, ‖γ' t - γ t‖ ≤ ‖γ' 0 - γ 0‖ * Real.exp (K * t) := by
  set c : ℝ := ‖γ' 0 - γ 0‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set d : ℝ → E := fun t => γ' t - γ t with hd
  have hdc : ContinuousOn d (Icc 0 T) := fun t ht =>
    ((hγ' t ht).continuousWithinAt).sub ((hγ t ht).continuousWithinAt)
  set s : Set ℝ := {t | ‖d t‖ ≤ c * Real.exp (K * t)} with hs
  have hclosed : IsClosed (s ∩ Icc 0 T) := by
    have h1 : s ∩ Icc 0 T = {t ∈ Icc (0 : ℝ) T | ‖d t‖ ≤ c * Real.exp (K * t)} := by
      ext t; simp [hs, and_comm]
    rw [h1]
    exact isClosed_Icc.isClosed_le hdc.norm (by fun_prop)
  have h0 : (0 : ℝ) ∈ s := by simp [hs, hd, hc]
  have hlt : ∀ t ∈ Icc 0 T, c * Real.exp (K * t) < ρ := fun t ht =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK)) hc0) hsmall
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hclosed h0 fun x hx => ?_
  obtain ⟨hxs, hxI⟩ := hx
  have hxI' : x ∈ Icc 0 T := ⟨hxI.1, hxI.2.le⟩
  -- near `x` the difference is still smaller than `ρ`
  have hnear : {t | ‖d t‖ < ρ} ∈ 𝓝[Icc 0 T] x :=
    (hdc x hxI').norm.preimage_mem_nhdsWithin (Iio_mem_nhds (lt_of_le_of_lt hxs (hlt x hxI')))
  obtain ⟨ε, hε, Hε⟩ := Metric.mem_nhdsWithin_iff.1 hnear
  have hb : x < min (x + ε) T := lt_min (by linarith) hxI.2
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT hb) fun u hu => ?_
  have huT : u ≤ T := hu.2.le.trans (min_le_right _ _)
  have hsub : Icc x u ⊆ Icc 0 T := fun v hv => ⟨hxI.1.trans hv.1, hv.2.trans huT⟩
  have hρ : ∀ v ∈ Icc x u, ‖d v‖ < ρ := by
    intro v hv
    refine Hε ⟨?_, hsub hv⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have : u < x + ε := hu.2.trans_le (min_le_left _ _)
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hder : ∀ v ∈ Icc x u, HasDerivWithinAt d (V (γ' v) - V (γ v)) (Icc x u) v := fun v hv =>
    ((hγ' v (hsub hv)).sub (hγ v (hsub hv))).mono hsub
  have hbd : ∀ v ∈ Icc x u, ‖V (γ' v) - V (γ v)‖ ≤ K * ‖d v‖ + 0 := fun v hv => by
    rw [add_zero]
    exact hLip v (hsub hv) (γ' v) (hρ v hv)
  have h1 := norm_le_gronwallBound_Icc hder hxs hbd u ⟨hu.1.le, le_rfl⟩
  rw [gronwallBound_ε0] at h1
  show ‖d u‖ ≤ c * Real.exp (K * u)
  calc ‖d u‖ ≤ c * Real.exp (K * x) * Real.exp (K * (u - x)) := h1
    _ = c * Real.exp (K * u) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- **Commuting flows along a rectangle of times** (Michor, Corollary 3.15, (1) ⇒ (3), non-local
form). Let `V` be `C¹` and `W` differentiable on an open set `U`, with `[V, W] = 0` on `U`. Let
`β` be such that, for every `σ` near `σ₀`, the curve `τ ↦ β τ σ` solves `ẋ = V x` on `[0, T]` in
`U`, and let `σ ↦ β 0 σ` have derivative `W (β 0 σ₀)` at `σ₀`. Then for every `τ ∈ [0, T]` the
curve `σ ↦ β τ σ` has derivative `W (β τ σ₀)` at `σ₀`.

With `β τ σ = Fl^V_τ (Fl^W_σ x)`: the composition is an integral curve of `W` in `σ`, hence equal
to `Fl^W_σ (Fl^V_τ x)`, wherever it is defined along the rectangle. -/
theorem hasDerivAt_of_lieBracket_eq_zero_rectangle {V W : E → E} {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ 1 V U) (hW : ∀ y ∈ U, DifferentiableAt ℝ W y)
    (hVW : ∀ y ∈ U, VectorField.lieBracket ℝ V W y = 0) {β : ℝ → ℝ → E} {T σ₀ : ℝ}
    (hβ : ∀ᶠ σ in 𝓝 σ₀, ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (fun τ => β τ σ) (V (β τ σ)) (Icc 0 T) τ ∧ β τ σ ∈ U)
    (h0 : HasDerivAt (fun σ => β 0 σ) (W (β 0 σ₀)) σ₀) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    HasDerivAt (fun σ => β τ σ) (W (β τ σ₀)) σ₀ := by
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have hβ₀ := hβ.self_of_nhds
  set γ : ℝ → E := fun t => β t σ₀ with hγdef
  have hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (V (γ t)) (Icc 0 T) t := fun t ht => (hβ₀ t ht).1
  have hγU : ∀ t ∈ Icc 0 T, γ t ∈ U := fun t ht => (hβ₀ t ht).2
  have hVd : ∀ y ∈ U, HasFDerivAt V (fderiv ℝ V y) y := fun y hy =>
    ((hV.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hDVc : ContinuousOn (fderiv ℝ V) U :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU).1 (by simpa using hV)).2.2.continuousOn
  -- the compact trajectory, a bound for `DV` near it, and a tube around it
  have hγc : ContinuousOn γ (Icc 0 T) := fun t ht => (hγ t ht).continuousWithinAt
  have hC : IsCompact (γ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hγc
  have hCU : γ '' Icc 0 T ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hγU t ht
  obtain ⟨K₀, hK₀⟩ := hC.exists_bound_of_continuousOn (hDVc.mono hCU)
  set K : ℝ := max K₀ 0 + 1 with hKdef
  have hK : 0 ≤ K := by positivity
  have hOopen : IsOpen (U ∩ {y | ‖fderiv ℝ V y‖ < K}) :=
    hDVc.norm.isOpen_inter_preimage hU isOpen_Iio
  have hCO : γ '' Icc 0 T ⊆ U ∩ {y | ‖fderiv ℝ V y‖ < K} := fun y hy =>
    ⟨hCU hy, lt_of_le_of_lt ((hK₀ y hy).trans (le_max_left _ _)) (lt_add_one _)⟩
  obtain ⟨ρ, hρ, hthick⟩ := hC.exists_thickening_subset_open hOopen hCO
  have hball : ∀ t ∈ Icc 0 T, ball (γ t) ρ ⊆ U ∩ {y | ‖fderiv ℝ V y‖ < K} := fun t ht =>
    (ball_subset_thickening (mem_image_of_mem γ ht) ρ).trans hthick
  have hLip : ∀ t ∈ Icc 0 T, ∀ y, ‖y - γ t‖ < ρ → ‖V y - V (γ t)‖ ≤ K * ‖y - γ t‖ := by
    intro t ht y hy
    refine (convex_ball (γ t) ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hVd z (hball t ht hz).1).hasFDerivWithinAt)
      (fun z hz => (hball t ht hz).2.le) (mem_ball_self hρ) (mem_ball_iff_norm.2 hy)
  have hDVat : ∀ y ∈ γ '' Icc 0 T, ContinuousAt (fderiv ℝ V) y := fun y hy =>
    hDVc.continuousAt (hU.mem_nhds (hCU hy))
  -- the derivative of `W` along the trajectory
  have hWγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => W (γ t))
      (fderiv ℝ V (γ t) (W (γ t))) (Icc 0 T) t := by
    intro t ht
    have h1 : HasDerivWithinAt (W ∘ γ) (fderiv ℝ W (γ t) (V (γ t))) (Icc 0 T) t :=
      (hW _ (hγU t ht)).hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
    have h2 : fderiv ℝ W (γ t) (V (γ t)) = fderiv ℝ V (γ t) (W (γ t)) := by
      have := hVW _ (hγU t ht)
      rw [VectorField.lieBracket] at this
      exact sub_eq_zero.1 this
    rw [h2] at h1
    exact h1
  -- the estimate
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c₀ hc₀
  set e : ℝ := Real.exp (K * T) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : 1 ≤ e := Real.one_le_exp (mul_nonneg hK hT)
  set L : ℝ := ‖W (γ 0)‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  -- choose `η` with `η e + η L e T e ≤ c₀`
  set η : ℝ := c₀ / (e + L * e * T * e + 1) with hη
  have hden : 0 < e + L * e * T * e + 1 := by positivity
  have hη0 : 0 < η := div_pos hc₀ hden
  have hηle : η * e + η * (L * e) * T * e ≤ c₀ := by
    have h1 : η * e + η * (L * e) * T * e = η * (e + L * e * T * e) := by ring
    rw [h1, hη, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [mul_pos hc₀ hden, mul_nonneg hL0.le (mul_nonneg (mul_nonneg he0.le hT) he0.le)]
  obtain ⟨δ₁, hδ₁, Hδ₁⟩ := Metric.mem_uniformity_dist.1
    (hC.uniformContinuousAt_of_continuousAt (fderiv ℝ V) hDVat (dist_mem_uniformity hη0))
  have h0' := h0
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff] at h0'
  have hz0 := h0' hη0
  have hlip0 := h0' one_pos
  have hshift : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt (fun τ => β τ (σ₀ + h)) (V (β τ (σ₀ + h))) (Icc 0 T) τ ∧
        β τ (σ₀ + h) ∈ U := by
    have : Tendsto (fun h : ℝ => σ₀ + h) (𝓝 0) (𝓝 σ₀) := by
      have h1 : Tendsto (fun h : ℝ => σ₀ + h) (𝓝 0) (𝓝 (σ₀ + 0)) :=
        (show Continuous fun h : ℝ => σ₀ + h by fun_prop).tendsto 0
      rw [add_zero] at h1
      exact h1
    exact this.eventually hβ
  have hsm : ∀ᶠ h in 𝓝 (0 : ℝ), L * |h| * e < min ρ δ₁ := by
    have hpos : 0 < min ρ δ₁ / (L * e) := div_pos (lt_min hρ hδ₁) (mul_pos hL0 he0)
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at hh
    calc L * |h| * e = |h| * (L * e) := by ring
      _ < min ρ δ₁ / (L * e) * (L * e) := mul_lt_mul_of_pos_right hh (mul_pos hL0 he0)
      _ = min ρ δ₁ := div_mul_cancel₀ _ (mul_pos hL0 he0).ne'
  filter_upwards [hz0, hlip0, hshift, hsm] with h hz hl hsh hsmall
  set γ' : ℝ → E := fun t => β t (σ₀ + h) with hγ'def
  have hγ' : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ' (V (γ' t)) (Icc 0 T) t := fun t ht => (hsh t ht).1
  have hγ'U : ∀ t ∈ Icc 0 T, γ' t ∈ U := fun t ht => (hsh t ht).2
  -- the initial distance is at most `L |h|`
  have hc : ‖γ' 0 - γ 0‖ ≤ L * |h| := by
    have h1 : ‖γ' 0 - γ 0 - h • W (γ 0)‖ ≤ 1 * ‖h‖ := hl
    have h2 : ‖γ' 0 - γ 0‖ ≤ ‖γ' 0 - γ 0 - h • W (γ 0)‖ + ‖h • W (γ 0)‖ := by
      have := norm_add_le (γ' 0 - γ 0 - h • W (γ 0)) (h • W (γ 0))
      simpa using this
    rw [norm_smul, Real.norm_eq_abs] at h2
    rw [Real.norm_eq_abs] at h1
    rw [hL]
    nlinarith [abs_nonneg h, norm_nonneg (W (γ 0))]
  have hce : ‖γ' 0 - γ 0‖ * e ≤ L * |h| * e := mul_le_mul_of_nonneg_right hc he0.le
  have hdist : ∀ t ∈ Icc 0 T, ‖γ' t - γ t‖ ≤ L * |h| * e := by
    intro t ht
    have h1 := norm_sub_le_of_trajectories_near hK hγ hγ' hLip
      (lt_of_le_of_lt hce (lt_of_lt_of_le hsmall (min_le_left _ _))) t ht
    have h2 : Real.exp (K * t) ≤ e := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hK)
    exact (h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))).trans hce
  -- Grönwall for `z = γ' - γ - h • W ∘ γ`
  have hzder : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun t => γ' t - γ t - h • W (γ t))
      (V (γ' t) - V (γ t) - h • fderiv ℝ V (γ t) (W (γ t))) (Icc 0 T) t := fun t ht =>
    ((hγ' t ht).sub (hγ t ht)).sub ((hWγ t ht).const_smul h)
  have hzbd : ∀ t ∈ Icc 0 T, ‖V (γ' t) - V (γ t) - h • fderiv ℝ V (γ t) (W (γ t))‖ ≤
      K * ‖γ' t - γ t - h • W (γ t)‖ + η * (L * |h| * e) := by
    intro t ht
    have hlt : ‖γ' t - γ t‖ < min ρ δ₁ := lt_of_le_of_lt (hdist t ht) hsmall
    have hR : ‖V (γ' t) - V (γ t) - fderiv ℝ V (γ t) (γ' t - γ t)‖ ≤ η * ‖γ' t - γ t‖ := by
      have hsubb : ball (γ t) (min ρ δ₁) ⊆ ball (γ t) ρ := ball_subset_ball (min_le_left _ _)
      refine (convex_ball (γ t) (min ρ δ₁)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (f := V) (f' := fderiv ℝ V)
        (fun y hy => (hVd y (hball t ht (hsubb hy)).1).hasFDerivWithinAt) (fun y hy => ?_)
        (mem_ball_self (lt_min hρ hδ₁)) (mem_ball_iff_norm.2 hlt)
      have hy' : dist (γ t) y < δ₁ := by
        rw [dist_comm]; exact lt_of_lt_of_le (mem_ball.1 hy) (min_le_right _ _)
      have h3 := Hδ₁ hy' (mem_image_of_mem γ ht)
      simp only [Set.mem_ofPred_eq] at h3
      rw [dist_comm, dist_eq_norm] at h3
      exact h3.le
    have hsplit : V (γ' t) - V (γ t) - h • fderiv ℝ V (γ t) (W (γ t)) =
        fderiv ℝ V (γ t) (γ' t - γ t - h • W (γ t)) +
          (V (γ' t) - V (γ t) - fderiv ℝ V (γ t) (γ' t - γ t)) := by
      simp only [map_sub, map_smul]
      abel
    have hKb : ‖fderiv ℝ V (γ t)‖ ≤ K := (hball t ht (mem_ball_self hρ)).2.le
    rw [hsplit]
    calc ‖fderiv ℝ V (γ t) (γ' t - γ t - h • W (γ t)) +
          (V (γ' t) - V (γ t) - fderiv ℝ V (γ t) (γ' t - γ t))‖
        ≤ ‖fderiv ℝ V (γ t)‖ * ‖γ' t - γ t - h • W (γ t)‖ + η * ‖γ' t - γ t‖ :=
          (norm_add_le _ _).trans (add_le_add ((fderiv ℝ V (γ t)).le_opNorm _) hR)
      _ ≤ K * ‖γ' t - γ t - h • W (γ t)‖ + η * (L * |h| * e) :=
          add_le_add (mul_le_mul_of_nonneg_right hKb (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hdist t ht) hη0.le)
  have hzinit : ‖γ' 0 - γ 0 - h • W (γ 0)‖ ≤ η * |h| := by
    have := hz
    rwa [Real.norm_eq_abs] at this
  have hfin := norm_le_gronwallBound_Icc hzder hzinit hzbd τ hτ
  have hε0 : 0 ≤ η * (L * |h| * e) :=
    mul_nonneg hη0.le (mul_nonneg (mul_nonneg hL0.le (abs_nonneg h)) he0.le)
  have hgb := gronwallBound_le (δ := η * |h|) (x := τ - 0) hK hε0
  have hexp : Real.exp (K * (τ - 0)) ≤ e := by
    rw [sub_zero]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hK)
  have hτ0 : 0 ≤ τ - 0 := by rw [sub_zero]; exact hτ.1
  have hτT : τ - 0 ≤ T := by rw [sub_zero]; exact hτ.2
  have hb1 : η * |h| * Real.exp (K * (τ - 0)) ≤ η * |h| * e :=
    mul_le_mul_of_nonneg_left hexp (mul_nonneg hη0.le (abs_nonneg h))
  have hb2 : η * (L * |h| * e) * (τ - 0) * Real.exp (K * (τ - 0)) ≤
      η * (L * |h| * e) * T * e :=
    mul_le_mul (mul_le_mul_of_nonneg_left hτT hε0) hexp (Real.exp_pos _).le
      (mul_nonneg hε0 hT)
  have hsum : η * |h| * e + η * (L * |h| * e) * T * e = (η * e + η * (L * e) * T * e) * |h| := by
    ring
  have hlast : (η * e + η * (L * e) * T * e) * |h| ≤ c₀ * |h| :=
    mul_le_mul_of_nonneg_right hηle (abs_nonneg h)
  show ‖β τ (σ₀ + h) - β τ σ₀ - h • W (β τ σ₀)‖ ≤ c₀ * ‖h‖
  rw [Real.norm_eq_abs]
  calc ‖β τ (σ₀ + h) - β τ σ₀ - h • W (β τ σ₀)‖
      ≤ gronwallBound (η * |h|) K (η * (L * |h| * e)) (τ - 0) := hfin
    _ ≤ c₀ * |h| := by linarith

/-- **Commuting flows along a rectangle of times, backward in the time of `V`**: the statement of
`hasDerivAt_of_lieBracket_eq_zero_rectangle` for `τ ∈ [-T, 0]`. -/
theorem hasDerivAt_of_lieBracket_eq_zero_rectangle_neg {V W : E → E} {U : Set E}
    (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) (hW : ∀ y ∈ U, DifferentiableAt ℝ W y)
    (hVW : ∀ y ∈ U, VectorField.lieBracket ℝ V W y = 0) {β : ℝ → ℝ → E} {T σ₀ : ℝ}
    (hβ : ∀ᶠ σ in 𝓝 σ₀, ∀ τ ∈ Icc (-T) 0,
      HasDerivWithinAt (fun τ => β τ σ) (V (β τ σ)) (Icc (-T) 0) τ ∧ β τ σ ∈ U)
    (h0 : HasDerivAt (fun σ => β 0 σ) (W (β 0 σ₀)) σ₀) {τ : ℝ} (hτ : τ ∈ Icc (-T) 0) :
    HasDerivAt (fun σ => β τ σ) (W (β τ σ₀)) σ₀ := by
  have hmaps : MapsTo (fun t : ℝ => -t) (Icc 0 T) (Icc (-T) 0) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hVW' : ∀ y ∈ U, VectorField.lieBracket ℝ (fun y => -V y) W y = 0 := by
    intro y hy
    have h1 := hVW y hy
    rw [VectorField.lieBracket] at h1 ⊢
    rw [fderiv_fun_neg, map_neg, neg_apply]
    rw [sub_eq_zero] at h1
    rw [h1]
    abel
  have hβ' : ∀ᶠ σ in 𝓝 σ₀, ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun t => β (-t) σ) (-V (β (-t) σ)) (Icc 0 T) t ∧ β (-t) σ ∈ U := by
    filter_upwards [hβ] with σ hσ t ht
    refine ⟨?_, (hσ (-t) (hmaps ht)).2⟩
    have h1 := HasDerivWithinAt.scomp t (hσ (-t) (hmaps ht)).1
      (hasDerivAt_neg t).hasDerivWithinAt hmaps
    simpa [Function.comp_def] using h1
  have h0' : HasDerivAt (fun σ => β (-0) σ) (W (β (-0) σ₀)) σ₀ := by simpa using h0
  have hτ' : -τ ∈ Icc 0 T := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have := hasDerivAt_of_lieBracket_eq_zero_rectangle (V := fun y => -V y) (W := W)
    (β := fun t σ => β (-t) σ) hU hV.neg hW hVW' hβ' h0' hτ'
  simpa using this

end Lightlike.ODE
