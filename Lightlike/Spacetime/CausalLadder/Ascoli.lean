import Mathlib

/-!
# A uniformly convergent subsequence of equi-Lipschitz curves

Arzelà–Ascoli for a sequence of `C`-Lipschitz maps `ℝ → E` with values in a fixed bounded set, on a
compact interval, in a finite-dimensional space `E` (Mathlib:
`BoundedContinuousFunction.arzela_ascoli`). The limit is `C`-Lipschitz.

Supporting lemma for the causal ladder; no catalogue entry. Compare Tau Ceti's
`TauCeti.tendsto_subseq_of_limsup_edist_le`, a refined Arzelà–Ascoli for asymptotically
equicontinuous sequences, which is not used here (no dependency on Tau Ceti).
-/

open Set Filter Topology BoundedContinuousFunction

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Arzelà–Ascoli for equi-Lipschitz curves.** A sequence of `C`-Lipschitz maps `ℝ → E` with
values in a ball has a subsequence that converges uniformly on `[α, β]` to a `C`-Lipschitz map. -/
theorem exists_subseq_tendstoUniformlyOn {C R : ℝ} (hC : 0 < C) (α β : ℝ) (f : ℕ → ℝ → E)
    (hlip : ∀ k x y, ‖f k x - f k y‖ ≤ C * |x - y|) (hR : ∀ k x, ‖f k x‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u : ℝ → E, (∀ x y, ‖u x - u y‖ ≤ C * |x - y|) ∧
      TendstoUniformlyOn (fun k => f (φ k)) u atTop (Icc α β) := by
  set β' : ℝ := max α β with hβ'
  have hαβ : α ≤ β' := le_max_left _ _
  let X := Icc α β'
  haveI : CompactSpace X := isCompact_iff_compactSpace.1 isCompact_Icc
  have hcont : ∀ k, Continuous (fun x : X => f k x) := fun k => by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have : LipschitzWith ⟨C, hC.le⟩ (f k) := LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, Real.dist_eq]; exact hlip k x y
    exact (this.continuous.comp continuous_subtype_val).continuousAt
  let g : ℕ → X →ᵇ E := fun k => BoundedContinuousFunction.mkOfCompact ⟨fun x : X => f k x, hcont k⟩
  have hg : ∀ k (x : X), g k x = f k x := fun k x => rfl
  have hequi : Equicontinuous ((↑) : range g → X → E) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    have hball : ∀ᶠ y in 𝓝 x₀, dist y x₀ < ε / (C + 1) :=
      Metric.ball_mem_nhds x₀ (by positivity)
    filter_upwards [hball] with y hy
    rintro ⟨_, k, rfl⟩
    simp only [hg, dist_eq_norm]
    have h1 : |(y : ℝ) - x₀| < ε / (C + 1) := by
      simpa [Subtype.dist_eq, Real.dist_eq] using hy
    calc ‖f k x₀ - f k y‖ ≤ C * |(x₀ : ℝ) - y| := hlip k _ _
      _ ≤ C * (ε / (C + 1)) := by rw [abs_sub_comm]; exact mul_le_mul_of_nonneg_left h1.le hC.le
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  have hK : IsCompact (closure (range g)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
      (range g) (fun f x ⟨k, hk⟩ => by rw [← hk]; simpa [hg] using hR k x) hequi
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  have hpt : ∀ x : X, Tendsto (fun k => f (φ k) x) atTop (𝓝 (a x)) := fun x =>
    Metric.tendsto_atTop.2 fun ε hε => (Metric.tendsto_atTop.1 hlim ε hε).imp fun N hN k hk =>
      lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist (f := g (φ k)) (g := a) x) (hN k hk)
  have halip : ∀ x y : X, ‖a x - a y‖ ≤ C * |(x : ℝ) - y| := by
    intro x y
    refine le_of_tendsto ((hpt x).sub (hpt y)).norm ?_ |>.trans le_rfl
    exact Eventually.of_forall fun k => hlip (φ k) _ _
  refine ⟨φ, hφ, fun x => a (Set.projIcc α β' hαβ x), ?_, ?_⟩
  · intro x y
    refine (halip _ _).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
    have := (LipschitzWith.projIcc hαβ).dist_le_mul x y
    simpa [Subtype.dist_eq, Real.dist_eq] using this
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have := Metric.tendsto_atTop.1 hlim ε hε
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with k hk x hx
    have hxX : x ∈ X := ⟨hx.1, hx.2.trans (le_max_right _ _)⟩
    have hproj : (Set.projIcc α β' hαβ x : ℝ) = x := Set.projIcc_of_mem hαβ hxX |> congrArg Subtype.val
    have := hN k hk
    have h2 := BoundedContinuousFunction.dist_coe_le_dist (f := g (φ k)) (g := a) ⟨x, hxX⟩
    have e : Set.projIcc α β' hαβ x = ⟨x, hxX⟩ := Set.projIcc_of_mem hαβ hxX
    simp only [e]
    rw [dist_comm]
    exact lt_of_le_of_lt h2 (by simpa [dist_comm] using this)

end Lightlike.Causal
