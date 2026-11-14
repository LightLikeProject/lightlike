import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Maximal lifts of an autonomous ODE

Mathlib proves local existence (Picard–Lindelöf) and uniqueness of solutions of `x' = v x`, but
has no maximal solutions. This file supplies the one statement about maximal solutions that the
steepest-descent proof of `RacahSumAsymptotics` needs for its descent paths: an **escape lemma**.

Let `v` be `C¹` on an open set `U`. A *lift* from `x₀` on `[0, T)` is a solution of `x' = v x`
with `x 0 = x₀` that stays in `U` (`IsLift`). If every lift has `T ≤ T₁` and speed at most `M`,
then there is a lift on some `[0, T)` that converges, as `t → T⁻`, to a point **outside** `U`
(`exists_isLift_tendsto_not_mem`).

The proof:

* two forward solutions that agree at one time agree afterwards, as long as one of them stays in
  `U` (`eqOn_Ico_of_hasDerivWithinAt`, by real induction and Mathlib's local uniqueness);
* the lifts therefore agree on their common domain (`IsLift.eqOn`), and glue to a lift on
  `[0, T*)`, with `T*` the supremum of all lift times;
* the speed bound makes that lift Lipschitz, so it converges as `t → T*⁻`;
* if the limit `p` were in `U`, a local solution through a point close to `p` would extend the
  lift beyond `T*`.
-/

open Set Filter Topology Metric

namespace Lightlike.Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `t ∈ [a, b)`, then `[a, b)` is a right neighbourhood of `t`. -/
lemma Ico_mem_nhdsGE_of_mem' {a b t : ℝ} (h : t ∈ Ico a b) : Ico a b ∈ 𝓝[≥] t :=
  mem_nhdsGE_iff_exists_Ico_subset.2 ⟨b, h.2, fun _ hy => ⟨h.1.trans hy.1, hy.2⟩⟩

/-- **Forward uniqueness.** Let `v` be `C¹` on `U`. Two forward solutions `f`, `g` of
`x' = v x` on `[a, b)` with `f a = g a` agree on `[a, b)`, provided that `f` stays in `U`.
Nothing is assumed about where `g` lies. -/
theorem eqOn_Ico_of_hasDerivWithinAt {v : E → E} {U : Set E}
    (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {f g : ℝ → E} {a b : ℝ}
    (hf : ∀ t ∈ Ico a b, HasDerivWithinAt f (v (f t)) (Ico a b) t)
    (hfU : ∀ t ∈ Ico a b, f t ∈ U)
    (hg : ∀ t ∈ Ico a b, HasDerivWithinAt g (v (g t)) (Ico a b) t)
    (ha : f a = g a) : EqOn f g (Ico a b) := by
  have hcont : ∀ {φ : ℝ → E}, (∀ t ∈ Ico a b, HasDerivWithinAt φ (v (φ t)) (Ico a b) t) →
      ∀ {c d : ℝ}, Icc c d ⊆ Ico a b → ContinuousOn φ (Icc c d) := fun hφ _ _ hcd τ hτ =>
    (hφ τ (hcd hτ)).continuousWithinAt.mono hcd
  intro t ht
  have hsub : Icc a t ⊆ Ico a b := fun τ hτ => ⟨hτ.1, hτ.2.trans_lt ht.2⟩
  have hs : IsClosed ({τ | f τ = g τ} ∩ Icc a t) := by
    have := ((hcont hf hsub).prodMk (hcont hg hsub)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_diagonal
    rw [inter_comm]
    exact this
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin hs ha (fun x ⟨hx, hxI⟩ => ?_)
    ⟨ht.1, le_rfl⟩
  have hxab : x ∈ Ico a b := ⟨hxI.1, hxI.2.trans ht.2⟩
  obtain ⟨K, N, hN, hK⟩ := (hv _ (hfU x hxab)).exists_lipschitzOnWith
  have hNg : N ∈ 𝓝 (g x) := by rw [← show f x = g x from hx]; exact hN
  have hev : ∀ᶠ τ in 𝓝[≥] x, f τ ∈ N ∧ g τ ∈ N ∧ τ ∈ Ico a b :=
    (((hf x hxab).continuousWithinAt.mono_of_mem_nhdsWithin
        (Ico_mem_nhdsGE_of_mem' hxab)).eventually_mem hN).and
      ((((hg x hxab).continuousWithinAt.mono_of_mem_nhdsWithin
        (Ico_mem_nhdsGE_of_mem' hxab)).eventually_mem hNg).and (Ico_mem_nhdsGE_of_mem' hxab))
  obtain ⟨u, hu, hIco⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
  have hxu : x < u := hu
  set c := (x + u) / 2
  have hxc : x < c := by simp only [c]; linarith
  have hcu : c < u := by simp only [c]; linarith
  have hIcc : Icc x c ⊆ Ico x u := fun τ hτ => ⟨hτ.1, hτ.2.trans_lt hcu⟩
  have hIcc' : Icc x c ⊆ Ico a b := fun τ hτ => (hIco (hIcc hτ)).2.2
  have huniq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => v) (s := fun _ => N) (K := K)
    (fun _ _ => hK) (hcont hf hIcc')
    (fun τ hτ => (hf τ (hIcc' (Ico_subset_Icc_self hτ))).mono_of_mem_nhdsWithin
      (Ico_mem_nhdsGE_of_mem' (hIcc' (Ico_subset_Icc_self hτ))))
    (fun τ hτ => (hIco (hIcc (Ico_subset_Icc_self hτ))).1) (hcont hg hIcc')
    (fun τ hτ => (hg τ (hIcc' (Ico_subset_Icc_self hτ))).mono_of_mem_nhdsWithin
      (Ico_mem_nhdsGE_of_mem' (hIcc' (Ico_subset_Icc_self hτ))))
    (fun τ hτ => (hIco (hIcc (Ico_subset_Icc_self hτ))).2.1) hx
  exact mem_of_superset (Ioo_mem_nhdsGT hxc) fun τ hτ => huniq ⟨hτ.1.le, hτ.2.le⟩

/-- `α` is a **lift** of the flow of `v` in `U` from `x₀` on `[0, T)`: a solution of
`α' = v ∘ α` on `[0, T)` (one-sided at `0`) with `α 0 = x₀` and values in `U`. -/
structure IsLift (v : E → E) (U : Set E) (x₀ : E) (T : ℝ) (α : ℝ → E) : Prop where
  /-- The lift is defined on a non-empty interval. -/
  pos : 0 < T
  /-- The lift starts at `x₀`. -/
  start : α 0 = x₀
  /-- The lift stays in `U`. -/
  mem : ∀ t ∈ Ico 0 T, α t ∈ U
  /-- The lift solves `α' = v ∘ α` on `[0, T)`. -/
  deriv : ∀ t ∈ Ico 0 T, HasDerivWithinAt α (v (α t)) (Ico 0 T) t

variable {v : E → E} {U : Set E} {x₀ : E}

/-- Two lifts from the same point agree on their common interval of definition. -/
theorem IsLift.eqOn (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) {T T' : ℝ} {α β : ℝ → E}
    (hα : IsLift v U x₀ T α) (hβ : IsLift v U x₀ T' β) : EqOn α β (Ico 0 (min T T')) :=
  eqOn_Ico_of_hasDerivWithinAt hv
    (fun t ht => (hα.deriv t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_left _ _)))
    (fun t ht => hα.mem t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)
    (fun t ht => (hβ.deriv t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_right _ _)))
    (hα.start.trans hβ.start.symm)

variable [CompleteSpace E]

/-- **Local existence.** If `v` is `C¹` on the open set `U` and `x₀ ∈ U`, a lift from `x₀`
exists. -/
theorem exists_isLift (hU : IsOpen U) (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x) (hx₀ : x₀ ∈ U) :
    ∃ T α, IsLift v U x₀ T α := by
  obtain ⟨α, h0, ε, hε, hα⟩ :=
    (hv x₀ hx₀).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hc : ContinuousAt α 0 := (hα 0 ⟨by linarith, by linarith⟩).continuousAt
  obtain ⟨δ, hδ, hδU⟩ :=
    Metric.mem_nhds_iff.1 (hc.preimage_mem_nhds (hU.mem_nhds (h0 ▸ hx₀)))
  refine ⟨min ε δ, α, ⟨lt_min hε hδ, h0, fun t ht => hδU ?_, fun t ht =>
    (hα t ⟨by linarith [ht.1], by linarith [ht.2, min_le_left ε δ]⟩).hasDerivWithinAt⟩⟩
  rw [mem_ball, Real.dist_0_eq_abs, abs_of_nonneg ht.1]
  exact ht.2.trans_le (min_le_right _ _)

/-- **Escape lemma.** Let `v` be `C¹` on the open set `U`, `x₀ ∈ U`, and suppose that every
lift from `x₀` lives at most up to time `T₁` and has speed at most `M`. Then some lift from
`x₀`, on `[0, T)`, converges as `t → T⁻` to a point `p` that is **not** in `U`. -/
theorem exists_isLift_tendsto_not_mem (hU : IsOpen U) (hv : ∀ x ∈ U, ContDiffAt ℝ 1 v x)
    (hx₀ : x₀ ∈ U) {T₁ M : ℝ} (hT : ∀ T α, IsLift v U x₀ T α → T ≤ T₁)
    (hM : ∀ T α, IsLift v U x₀ T α → ∀ t ∈ Ico 0 T, ‖v (α t)‖ ≤ M) :
    ∃ T α p, IsLift v U x₀ T α ∧ Tendsto α (𝓝[<] T) (𝓝 p) ∧ p ∉ U := by
  set S := {T | ∃ α, IsLift v U x₀ T α}
  obtain ⟨T₀, α₀, h₀⟩ := exists_isLift hU hv hx₀
  have hne : S.Nonempty := ⟨T₀, α₀, h₀⟩
  have hbdd : BddAbove S := ⟨T₁, fun T ⟨α, hα⟩ => hT T α hα⟩
  set T' := sSup S
  -- The glued lift: at time `t`, follow any lift that lives beyond `t`.
  let P : ℝ → ℝ × (ℝ → E) → Prop := fun t q => IsLift v U x₀ q.1 q.2 ∧ t < q.1
  let A : ℝ → E := fun t => (Classical.epsilon (P t)).2 t
  have hA : ∀ T β, IsLift v U x₀ T β → ∀ t ∈ Ico 0 T, A t = β t := by
    intro T β hβ t ht
    have hq : P t (Classical.epsilon (P t)) := Classical.epsilon_spec ⟨(T, β), hβ, ht.2⟩
    exact hq.1.eqOn hv hβ ⟨ht.1, lt_min hq.2 ht.2⟩
  have hex : ∀ t < T', ∃ T β, IsLift v U x₀ T β ∧ t < T := fun t ht => by
    obtain ⟨T, ⟨β, hβ⟩, htT⟩ := exists_lt_of_lt_csSup hne ht
    exact ⟨T, β, hβ, htT⟩
  have hlift : IsLift v U x₀ T' A := by
    refine ⟨h₀.pos.trans_le (le_csSup hbdd ⟨α₀, h₀⟩),
      (hA T₀ α₀ h₀ 0 ⟨le_rfl, h₀.pos⟩).trans h₀.start, fun t ht => ?_, fun t ht => ?_⟩
    · obtain ⟨T, β, hβ, htT⟩ := hex t ht.2
      rw [hA T β hβ t ⟨ht.1, htT⟩]
      exact hβ.mem t ⟨ht.1, htT⟩
    · obtain ⟨T, β, hβ, htT⟩ := hex t ht.2
      have heq : A t = β t := hA T β hβ t ⟨ht.1, htT⟩
      have h1 : HasDerivWithinAt A (v (A t)) (Ico 0 T) t := by
        rw [heq]
        exact (hβ.deriv t ⟨ht.1, htT⟩).congr (fun s hs => hA T β hβ s hs) heq
      exact h1.mono_of_mem_nhdsWithin
        (mem_nhdsWithin.2 ⟨Iio T, isOpen_Iio, htT, fun s hs => ⟨hs.2.1, hs.1⟩⟩)
  -- The glued lift is `M`-Lipschitz, hence converges as `t → T'⁻`.
  have hLip : ∀ s ∈ Ico 0 T', ∀ t ∈ Ico 0 T', ‖A t - A s‖ ≤ M * ‖t - s‖ := fun s hs t ht =>
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hlift.deriv (hM _ _ hlift)
      (convex_Ico 0 T') hs ht
  obtain ⟨p, hp⟩ : ∃ p, Tendsto A (𝓝[<] T') (𝓝 p) := by
    rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    have hδ : 0 < min T' (ε / (|M| + 1)) := lt_min hlift.pos (by positivity)
    refine ⟨A '' Ioo (T' - min T' (ε / (|M| + 1))) T', image_mem_map (Ioo_mem_nhdsLT
      (by linarith)), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    have hs' : s ∈ Ico 0 T' := ⟨by linarith [hs.1, min_le_left T' (ε / (|M| + 1))], hs.2⟩
    have ht' : t ∈ Ico 0 T' := ⟨by linarith [ht.1, min_le_left T' (ε / (|M| + 1))], ht.2⟩
    have hst : ‖s - t‖ < ε / (|M| + 1) := by
      rw [Real.norm_eq_abs, abs_sub_lt_iff]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2, min_le_right T' (ε / (|M| + 1))]
    rw [dist_eq_norm]
    have h1 := hLip t ht' s hs'
    rw [lt_div_iff₀ (by positivity)] at hst
    nlinarith [abs_nonneg M, norm_nonneg (s - t), le_abs_self M]
  refine ⟨T', A, p, hlift, hp, fun hpU => ?_⟩
  -- If the limit were in `U`, a local solution near `p` would extend the lift beyond `T'`.
  obtain ⟨r, hr, ε, hε, hloc⟩ :=
    (hv p hpU).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  obtain ⟨t₁, ht₁B, ht₁⟩ := ((hp.eventually (closedBall_mem_nhds p hr)).and
    (Ioo_mem_nhdsLT (max_lt hlift.pos (by linarith) : max 0 (T' - ε) < T'))).exists
  obtain ⟨γ, hγ0, hγ⟩ := hloc (A t₁) ht₁B
  set β : ℝ → E := fun t => γ (t - t₁)
  have hβ : ∀ t ∈ Ioo (t₁ - ε) (t₁ + ε), HasDerivAt β (v (β t)) t := fun t ht =>
    (hγ (t - t₁) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_sub_const t t₁
  have ht₁0 : 0 ≤ t₁ := (le_max_left _ _).trans ht₁.1.le
  have hT'ε : T' < t₁ + ε := by linarith [ht₁.1, le_max_right 0 (T' - ε)]
  have hagree : EqOn A β (Ico t₁ T') := eqOn_Ico_of_hasDerivWithinAt hv
    (fun t ht => (hlift.deriv t ⟨ht₁0.trans ht.1, ht.2⟩).mono (Ico_subset_Ico_left ht₁0))
    (fun t ht => hlift.mem t ⟨ht₁0.trans ht.1, ht.2⟩)
    (fun t ht => (hβ t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivWithinAt)
    (by simp only [β, sub_self, hγ0])
  have hβT' : HasDerivAt β (v (β T')) T' := hβ T' ⟨by linarith [ht₁.2], hT'ε⟩
  have hβp : β T' = p := tendsto_nhds_unique
    (hβT'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hp.congr' (eventuallyEq_of_mem (Ioo_mem_nhdsLT ht₁.2) fun t ht => hagree ⟨ht.1.le, ht.2⟩))
  obtain ⟨δ, hδ, hδU⟩ :=
    Metric.mem_nhds_iff.1 (hβT'.continuousAt.preimage_mem_nhds (hU.mem_nhds (hβp ▸ hpU)))
  set T₂ := min (T' + δ) (t₁ + ε)
  have hT'T₂ : T' < T₂ := lt_min (by linarith) hT'ε
  let A₂ : ℝ → E := fun t => if t < T' then A t else β t
  have hA₂β : ∀ t, t₁ < t → A₂ t = β t := fun t ht => by
    by_cases htT : t < T'
    · simp only [A₂, htT, ite_true]; exact hagree ⟨ht.le, htT⟩
    · simp only [A₂, htT, ite_false]
  have hlift₂ : IsLift v U x₀ T₂ A₂ := by
    refine ⟨hlift.pos.trans hT'T₂, by simp only [A₂, hlift.pos, ite_true, hlift.start],
      fun t ht => ?_, fun t ht => ?_⟩
    · by_cases htT : t < T'
      · simp only [A₂, htT, ite_true]; exact hlift.mem t ⟨ht.1, htT⟩
      · simp only [A₂, htT, ite_false]
        apply hδU
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [not_lt.1 htT, ht.2, min_le_left (T' + δ) (t₁ + ε)]
    · by_cases htT : t < T'
      · have hd : HasDerivWithinAt A (v (A t)) (Ico 0 T₂) t :=
          (hlift.deriv t ⟨ht.1, htT⟩).mono_of_mem_nhdsWithin
            (mem_nhdsWithin.2 ⟨Iio T', isOpen_Iio, htT, fun s hs => ⟨hs.2.1, hs.1⟩⟩)
        have heq : A₂ =ᶠ[𝓝 t] A := eventuallyEq_of_mem (Iio_mem_nhds htT) fun s hs => by
          simp only [A₂, show s < T' from hs, ite_true]
        rw [heq.eq_of_nhds]
        exact hd.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds
      · have ht₁t : t₁ < t := ht₁.2.trans_le (not_lt.1 htT)
        have heq : A₂ =ᶠ[𝓝 t] β := eventuallyEq_of_mem (Ioi_mem_nhds ht₁t) fun s hs => hA₂β s hs
        rw [heq.eq_of_nhds]
        exact ((hβ t ⟨by linarith, ht.2.trans_le (min_le_right _ _)⟩).congr_of_eventuallyEq
          heq).hasDerivWithinAt
  linarith [le_csSup hbdd ⟨A₂, hlift₂⟩]

end Lightlike.Asymptotics
