import Lightlike.Canonical.HolonomyPaths
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Intersections of analytic arcs

Two analytic arcs in `ℝ³` that meet at points accumulating at a point, where the second has a nonzero velocity, share a
segment there: locally the first is the second composed with an analytic reparametrisation
(`eventually_eq_comp_of_tendsto`). Consequently two regular analytic arcs (`Edge.IsAnalytic`: analytic, with nonzero
velocity) meet in finitely many pieces: the boundary points of the set of parameters at which one meets the other are
finitely many (`Edge.meetFrontier_finite`). This is the fact behind the common refinement of two graphs with analytic
edges (Ashtekar–Lewandowski, arXiv:gr-qc/0404018, p. 35); their edges are embedded (footnote 13, p. 27) with analytic
pieces (footnote 17, p. 33), read as analytic immersions.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace Lightlike.Canonical

/-- **Two analytic arcs meeting at accumulating points share a segment.** Let `e`, `f : ℝ → ℝ³` be analytic at `s₀`,
`t₀`, with `f'(t₀) ≠ 0`, and let `e(u n) = f(v n)` with `u n → s₀`, `u n ≠ s₀`, `v n → t₀`. Then `e = f ∘ φ` near `s₀`
for a `φ` analytic at `s₀` with `φ(s₀) = t₀`. -/
theorem eventually_eq_comp_of_tendsto {e f : ℝ → Fin 3 → ℝ} {s₀ t₀ : ℝ} (he : AnalyticAt ℝ e s₀)
    (hf : AnalyticAt ℝ f t₀) (hf' : deriv f t₀ ≠ 0) {u v : ℕ → ℝ} (hu : Tendsto u atTop (𝓝[≠] s₀))
    (hv : Tendsto v atTop (𝓝 t₀)) (heq : ∀ n, e (u n) = f (v n)) :
    ∃ φ : ℝ → ℝ, AnalyticAt ℝ φ s₀ ∧ φ s₀ = t₀ ∧ ∀ᶠ s in 𝓝 s₀, e s = f (φ s) := by
  -- a coordinate in which `f` has a nonzero derivative
  have hfd : ∀ k, DifferentiableAt ℝ (fun t => f t k) t₀ := fun k => (analyticAt_pi_iff.1 hf k).differentiableAt
  obtain ⟨k, hk⟩ : ∃ k, deriv (fun t => f t k) t₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf' (by rw [deriv_pi hfd]; exact funext hcon)
  have hfk : AnalyticAt ℝ (fun t => f t k) t₀ := analyticAt_pi_iff.1 hf k
  have hek : ∀ s, AnalyticAt ℝ e s → AnalyticAt ℝ (fun s => e s k) s := fun s h => analyticAt_pi_iff.1 h k
  set g := hfk.hasStrictDerivAt.localInverse _ _ _ hk with hg
  have hga : AnalyticAt ℝ g (f t₀ k) := hfk.analyticAt_localInverse hk
  have hleft : ∀ᶠ t in 𝓝 t₀, g (f t k) = t := hfk.hasStrictDerivAt.eventually_left_inverse hk
  -- `e(s₀) = f(t₀)`
  have hu' : Tendsto u atTop (𝓝 s₀) := hu.mono_right nhdsWithin_le_nhds
  have he0 : e s₀ = f t₀ := by
    have h1 : Tendsto (fun n => e (u n)) atTop (𝓝 (e s₀)) := (he.continuousAt.tendsto).comp hu'
    have h2 : Tendsto (fun n => f (v n)) atTop (𝓝 (f t₀)) := (hf.continuousAt.tendsto).comp hv
    exact tendsto_nhds_unique h1 (by simpa only [heq] using h2)
  set φ : ℝ → ℝ := fun s => g (e s k) with hφ
  have hφa : AnalyticAt ℝ φ s₀ := hga.comp_of_eq (hek s₀ he) (by simp only [he0])
  have hφ0 : φ s₀ = t₀ := by simp only [hφ, he0]; exact hleft.self_of_nhds
  have hfφ : AnalyticAt ℝ (fun s => f (φ s)) s₀ := hf.comp_of_eq hφa hφ0
  set h : ℝ → Fin 3 → ℝ := fun s => e s - f (φ s) with hh
  have hha : AnalyticAt ℝ h s₀ := he.sub hfφ
  -- `h` vanishes at the points `u n`, for `n` large
  have hzero : ∀ᶠ n in atTop, h (u n) = 0 := by
    filter_upwards [hv.eventually hleft] with n hn
    simp only [hh, hφ, heq n, hn, sub_self]
  refine ⟨φ, hφa, hφ0, ?_⟩
  rcases hha.eventually_eq_zero_or_eventually_ne_zero with h0 | hne
  · filter_upwards [h0] with s hs
    exact sub_eq_zero.1 hs
  · exfalso
    obtain ⟨n, hn1, hn2⟩ := (hzero.and (hu.eventually hne)).exists
    exact hn2 hn1


/-- A real analytic function with nonzero derivative is injective near the point. -/
lemma exists_injOn_of_deriv_ne_zero {ψ : ℝ → ℝ} {s₀ : ℝ} (hψ : AnalyticAt ℝ ψ s₀) (hψ' : deriv ψ s₀ ≠ 0) :
    ∃ U ∈ 𝓝 s₀, InjOn ψ U := by
  have hleft := hψ.hasStrictDerivAt.eventually_left_inverse hψ'
  exact ⟨_, hleft, fun s hs s' hs' h => by
    have h1 : _ = s := hs
    have h2 : _ = s' := hs'
    rw [← h1, ← h2, h]⟩

/-- An analytic arc in `ℝ³` with nonzero velocity is injective near the point. -/
lemma exists_injOn_of_deriv_ne_zero' {f : ℝ → Fin 3 → ℝ} {t₀ : ℝ} (hf : AnalyticAt ℝ f t₀)
    (hf' : deriv f t₀ ≠ 0) : ∃ U ∈ 𝓝 t₀, InjOn f U := by
  have hfd : ∀ k, DifferentiableAt ℝ (fun t => f t k) t₀ := fun k => (analyticAt_pi_iff.1 hf k).differentiableAt
  obtain ⟨k, hk⟩ : ∃ k, deriv (fun t => f t k) t₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf' (by rw [deriv_pi hfd]; exact funext hcon)
  obtain ⟨U, hU, hinj⟩ := exists_injOn_of_deriv_ne_zero (analyticAt_pi_iff.1 hf k) hk
  exact ⟨U, hU, fun t ht t' ht' h => hinj ht ht' (by simp only [h])⟩

namespace Edge

/-- An edge is a **regular analytic arc**: analytic at every point of its parameter interval, with nonzero velocity
there. -/
def IsAnalytic (e : Edge) : Prop :=
  ∀ t ∈ Icc e.t₀ e.t₁, AnalyticAt ℝ e.path t ∧ deriv e.path t ≠ 0

/-- The parameters of `e` at which `e` meets the image of `f` but not on a neighbourhood (within the parameter interval):
the boundary points of the meeting set. -/
def meetFrontier (e f : Edge) : Set ℝ :=
  {s | s ∈ Icc e.t₀ e.t₁ ∧ e.path s ∈ f.path '' Icc f.t₀ f.t₁ ∧
    ¬ ∀ᶠ s' in 𝓝[Icc e.t₀ e.t₁] s, e.path s' ∈ f.path '' Icc f.t₀ f.t₁}

/-- **Two regular analytic arcs meet in finitely many pieces**: the boundary points of the set of parameters at which `e`
meets the image of `f` are finitely many. -/
theorem meetFrontier_finite {e f : Edge} (he : e.IsAnalytic) (hf : f.IsAnalytic) : (meetFrontier e f).Finite := by
  by_contra hinf
  obtain ⟨s₀, hs₀, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc (fun s hs => hs.1)
  rw [accPt_iff_frequently] at hacc
  obtain ⟨u, hu, hu'⟩ := exists_seq_forall_of_frequently hacc
  choose v hv hev using fun n => (hu' n).2.2.1
  obtain ⟨t₀, ht₀, σ, hσ, hvσ⟩ := isCompact_Icc.tendsto_subseq hv
  have huσ' : Tendsto (u ∘ σ) atTop (𝓝 s₀) := hu.comp hσ.tendsto_atTop
  have huσ : Tendsto (u ∘ σ) atTop (𝓝[≠] s₀) :=
    tendsto_nhdsWithin_iff.2 ⟨huσ', Eventually.of_forall fun n => (hu' (σ n)).1⟩
  obtain ⟨ψ, hψa, hψ0, hψe⟩ := eventually_eq_comp_of_tendsto (he s₀ hs₀).1 (hf t₀ ht₀).1 (hf t₀ ht₀).2 huσ hvσ
    (fun n => (hev (σ n)).symm)
  have hψd : deriv ψ s₀ ≠ 0 := by
    have h1 : deriv e.path s₀ = deriv (f.path ∘ ψ) s₀ := Filter.EventuallyEq.deriv_eq hψe
    have hfd : DifferentiableAt ℝ f.path (ψ s₀) := by rw [hψ0]; exact (hf t₀ ht₀).1.differentiableAt
    rw [deriv.scomp s₀ hfd hψa.differentiableAt, hψ0] at h1
    intro h0
    rw [h0, zero_smul] at h1
    exact (he s₀ hs₀).2 h1
  obtain ⟨Uf, hUf, hinjf⟩ := exists_injOn_of_deriv_ne_zero' (hf t₀ ht₀).1 (hf t₀ ht₀).2
  obtain ⟨Uψ, hUψ, hinjψ⟩ := exists_injOn_of_deriv_ne_zero hψa hψd
  have hA : ∀ᶠ n in atTop, v (σ n) ∈ Uf := hvσ.eventually hUf
  have hB : ∀ᶠ n in atTop, ψ (u (σ n)) ∈ Uf := by
    have : Tendsto (fun n => ψ (u (σ n))) atTop (𝓝 t₀) := by
      rw [← hψ0]; exact hψa.continuousAt.tendsto.comp huσ'
    exact this.eventually hUf
  have hC : ∀ᶠ n in atTop, u (σ n) ∈ Uψ := huσ'.eventually hUψ
  have hD : ∀ᶠ n in atTop, ∀ᶠ s in 𝓝 (u (σ n)), e.path s = f.path (ψ s) ∧ AnalyticAt ℝ ψ s :=
    huσ'.eventually (eventually_eventually_nhds.2 (hψe.and hψa.eventually_analyticAt))
  have hE : ∀ᶠ n in atTop, ψ (u (σ n)) ∈ ({f.t₀, f.t₁} : Set ℝ) := by
    filter_upwards [hA, hB, hD] with n hn1 hn2 hn3
    have heq : v (σ n) = ψ (u (σ n)) := hinjf hn1 hn2 ((hev (σ n)).trans hn3.self_of_nhds.1)
    by_contra hnot
    have hin : ψ (u (σ n)) ∈ Ioo f.t₀ f.t₁ := by
      refine ⟨lt_of_le_of_ne (heq ▸ (hv (σ n)).1) fun h => hnot (Or.inl h.symm),
        lt_of_le_of_ne (heq ▸ (hv (σ n)).2) fun h => hnot (Or.inr h)⟩
    apply (hu' (σ n)).2.2.2
    have hcont : ∀ᶠ s in 𝓝 (u (σ n)), ψ s ∈ Ioo f.t₀ f.t₁ :=
      hn3.self_of_nhds.2.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hin)
    have : ∀ᶠ s in 𝓝 (u (σ n)), e.path s ∈ f.path '' Icc f.t₀ f.t₁ := by
      filter_upwards [hn3, hcont] with s hs1 hs2
      exact ⟨ψ s, Ioo_subset_Icc_self hs2, hs1.1.symm⟩
    exact nhdsWithin_le_nhds this
  obtain ⟨N, hN⟩ := (hE.and hC).exists_forall_of_atTop
  -- three indices beyond `N` with distinct values, two of which `ψ` must identify
  set w := u ∘ σ with hw
  have hne : ∀ n, w n ≠ s₀ := fun n => (hu' (σ n)).1
  have hpos : ∀ n, 0 < dist (w n) s₀ := fun n => dist_pos.2 (hne n)
  obtain ⟨n₂, hn₂⟩ := (Metric.tendsto_atTop.1 huσ') _ (hpos N)
  set m₂ := max n₂ N
  have hd₂ : dist (w m₂) s₀ < dist (w N) s₀ := hn₂ m₂ (le_max_left _ _)
  obtain ⟨n₃, hn₃⟩ := (Metric.tendsto_atTop.1 huσ') _ (hpos m₂)
  set m₃ := max n₃ N
  have hd₃ : dist (w m₃) s₀ < dist (w m₂) s₀ := hn₃ m₃ (le_max_left _ _)
  have h12 : w m₂ ≠ w N := fun h => by rw [h] at hd₂; exact lt_irrefl _ hd₂
  have h23 : w m₃ ≠ w m₂ := fun h => by rw [h] at hd₃; exact lt_irrefl _ hd₃
  have h13 : w m₃ ≠ w N := fun h => by rw [h] at hd₃; exact lt_irrefl _ (hd₃.trans hd₂)
  have hval : ∀ n ≥ N, ψ (w n) = f.t₀ ∨ ψ (w n) = f.t₁ := fun n hn => by
    have := (hN n hn).1
    simpa [w] using this
  have hinj : ∀ i j, i ≥ N → j ≥ N → ψ (w i) = ψ (w j) → w i = w j := fun i j hi hj h =>
    hinjψ (hN i hi).2 (hN j hj).2 h
  have hm₂ : m₂ ≥ N := le_max_right _ _
  have hm₃ : m₃ ≥ N := le_max_right _ _
  rcases hval N le_rfl with h1 | h1 <;> rcases hval m₂ hm₂ with h2 | h2 <;> rcases hval m₃ hm₃ with h3 | h3
  all_goals first
    | exact h12 (hinj m₂ N hm₂ le_rfl (h2.trans h1.symm))
    | exact h13 (hinj m₃ N hm₃ le_rfl (h3.trans h1.symm))
    | exact h23 (hinj m₃ m₂ hm₃ hm₂ (h3.trans h2.symm))

end Edge


namespace Edge

/-- **The meeting set between two cut points.** For regular analytic `e`, `f`, on an open interval `(a, b) ⊆ [t₀, t₁]`
that contains no boundary point of the meeting set, `e` either avoids the image of `f` or lies in it on all of `[a, b]`. -/
theorem meet_dichotomy {e f : Edge} {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ Icc e.t₀ e.t₁)
    (hfr : ∀ s ∈ Ioo a b, s ∉ meetFrontier e f) :
    (∀ s ∈ Ioo a b, e.path s ∉ f.path '' Icc f.t₀ f.t₁) ∨ (∀ s ∈ Icc a b, e.path s ∈ f.path '' Icc f.t₀ f.t₁) := by
  set F := f.path '' Icc f.t₀ f.t₁ with hF
  have hFc : IsClosed F := (isCompact_Icc.image f.smooth.continuous).isClosed
  have hec : Continuous e.path := e.smooth.continuous
  classical
  set χ : ℝ → Bool := fun s => decide (e.path s ∈ F) with hχ
  have hloc : ContinuousOn χ (Ioo a b) := by
    intro s hs
    refine tendsto_nhds_of_eventually_eq ?_
    have hs' : s ∈ Icc e.t₀ e.t₁ := hsub (Ioo_subset_Icc_self hs)
    have hnhds : Ioo a b ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs
    by_cases hin : e.path s ∈ F
    · have hev : ∀ᶠ s' in 𝓝[Icc e.t₀ e.t₁] s, e.path s' ∈ F := by
        by_contra hcon
        exact hfr s hs ⟨hs', hin, hcon⟩
      have hev' : ∀ᶠ s' in 𝓝 s, e.path s' ∈ F := by
        have hI : Icc e.t₀ e.t₁ ∈ 𝓝 s := Filter.mem_of_superset hnhds (Ioo_subset_Icc_self.trans hsub)
        rwa [nhdsWithin_eq_nhds.2 hI] at hev
      filter_upwards [nhdsWithin_le_nhds hev'] with s' hs'
      simp [hχ, hs', hin]
    · have hev' : ∀ᶠ s' in 𝓝 s, e.path s' ∉ F :=
        hec.continuousAt.preimage_mem_nhds (hFc.isOpen_compl.mem_nhds hin)
      filter_upwards [nhdsWithin_le_nhds hev'] with s' hs'
      simp [hχ, hs', hin]
  have hconst : ∀ s ∈ Ioo a b, ∀ s' ∈ Ioo a b, χ s = χ s' := fun s hs s' hs' =>
    isPreconnected_Ioo.constant hloc hs hs'
  set m := (a + b) / 2 with hm
  have hmI : m ∈ Ioo a b := ⟨by linarith, by linarith⟩
  by_cases hmF : e.path m ∈ F
  · right
    have hall : ∀ s ∈ Ioo a b, e.path s ∈ F := fun s hs => by
      have := hconst s hs m hmI
      simpa [hχ, hmF] using this
    have hcl : closure (Ioo a b) ⊆ e.path ⁻¹' F :=
      closure_minimal hall (hFc.preimage hec)
    rw [closure_Ioo hab.ne] at hcl
    exact fun s hs => hcl hs
  · left
    intro s hs hsF
    have := hconst s hs m hmI
    simp [hχ, hsF, hmF] at this

end Edge

end Lightlike.Canonical
