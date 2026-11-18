import Lightlike.Spacetime.Causal.ChainStep
import Lightlike.Spacetime.Causal.MeshSequence

/-!
# A descending chain of points above a past inextendible causal curve

Let `λ` be a curve that is continuous on an interval `s` without a least element and runs into the
causal future (`λ b ∈ J⁺(λ a)` for `a ≤ b`). Starting from `q₀ ∈ I⁺(λ t₀)` there are parameters
`t k ↓` the bottom of `s` and points `q k` with `q k ∈ I⁺(λ (t k))`, `q k ∈ I⁺(q (k+1))`, and such that
whenever the `q k` converge to `e`, the curve has `e` as a past endpoint: for every neighbourhood `N` of `e`,
`λ x ∈ N` for all `x ∈ s` below some parameter. The parameters come from `exists_mesh_sequence`, the points
from `exists_chain_step`, and the convergence from a metric on `M` (a second countable Hausdorff manifold is
metrizable). So if `λ` has no past endpoint, the chain, joined by timelike pieces, has none either.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **The chain above a curve.** See the module docstring. -/
theorem exists_chain [T2Space M] [SecondCountableTopology M]
    (hpush : ∀ x y z : M, y ∈ causalFuture T x → z ∈ chronFuture T y → z ∈ chronFuture T x)
    {lam : ℝ → M} {s : Set ℝ} (hs : s.OrdConnected) (hcont : ContinuousOn lam s)
    (hnm : ∀ t ∈ s, ∃ u ∈ s, u < t)
    (hcaus : ∀ a ∈ s, ∀ b ∈ s, a ≤ b → lam b ∈ causalFuture T (lam a))
    {t₀ : ℝ} (ht₀ : t₀ ∈ s) {q₀ : M} (hq₀ : q₀ ∈ chronFuture T (lam t₀)) :
    ∃ (t : ℕ → ℝ) (q : ℕ → M), t 0 = t₀ ∧ q 0 = q₀ ∧ StrictAnti t ∧ (∀ k, t k ∈ s) ∧
      (∀ x ∈ s, ∃ k, t k < x) ∧ (∀ k, q k ∈ chronFuture T (lam (t k))) ∧
      (∀ k, q k ∈ chronFuture T (q (k + 1))) ∧
      ∀ e : M, Tendsto q atTop (𝓝 e) → ∀ N ∈ 𝓝 e, ∃ c ∈ s, ∀ x ∈ s, x ≤ c → lam x ∈ N := by
  have hfd : FiniteDimensional ℝ E := by
    obtain ⟨e, -⟩ := g.lorentzian q₀
    exact Module.Finite.of_basis e
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  haveI : TopologicalSpace.MetrizableSpace M := inferInstance
  letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨t, r, ht0, hanti, hts, hexh, hrpos, hrlim, hmesh⟩ :=
    exists_mesh_sequence (f := lam) hs hcont ht₀ hnm
  -- the step of the chain
  have hstep : ∀ k (x : M), x ∈ chronFuture T (lam (t k)) →
      ∃ q' ∈ Metric.ball (lam (t (k + 1))) (r (k + 1)), q' ∈ chronFuture T (lam (t (k + 1))) ∧
        x ∈ chronFuture T q' := by
    intro k x hx
    exact exists_chain_step T hpush (hcaus _ (hts (k + 1)) _ (hts k) (hanti (Nat.lt_succ_self k)).le) hx
      (Metric.ball_mem_nhds _ (hrpos (k + 1)))
  let S : ℕ → Type _ := fun k => {x : M // x ∈ chronFuture T (lam (t k))}
  choose F hFball hFmem hFlt using fun k (x : S k) => hstep k x.1 x.2
  let Q : (k : ℕ) → S k := fun k => Nat.rec (motive := S) ⟨q₀, by rw [ht0]; exact hq₀⟩
    (fun k x => ⟨F k x, hFmem k x⟩) k
  have hQsucc : ∀ k, (Q (k + 1)).1 = F k (Q k) := fun k => rfl
  refine ⟨t, fun k => (Q k).1, ht0, rfl, hanti, hts, hexh, fun k => (Q k).2, ?_, ?_⟩
  · intro k
    show (Q k).1 ∈ chronFuture T (Q (k + 1)).1
    rw [hQsucc]
    exact hFlt k (Q k)
  · intro e he N hN
    obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
    have h1 : ∀ᶠ k in atTop, (Q k).1 ∈ Metric.ball e (ε / 3) := he.eventually (Metric.ball_mem_nhds _ (by positivity))
    have h2 : ∀ᶠ k in atTop, r k < ε / 3 := hrlim.eventually (gt_mem_nhds (by positivity))
    obtain ⟨K, hK⟩ := ((h1.and h2).and (eventually_ge_atTop 1)).exists_forall_of_atTop
    refine ⟨t K, hts K, fun x hx hxK => ?_⟩
    apply hεN
    -- the interval of the chain containing `x`
    have hex : ∃ k, t k ≤ x := by
      obtain ⟨k, hk⟩ := hexh x hx
      exact ⟨k, hk.le⟩
    classical
    set k₀ := Nat.find hex with hk₀
    have hk₀spec : t k₀ ≤ x := Nat.find_spec hex
    have hk₀min : ∀ j < k₀, x < t j := fun j hj => not_le.1 (Nat.find_min hex hj)
    have hKk : K ≤ k₀ := by
      by_contra hlt
      have := hanti (not_le.1 hlt)
      linarith
    obtain ⟨k', hk'K, hk'1, hk'2⟩ : ∃ k', K ≤ k' ∧ t (k' + 1) ≤ x ∧ x ≤ t k' := by
      by_cases hkK : k₀ = K
      · refine ⟨K, le_rfl, ?_, ?_⟩
        · have : t (K + 1) < t K := hanti (Nat.lt_succ_self K)
          have h3 : t K ≤ x := by rw [← hkK]; exact hk₀spec
          linarith
        · exact hxK
      · refine ⟨k₀ - 1, by omega, ?_, (hk₀min (k₀ - 1) (by omega)).le⟩
        have : k₀ - 1 + 1 = k₀ := by omega
        rw [this]; exact hk₀spec
    obtain ⟨⟨hq1, hr1⟩, hge⟩ := hK k' hk'K
    have hd1 := hmesh k' x hx hk'1 hk'2
    -- `Q k'` is within `r k'` of `lam (t k')`
    obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    have hd2 : dist (Q (j + 1)).1 (lam (t (j + 1))) < r (j + 1) := by
      rw [hQsucc]; exact Metric.mem_ball.1 (hFball j (Q j))
    rw [Metric.mem_ball] at hq1 ⊢
    calc dist (lam x) e ≤ dist (lam x) (lam (t (j + 1))) + dist (lam (t (j + 1))) (Q (j + 1)).1 +
          dist (Q (j + 1)).1 e := by
          have := dist_triangle (lam x) (lam (t (j + 1))) (Q (j + 1)).1
          have := dist_triangle (lam x) (Q (j + 1)).1 e
          linarith [dist_comm (lam (t (j + 1))) (Q (j + 1)).1]
      _ < ε := by linarith [dist_comm (lam (t (j + 1))) (Q (j + 1)).1]

end Lightlike.Causal
