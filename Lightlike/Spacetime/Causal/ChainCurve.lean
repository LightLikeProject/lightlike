import Lightlike.Spacetime.Causal.CauchyDomain
import Lightlike.Spacetime.Causal.CurveGlobal
import Lightlike.Spacetime.Causal.CurveOps

/-!
# A curve through a descending chain of timelike pieces

If `q k ∈ I⁺(q (k + 1))` for all `k`, the points `q k` lie on one future-directed timelike curve `G`:
`G (β k) = q k` for parameters `β k` decreasing from `β 0 = 0`, and `G` is timelike on each
`[β (K + 1), 0]` (`exists_chain_curve`). The pieces come from the definition of `I⁺` and are placed by
translation of the parameter (`IsFutureTimelikeCurve.shift`) on consecutive intervals, so only
translations are needed.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Bundle Manifold Filter Topology
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **Translation of the parameter of a timelike curve.** -/
theorem IsFutureTimelikeCurve.shift {γ : ℝ → M} {a b : ℝ} (h : IsFutureTimelikeCurve T γ (Icc a b))
    (hab : a < b) (k : ℝ) : IsFutureTimelikeCurve T (fun t => γ (t + k)) (Icc (a - k) (b - k)) := by
  obtain ⟨ε, hε, hm⟩ := h.2 a b hab subset_rfl
  exact isFutureTimelikeCurve_of_margin T hε (hm.shift hab k)

/-- **A descending chain of timelike pieces lies on one timelike curve.** If `q k ∈ I⁺(q (k + 1))` for all
`k`, there are parameters `β k` strictly decreasing from `β 0 = 0` and a curve `G` with `G (β k) = q k` that is a
future-directed timelike curve on `[β (K + 1), 0]` for every `K`. -/
theorem exists_chain_curve {q : ℕ → M} (hq : ∀ k, q k ∈ chronFuture T (q (k + 1))) :
    ∃ (G : ℝ → M) (β : ℕ → ℝ), β 0 = 0 ∧ StrictAnti β ∧ (∀ k, G (β k) = q k) ∧
      ∀ K, IsFutureTimelikeCurve T G (Icc (β (K + 1)) 0) := by
  -- the pieces
  choose c a b hab hc hca hcb using fun k => hq k
  -- the parameter placement
  let β : ℕ → ℝ := fun k => -∑ i ∈ Finset.range k, (b i - a i)
  have hβ0 : β 0 = 0 := by simp [β]
  have hβs : ∀ k, β (k + 1) = β k - (b k - a k) := fun k => by
    simp [β, Finset.sum_range_succ]; ring
  have hβanti : StrictAnti β := strictAnti_nat_of_succ_lt fun k => by
    rw [hβs]; linarith [hab k]
  classical
  let K₀ : ℝ → ℕ := fun σ => if h : ∃ k, β (k + 1) ≤ σ then Nat.find h else 0
  let G : ℝ → M := fun σ => c (K₀ σ) (σ + (a (K₀ σ) - β (K₀ σ + 1)))
  -- the block index
  have hKeq : ∀ k σ, β (k + 1) ≤ σ → (∀ j < k, σ < β (j + 1)) → K₀ σ = k := by
    intro k σ h1 h2
    have h : ∃ j, β (j + 1) ≤ σ := ⟨k, h1⟩
    simp only [K₀, h, dite_true]
    exact (Nat.find_eq_iff h).2 ⟨h1, fun j hj => not_le.2 (h2 j hj)⟩
  -- on the `k`-th block, `G` is the translated piece
  have hGblock : ∀ k, ∀ σ ∈ Icc (β (k + 1)) (β k), G σ = c k (σ + (a k - β (k + 1))) := by
    intro k σ hσ
    rcases hσ.2.lt_or_eq with hlt | heq
    · have hK : K₀ σ = k := hKeq k σ hσ.1 (fun j hj => lt_of_lt_of_le hlt (hβanti.antitone (by omega)))
      simp only [G, hK]
    · rcases k with _ | j
      · have hK : K₀ σ = 0 := hKeq 0 σ hσ.1 (fun j hj => absurd hj (by omega))
        simp only [G, hK]
      · have hK : K₀ σ = j := hKeq j σ (by rw [heq]) (fun m hm => by
          rw [heq]; exact hβanti (by omega))
        simp only [G, hK]
        rw [heq]
        have e1 : β (j + 1) + (a j - β (j + 1)) = a j := by ring
        have e2 : β (j + 1) + (a (j + 1) - β (j + 1 + 1)) = b (j + 1) := by
          rw [hβs (j + 1)]; ring
        rw [e1, e2, hca j, hcb (j + 1)]
  refine ⟨G, β, hβ0, hβanti, ?_, ?_⟩
  · intro k
    have h1 := hGblock k (β k) ⟨(hβanti (Nat.lt_succ_self k)).le, le_rfl⟩
    rw [h1]
    have : β k + (a k - β (k + 1)) = b k := by rw [hβs k]; ring
    rw [this, hcb k]
  · intro K
    induction K with
    | zero =>
      have hpiece : IsFutureTimelikeCurve T (fun t => c 0 (t + (a 0 - β 1))) (Icc (β 1) (β 0)) := by
        have := (hc 0).shift T (hab 0) (a 0 - β 1)
        have e1 : a 0 - (a 0 - β 1) = β 1 := by ring
        have e2 : b 0 - (a 0 - β 1) = β 0 := by rw [hβs 0]; ring
        rw [e1, e2] at this
        exact this
      have hG0 : IsFutureTimelikeCurve T G (Icc (β 1) (β 0)) :=
        hpiece.congr_Icc T fun t ht => hGblock 0 t ht
      rw [hβ0] at hG0
      exact hG0
    | succ K ih =>
      have hpiece : IsFutureTimelikeCurve T (fun t => c (K + 1) (t + (a (K + 1) - β (K + 2))))
          (Icc (β (K + 2)) (β (K + 1))) := by
        have := (hc (K + 1)).shift T (hab (K + 1)) (a (K + 1) - β (K + 2))
        have e1 : a (K + 1) - (a (K + 1) - β (K + 2)) = β (K + 2) := by ring
        have e2 : b (K + 1) - (a (K + 1) - β (K + 2)) = β (K + 1) := by rw [hβs (K + 1)]; ring
        rw [e1, e2] at this
        exact this
      have hlt1 : β (K + 2) < β (K + 1) := hβanti (Nat.lt_succ_self _)
      have hlt2 : β (K + 1) < 0 := by rw [← hβ0]; exact hβanti (Nat.succ_pos K)
      have hjoin : (fun t => c (K + 1) (t + (a (K + 1) - β (K + 2)))) (β (K + 1)) = G (β (K + 1)) :=
        (hGblock (K + 1) (β (K + 1)) ⟨hlt1.le, le_rfl⟩).symm
      have hglue := IsFutureTimelikeCurve.glue T hpiece ih hlt1 hlt2 hjoin
      refine hglue.congr_Icc T fun t ht => ?_
      by_cases htb : t ≤ β (K + 1)
      · simp only [htb, if_true]
        exact hGblock (K + 1) t ⟨ht.1, htb⟩
      · simp [htb]

end Lightlike.Causal
