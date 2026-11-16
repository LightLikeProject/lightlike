import Lightlike.PL.LoopErase

/-!
# Approximating a continuous arc by a polygonal chain

A continuous map on `[0, 1]` into the plane is uniformly continuous, so the polygonal chain through
its values at the points `k / N`, for `N` large, stays within any prescribed distance of the arc.

## Main results

* `exists_chain_near`: a chain from `f 0` to `f 1` whose set lies within `ε` of the image of `f`.
* `exists_simple_chain_near`: the same for a simple chain, when `f 0 ≠ f 1`.
-/

open Set

namespace Lightlike.PL

/-- The chain of the points `g k, g (k + 1), …, g (k + m)`. -/
def sampleFrom (g : ℕ → ℝ × ℝ) : ℕ → ℕ → List (ℝ × ℝ)
  | k, 0 => [g k]
  | k, m + 1 => g k :: sampleFrom g (k + 1) m

lemma sampleFrom_head (g : ℕ → ℝ × ℝ) (k m : ℕ) : (sampleFrom g k m).head? = some (g k) := by
  cases m <;> simp [sampleFrom]

lemma sampleFrom_last (g : ℕ → ℝ × ℝ) : ∀ m k, (sampleFrom g k m).getLast? = some (g (k + m))
  | 0, k => by simp [sampleFrom]
  | m + 1, k => by
    have := sampleFrom_last g m (k + 1)
    cases hm : sampleFrom g (k + 1) m with
    | nil => simp [hm] at this
    | cons a t =>
      rw [hm] at this
      simp only [sampleFrom, hm, List.getLast?_cons_cons]
      rw [this]; congr 2; omega

/-- A point of a segment between two points at distance less than `ε` is within `ε` of the first. -/
lemma dist_lt_of_mem_segment {p q y : ℝ × ℝ} {ε : ℝ} (hy : y ∈ segment ℝ p q) (h : dist p q < ε) :
    dist y p < ε := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have e : a • p + b • q - p = b • (q - p) := by
    obtain rfl : a = 1 - b := by linarith
    module
  rw [dist_eq_norm, e, norm_smul, Real.norm_of_nonneg hb]
  have : ‖q - p‖ < ε := by rw [← dist_eq_norm, dist_comm]; exact h
  calc b * ‖q - p‖ ≤ 1 * ‖q - p‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := by linarith

lemma chainSet_sampleFrom_succ (g : ℕ → ℝ × ℝ) (k m : ℕ) :
    chainSet (sampleFrom g k (m + 1)) = segment ℝ (g k) (g (k + 1)) ∪ chainSet (sampleFrom g (k + 1) m) := by
  cases m <;> simp [sampleFrom, chainSet]

lemma sampleFrom_near (g : ℕ → ℝ × ℝ) {ε : ℝ} (hε : 0 < ε) : ∀ m k,
    (∀ j, k ≤ j → j < k + m → dist (g j) (g (j + 1)) < ε) →
    ∀ y ∈ chainSet (sampleFrom g k m), ∃ j, k ≤ j ∧ j ≤ k + m ∧ dist y (g j) < ε
  | 0, k, _, y, hy => by
    simp only [sampleFrom, chainSet, mem_singleton_iff] at hy
    exact ⟨k, le_rfl, by omega, by simp [hy, hε]⟩
  | m + 1, k, h, y, hy => by
    rw [chainSet_sampleFrom_succ] at hy
    rcases hy with hy | hy
    · exact ⟨k, le_rfl, by omega, dist_lt_of_mem_segment hy (h k le_rfl (by omega))⟩
    · obtain ⟨j, hj1, hj2, hj3⟩ := sampleFrom_near g hε m (k + 1)
        (fun j hj1 hj2 => h j (by omega) (by omega)) y hy
      exact ⟨j, by omega, by omega, hj3⟩

/-- **A chain close to a continuous arc.** -/
theorem exists_chain_near {f : ℝ → ℝ × ℝ} (hf : ContinuousOn f (Icc 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × ℝ), l.head? = some (f 0) ∧ l.getLast? = some (f 1) ∧
      ∀ y ∈ chainSet l, ∃ t ∈ Icc (0 : ℝ) 1, dist y (f t) < ε := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  set N : ℕ := n + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hNδ : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    have : 1 < δ * n := by rwa [div_lt_iff₀ hδ, mul_comm] at hn
    have : (n : ℝ) ≤ N := by simp [hN]
    nlinarith
  set g : ℕ → ℝ × ℝ := fun k => f (k / N) with hg
  have hmem : ∀ j : ℕ, j ≤ N → (j : ℝ) / N ∈ Icc (0 : ℝ) 1 := fun j hj =>
    ⟨by positivity, by rw [div_le_one hNpos]; exact_mod_cast hj⟩
  refine ⟨sampleFrom g 0 N, by simpa [hg] using sampleFrom_head g 0 N, ?_, ?_⟩
  · rw [sampleFrom_last]
    simp [hg, hNpos.ne']
  · intro y hy
    obtain ⟨j, -, hj, hyj⟩ := sampleFrom_near g hε N 0 (fun j _ hj => by
      have := hd _ (hmem j (by omega)) _ (hmem (j + 1) (by omega)) (by
        rw [Real.dist_eq]
        have : ((j + 1 : ℕ) : ℝ) / N - (j : ℝ) / N = 1 / N := by push_cast; field_simp; ring
        rw [show (j : ℝ) / N - ((j + 1 : ℕ) : ℝ) / N = -(1 / N) by linarith, abs_neg,
          abs_of_pos (by positivity)]
        exact hNδ)
      exact this) y hy
    exact ⟨j / N, hmem j (by omega), hyj⟩

/-- **A simple chain close to a continuous arc.** -/
theorem exists_simple_chain_near {f : ℝ → ℝ × ℝ} (hf : ContinuousOn f (Icc 0 1)) {ε : ℝ}
    (hε : 0 < ε) : ∃ s : List (ℝ × ℝ), IsSimpleChain s ∧ s.head? = some (f 0) ∧
      s.getLast? = some (f 1) ∧ ∀ y ∈ chainSet s, ∃ t ∈ Icc (0 : ℝ) 1, dist y (f t) < ε := by
  obtain ⟨l, h1, h2, h3⟩ := exists_chain_near hf hε
  obtain ⟨s, hs, hs1, hs2, hs3⟩ := exists_simple_sub l _ _ h1 h2
  exact ⟨s, hs, hs1, hs2, fun y hy => h3 y (hs3 hy)⟩

end Lightlike.PL
