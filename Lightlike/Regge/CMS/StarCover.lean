import Mathlib

/-!
# Stars of a triangulation cover it three times (RC6b)

Combinatorial and measure-theoretic part of the passage from a triangulation to the cell
hypotheses of the deficit convergence theorem. For a finite family of measurable sets `A t`
(triangles) that overlap only in null sets, and a finite set `V` of vertices whose stars `tt v`
list the triangles containing `v`:

* `sum_star_indicator`: `∑_{v ∈ V} ∑_j 1_{A (tt v j)} = ∑_t m t · 1_{A t}` with `m t` the number of
  corners of `t` in `V`;
* `star_cover_le`: almost everywhere the stars cover at most three times;
* `star_cover_eq`: almost everywhere outside the triangles that have a corner outside `V`, they
  cover exactly three times the union of the triangles with all corners in `V`.
-/

open MeasureTheory Set Finset

namespace Lightlike.CMS

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {τ ι : Type*} [Fintype τ]

/-- Almost everywhere, a point lies in at most one of the pairwise a.e.-disjoint sets `A t`. -/
theorem ae_unique_mem (A : τ → Set E) (hd : ∀ t t', t ≠ t' → AEDisjoint μ (A t) (A t')) :
    ∀ᵐ x ∂μ, ∀ t t', t ≠ t' → x ∈ A t → x ∉ A t' := by
  rw [ae_all_iff]; intro t
  rw [ae_all_iff]; intro t'
  by_cases h : t = t'
  · exact Filter.Eventually.of_forall fun x h' => absurd h h'
  · have : ∀ᵐ x ∂μ, x ∉ A t ∩ A t' := by
      have := hd t t' h
      unfold AEDisjoint at this
      rw [ae_iff]; simpa using this
    filter_upwards [this] with x hx _ h1 h2 using hx ⟨h1, h2⟩

theorem sum_indicator_eq (A : τ → Set E) (m : τ → ℕ) (x : E) (t0 : τ) (h0 : x ∈ A t0)
    (hx : ∀ t t', t ≠ t' → x ∈ A t → x ∉ A t') :
    (∑ t, (m t : ℝ) * (A t).indicator (fun _ => (1 : ℝ)) x) = m t0 := by
  classical
  rw [Finset.sum_eq_single t0]
  · simp [h0]
  · intro t _ htne
    have : x ∉ A t := fun hxt => hx _ _ htne.symm h0 hxt
    simp [this]
  · simp

omit [MeasurableSpace E] in
theorem sum_indicator_zero (A : τ → Set E) (m : τ → ℕ) (x : E) (h : ∀ t, x ∉ A t) :
    (∑ t, (m t : ℝ) * (A t).indicator (fun _ => (1 : ℝ)) x) = 0 := by
  simp [h]

section reindex
variable [DecidableEq ι] {c : τ → Fin 3 → ι} {V : Finset ι} {n : ι → ℕ}

/-- The number of corners of the triangle `t` that lie in `V`. -/
def cornersIn (c : τ → Fin 3 → ι) (V : Finset ι) (t : τ) : ℕ :=
  (Finset.univ.filter fun k : Fin 3 => c t k ∈ V).card

theorem cornersIn_le (c : τ → Fin 3 → ι) (V : Finset ι) (t : τ) : cornersIn c V t ≤ 3 := by
  unfold cornersIn
  calc _ ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_filter_le _ _
    _ = 3 := by simp

theorem cornersIn_eq_three_iff (c : τ → Fin 3 → ι) (V : Finset ι) (t : τ) :
    cornersIn c V t = 3 ↔ ∀ k, c t k ∈ V := by
  unfold cornersIn
  constructor
  · intro h k
    have := Finset.eq_univ_of_card (Finset.univ.filter fun k : Fin 3 => c t k ∈ V) (by simpa using h)
    have hk : k ∈ Finset.univ.filter fun k : Fin 3 => c t k ∈ V := by rw [this]; exact Finset.mem_univ _
    simpa using hk
  · intro h
    simp [h]

theorem sum_star_reindex (hinj : ∀ t, Function.Injective (c t))
    (tt : (v : ι) → ZMod (n v) → τ) [∀ v, NeZero (n v)]
    (hstar : ∀ v ∈ V, Function.Injective (tt v) ∧ ∀ t, (∃ k, c t k = v) ↔ ∃ j, tt v j = t)
    (F : τ → ℝ) :
    (∑ v ∈ V, ∑ j, F (tt v j)) = ∑ t, (cornersIn c V t : ℝ) * F t := by
  have h1 : ∀ v ∈ V, (∑ j, F (tt v j)) =
      ∑ t, if (∃ k, c t k = v) then F t else 0 := by
    intro v hv
    obtain ⟨hi, hs⟩ := hstar v hv
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun j _ => tt v j) ?_ ?_ ?_ ?_
    · intro j _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (hs _).2 ⟨j, rfl⟩
    · intro j _ j' _ h; exact hi h
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      obtain ⟨j, hj⟩ := (hs t).1 ht
      exact ⟨j, Finset.mem_univ _, hj⟩
    · intro j _; rfl
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  unfold cornersIn
  symm
  refine Finset.card_bij (fun k _ => c t k) ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢; exact ⟨hk, k, rfl⟩
  · intro k _ k' _ h; exact hinj t h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨hvV, k, rfl⟩ := hv
    exact ⟨k, hvV, rfl⟩


omit [Fintype τ] in
theorem indicator_iUnion_of_unique {J : Type*} [Fintype J] (A : J → Set E) (x : E)
    (hx : ∀ j j', j ≠ j' → x ∈ A j → x ∉ A j') :
    (⋃ j, A j).indicator (fun _ => (1 : ℝ)) x = ∑ j, (A j).indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases h : ∃ j0, x ∈ A j0
  · obtain ⟨j0, hj0⟩ := h
    rw [Set.indicator_of_mem (Set.mem_iUnion.2 ⟨j0, hj0⟩), Finset.sum_eq_single j0]
    · simp [hj0]
    · intro j _ hne
      have : x ∉ A j := fun hxj => hx _ _ hne.symm hj0 hxj
      simp [this]
    · simp
  · push Not at h
    rw [Set.indicator_of_notMem (by simpa using h)]
    simp [h]

/-- **Covering three times.** Almost everywhere, the cells `⋃ j, A (tt v j)` of the stars of `V`
cover at most three times, and outside the triangles with a corner outside `V` exactly three times
the union of the triangles with all corners in `V`. -/
theorem star_cover (A : τ → Set E) (hd : ∀ t t', t ≠ t' → AEDisjoint μ (A t) (A t'))
    (hinj : ∀ t, Function.Injective (c t)) (tt : (v : ι) → ZMod (n v) → τ) [∀ v, NeZero (n v)]
    (hstar : ∀ v ∈ V, Function.Injective (tt v) ∧ ∀ t, (∃ k, c t k = v) ↔ ∃ j, tt v j = t) :
    (∀ᵐ x ∂μ, ∑ v ∈ V, (⋃ j, A (tt v j)).indicator (fun _ => (1 : ℝ)) x ≤ 3) ∧
    (∀ᵐ x ∂μ, x ∉ (⋃ t ∈ Finset.univ.filter (fun t => cornersIn c V t ≠ 3), A t) →
      ∑ v ∈ V, (⋃ j, A (tt v j)).indicator (fun _ => (1 : ℝ)) x =
        3 * (⋃ t ∈ Finset.univ.filter (fun t => cornersIn c V t = 3), A t).indicator
          (fun _ => (1 : ℝ)) x) := by
  have key : ∀ x, (∀ t t', t ≠ t' → x ∈ A t → x ∉ A t') →
      ∑ v ∈ V, (⋃ j, A (tt v j)).indicator (fun _ => (1 : ℝ)) x =
        ∑ t, (cornersIn c V t : ℝ) * (A t).indicator (fun _ => (1 : ℝ)) x := by
    intro x hx
    rw [← sum_star_reindex hinj tt hstar (fun t => (A t).indicator (fun _ => (1 : ℝ)) x)]
    refine Finset.sum_congr rfl fun v hv => ?_
    exact indicator_iUnion_of_unique (fun j => A (tt v j)) x fun j j' hne =>
      hx _ _ (fun h => hne ((hstar v hv).1 h))
  have hae := ae_unique_mem A hd
  constructor
  · filter_upwards [hae] with x hx
    rw [key x hx]
    by_cases h : ∃ t0, x ∈ A t0
    · obtain ⟨t0, ht0⟩ := h
      rw [sum_indicator_eq A (cornersIn c V) x t0 ht0 hx]
      exact_mod_cast cornersIn_le c V t0
    · push Not at h
      rw [sum_indicator_zero A _ x h]; norm_num
  · filter_upwards [hae] with x hx hxB
    rw [key x hx]
    by_cases h : ∃ t0, x ∈ A t0
    · obtain ⟨t0, ht0⟩ := h
      rw [sum_indicator_eq A (cornersIn c V) x t0 ht0 hx]
      have h3 : cornersIn c V t0 = 3 := by
        by_contra hne
        exact hxB (Set.mem_iUnion₂.2 ⟨t0, by simpa using hne, ht0⟩)
      rw [Set.indicator_of_mem (Set.mem_iUnion₂.2 ⟨t0, by simpa using h3, ht0⟩), h3]
      norm_num
    · push Not at h
      rw [sum_indicator_zero A _ x h, Set.indicator_of_notMem]
      · norm_num
      · intro hm
        obtain ⟨t, _, ht⟩ := Set.mem_iUnion₂.1 hm
        exact h t ht

end reindex

end Lightlike.CMS
