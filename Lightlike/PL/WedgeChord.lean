import Mathlib

/-!
# A segment that leaves an open convex region through its boundary

Let `W` be the set where finitely many affine functions are all positive. A segment that passes
through a point `q` of `W` and starts at a point outside `W` meets the boundary of the closure of
`W` between its start and `q`.

## Main results

* `Lightlike.PL.exists_boundary_point`: the first point of the segment from `q` towards `x` at
  which one of the functions vanishes lies in the closure of `W`.
-/

open Set Finset

namespace Lightlike.PL

/-- **A segment from a point of an open polyhedral region to a point outside it exits through
the boundary.** For affine functions `f i`, if all are positive at `q` and one is nonpositive at
`x`, then some point `r` of the segment from `x` to `q` has all `f i r ≥ 0` and some `f i r = 0`, at an index where `f i x ≤ 0`. -/
theorem exists_boundary_point {ι : Type*} [Fintype ι] {f : ι → ℝ × ℝ → ℝ}
    (hf : ∀ i (x y : ℝ × ℝ) (s t : ℝ), s + t = 1 → f i (s • x + t • y) = s * f i x + t * f i y)
    {x q : ℝ × ℝ} (hq : ∀ i, 0 < f i q) (hx : ∃ i, f i x ≤ 0) :
    ∃ r ∈ segment ℝ x q, (∀ i, 0 ≤ f i r) ∧ ∃ i, f i x ≤ 0 ∧ f i r = 0 := by
  classical
  set I : Finset ι := univ.filter fun i => f i x ≤ 0 with hI
  obtain ⟨i₁, hi₁⟩ := hx
  have hne : I.Nonempty := ⟨i₁, by simp [hI, hi₁]⟩
  set τ : ι → ℝ := fun i => f i q / (f i q - f i x) with hτ
  obtain ⟨i₀, hi₀I, hmin⟩ := I.exists_min_image τ hne
  have hden : ∀ i ∈ I, 0 < f i q - f i x := by
    intro i hi
    have : f i x ≤ 0 := by simpa [hI] using hi
    linarith [hq i]
  have hτ0 : ∀ i ∈ I, 0 < τ i := fun i hi => div_pos (hq i) (hden i hi)
  have hτ1 : ∀ i ∈ I, τ i ≤ 1 := by
    intro i hi
    rw [hτ, div_le_one (hden i hi)]
    have : f i x ≤ 0 := by simpa [hI] using hi
    linarith
  set t := τ i₀ with ht
  have ht0 := hτ0 i₀ hi₀I
  have ht1 := hτ1 i₀ hi₀I
  -- the point at parameter `t` on the way from `q` to `x`
  have hg : ∀ i, f i ((1 - t) • q + t • x) = f i q + t * (f i x - f i q) := by
    intro i
    rw [hf i q x (1 - t) t (by ring)]; ring
  refine ⟨(1 - t) • q + t • x, ⟨t, 1 - t, ht0.le, by linarith, by ring, by
    rw [add_comm]⟩, fun i => ?_, i₀, by simpa [hI] using hi₀I, ?_⟩
  · rw [hg]
    by_cases hi : i ∈ I
    · have h1 : t ≤ τ i := hmin i hi
      have hd := hden i hi
      have : τ i * (f i q - f i x) = f i q := by rw [hτ]; field_simp
      nlinarith [hq i]
    · have : 0 < f i x := by simpa [hI] using hi
      nlinarith [hq i]
  · rw [hg, ht, hτ]
    have := (hden i₀ hi₀I).ne'
    field_simp
    ring

/-- **A segment from a boundary point towards a point strictly inside a face's half-space enters
the open region.** If all the affine functions are nonnegative at `q`, and each one that vanishes
at `q` is positive at `x`, then points of the segment close to `q` (other than `q`) have all
functions positive. -/
theorem exists_interior_point {ι : Type*} [Fintype ι] {f : ι → ℝ × ℝ → ℝ}
    (hf : ∀ i (x y : ℝ × ℝ) (s t : ℝ), s + t = 1 → f i (s • x + t • y) = s * f i x + t * f i y)
    {x q : ℝ × ℝ} (hq : ∀ i, 0 ≤ f i q) (hx : ∀ i, f i q = 0 → 0 < f i x) :
    ∃ q' ∈ segment ℝ q x, ∀ i, 0 < f i q' := by
  have hφ : ∀ i (ε : ℝ), f i ((1 - ε) • q + ε • x) = f i q + ε * (f i x - f i q) := by
    intro i ε
    rw [hf i q x (1 - ε) ε (by ring)]; ring
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 ∧ ∀ i, 0 < f i q + ε * (f i x - f i q) := by
    have h1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 :=
      nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
    have h2 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, 0 < f i q + ε * (f i x - f i q) := by
      rw [Filter.eventually_all]
      intro i
      rcases (hq i).lt_or_eq with h | h
      · have hc : Continuous fun ε : ℝ => f i q + ε * (f i x - f i q) := by fun_prop
        have := hc.continuousAt (x := 0) |>.eventually (lt_mem_nhds (by simpa using h))
        exact nhdsWithin_le_nhds this
      · have hxi := hx i h.symm
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have : 0 < ε := hε
        rw [← h]; nlinarith
    exact h1.and h2
  obtain ⟨ε, ⟨hε1, hε2⟩, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0' : 0 < ε := hε0
  exact ⟨(1 - ε) • q + ε • x, ⟨1 - ε, ε, by linarith, hε0'.le, by ring, rfl⟩, fun i => by
    rw [hφ]; exact hε2 i⟩

end Lightlike.PL
