import Lightlike.PL.ArcK33

/-!
# The horizontal segment of the weak Jordan theorem

Two arcs from `a` to `b` that meet only at their ends are cut by a horizontal line strictly between
the heights of `a` and `b` at one point each; among such pairs of points, one at minimal distance has
the open segment between them off both arcs.

## Main results

* `exists_T`: the pair of points and the segment between them (Klazar, arXiv:2604.04296, Section 2,
  Claim 4, with Propositions 1.22 and 1.23, which this replaces by a minimum over a compact set).
-/

open Set

namespace Lightlike.PL

/-- An arc from `a` to `b` meets every horizontal line between their heights. -/
lemma IsArc.exists_height {A : Set (ℝ × ℝ)} {a b : ℝ × ℝ} (h : IsArc A a b) {y₀ : ℝ}
    (h1 : b.2 ≤ y₀) (h2 : y₀ ≤ a.2) : ∃ z ∈ A, z.2 = y₀ := by
  obtain ⟨γ, hc, -, h0, h1', rfl⟩ := h
  have hc2 : ContinuousOn (fun t => (γ t).2) (Icc 0 1) := continuous_snd.comp_continuousOn hc
  obtain ⟨t, ht, hty⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hc2 ⟨by simpa [h1'] using h1, by simpa [h0] using h2⟩
  exact ⟨γ t, ⟨t, ht, rfl⟩, hty⟩

/-- **The extremal horizontal segment.** -/
theorem exists_T {A₀ A₁ : Set (ℝ × ℝ)} {a b : ℝ × ℝ} (h₀ : IsArc A₀ a b) (h₁ : IsArc A₁ a b)
    {y₀ : ℝ} (h1 : b.2 ≤ y₀) (h2 : y₀ ≤ a.2) :
    ∃ c d : ℝ × ℝ, c ∈ A₀ ∧ d ∈ A₁ ∧ c.2 = y₀ ∧ d.2 = y₀ ∧
      ∀ z ∈ segment ℝ c d, (z ∈ A₀ → z = c) ∧ (z ∈ A₁ → z = d) := by
  obtain ⟨c₀, hc₀, hc₀y⟩ := h₀.exists_height h1 h2
  obtain ⟨d₀, hd₀, hd₀y⟩ := h₁.exists_height h1 h2
  have hcomp : ∀ {A : Set (ℝ × ℝ)} {p q : ℝ × ℝ}, IsArc A p q → IsCompact A := by
    rintro A p q ⟨γ, hc, -, -, -, rfl⟩
    exact isCompact_Icc.image_of_continuousOn hc
  have hK : ∀ {A : Set (ℝ × ℝ)}, IsCompact A → IsCompact (A ∩ {z | z.2 = y₀}) := fun hA =>
    hA.inter_right (isClosed_eq continuous_snd continuous_const)
  obtain ⟨⟨c, d⟩, ⟨⟨hcA, hcy⟩, ⟨hdA, hdy⟩⟩, hmin⟩ := ((hK (hcomp h₀)).prod (hK (hcomp h₁))).exists_isMinOn
    ⟨(c₀, d₀), ⟨hc₀, hc₀y⟩, ⟨hd₀, hd₀y⟩⟩
    (by fun_prop : Continuous fun q : (ℝ × ℝ) × (ℝ × ℝ) => dist q.1 q.2).continuousOn
  simp only [mem_ofPred_eq] at hcy hdy
  simp only at hcA hdA
  have hzy : ∀ z ∈ segment ℝ c d, z.2 = y₀ := by
    rintro z ⟨p, q, hp, hq, hpq, rfl⟩
    have : (p • c + q • d).2 = p * c.2 + q * d.2 := by simp
    rw [this, hcy, hdy, ← add_mul, hpq, one_mul]
  refine ⟨c, d, hcA, hdA, hcy, hdy, fun z hz => ⟨fun hzA => ?_, fun hzA => ?_⟩⟩
  · have h3 := hmin (a := (z, d)) ⟨⟨hzA, hzy z hz⟩, ⟨hdA, hdy⟩⟩
    have h4 := dist_add_dist_of_mem_segment hz
    have h5 : dist c d ≤ dist z d := h3
    have h6 := dist_nonneg (x := z) (y := d)
    have : dist c z ≤ 0 := by linarith
    exact (dist_le_zero.1 this).symm
  · have h3 := hmin (a := (c, z)) ⟨⟨hcA, hcy⟩, ⟨hzA, hzy z hz⟩⟩
    have h4 := dist_add_dist_of_mem_segment hz
    have h5 : dist c d ≤ dist c z := h3
    have h6 := dist_nonneg (x := c) (y := z)
    have : dist z d ≤ 0 := by linarith
    exact dist_le_zero.1 this

end Lightlike.PL
