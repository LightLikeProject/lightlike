import Mathlib

/-!
# A descending sequence of parameters with a mesh condition

Let `s ⊆ ℝ` be an interval without a least element and `f : ℝ → X` a map into a metric space that is
continuous on `s`. There is a strictly decreasing sequence `t k` in `s`, starting at a given `t 0 ∈ s`
and descending to the bottom of `s` (every point of `s` is above some `t k`), and radii `r k → 0` such that
`f` moves less than `r k` on the interval `[t (k+1), t k]`: `dist (f x) (f (t k)) < r k` for `x` in it.
The proof exhausts `s` by `u j` and uses the uniform continuity of `f` on each `[u (j+1), u j]`.

This is the first step of the construction of a timelike curve that follows a past inextendible causal
curve closely.

Supporting lemma for the causal structure; no catalogue entry.
-/

open Set Filter Topology

namespace Lightlike.Causal

/-- An interval without a least element has a strictly decreasing exhausting sequence from any of its
points. -/
lemma exists_strictAnti_exhaust {s : Set ℝ} (hs : s.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnm : ∀ t ∈ s, ∃ u ∈ s, u < t) :
    ∃ u : ℕ → ℝ, u 0 = t₀ ∧ StrictAnti u ∧ (∀ j, u j ∈ s) ∧ ∀ x ∈ s, ∃ j, u j < x := by
  by_cases hb : BddBelow s
  · set L := sInf s with hL
    have hne : s.Nonempty := ⟨t₀, ht₀⟩
    have hLlt : ∀ x ∈ s, L < x := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hnm x hx
      exact lt_of_le_of_lt (csInf_le hb hy) hyx
    have hLt₀ : L < t₀ := hLlt t₀ ht₀
    have hpos : (0 : ℝ) < t₀ - L := by linarith
    refine ⟨fun j => L + (t₀ - L) / (j + 1), by simp, ?_, ?_, ?_⟩
    · intro i j hij
      have hi : (0 : ℝ) < i + 1 := by positivity
      have hij' : (i : ℝ) + 1 < j + 1 := by exact_mod_cast Nat.succ_lt_succ hij
      have := div_lt_div_of_pos_left hpos hi hij'
      simp only
      linarith
    · intro j
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hlt : L < L + (t₀ - L) / (j + 1) := by
        have : 0 < (t₀ - L) / (j + 1) := div_pos hpos hj
        linarith
      obtain ⟨y, hy, hyu⟩ := exists_lt_of_csInf_lt hne hlt
      have hle : L + (t₀ - L) / (j + 1) ≤ t₀ := by
        have : (t₀ - L) / (j + 1) ≤ t₀ - L := div_le_self hpos.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
        linarith
      exact hs.out hy ht₀ ⟨hyu.le, hle⟩
    · intro x hx
      have hx' : 0 < x - L := by linarith [hLlt x hx]
      obtain ⟨j, hj⟩ := exists_nat_gt ((t₀ - L) / (x - L))
      refine ⟨j, ?_⟩
      have hj1 : (t₀ - L) / (x - L) < (j : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ hx'] at hj1
      have : (t₀ - L) / ((j : ℝ) + 1) < x - L := by
        rw [div_lt_iff₀ (by positivity)]; linarith
      simp only
      linarith
  · rw [not_bddBelow_iff] at hb
    refine ⟨fun j => t₀ - j, by simp, ?_, ?_, ?_⟩
    · intro i j hij
      have : (i : ℝ) < j := by exact_mod_cast hij
      simp only
      linarith
    · intro j
      obtain ⟨y, hy, hyu⟩ := hb (t₀ - j)
      exact hs.out hy ht₀ ⟨hyu.le, by simp⟩
    · intro x hx
      obtain ⟨j, hj⟩ := exists_nat_gt (t₀ - x)
      exact ⟨j, by simp only; linarith⟩

/-- **A descending sequence of parameters with a mesh condition.** See the module docstring. -/
theorem exists_mesh_sequence {X : Type*} [PseudoMetricSpace X] {f : ℝ → X} {s : Set ℝ}
    (hs : s.OrdConnected) (hcont : ContinuousOn f s) {t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hnm : ∀ t ∈ s, ∃ u ∈ s, u < t) :
    ∃ (t : ℕ → ℝ) (r : ℕ → ℝ), t 0 = t₀ ∧ StrictAnti t ∧ (∀ k, t k ∈ s) ∧
      (∀ x ∈ s, ∃ k, t k < x) ∧ (∀ k, 0 < r k) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ k, ∀ x ∈ s, t (k + 1) ≤ x → x ≤ t k → dist (f x) (f (t k)) < r k := by
  obtain ⟨u, hu0, hua, hus, hux⟩ := exists_strictAnti_exhaust hs ht₀ hnm
  -- the blocks `[u (j+2), u j]` and their meshes
  have hblock : ∀ j : ℕ, ∃ m : ℝ, 0 < m ∧ m ≤ u (j + 1) - u (j + 2) ∧
      ∀ x ∈ Icc (u (j + 2)) (u j), ∀ y ∈ Icc (u (j + 2)) (u j), |x - y| ≤ m →
        dist (f x) (f y) < 1 / ((j : ℝ) + 1) := by
    intro j
    have hsub : Icc (u (j + 2)) (u j) ⊆ s := fun x hx => hs.out (hus (j + 2)) (hus j) hx
    have huc := (isCompact_Icc (a := u (j + 2)) (b := u j)).uniformContinuousOn_of_continuous
      (hcont.mono hsub)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc (1 / ((j : ℝ) + 1)) (by positivity)
    have hgap : 0 < u (j + 1) - u (j + 2) := by linarith [hua (Nat.lt_succ_self (j + 1))]
    refine ⟨min (δ / 2) (u (j + 1) - u (j + 2)), lt_min (by positivity) hgap, min_le_right _ _, ?_⟩
    intro x hx y hy hxy
    refine hδ' x hx y hy ?_
    rw [Real.dist_eq]
    have : min (δ / 2) (u (j + 1) - u (j + 2)) ≤ δ / 2 := min_le_left _ _
    linarith
  choose m hm0 hmgap hmesh using hblock
  classical
  -- the block index of a parameter
  let J : ℝ → ℕ := fun t => if h : ∃ j : ℕ, u (j + 1) < t then Nat.find h else 0
  have hJ1 : ∀ t : ℝ, (∃ j : ℕ, u (j + 1) < t) → u (J t + 1) < t := by
    intro t h
    have : J t = Nat.find h := by simp [J, h]
    rw [this]; exact Nat.find_spec h
  have hJ2 : ∀ t : ℝ, ∀ j : ℕ, u (j + 1) < t → J t ≤ j := by
    intro t j hj
    have h : ∃ j : ℕ, u (j + 1) < t := ⟨j, hj⟩
    have : J t = Nat.find h := by simp [J, h]
    rw [this]; exact Nat.find_min' h hj
  have hJ3 : ∀ t : ℝ, (∃ j : ℕ, u (j + 1) < t) → t ≤ t₀ → t ≤ u (J t) := by
    intro t h ht
    rcases Nat.eq_zero_or_pos (J t) with h0 | hpos
    · rw [h0, hu0]; exact ht
    · by_contra hlt
      push Not at hlt
      have : u (J t - 1 + 1) < t := by
        have e : J t - 1 + 1 = J t := by omega
        rw [e]; exact hlt
      have := hJ2 t (J t - 1) this
      omega
  -- one step
  let step : ℝ → ℝ := fun t => t - m (J t)
  have hgood : ∀ t : ℝ, (t ∈ s ∧ t ≤ t₀ ∧ ∃ j : ℕ, u (j + 1) < t) →
      (step t ∈ s ∧ step t ≤ t₀ ∧ ∃ j : ℕ, u (j + 1) < step t) ∧ step t < t := by
    rintro t ⟨hts, htle, hex⟩
    have hJs := hJ1 t hex
    have hgap := hmgap (J t)
    have hpos := hm0 (J t)
    have h2 : u (J t + 2) < step t := by simp only [step]; linarith
    refine ⟨⟨?_, ?_, ⟨J t + 1, h2⟩⟩, by simp only [step]; linarith⟩
    · exact hs.out (hus (J t + 2)) hts ⟨h2.le, by simp only [step]; linarith⟩
    · simp only [step]; linarith
  let tseq : ℕ → ℝ := fun k => step^[k] t₀
  have hgood0 : t₀ ∈ s ∧ t₀ ≤ t₀ ∧ ∃ j : ℕ, u (j + 1) < t₀ :=
    ⟨ht₀, le_rfl, 0, by rw [← hu0]; exact hua (Nat.lt_succ_self 0)⟩
  have hinv : ∀ k, tseq k ∈ s ∧ tseq k ≤ t₀ ∧ ∃ j : ℕ, u (j + 1) < tseq k := by
    intro k
    induction k with
    | zero => exact hgood0
    | succ k ih =>
      have : tseq (k + 1) = step (tseq k) := Function.iterate_succ_apply' step k t₀
      rw [this]; exact (hgood _ ih).1
  have htsucc : ∀ k, tseq (k + 1) = tseq k - m (J (tseq k)) := fun k =>
    Function.iterate_succ_apply' step k t₀
  have hanti : StrictAnti tseq := strictAnti_nat_of_succ_lt fun k => by
    rw [htsucc]; linarith [hm0 (J (tseq k))]
  have hJspec : ∀ k, u (J (tseq k) + 1) < tseq k := fun k => hJ1 _ (hinv k).2.2
  have hJle : ∀ k, tseq k ≤ u (J (tseq k)) := fun k => hJ3 _ (hinv k).2.2 (hinv k).2.1
  -- the sequence exhausts `s`
  have hexh : ∀ x ∈ s, ∃ k, tseq k < x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀⟩ := hux x hx
    have hJb : ∀ k, J (tseq k) ≤ j₀ := by
      intro k
      rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
      · exfalso
        rw [h0, hu0] at hj₀
        linarith [(hinv k).2.1, hcon k]
      · have e : j₀ - 1 + 1 = j₀ := by omega
        have : u (j₀ - 1 + 1) < tseq k := by rw [e]; linarith [hcon k]
        have := hJ2 _ _ this
        omega
    -- a uniform lower bound for the steps
    obtain ⟨mstar, hmstar0, hmstar⟩ : ∃ mstar : ℝ, 0 < mstar ∧ ∀ j ≤ j₀, mstar ≤ m j := by
      refine ⟨(Finset.range (j₀ + 1)).inf' (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero j₀)) m, ?_, ?_⟩
      · obtain ⟨j, -, hj'⟩ := Finset.exists_mem_eq_inf' ((Finset.nonempty_range_iff.2 (Nat.succ_ne_zero j₀))) m
        rw [hj']; exact hm0 j
      · intro j hj; exact Finset.inf'_le _ (by simpa [Nat.lt_succ_iff] using hj)
    have hlin : ∀ k, tseq k ≤ t₀ - k * mstar := by
      intro k
      induction k with
      | zero => simp [tseq]
      | succ k ih =>
        rw [htsucc]
        have := hmstar (J (tseq k)) (hJb k)
        push_cast
        linarith
    obtain ⟨K, hK⟩ := exists_nat_gt ((t₀ - x) / mstar)
    have := hlin K
    have h2 := hcon K
    have : (t₀ - x) < K * mstar := by
      rw [div_lt_iff₀ hmstar0] at hK; exact hK
    linarith
  -- the radii
  have hJt : Tendsto (fun k => J (tseq k)) atTop atTop := by
    refine tendsto_atTop.2 fun j₁ => ?_
    obtain ⟨k₁, hk₁⟩ := hexh (u j₁) (hus j₁)
    filter_upwards [eventually_ge_atTop k₁] with k hk
    have h1 : tseq k < u j₁ := lt_of_le_of_lt (hanti.antitone hk) hk₁
    have h2 := hJspec k
    by_contra hcon
    push Not at hcon
    have : u j₁ ≤ u (J (tseq k) + 1) := hua.antitone (by omega)
    linarith
  refine ⟨tseq, fun k => 1 / ((J (tseq k) : ℝ) + 1), rfl, hanti, fun k => (hinv k).1, hexh,
    fun k => by positivity, ?_, ?_⟩
  · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hJt
  · intro k x hxs hx1 hx2
    set j := J (tseq k) with hj
    have hlow : u (j + 2) < tseq (k + 1) := by
      rw [htsucc]
      have := hmgap j
      have := hJspec k
      simp only [hj] at *
      linarith
    have hup := hJle k
    have hlowk : u (j + 2) < tseq k := by
      have := hm0 j
      rw [htsucc] at hlow; linarith
    refine hmesh j x ⟨by linarith, by simp only [hj] at *; linarith⟩ (tseq k)
      ⟨hlowk.le, hup⟩ ?_
    rw [abs_of_nonpos (by linarith)]
    rw [htsucc] at hx1
    simp only [hj] at *
    linarith

end Lightlike.Causal
