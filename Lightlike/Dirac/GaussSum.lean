import Mathlib

/-!
# An elementary evaluation of `₂F₁(a, −a; c; 1)`

`hgTerm a c n = (a)_n (−a)_n / ((c)_n n!)`.  Telescoping gives `(c² − a²) S(c+1) = c² S(c)` for the sums
`S(c) = Σ hgTerm a c n`, and for `c = 1` the terms are `P_n − P_{n−1}` with `P_n = ∏_{j ≤ n}(1 − a²/j²)`, so
`S(1) = sin(πa)/(πa)` (Euler's product).  This is the evaluation at infinity of the regular solution of the Dirac mode
system on the sphere.
-/

namespace Lightlike.Dirac

/-- The terms `(a)_n (−a)_n / ((c)_n n!)` of `₂F₁(a, −a; c; 1)`. -/
noncomputable def hgTerm (a c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => hgTerm a c n * (((n : ℂ) + a) * ((n : ℂ) - a)) / ((c + n) * ((n : ℂ) + 1))

/-- Shifting `c` by one multiplies the `n`-th term by `c / (c + n)`. -/
lemma hgTerm_shift (a c : ℂ) (hc : ∀ n : ℕ, c + n ≠ 0) : ∀ n : ℕ,
    hgTerm a (c + 1) n = c / (c + n) * hgTerm a c n := by
  intro n
  induction n with
  | zero =>
    have : c ≠ 0 := by simpa using hc 0
    simp [hgTerm, div_self this]
  | succ n ih =>
    have h1 : c + n ≠ 0 := hc n
    have h2 : c + (n + 1 : ℕ) ≠ 0 := hc (n + 1)
    have h3 : c + 1 + n ≠ 0 := by
      have := hc (n + 1); push_cast at this; intro h; apply this; linear_combination h
    have h4 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp only [hgTerm, ih]
    push_cast at h2 ⊢
    field_simp
    ring

/-- **The telescoping identity.** -/
lemma hgTerm_telescope (a c : ℂ) (hc : ∀ n : ℕ, c + n ≠ 0) (n : ℕ) :
    (c ^ 2 - a ^ 2) * hgTerm a (c + 1) n - c ^ 2 * hgTerm a c n =
      c * ((n : ℂ) + 1) * hgTerm a c (n + 1) - c * (n : ℂ) * hgTerm a c n := by
  have h1 : c + n ≠ 0 := hc n
  have h4 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [hgTerm_shift a c hc n]
  simp only [hgTerm]
  field_simp
  ring

/-- **Partial sums of the telescoping identity.** -/
lemma hgTerm_partial (a c : ℂ) (hc : ∀ n : ℕ, c + n ≠ 0) (N : ℕ) :
    (c ^ 2 - a ^ 2) * ∑ n ∈ Finset.range N, hgTerm a (c + 1) n - c ^ 2 * ∑ n ∈ Finset.range N, hgTerm a c n =
      c * (N : ℂ) * hgTerm a c N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
    have := hgTerm_telescope a c hc N
    push_cast
    linear_combination ih + this

/-- The partial products of Euler's sine product. -/
noncomputable def eulerProd (a : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1 - a ^ 2 / ((j : ℂ) + 1) ^ 2)

/-- One more factor of the Euler product. -/
lemma eulerProd_succ (a : ℂ) (n : ℕ) :
    eulerProd a (n + 1) = eulerProd a n * (1 - a ^ 2 / ((n : ℂ) + 1) ^ 2) := by
  unfold eulerProd; rw [Finset.prod_range_succ]

/-- For `c = 1` the terms are the differences of the Euler products. -/
lemma hgTerm_one_succ (a : ℂ) (n : ℕ) :
    hgTerm a 1 (n + 1) = -(a ^ 2 / ((n : ℂ) + 1) ^ 2) * eulerProd a n := by
  induction n with
  | zero => simp [hgTerm, eulerProd]; ring
  | succ n ih =>
    have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : ((n : ℂ) + 1 + 1) ≠ 0 := by
      have : (0 : ℝ) < n + 1 + 1 := by positivity
      exact_mod_cast this.ne'
    have h3 : (2 + (n : ℂ)) ≠ 0 := by
      have : (0 : ℝ) < 2 + n := by positivity
      exact_mod_cast this.ne'
    have h4 : ((n : ℂ) + 2) ≠ 0 := by
      have : (0 : ℝ) < n + 2 := by positivity
      exact_mod_cast this.ne'
    rw [hgTerm, ih, eulerProd_succ]
    push_cast
    rw [show (1 : ℂ) + ((n : ℂ) + 1) = (n : ℂ) + 2 by ring, show ((n : ℂ) + 1) + 1 = (n : ℂ) + 2 by ring]
    field_simp
    ring

/-- The partial sums for `c = 1` are the Euler products. -/
lemma hgTerm_one_partial (a : ℂ) (N : ℕ) : ∑ n ∈ Finset.range (N + 1), hgTerm a 1 n = eulerProd a N := by
  induction N with
  | zero => simp [hgTerm, eulerProd]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, hgTerm_one_succ, eulerProd_succ]
    have h1 : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    field_simp
    ring

/-- **Euler's product**: the partial products converge to `sin(πa)/(πa)` for `a ≠ 0`. -/
lemma tendsto_eulerProd {a : ℂ} (ha : a ≠ 0) :
    Filter.Tendsto (fun N : ℕ => eulerProd a N) Filter.atTop (nhds (Complex.sin (Real.pi * a) / (Real.pi * a))) := by
  have := tendsto_euler_sin_prod' ha
  refine this.congr fun N => ?_
  unfold eulerProd
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [sineTerm]
  ring

/-- Partial sums `Σ_{n<N} hgTerm a c n`. -/
noncomputable def hgPartial (a c : ℂ) (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, hgTerm a c n

/-- The terms for `c = 1` decay like `1/N²`, so `N · h_N → 0`. -/
lemma tendsto_mul_hgTerm_one {a : ℂ} (ha : a ≠ 0) :
    Filter.Tendsto (fun N : ℕ => (N : ℂ) * hgTerm a 1 N) Filter.atTop (nhds 0) := by
  have hP := tendsto_eulerProd ha
  have h1 : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    refine this.congr fun n => ?_
    simp
  have h2 : Filter.Tendsto (fun n : ℕ => eulerProd a n * (-a ^ 2 * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ))) Filter.atTop
      (nhds 0) := by
    have := hP.mul (h1.const_mul (-a ^ 2))
    simpa using this
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine h2.congr fun n => ?_
  rw [hgTerm_one_succ]
  have h3 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-- `N · h_N(c) → 0` for every integer `c = j + 1 ≥ 1`. -/
lemma tendsto_mul_hgTerm {a : ℂ} (ha : a ≠ 0) (j : ℕ) :
    Filter.Tendsto (fun N : ℕ => (N : ℂ) * hgTerm a ((j : ℂ) + 1) N) Filter.atTop (nhds 0) := by
  induction j with
  | zero => simpa using tendsto_mul_hgTerm_one ha
  | succ j ih =>
    have hc : ∀ n : ℕ, ((j : ℂ) + 1) + n ≠ 0 := fun n => by
      have : (0 : ℝ) < j + 1 + n := by positivity
      exact_mod_cast this.ne'
    have h1 : Filter.Tendsto (fun N : ℕ => ((j : ℂ) + 1) / (((j : ℂ) + 1) + N)) Filter.atTop (nhds 0) := by
      have hr : Filter.Tendsto (fun N : ℕ => (((j : ℝ) + 1) / (((j : ℝ) + 1) + N) : ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
      have := (Complex.continuous_ofReal.tendsto 0).comp hr
      refine this.congr fun N => ?_
      simp
    have := h1.mul ih
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    have e := hgTerm_shift a ((j : ℂ) + 1) hc N
    push_cast
    rw [e]
    ring

/-- **The value at infinity.** For `a ≠ 0` with `a² ≠ j²` for `1 ≤ j ≤ m`, the partial sums of `₂F₁(a, −a; m+1; 1)`
converge to `sin(πa)/(πa) · ∏_{j=1}^m j² / (j² − a²)`. -/
theorem tendsto_hgPartial {a : ℂ} (ha : a ≠ 0) (m : ℕ) (hne : ∀ j < m, ((j : ℂ) + 1) ^ 2 ≠ a ^ 2) :
    Filter.Tendsto (fun N : ℕ => hgPartial a ((m : ℂ) + 1) N) Filter.atTop
      (nhds (Complex.sin (Real.pi * a) / (Real.pi * a) *
        ∏ j ∈ Finset.range m, (((j : ℂ) + 1) ^ 2 / (((j : ℂ) + 1) ^ 2 - a ^ 2)))) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Finset.range_zero, Finset.prod_empty, mul_one]
    have := tendsto_eulerProd ha
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    refine this.congr fun N => ?_
    unfold hgPartial
    rw [hgTerm_one_partial]
  | succ m ih =>
    have ih' := ih (fun j hj => hne j (Nat.lt_succ_of_lt hj))
    set c : ℂ := (m : ℂ) + 1 with hc
    have hcn : ∀ n : ℕ, c + n ≠ 0 := fun n => by
      have : (0 : ℝ) < m + 1 + n := by positivity
      rw [hc]; exact_mod_cast this.ne'
    have hden : c ^ 2 - a ^ 2 ≠ 0 := sub_ne_zero.mpr (hne m (Nat.lt_succ_self m))
    have hN := tendsto_mul_hgTerm ha m
    rw [← hc] at hN
    have h1 := (ih'.const_mul (c ^ 2)).add (hN.const_mul c)
    have h2 := h1.div_const (c ^ 2 - a ^ 2)
    have hlim : (c ^ 2 * (Complex.sin (Real.pi * a) / (Real.pi * a) *
          ∏ j ∈ Finset.range m, (((j : ℂ) + 1) ^ 2 / (((j : ℂ) + 1) ^ 2 - a ^ 2))) + c * 0) / (c ^ 2 - a ^ 2) =
        Complex.sin (Real.pi * a) / (Real.pi * a) *
          ((∏ j ∈ Finset.range m, (((j : ℂ) + 1) ^ 2 / (((j : ℂ) + 1) ^ 2 - a ^ 2))) * (c ^ 2 / (c ^ 2 - a ^ 2))) := by
      field_simp
      ring
    have key : Filter.Tendsto (fun N : ℕ => hgPartial a (c + 1) N) Filter.atTop
        (nhds (Complex.sin (Real.pi * a) / (Real.pi * a) *
          ((∏ j ∈ Finset.range m, (((j : ℂ) + 1) ^ 2 / (((j : ℂ) + 1) ^ 2 - a ^ 2))) * (c ^ 2 / (c ^ 2 - a ^ 2))))) := by
      rw [← hlim]
      refine h2.congr fun N => ?_
      have hp := hgTerm_partial a c hcn N
      simp only [hgPartial]
      field_simp
      linear_combination (-1 : ℂ) * hp
    rw [Finset.prod_range_succ]
    have e1 : ((m + 1 : ℕ) : ℂ) + 1 = c + 1 := by rw [hc]; push_cast; ring
    have e2 : (((m : ℕ) : ℂ) + 1) = c := hc.symm
    rw [e1, e2]
    exact key

/-- **The recursion on the limit**: `S(c+1) = c² S(c) / (c² − a²)`. -/
lemma tendsto_hgPartial_step {a c L : ℂ} (hcn : ∀ n : ℕ, c + n ≠ 0) (hden : c ^ 2 - a ^ 2 ≠ 0)
    (hN : Filter.Tendsto (fun N : ℕ => (N : ℂ) * hgTerm a c N) Filter.atTop (nhds 0))
    (hL : Filter.Tendsto (fun N : ℕ => hgPartial a c N) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun N : ℕ => hgPartial a (c + 1) N) Filter.atTop (nhds (c ^ 2 * L / (c ^ 2 - a ^ 2))) := by
  have h1 := (hL.const_mul (c ^ 2)).add (hN.const_mul c)
  have h2 := h1.div_const (c ^ 2 - a ^ 2)
  rw [mul_zero, add_zero] at h2
  refine h2.congr fun N => ?_
  have hp := hgTerm_partial a c hcn N
  simp only [hgPartial]
  field_simp
  linear_combination (-1 : ℂ) * hp

/-- The partial-fraction identity `Σ_{n ≤ j} (−1)^n C(j,n)/(s+n) = j! / ∏_{i ≤ j} (s+i)`. -/
lemma alt_binomial_sum : ∀ j : ℕ, ∀ s : ℂ, (∀ i : ℕ, i ≤ j → s + i ≠ 0) →
    ∑ n ∈ Finset.range (j + 1), (-1 : ℂ) ^ n * (j.choose n : ℂ) / (s + n) =
      (j.factorial : ℂ) / ∏ i ∈ Finset.range (j + 1), (s + i) := by
  intro j
  induction j with
  | zero => intro s h; simp
  | succ j ih =>
    intro s hs
    have hs0 : s ≠ 0 := by simpa using hs 0 (Nat.zero_le _)
    have hsj : ∀ i : ℕ, i ≤ j → s + i ≠ 0 := fun i hi => hs i (by omega)
    have hsj1 : ∀ i : ℕ, i ≤ j → (s + 1) + i ≠ 0 := fun i hi => by
      have := hs (i + 1) (by omega)
      push_cast at this
      intro h; apply this; linear_combination h
    have hlast : s + (j + 1 : ℕ) ≠ 0 := hs (j + 1) le_rfl
    have hA := ih s hsj
    have hA1 := ih (s + 1) hsj1
    set h : ℕ → ℂ := fun m => (-1 : ℂ) ^ m * (j.choose m : ℂ) / (s + m) with hh
    have e1 : ∑ n ∈ Finset.range (j + 1 + 1), (-1 : ℂ) ^ n * ((j + 1).choose n : ℂ) / (s + n) =
        1 / s + ∑ n ∈ Finset.range (j + 1), (-1 : ℂ) ^ (n + 1) * ((j + 1).choose (n + 1) : ℂ) / (s + (n + 1 : ℕ)) := by
      rw [Finset.sum_range_succ']
      simp [add_comm]
    have e2 : ∀ n : ℕ, (-1 : ℂ) ^ (n + 1) * ((j + 1).choose (n + 1) : ℂ) / (s + (n + 1 : ℕ)) =
        -( (-1 : ℂ) ^ n * (j.choose n : ℂ) / ((s + 1) + n)) + h (n + 1) := by
      intro n
      rw [Nat.choose_succ_succ]
      simp only [hh]
      push_cast
      have : s + ((n : ℂ) + 1) = (s + 1) + n := by ring
      rw [this]
      ring
    simp only [e2, Finset.sum_add_distrib, Finset.sum_neg_distrib] at e1
    have e3 : ∑ n ∈ Finset.range (j + 1), h (n + 1) = ∑ n ∈ Finset.range (j + 1), h n - 1 / s := by
      have hz : h (j + 1) = 0 := by simp [hh]
      have := Finset.sum_range_succ' h (j + 1)
      rw [Finset.sum_range_succ, hz, add_zero] at this
      have h0 : h 0 = 1 / s := by simp [hh]
      rw [h0] at this
      linear_combination -this
    rw [e1, e3]
    -- products
    have hp1 : ∏ i ∈ Finset.range (j + 1 + 1), (s + (i : ℂ)) = (∏ i ∈ Finset.range (j + 1), (s + (i : ℂ))) * (s + (j + 1 : ℕ)) :=
      Finset.prod_range_succ _ _
    have hp2 : ∏ i ∈ Finset.range (j + 1 + 1), (s + (i : ℂ)) = s * ∏ i ∈ Finset.range (j + 1), ((s + 1) + (i : ℂ)) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, add_zero]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      push_cast; ring
    have hP0 : ∏ i ∈ Finset.range (j + 1), (s + (i : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hsj i (by simpa [Nat.lt_succ_iff] using hi)
    have hP1 : ∏ i ∈ Finset.range (j + 1), ((s + 1) + (i : ℂ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hsj1 i (by simpa [Nat.lt_succ_iff] using hi)
    have hP1' : ∏ i ∈ Finset.range (j + 1), ((s + 1) + (i : ℂ)) =
        (∏ i ∈ Finset.range (j + 1), (s + (i : ℂ))) * (s + (j + 1 : ℕ)) / s := by
      field_simp
      rw [← hp2, hp1]
    rw [hA, hA1, hP1', hp1]
    push_cast at hlast ⊢
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- For `a = j` and `c = j + 1` the terms are `(−1)^n C(j,n) j / (j + n)`: a terminating series. -/
lemma hgTerm_int (j : ℕ) (hj : 1 ≤ j) : ∀ n : ℕ,
    hgTerm (j : ℂ) ((j : ℂ) + 1) n = (-1 : ℂ) ^ n * (j.choose n : ℂ) * j / ((j : ℂ) + n) := by
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  intro n
  induction n with
  | zero => simp [hgTerm, hj0]
  | succ n ih =>
    have hjpos : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hjn : (j : ℂ) + n ≠ 0 := by
      have : (0 : ℝ) < j + n := by positivity
      exact_mod_cast this.ne'
    have hjn1 : (j : ℂ) + (n + 1 : ℕ) ≠ 0 := by
      have : (0 : ℝ) < j + (n + 1 : ℕ) := by positivity
      exact_mod_cast this.ne'
    have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hjn2 : (j : ℂ) + 1 + n ≠ 0 := by
      have : (0 : ℝ) < j + 1 + n := by positivity
      exact_mod_cast this.ne'
    rw [hgTerm, ih]
    rcases le_or_gt n j with hn | hn
    · have hch : ((j.choose (n + 1) : ℕ) : ℂ) * ((n : ℂ) + 1) = (j.choose n : ℂ) * ((j : ℂ) - n) := by
        have := Nat.choose_succ_right_eq j n
        have h2 : ((j.choose (n + 1) * (n + 1) : ℕ) : ℂ) = ((j.choose n * (j - n) : ℕ) : ℂ) := by rw [this]
        push_cast [Nat.cast_sub hn] at h2
        exact h2
      push_cast at hjn1 ⊢
      field_simp
      have : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by ring
      rw [this]
      linear_combination ((-1 : ℂ) ^ n * ((j : ℂ) + n) * ((j : ℂ) + n + 1)) * hch
    · have h0 : (j.choose n : ℂ) = 0 := by rw [Nat.choose_eq_zero_of_lt hn]; simp
      have h1 : (j.choose (n + 1) : ℂ) = 0 := by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
      simp [h0, h1]

/-- For `a = j ≥ 1` the partial sums at `c = j + 1` are eventually constant and non-zero. -/
lemma tendsto_hgPartial_int_base (j : ℕ) (hj : 1 ≤ j) :
    ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto (fun N : ℕ => hgPartial (j : ℂ) ((j : ℂ) + 1) N) Filter.atTop (nhds L) := by
  have hjpos : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hs : ∀ i : ℕ, i ≤ j → (j : ℂ) + i ≠ 0 := fun i _ => by
    have : (0 : ℝ) < j + i := by positivity
    exact_mod_cast this.ne'
  have hpf := alt_binomial_sum j (j : ℂ) hs
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  refine ⟨(j : ℂ) * ((j.factorial : ℂ) / ∏ i ∈ Finset.range (j + 1), ((j : ℂ) + i)), ?_, ?_⟩
  · refine mul_ne_zero hj0 (div_ne_zero (by exact_mod_cast (Nat.factorial_pos j).ne') ?_)
    exact Finset.prod_ne_zero_iff.mpr fun i hi => hs i (by simpa [Nat.lt_succ_iff] using hi)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (j + 1)] with N hN
    unfold hgPartial
    have hsplit : ∑ n ∈ Finset.range N, hgTerm (j : ℂ) ((j : ℂ) + 1) n =
        ∑ n ∈ Finset.range (j + 1), hgTerm (j : ℂ) ((j : ℂ) + 1) n := by
      symm
      apply Finset.sum_subset
      · intro n hn; simp only [Finset.mem_range] at hn ⊢; omega
      · intro n _ hn
        simp only [Finset.mem_range, not_lt] at hn
        rw [hgTerm_int j hj, Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [hsplit, ← hpf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hgTerm_int j hj]
    ring

/-- **The integer case `1 ≤ |a| ≤ m`**: the value at infinity is non-zero. -/
theorem tendsto_hgPartial_int (j m : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    ∃ L : ℂ, L ≠ 0 ∧ Filter.Tendsto (fun N : ℕ => hgPartial (j : ℂ) ((m : ℂ) + 1) N) Filter.atTop (nhds L) := by
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  induction m, hjm using Nat.le_induction with
  | base => exact tendsto_hgPartial_int_base j hj
  | succ m hjm ih =>
    obtain ⟨L, hL0, hL⟩ := ih
    have hcn : ∀ n : ℕ, ((m : ℂ) + 1) + n ≠ 0 := fun n => by
      have : (0 : ℝ) < m + 1 + n := by positivity
      exact_mod_cast this.ne'
    have hden : ((m : ℂ) + 1) ^ 2 - (j : ℂ) ^ 2 ≠ 0 := by
      have : ((m : ℝ) + 1) ^ 2 - (j : ℝ) ^ 2 ≠ 0 := by
        have : (j : ℝ) < (m : ℝ) + 1 := by exact_mod_cast Nat.lt_succ_of_le hjm
        have h2 : (0 : ℝ) < j := by exact_mod_cast hj
        nlinarith
      exact_mod_cast this
    refine ⟨((m : ℂ) + 1) ^ 2 * L / (((m : ℂ) + 1) ^ 2 - (j : ℂ) ^ 2), ?_, ?_⟩
    · have hm1 : ((m : ℂ) + 1) ≠ 0 := by simpa using hcn 0
      exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 hm1) hL0) hden
    · have := tendsto_hgPartial_step hcn hden (tendsto_mul_hgTerm hj0 m) hL
      push_cast
      exact this

/-- The terms depend on `a` only through `a²`. -/
lemma hgTerm_neg (a c : ℂ) (n : ℕ) : hgTerm (-a) c n = hgTerm a c n := by
  induction n with
  | zero => simp [hgTerm]
  | succ n ih => simp only [hgTerm, ih]; ring

/-- For `a = 0` the series is `1 + 0 + 0 + ⋯`. -/
lemma hgPartial_zero (c : ℂ) (N : ℕ) (hN : 1 ≤ N) : hgPartial 0 c N = 1 := by
  have h : ∀ n : ℕ, hgTerm 0 c (n + 1) = 0 := by
    intro n
    induction n with
    | zero => simp [hgTerm]
    | succ n ih => rw [hgTerm, ih]; simp
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  unfold hgPartial
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun n _ => h n]
  simp [hgTerm]

/-- **Classification of the value at infinity.** The partial sums of `₂F₁(a, −a; m+1; 1)` converge, and the limit
vanishes exactly when `a = ±k` for an integer `k ≥ m + 1`. -/
theorem hgPartial_limit (a : ℂ) (m : ℕ) :
    ∃ L : ℂ, Filter.Tendsto (fun N : ℕ => hgPartial a ((m : ℂ) + 1) N) Filter.atTop (nhds L) ∧
      (L = 0 ↔ ∃ k : ℕ, m + 1 ≤ k ∧ (a = k ∨ a = -(k : ℂ))) := by
  by_cases ha : a = 0
  · subst ha
    refine ⟨1, ?_, ?_⟩
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      exact (hgPartial_zero _ N hN).symm
    · constructor
      · intro h; exact absurd h one_ne_zero
      · rintro ⟨k, hk, hk0 | hk0⟩
        · have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
          exact absurd hk0.symm this
        · have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
          exact absurd (neg_eq_zero.mp hk0.symm) this
  by_cases hint : ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧ (a = j ∨ a = -(j : ℂ))
  · obtain ⟨j, hj, hjm, hja⟩ := hint
    have hsq : a ^ 2 = (j : ℂ) ^ 2 := by rcases hja with h | h <;> rw [h] <;> ring
    -- the terms depend on a² only
    have hterm : ∀ n, hgTerm a ((m : ℂ) + 1) n = hgTerm (j : ℂ) ((m : ℂ) + 1) n := by
      rcases hja with h | h
      · intro n; rw [h]
      · intro n; rw [h, hgTerm_neg]
    obtain ⟨L, hL0, hL⟩ := tendsto_hgPartial_int j m hj hjm
    refine ⟨L, ?_, ?_⟩
    · refine hL.congr fun N => ?_
      unfold hgPartial; exact Finset.sum_congr rfl fun n _ => (hterm n).symm
    · constructor
      · intro h; exact absurd h hL0
      · rintro ⟨k, hk, hk0⟩
        exfalso
        have : (k : ℂ) ^ 2 = (j : ℂ) ^ 2 := by rcases hk0 with h | h <;> rw [← hsq, h] <;> ring
        have : (k : ℕ) ^ 2 = j ^ 2 := by exact_mod_cast this
        nlinarith
  · push_neg at hint
    have hne : ∀ j < m, ((j : ℂ) + 1) ^ 2 ≠ a ^ 2 := by
      intro j hj h
      have := hint (j + 1) (by omega) (by omega)
      have h2 : a = ((j : ℂ) + 1) ∨ a = -((j : ℂ) + 1) := by
        have : (a - ((j : ℂ) + 1)) * (a + ((j : ℂ) + 1)) = 0 := by linear_combination -h
        rcases mul_eq_zero.mp this with h1 | h1
        · left; linear_combination h1
        · right; linear_combination h1
      rcases h2 with h2 | h2
      · exact this.1 (by rw [h2]; push_cast; ring)
      · exact this.2 (by rw [h2]; push_cast; ring)
    refine ⟨_, tendsto_hgPartial ha m hne, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hprod : ∏ j ∈ Finset.range m, (((j : ℂ) + 1) ^ 2 / (((j : ℂ) + 1) ^ 2 - a ^ 2)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have hj' : j < m := Finset.mem_range.mp hj
      have h1 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      exact div_ne_zero (pow_ne_zero 2 h1) (sub_ne_zero.mpr (hne j hj'))
    constructor
    · intro h
      have h1 : Complex.sin (Real.pi * a) / (Real.pi * a) = 0 := (mul_eq_zero.mp h).resolve_right hprod
      have h2 : Complex.sin (Real.pi * a) = 0 := by
        rcases div_eq_zero_iff.mp h1 with h | h
        · exact h
        · exact absurd h (mul_ne_zero hpi ha)
      obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h2
      have hak : a = (k : ℂ) := by
        have : (Real.pi : ℂ) * a = (Real.pi : ℂ) * k := by rw [hk]; ring
        exact mul_left_cancel₀ hpi this
      have hk0 : k ≠ 0 := by rintro rfl; simp at hak; exact ha hak
      have hcast : (k : ℂ) = (k.natAbs : ℂ) ∨ (k : ℂ) = -(k.natAbs : ℂ) := by
        rcases Int.natAbs_eq k with h | h
        · left; have := congrArg (Int.cast (R := ℂ)) h; simp only [Int.cast_natCast] at this; exact this
        · right; have := congrArg (Int.cast (R := ℂ)) h; simp only [Int.cast_neg, Int.cast_natCast] at this; exact this
      refine ⟨k.natAbs, ?_, ?_⟩
      · by_contra hlt
        push_neg at hlt
        have := hint k.natAbs (by omega) (by omega)
        rcases hcast with h | h
        · exact this.1 (hak.trans h)
        · exact this.2 (hak.trans h)
      · rcases hcast with h | h
        · left; exact hak.trans h
        · right; exact hak.trans h
    · rintro ⟨k, hk, hk0⟩
      have : Complex.sin (Real.pi * a) = 0 := by
        rcases hk0 with h | h
        · rw [h, mul_comm]; exact Complex.sin_nat_mul_pi k
        · rw [h, mul_neg, Complex.sin_neg, mul_comm]; simp [Complex.sin_nat_mul_pi k]
      rw [this]; simp

end Lightlike.Dirac
