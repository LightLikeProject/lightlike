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

end Lightlike.Dirac
