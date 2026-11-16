import Lightlike.Regge.Conv3.StarAngle

/-!
# Closed fans, and pinning the multiple of `2π`

Three elementary lemmas used to show that the dihedral angles around an edge of a flat star, whose
vertices are displaced consistently, still add up to `2π`.

* `closed_fan_sum`: the arguments of the consecutive products `conj z_i * z_{i+1}` of a positively
  oriented closed polygon of nonzero complex numbers add up to `2π k` with `0 < k` and `2 k < n`.
  (Mathlib: `Complex.arg_mul_coe_angle` for the sum modulo `2π`, `Complex.arg_lt_pi_iff` and
  `Complex.arg_nonneg_iff` for `0 < arg < π`.)
* `eventually_eq_of_int_mul`: a function that is continuous at `0`, equal to `2π` at `0` and
  eventually a multiple of `2π`, is eventually `2π`.
* `coeffs_zero_of_expansion`: if `F ε = 2π` for small `ε > 0` and
  `|F ε - 2π - a ε - b ε²| ≤ M ε³`, then `a = b = 0`.

**Limits.** The closed fan is a statement about complex numbers; it does not say that vectors in
space form a fan. That is done for the Kuhn star in `StarAngle.lean` (lattice case) and in the
chart-change files (displaced vertices). The lemmas are classical (winding number of a closed
polygon, discreteness of `2πℤ`, uniqueness of a vanishing asymptotic expansion); the catalogue label
is `structural`.
-/

open Complex Real Filter Topology
namespace Lightlike.Regge.Conv3

/-- **A closed fan.** If the vectors `z 0, …, z n` of the plane quotient are nonzero, consecutive
ones are positively oriented (`Im (conj z_i z_{i+1}) > 0`) and the fan closes (`z n = z 0`), then the
angles `arg (conj z_i z_{i+1})` add up to `2π k` with `0 < k` and `2 k < n`. -/
theorem closed_fan_sum {n : ℕ} (hn : 0 < n) (z : ℕ → ℂ) (hz : ∀ i ≤ n, z i ≠ 0)
    (him : ∀ i < n, 0 < (starRingEnd ℂ (z i) * z (i + 1)).im) (hc : z n = z 0) :
    ∃ k : ℤ, ∑ i ∈ Finset.range n, arg (starRingEnd ℂ (z i) * z (i + 1)) = 2 * π * k
      ∧ 0 < k ∧ 2 * k < n := by
  obtain ⟨k, hk⟩ := fan_angle z hz him
  have h0 : starRingEnd ℂ (z 0) * z n = ((Complex.normSq (z 0) : ℝ) : ℂ) := by
    rw [hc, Complex.normSq_eq_conj_mul_self]
  rw [h0, Complex.arg_ofReal_of_nonneg (Complex.normSq_nonneg _), zero_add] at hk
  have hb : ∀ i ∈ Finset.range n, 0 < arg (starRingEnd ℂ (z i) * z (i + 1)) ∧
      arg (starRingEnd ℂ (z i) * z (i + 1)) < π := fun i hi =>
    arg_pos_of_im (him i (Finset.mem_range.1 hi))
  have hpos : 0 < ∑ i ∈ Finset.range n, arg (starRingEnd ℂ (z i) * z (i + 1)) :=
    Finset.sum_pos (fun i hi => (hb i hi).1) ⟨0, Finset.mem_range.2 hn⟩
  have hlt : ∑ i ∈ Finset.range n, arg (starRingEnd ℂ (z i) * z (i + 1)) < n * π := by
    calc _ < ∑ i ∈ Finset.range n, π := Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 hn⟩
          (fun i hi => (hb i hi).2)
      _ = n * π := by simp
  have hpi := Real.pi_pos
  refine ⟨k, hk, ?_, ?_⟩
  · have : (0 : ℝ) < k := by nlinarith
    exact_mod_cast this
  · have : (2 * k : ℝ) < n := by nlinarith
    exact_mod_cast this

/-- **Pinning the multiple.** A function that is continuous at `0`, equals `2π` there, and is
eventually a multiple of `2π`, is eventually equal to `2π`. -/
theorem eventually_eq_of_int_mul {S : ℝ → ℝ} (hS : ContinuousAt S 0) (h0 : S 0 = 2 * π)
    (hint : ∀ᶠ ε in 𝓝 (0 : ℝ), ∃ k : ℤ, S ε = 2 * π * k) : ∀ᶠ ε in 𝓝 (0 : ℝ), S ε = 2 * π := by
  have hpi := Real.pi_pos
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), |S ε - 2 * π| < π := by
    have := hS.eventually (Metric.ball_mem_nhds (S 0) hpi)
    filter_upwards [this] with ε hε
    rw [h0] at hε
    simpa [Metric.mem_ball, Real.dist_eq] using hε
  filter_upwards [hint, hnear] with ε ⟨k, hk⟩ hε
  rw [hk] at hε ⊢
  have h1 : |2 * π * ((k : ℝ) - 1)| < π := by
    have : 2 * π * k - 2 * π = 2 * π * ((k : ℝ) - 1) := by ring
    rwa [this] at hε
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h1
  have h2 : |(k : ℝ) - 1| < 1 / 2 := by
    by_contra h; push_neg at h; nlinarith
  have h3 : k = 1 := by
    have : |((k - 1 : ℤ) : ℝ)| < 1 := by push_cast; linarith
    have := Int.abs_lt_one_iff.1 (by exact_mod_cast this)
    omega
  subst h3; simp

/-- **Coefficients of a vanishing expansion.** If `F ε = 2π` for all small `ε > 0` and
`|F ε - 2π - a ε - b ε²| ≤ M ε³` for `0 < ε ≤ r`, then `a = 0` and `b = 0`. -/
theorem coeffs_zero_of_expansion {F : ℝ → ℝ} {a b M r : ℝ} (hr : 0 < r)
    (hF : ∀ ε, 0 < ε → ε ≤ r → F ε = 2 * π)
    (hexp : ∀ ε, 0 < ε → ε ≤ r → |F ε - 2 * π - a * ε - b * ε ^ 2| ≤ M * ε ^ 3) :
    a = 0 ∧ b = 0 := by
  have key : ∀ ε, 0 < ε → ε ≤ r → |a * ε + b * ε ^ 2| ≤ M * ε ^ 3 := by
    intro ε h1 h2
    have := hexp ε h1 h2
    rw [hF ε h1 h2] at this
    have e : 2 * π - 2 * π - a * ε - b * ε ^ 2 = -(a * ε + b * ε ^ 2) := by ring
    rwa [e, abs_neg] at this
  have ha : a = 0 := by
    by_contra ha
    have hA : 0 < |a| := abs_pos.2 ha
    set C := |b| + |M| + 1 with hC
    have hCpos : 0 < C := by positivity
    set ε := min (min r 1) (|a| / (2 * C)) with hε
    have hεpos : 0 < ε := lt_min (lt_min hr one_pos) (by positivity)
    have hεr : ε ≤ r := (min_le_left _ _).trans (min_le_left _ _)
    have hε1 : ε ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
    have hεa : ε ≤ |a| / (2 * C) := min_le_right _ _
    have h := key ε hεpos hεr
    have h2 : |a * ε| ≤ |b * ε ^ 2| + |M * ε ^ 3| := by
      have e : a * ε = (a * ε + b * ε ^ 2) - b * ε ^ 2 := by ring
      calc |a * ε| = |(a * ε + b * ε ^ 2) - b * ε ^ 2| := by rw [← e]
        _ ≤ |a * ε + b * ε ^ 2| + |b * ε ^ 2| := abs_sub _ _
        _ ≤ |M * ε ^ 3| + |b * ε ^ 2| := by
          exact add_le_add_left (h.trans (le_abs_self _)) _
        _ = |b * ε ^ 2| + |M * ε ^ 3| := add_comm _ _
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hεpos, abs_pow, abs_of_pos hεpos, abs_pow,
      abs_of_pos hεpos] at h2
    have h4 : |a| ≤ |b| * ε + |M| * ε ^ 2 := by
      have : |a| * ε ≤ (|b| * ε + |M| * ε ^ 2) * ε := by nlinarith
      exact le_of_mul_le_mul_right this hεpos
    have h5 : |a| ≤ C * ε := by nlinarith [abs_nonneg b, abs_nonneg M, mul_nonneg (abs_nonneg M) hεpos.le]
    have h6 : C * ε ≤ |a| / 2 := by
      calc C * ε ≤ C * (|a| / (2 * C)) := by gcongr
        _ = |a| / 2 := by field_simp
    linarith
  subst ha
  refine ⟨rfl, ?_⟩
  by_contra hb
  have hB : 0 < |b| := abs_pos.2 hb
  set C := |M| + 1 with hC
  have hCpos : 0 < C := by positivity
  set ε := min (min r 1) (|b| / (2 * C)) with hε
  have hεpos : 0 < ε := lt_min (lt_min hr one_pos) (by positivity)
  have hεr : ε ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hεb : ε ≤ |b| / (2 * C) := min_le_right _ _
  have h := key ε hεpos hεr
  simp only [zero_mul, zero_add] at h
  rw [abs_mul, abs_pow, abs_of_pos hεpos] at h
  have h4 : |b| * ε ^ 2 ≤ |M| * ε ^ 3 := by
    have := le_abs_self M
    calc |b| * ε ^ 2 ≤ M * ε ^ 3 := h
      _ ≤ |M| * ε ^ 3 := by gcongr
  have h5 : |b| ≤ |M| * ε := by
    have : |b| * ε ^ 2 ≤ (|M| * ε) * ε ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  have h6 : |M| * ε ≤ |b| / 2 := by
    calc |M| * ε ≤ C * ε := by gcongr; linarith [hC]
      _ ≤ C * (|b| / (2 * C)) := by gcongr
      _ = |b| / 2 := by field_simp
  linarith

end Lightlike.Regge.Conv3
