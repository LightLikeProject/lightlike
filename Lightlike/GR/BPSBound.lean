import Mathlib

/-!
# The BPS bound of the extended supersymmetry algebra

In a unitary representation of the `N = 2` supersymmetry algebra in the rest frame,
`{Q^I_α, (Q^J_β)†} = 2m δ_αβ δ^IJ` and `{Q^I_α, Q^J_β} = ε_αβ Z^IJ`, the mass and the central
charge satisfy `2m ≥ |Z|` (`bps_bound_restFrame`): the operator `a = Q¹₁ + c (Q²₂)†` with a phase
`c` has `a a† + a† a = (4m − 2|Z|) · 1`, and `⟪x, (a a† + a† a) x⟫ = ‖a† x‖² + ‖a x‖² ≥ 0`. At
saturation `2m = |Z|` the operator `a` vanishes (`bps_saturated`): the multiplet is short.

The operators are bounded operators on a Hilbert space, with `star` the adjoint; the unbounded
supercharges of a field theory are not covered.

## Main results

* `re_inner_anticomm_self`: `re ⟪x, (T T† + T† T) x⟫ = ‖T† x‖² + ‖T x‖²`.
* `anticomm_phase`: the anticommutator of `A + c B†` with its adjoint.
* `bps_bound`, `bps_saturated`: `|w| ≤ 2m` for `{A, A†} = {B, B†} = 2m`, `{A, B} = w`, and
  `A + c B† = 0` at saturation.
* `bps_bound_restFrame`: Bilal's bound (3.16) for the rest-frame algebra (3.12) with `N = 2`.

## References

* A. Bilal, *Introduction to supersymmetry*, arXiv:hep-th/0101055v1: the algebra (3.2)–(3.3),
  p. 9–10; the rest frame (3.12), the oscillators (3.14)–(3.15) and the bound `2m ≥ |q_n|` (3.16),
  pp. 13–14; at saturation "the corresponding operators must be set to zero", p. 14. Difference:
  Bilal brings `Z` to the real standard form (3.13) by a `U(N)` rotation; here the rotation is the
  phase `c`, and the bound is stated for the modulus of the complex central charge.
-/

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Lightlike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `re ⟪x, (T T† + T† T) x⟫ = ‖T† x‖² + ‖T x‖²` for a bounded operator `T`. -/
lemma re_inner_anticomm_self (T : E →L[ℂ] E) (x : E) :
    RCLike.re ⟪x, (T * star T + star T * T) x⟫_ℂ = ‖star T x‖ ^ 2 + ‖T x‖ ^ 2 := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  change RCLike.re ⟪x, T (ContinuousLinearMap.adjoint T x) +
    ContinuousLinearMap.adjoint T (T x)⟫_ℂ = _
  rw [inner_add_right, map_add,
    ← ContinuousLinearMap.adjoint_inner_left T (ContinuousLinearMap.adjoint T x) x,
    ContinuousLinearMap.adjoint_inner_right T x (T x), inner_self_eq_norm_sq, inner_self_eq_norm_sq]

/-- The anticommutator of `a = A + c B†` with its adjoint, for `{A, A†} = {B, B†} = s` and
`{A, B} = w`. -/
lemma anticomm_phase (A B : E →L[ℂ] E) (s w c : ℂ) (hA : A * star A + star A * A = s • 1)
    (hB : B * star B + star B * B = s • 1) (hAB : A * B + B * A = w • 1) :
    (A + c • star B) * star (A + c • star B) + star (A + c • star B) * (A + c • star B) =
      (s + star c * w + c * star w + c * star c * s) • 1 := by
  have hBA : star B * star A + star A * star B = star w • 1 := by
    have := congrArg star hAB
    rw [star_add, star_mul, star_mul, star_smul, star_one] at this
    exact this
  have e : (A + c • star B) * star (A + c • star B) + star (A + c • star B) * (A + c • star B) =
      (A * star A + star A * A) + star c • (A * B + B * A) +
        c • (star B * star A + star A * star B) + (c * star c) • (B * star B + star B * B) := by
    simp only [star_add, star_smul, star_star, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_add]
    rw [mul_comm (star c) c]
    abel
  rw [e, hA, hB, hAB, hBA, smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul, ← add_smul]

/-- A phase turning the central charge to the negative real axis: `‖c‖ = 1`, `c̄ w = −|w|`. -/
lemma exists_phase (w : ℂ) : ∃ c : ℂ, ‖c‖ = 1 ∧ star c * w = -(‖w‖ : ℂ) := by
  by_cases hw : w = 0
  · exact ⟨1, by simp, by simp [hw]⟩
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  refine ⟨-(w / ‖w‖), ?_, ?_⟩
  · rw [norm_neg, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hw)]
  · rw [star_neg, star_div₀, Complex.star_def, Complex.conj_ofReal, neg_mul, div_mul_eq_mul_div,
      Complex.conj_mul', sq, mul_div_assoc, div_self hn, mul_one]

/-- The anticommutator `a a† + a† a` for the phase of `exists_phase`: `(4m − 2|w|) · 1`. -/
lemma anticomm_phase_eq (A B : E →L[ℂ] E) (m : ℝ) (w c : ℂ) (hc : ‖c‖ = 1)
    (hcw : star c * w = -(‖w‖ : ℂ))
    (hA : A * star A + star A * A = ((2 * m : ℝ) : ℂ) • 1)
    (hB : B * star B + star B * B = ((2 * m : ℝ) : ℂ) • 1) (hAB : A * B + B * A = w • 1) :
    (A + c • star B) * star (A + c • star B) + star (A + c • star B) * (A + c • star B) =
      ((4 * m - 2 * ‖w‖ : ℝ) : ℂ) • 1 := by
  rw [anticomm_phase A B _ w c hA hB hAB]
  congr 1
  have h1 : c * star w = -(‖w‖ : ℂ) := by
    have := congrArg star hcw
    rw [star_mul, star_star, star_neg, Complex.star_def, Complex.conj_ofReal, mul_comm] at this
    exact this
  have h2 : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj', hc]; simp
  rw [hcw, h1, h2]
  push_cast
  ring

/-- **The BPS bound**: if `{A, A†} = {B, B†} = 2m` and `{A, B} = w` on a nonzero Hilbert space,
then `|w| ≤ 2m`. -/
theorem bps_bound [Nontrivial E] (A B : E →L[ℂ] E) (m : ℝ) (w : ℂ)
    (hA : A * star A + star A * A = ((2 * m : ℝ) : ℂ) • 1)
    (hB : B * star B + star B * B = ((2 * m : ℝ) : ℂ) • 1) (hAB : A * B + B * A = w • 1) :
    ‖w‖ ≤ 2 * m := by
  obtain ⟨c, hc, hcw⟩ := exists_phase w
  have e := anticomm_phase_eq A B m w c hc hcw hA hB hAB
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have h := re_inner_anticomm_self (A + c • star B) x
  rw [e] at h
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have h3 : RCLike.re ⟪x, (((4 * m - 2 * ‖w‖ : ℝ) : ℂ) • (1 : E →L[ℂ] E)) x⟫_ℂ =
      (4 * m - 2 * ‖w‖) * ‖x‖ ^ 2 := by
    have hs : (((4 * m - 2 * ‖w‖ : ℝ) : ℂ) • (1 : E →L[ℂ] E)) x =
        ((4 * m - 2 * ‖w‖ : ℝ) : ℂ) • x := by simp
    rw [hs, inner_smul_right, inner_self_eq_norm_sq_to_K]
    show Complex.re (((4 * m - 2 * ‖w‖ : ℝ) : ℂ) * ((‖x‖ : ℝ) : ℂ) ^ 2) = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h3] at h
  have h4 : 0 ≤ (4 * m - 2 * ‖w‖) * ‖x‖ ^ 2 := by rw [h]; positivity
  have h5 : 0 ≤ 4 * m - 2 * ‖w‖ := nonneg_of_mul_nonneg_left h4 hx2
  linarith

/-- **Saturation shortens the multiplet**: if moreover `|w| = 2m`, then `A + c B† = 0` for a phase
`c`. -/
theorem bps_saturated (A B : E →L[ℂ] E) (m : ℝ) (w : ℂ)
    (hA : A * star A + star A * A = ((2 * m : ℝ) : ℂ) • 1)
    (hB : B * star B + star B * B = ((2 * m : ℝ) : ℂ) • 1) (hAB : A * B + B * A = w • 1)
    (hsat : ‖w‖ = 2 * m) : ∃ c : ℂ, ‖c‖ = 1 ∧ A + c • star B = 0 := by
  obtain ⟨c, hc, hcw⟩ := exists_phase w
  refine ⟨c, hc, ContinuousLinearMap.ext fun x => ?_⟩
  have e := anticomm_phase_eq A B m w c hc hcw hA hB hAB
  have h := re_inner_anticomm_self (A + c • star B) x
  rw [e, show (4 * m - 2 * ‖w‖ : ℝ) = 0 by rw [hsat]; ring] at h
  have hz : (((0 : ℝ) : ℂ) • (1 : E →L[ℂ] E)) x = 0 := by simp
  rw [hz, inner_zero_right, map_zero] at h
  have h0 : ‖(A + c • star B) x‖ ^ 2 = 0 := by
    have := sq_nonneg ‖star (A + c • star B) x‖
    have := sq_nonneg ‖(A + c • star B) x‖
    linarith
  rw [show (0 : E →L[ℂ] E) x = 0 from rfl]
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)

/-- **Bilal's bound (3.16) for `N = 2`**: in a unitary representation of the rest-frame algebra
(3.12), `{Q^I_α, (Q^I_α)†} = 2m` and `{Q¹₁, Q²₂} = ε₁₂ Z` with `|ε₁₂| = 1`, on a nonzero Hilbert
space, `|Z| ≤ 2m`. -/
theorem bps_bound_restFrame [Nontrivial E] (Q : Fin 2 → Fin 2 → (E →L[ℂ] E)) (m : ℝ) (Z ε₁₂ : ℂ)
    (hε : ‖ε₁₂‖ = 1)
    (hQ : ∀ I α, Q I α * star (Q I α) + star (Q I α) * Q I α = ((2 * m : ℝ) : ℂ) • 1)
    (hZ : Q 0 0 * Q 1 1 + Q 1 1 * Q 0 0 = (ε₁₂ * Z) • 1) : ‖Z‖ ≤ 2 * m := by
  have := bps_bound (Q 0 0) (Q 1 1) m (ε₁₂ * Z) (hQ 0 0) (hQ 1 1) hZ
  rwa [norm_mul, hε, one_mul] at this

/-! ### Trust checks: the hypotheses are satisfiable, and the bound is attained

On `E = ℂ`, `A = B = 1` has `{A, A†} = {B, B†} = 2` and `{A, B} = 2`: `m = 1`, `|w| = 2 = 2m`, and
`A − B† = 0`. -/

example : ‖(2 : ℂ)‖ ≤ 2 * 1 := by
  refine bps_bound (E := ℂ) 1 1 1 2 ?_ ?_ ?_ <;> simp [two_smul]

example : ∃ c : ℂ, ‖c‖ = 1 ∧ (1 : ℂ →L[ℂ] ℂ) + c • star (1 : ℂ →L[ℂ] ℂ) = 0 := by
  refine bps_saturated (E := ℂ) 1 1 1 2 ?_ ?_ ?_ ?_ <;> simp [two_smul]

end Lightlike
