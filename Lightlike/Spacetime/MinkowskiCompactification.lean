import Mathlib

/-!
# Minkowski space is conformal to a region of the Einstein static universe (G1-016)

In the coordinates `η = U + V`, `χ = U - V` with `U = arctan u`, `V = arctan v`, `u = (t + r)/2`, `v = (t - r)/2`, the
Minkowski metric `-dt² + dr² + r² dΩ²` is `ω⁻² (-dη² + dχ² + sin² χ dΩ²)` with `ω = (cos η + cos χ)/2`: Minkowski space
is conformal to the region `0 < χ`, `|η| + χ < π` of the Einstein static universe `-dη² + dχ² + sin² χ dΩ²` on
`ℝ × S³`.

* `compT`, `compR`, `compOmega`: `t = sin η / ω`, `r = sin χ / ω`, `ω = (cos η + cos χ)/2 = cos U cos V`
  (`compOmega_eq_cos_mul_cos`), positive on the region (`compOmega_pos`); `t = tan U + tan V`, `r = tan U - tan V`
  (`compT_eq_tan_add`, `compR_eq_tan_sub`);
* `hasDerivAt_compT_eta`, `hasDerivAt_compT_chi`, `hasDerivAt_compR_eta`, `hasDerivAt_compR_chi`: the Jacobian
  `(2ω²)⁻¹ [[1 + cos η cos χ, sin η sin χ], [sin η sin χ, 1 + cos η cos χ]]`, and `sq_sub_sq_compDeriv`: its entries
  satisfy `A² - B² = ω⁻²`;
* `minkowski_eq_conformal_esu`: the Minkowski metric on the image of a tangent vector `a ∂_η + b ∂_χ + w` (`w` tangent to
  the sphere, `q = dΩ²(w, w)`) is `ω⁻² (-a² + b² + sin² χ q)`;
* `bijOn_comp`: `(η, χ) ↦ (t, r)` maps `compRegion` bijectively onto the half-plane `r > 0`.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 7, eqs. (7.86)–(7.102),
  pp. 192–195: the null coordinates (7.88), `U = arctan u`, `V = arctan v` (7.91) with the ranges (7.92), the metric
  (7.97), `η = U + V`, `χ = U - V` (7.98) with the ranges (7.99), and `ds² = ω⁻² (-dη² + dχ² + sin² χ dΩ²)` (7.100),
  `ω = cos U cos V = ½ (cos η + cos χ)` (7.101), the Einstein static universe (7.102).
-/

noncomputable section

namespace Lightlike

open Real

/-- The conformal factor `ω = (cos η + cos χ)/2`. -/
def compOmega (η χ : ℝ) : ℝ := (cos η + cos χ) / 2

/-- The Minkowski time `t = sin η / ω`. -/
def compT (η χ : ℝ) : ℝ := sin η / compOmega η χ

/-- The Minkowski radius `r = sin χ / ω`. -/
def compR (η χ : ℝ) : ℝ := sin χ / compOmega η χ

section Derivatives

variable {η χ : ℝ} (hω : compOmega η χ ≠ 0)
include hω

/-- `∂_η t = (1 + cos η cos χ) / (2ω²)`. -/
theorem hasDerivAt_compT_eta :
    HasDerivAt (fun e => compT e χ) ((1 + cos η * cos χ) / (2 * compOmega η χ ^ 2)) η := by
  have h := (hasDerivAt_sin η).div (((hasDerivAt_cos η).add_const (cos χ)).div_const 2) hω
  refine h.congr_deriv ?_
  unfold compOmega at hω ⊢
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (((cos η + cos χ) / 2) ^ 2) * sin_sq_add_cos_sq η

/-- `∂_χ t = sin η sin χ / (2ω²)`. -/
theorem hasDerivAt_compT_chi :
    HasDerivAt (fun c => compT η c) (sin η * sin χ / (2 * compOmega η χ ^ 2)) χ := by
  have h := (hasDerivAt_const χ (sin η)).div (((hasDerivAt_cos χ).const_add (cos η)).div_const 2) hω
  refine h.congr_deriv ?_
  unfold compOmega at hω ⊢
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `∂_η r = sin η sin χ / (2ω²)`. -/
theorem hasDerivAt_compR_eta :
    HasDerivAt (fun e => compR e χ) (sin η * sin χ / (2 * compOmega η χ ^ 2)) η := by
  have h := (hasDerivAt_const η (sin χ)).div (((hasDerivAt_cos η).add_const (cos χ)).div_const 2) hω
  refine h.congr_deriv ?_
  unfold compOmega at hω ⊢
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- `∂_χ r = (1 + cos η cos χ) / (2ω²)`. -/
theorem hasDerivAt_compR_chi :
    HasDerivAt (fun c => compR η c) ((1 + cos η * cos χ) / (2 * compOmega η χ ^ 2)) χ := by
  have h := (hasDerivAt_sin χ).div (((hasDerivAt_cos χ).const_add (cos η)).div_const 2) hω
  refine h.congr_deriv ?_
  unfold compOmega at hω ⊢
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (((cos η + cos χ) / 2) ^ 2) * sin_sq_add_cos_sq χ

/-- The identity behind the conformal factor: `A² - B² = ω⁻²` for the entries `A = (1 + cos η cos χ)/(2ω²)` and
`B = sin η sin χ/(2ω²)` of the Jacobian of `(η, χ) ↦ (t, r)`. -/
theorem sq_sub_sq_compDeriv :
    ((1 + cos η * cos χ) / (2 * compOmega η χ ^ 2)) ^ 2 - (sin η * sin χ / (2 * compOmega η χ ^ 2)) ^ 2 =
      (compOmega η χ ^ 2)⁻¹ := by
  have key : (1 + cos η * cos χ) ^ 2 - (sin η * sin χ) ^ 2 = (cos η + cos χ) ^ 2 := by
    linear_combination (-(1 - cos χ ^ 2)) * sin_sq_add_cos_sq η + (-(sin η ^ 2)) * sin_sq_add_cos_sq χ
  have hS : cos η + cos χ = 2 * compOmega η χ := by unfold compOmega; ring
  rw [div_pow, div_pow, ← sub_div, key, hS]
  field_simp

/-- **The Minkowski metric in the coordinates `(η, χ)`** (Carroll (7.100)): for a tangent vector
`v = a ∂_η + b ∂_χ + w` with `w` tangent to the sphere and `q = dΩ²(w, w)`, the Minkowski metric `-dt² + dr² + r² dΩ²`
evaluated on the image of `v` (`dt(v) = A a + B b`, `dr(v) = B a + A b` by `hasDerivAt_compT_eta`, ...) is
`ω⁻² (-a² + b² + sin² χ q)`, the metric `ω⁻² (-dη² + dχ² + sin² χ dΩ²)`. -/
theorem minkowski_eq_conformal_esu (a b q : ℝ) :
    -((1 + cos η * cos χ) / (2 * compOmega η χ ^ 2) * a + sin η * sin χ / (2 * compOmega η χ ^ 2) * b) ^ 2 +
        (sin η * sin χ / (2 * compOmega η χ ^ 2) * a + (1 + cos η * cos χ) / (2 * compOmega η χ ^ 2) * b) ^ 2 +
        compR η χ ^ 2 * q =
      (compOmega η χ ^ 2)⁻¹ * (-a ^ 2 + b ^ 2 + sin χ ^ 2 * q) := by
  have e : ∀ A B : ℝ, -(A * a + B * b) ^ 2 + (B * a + A * b) ^ 2 = (A ^ 2 - B ^ 2) * (-a ^ 2 + b ^ 2) := fun A B => by
    ring
  rw [e, sq_sub_sq_compDeriv hω]
  unfold compR
  field_simp

end Derivatives


/-- `2ω = cos η + cos χ = 2 cos U cos V` with `U = (η + χ)/2`, `V = (η - χ)/2` (Carroll (7.101)). -/
theorem compOmega_eq_cos_mul_cos (η χ : ℝ) : compOmega η χ = cos ((η + χ) / 2) * cos ((η - χ) / 2) := by
  unfold compOmega
  rw [cos_add_cos]
  ring_nf

/-- The conformal factor is positive on the region `|η| + χ < π`, `0 ≤ χ` (Carroll (7.99)). -/
theorem compOmega_pos {η χ : ℝ} (hχ : 0 ≤ χ) (h : |η| + χ < π) : 0 < compOmega η χ := by
  rw [compOmega_eq_cos_mul_cos]
  have h1 := neg_abs_le η
  have h2 := le_abs_self η
  apply mul_pos <;> apply cos_pos_of_mem_Ioo <;> constructor <;> linarith

/-- `t = tan U + tan V` (Carroll (7.91), `u = tan U`, `v = tan V`, `t = u + v`). -/
theorem compT_eq_tan_add {η χ : ℝ} (hχ : 0 ≤ χ) (h : |η| + χ < π) :
    compT η χ = tan ((η + χ) / 2) + tan ((η - χ) / 2) := by
  have hω := compOmega_pos hχ h
  rw [compOmega_eq_cos_mul_cos] at hω
  have hU : cos ((η + χ) / 2) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hω; exact lt_irrefl _ hω
  have hV : cos ((η - χ) / 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hω; exact lt_irrefl _ hω
  have hs : sin η = sin ((η + χ) / 2) * cos ((η - χ) / 2) + cos ((η + χ) / 2) * sin ((η - χ) / 2) := by
    rw [← sin_add]; ring_nf
  unfold compT
  rw [compOmega_eq_cos_mul_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_add_div _ _ hU hV, hs]


/-- `r = tan U - tan V` (`r = u - v`). -/
theorem compR_eq_tan_sub {η χ : ℝ} (hχ : 0 ≤ χ) (h : |η| + χ < π) :
    compR η χ = tan ((η + χ) / 2) - tan ((η - χ) / 2) := by
  have hω := compOmega_pos hχ h
  rw [compOmega_eq_cos_mul_cos] at hω
  have hU : cos ((η + χ) / 2) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hω; exact lt_irrefl _ hω
  have hV : cos ((η - χ) / 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hω; exact lt_irrefl _ hω
  have hs : sin χ = sin ((η + χ) / 2) * cos ((η - χ) / 2) - cos ((η + χ) / 2) * sin ((η - χ) / 2) := by
    rw [← sin_sub]; ring_nf
  unfold compR
  rw [compOmega_eq_cos_mul_cos, tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_sub_div _ _ hU hV, hs]

/-- The region `0 < χ`, `|η| + χ < π` of the Einstein static universe that is Minkowski space (Carroll (7.99)). -/
def compRegion : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ |p.1| + p.2 < π}

/-- **Minkowski space is the region `|η| + χ < π` of the Einstein static universe** (Carroll (7.91)–(7.99)): the map
`(η, χ) ↦ (t, r)` is a bijection from `compRegion` onto the half-plane `r > 0` of the radial coordinates. -/
theorem bijOn_comp :
    Set.BijOn (fun p : ℝ × ℝ => (compT p.1 p.2, compR p.1 p.2)) compRegion {q : ℝ × ℝ | 0 < q.2} := by
  have hI : ∀ {η χ : ℝ}, 0 ≤ χ → |η| + χ < π →
      (η + χ) / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) ∧ (η - χ) / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    intro η χ hχ h
    have h1 := neg_abs_le η
    have h2 := le_abs_self η
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_, fun q hq => ?_⟩
  · obtain ⟨hχ, h⟩ := hp
    have hpi : p.2 < π := by linarith [abs_nonneg p.1]
    exact div_pos (sin_pos_of_pos_of_lt_pi hχ hpi) (compOmega_pos hχ.le h)
  · obtain ⟨hpχ, hp⟩ := hp
    obtain ⟨hqχ, hq⟩ := hq
    simp only [Prod.mk.injEq] at hpq
    rw [compT_eq_tan_add hpχ.le hp, compT_eq_tan_add hqχ.le hq] at hpq
    rw [compR_eq_tan_sub hpχ.le hp, compR_eq_tan_sub hqχ.le hq] at hpq
    obtain ⟨hU, hV⟩ := hpq
    have eU : (p.1 + p.2) / 2 = (q.1 + q.2) / 2 :=
      injOn_tan (hI hpχ.le hp).1 (hI hqχ.le hq).1 (by linarith)
    have eV : (p.1 - p.2) / 2 = (q.1 - q.2) / 2 :=
      injOn_tan (hI hpχ.le hp).2 (hI hqχ.le hq).2 (by linarith)
    exact Prod.ext (by linarith) (by linarith)
  · obtain ⟨t, r⟩ := q
    change 0 < r at hq
    set U := arctan ((t + r) / 2)
    set V := arctan ((t - r) / 2)
    have hUV : V < U := arctan_strictMono (by linarith)
    have hU := arctan_lt_pi_div_two ((t + r) / 2)
    have hV := neg_pi_div_two_lt_arctan ((t - r) / 2)
    have hU' := neg_pi_div_two_lt_arctan ((t + r) / 2)
    have hV' := arctan_lt_pi_div_two ((t - r) / 2)
    have hreg : |U + V| + (U - V) < π := by
      rcases abs_cases (U + V) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
    refine ⟨(U + V, U - V), ⟨by simp only; linarith, hreg⟩, ?_⟩
    simp only
    rw [compT_eq_tan_add (by linarith) hreg, compR_eq_tan_sub (by linarith) hreg,
      show (U + V + (U - V)) / 2 = U by ring, show (U + V - (U - V)) / 2 = V by ring, tan_arctan, tan_arctan]
    exact Prod.ext (by simp only; ring) (by simp only; ring)

end Lightlike
