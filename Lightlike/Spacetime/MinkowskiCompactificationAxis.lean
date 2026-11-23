import Mathlib

/-!
# The conformal embedding of Minkowski space including the axis, in Cartesian form (G1-016)

`MinkowskiCompactification` writes the embedding in the polar coordinates `(η, χ)`, which degenerate on the axis
`r = 0` (`χ = 0`). Here the sphere `S³` is the unit sphere `p = (p₀, p⃗)`, `p₀² + |p⃗|² = 1`, of `ℝ × ℝ³`
(`p₀ = cos χ`, `p⃗ = sin χ · n`), and the embedding is
`t = sin η / ω`, `x⃗ = p⃗ / ω`, `ω = (cos η + p₀) / 2`.
The axis is the ordinary point `p = (1, 0)`.

* `cartOmega`, `cartT`, `cartX`: the conformal factor and the Cartesian map;
* `cartOmega_eq_cos_mul_cos`: on the axis `ω = cos²(η/2)` (`cartOmega_axis`), and `cartT_axis`: `t = 2 tan (η/2)`
  there, `cartX_axis`: `x⃗ = 0`;
* `minkowski_eq_conformal_esu_cartesian`: for a tangent vector `a ∂_η + v` to `ℝ × S³` (`⟨p, v⟩ = 0`), the
  Minkowski metric `-dt² + |dx⃗|²` on its image is `ω⁻² (-a² + |v|²)`, with `|v|² = v₀² + |v⃗|²`: the metric of the
  Einstein static universe, at every point of the region `ω ≠ 0`, the axis included;
* `bijOn_cartMap`: `(η, p) ↦ (t, x⃗)` is a bijection from `cartRegion` (`|η| < π`, `p ∈ S³`, `ω > 0`) onto all of
  `ℝ × ℝ³`, the axis included. The inverse is algebraic: with `u = (t + ρ)/2`, `v = (t - ρ)/2`, `ρ = |x⃗|`,
  `ω = ((1 + uv)² + ρ²)^(-1/2)`, `sin η = ω t`, `cos η = ω (1 - uv)`, `p₀ = ω (1 + uv)`, `p⃗ = ω x⃗`
  (`cart_key` is the forward identity `ω (1 + uv) = p₀`, `ω² (1 + u²)(1 + v²) = 1`; `eta_unique`, `exists_eta`).

## Difference from the source (representation)

Carroll writes the sphere part as `sin² χ dΩ²` on `(η, χ)` with `|η| + χ < π`. Here the sphere is `S³ ⊂ ℝ⁴` in
Cartesian form and the region is `|η| < π`, `ω > 0` (equivalent to `|η| + χ < π`); the metric on `S³` is the same.

## References

* S. M. Carroll, *Lecture Notes on General Relativity*, arXiv gr-qc/9712019, chapter 7, eqs. (7.86)–(7.102),
  pp. 192–195; the axis `r = 0` is "well-behaved" (after (7.87)), here made explicit by the Cartesian form.
-/

noncomputable section

namespace Lightlike

open Real

/-- The conformal factor `ω = (cos η + p₀) / 2` in Cartesian form (`p₀ = cos χ`). -/
def cartOmega (η p₀ : ℝ) : ℝ := (cos η + p₀) / 2

/-- The Minkowski time `t = sin η / ω`. -/
def cartT (η p₀ : ℝ) : ℝ := sin η / cartOmega η p₀

/-- The Minkowski position `x⃗ = p⃗ / ω`, for `p⃗ ∈ ℝ³`. -/
def cartX (η p₀ : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (cartOmega η p₀)⁻¹ • p

/-- On the axis `p = (1, 0)` the conformal factor is `cos² (η/2)`. -/
theorem cartOmega_axis (η : ℝ) : cartOmega η 1 = cos (η / 2) ^ 2 := by
  unfold cartOmega
  have := cos_sq (η / 2)
  rw [show 2 * (η / 2) = η by ring] at this
  linarith

/-- On the axis the Minkowski time is `t = 2 tan (η/2)` (where `cos (η/2) ≠ 0`). -/
theorem cartT_axis {η : ℝ} (h : cos (η / 2) ≠ 0) : cartT η 1 = 2 * tan (η / 2) := by
  unfold cartT
  rw [cartOmega_axis, tan_eq_sin_div_cos]
  have h2 : sin η = 2 * sin (η / 2) * cos (η / 2) := by
    rw [← sin_two_mul]; congr 1; ring
  rw [h2]
  field_simp

/-- On the axis the Minkowski position is `x⃗ = 0`: the axis is mapped to the axis `r = 0`. -/
theorem cartX_axis (η : ℝ) : cartX η 1 0 = 0 := by
  simp [cartX]

/-- **The embedding is conformal, axis included** (Carroll (7.100) in Cartesian form): for `(p₀, p⃗)` on the unit
sphere and a tangent vector `a ∂_η + (v₀, v⃗)` with `p₀ v₀ + ⟨p⃗, v⃗⟩ = 0`, and `ω ≠ 0`, the differential of
`(η, p) ↦ (t, x⃗)` carries it to `(dt, dx⃗)` with `-dt² + |dx⃗|² = ω⁻² (-a² + v₀² + |v⃗|²)`. -/
theorem minkowski_eq_conformal_esu_cartesian (η a p₀ v₀ : ℝ) (p v : EuclideanSpace ℝ (Fin 3))
    (hp : p₀ ^ 2 + ‖p‖ ^ 2 = 1) (hv : p₀ * v₀ + @inner ℝ _ _ p v = 0) (hω : cartOmega η p₀ ≠ 0) :
    let ω := cartOmega η p₀
    let dω := (v₀ - sin η * a) / 2
    let dt := cos η * a / ω - sin η * dω / ω ^ 2
    let dx : EuclideanSpace ℝ (Fin 3) := ω⁻¹ • v - (dω / ω ^ 2) • p
    (-dt ^ 2 + ‖dx‖ ^ 2) = ω⁻¹ ^ 2 * (-a ^ 2 + v₀ ^ 2 + ‖v‖ ^ 2) := by
  intro ω dω dt dx
  have hω : ω ≠ 0 := hω
  have hn : ‖dx‖ ^ 2 = (ω⁻¹) ^ 2 * ‖v‖ ^ 2 - 2 * (ω⁻¹ * (dω / ω ^ 2)) * @inner ℝ _ _ v p
      + (dω / ω ^ 2) ^ 2 * ‖p‖ ^ 2 := by
    simp only [dx, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, real_inner_comm p v]
    simp
    ring
  rw [hn]
  have hpv : @inner ℝ _ _ v p = -(p₀ * v₀) := by rw [real_inner_comm]; linarith
  rw [hpv]
  have hp' : ‖p‖ ^ 2 = 1 - p₀ ^ 2 := by linarith
  rw [hp']
  have hωdef : 2 * ω = cos η + p₀ := by simp only [ω, cartOmega]; ring
  have hc : cos η = 2 * ω - p₀ := by linarith
  have hs : sin η ^ 2 = 1 - (2 * ω - p₀) ^ 2 := by
    have := sin_sq_add_cos_sq η
    rw [hc] at this; linarith
  simp only [dt, dω]
  clear_value ω
  rw [hc]
  have hω2 : ω ≠ 0 := hω
  field_simp
  linear_combination (-(sin η ^ 2) * a ^ 2 + 2 * sin η * a * v₀ - 4 * a ^ 2 * ω ^ 2 - v₀ ^ 2) * hs

/-- Non-vacuity: the hypotheses hold on the axis `η = 0`, `p = (1, 0)`, with the tangent vector `a = 1`, `v₀ = 0`,
`v⃗ = e₀`; there `ω = 1`, and the identity reads `-1 + 1 = 1 * (-1 + 0 + 1)`. -/
example : cartOmega 0 1 ≠ 0 ∧ (1 : ℝ) ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = 1 ∧
    (1 : ℝ) * 0 + @inner ℝ _ _ (0 : EuclideanSpace ℝ (Fin 3)) (EuclideanSpace.single 0 1) = 0 := by
  refine ⟨by simp [cartOmega], by simp, by simp⟩

/-- An angle in `(-π, π)` is determined by its sine and cosine. -/
theorem eta_unique {η η' : ℝ} (h : |η| < π) (h' : |η'| < π) (hs : sin η = sin η')
    (hc : cos η = cos η') : η = η' := by
  have h1 : cos (η - η') = 1 := by
    rw [cos_sub, hs, hc]; nlinarith [sin_sq_add_cos_sq η']
  obtain ⟨n, hn⟩ := (cos_eq_one_iff _).1 h1
  have hlt : |(n : ℝ)| * (2 * π) < 2 * π := by
    rw [← abs_of_pos (show 0 < 2 * π by positivity), ← abs_mul, hn,
      abs_of_pos (show 0 < 2 * π by positivity)]
    calc |η - η'| ≤ |η| + |η'| := abs_sub _ _
      _ < π + π := add_lt_add h h'
      _ = 2 * π := by ring
  have : |(n : ℝ)| < 1 := by
    by_contra hh
    have hh := not_lt.1 hh
    nlinarith [pi_pos]
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast this
    exact Int.abs_lt_one_iff.1 this
  subst hn0
  simp at hn; linarith

/-- Every `(s, c)` on the unit circle with `c > -1` is `(sin η, cos η)` for an `η ∈ (-π, π)`. -/
theorem exists_eta {s c : ℝ} (h : s ^ 2 + c ^ 2 = 1) (hc : -1 < c) :
    ∃ η : ℝ, |η| < π ∧ sin η = s ∧ cos η = c := by
  set z := s / (1 + c) with hz
  have h1 : 0 < 1 + c := by linarith
  refine ⟨2 * arctan z, ?_, ?_, ?_⟩
  · have := arctan_lt_pi_div_two z
    have := neg_pi_div_two_lt_arctan z
    rw [abs_lt]; constructor <;> linarith
  · rw [sin_two_mul, sin_arctan, cos_arctan]
    have hz2 : 1 + z ^ 2 = 2 / (1 + c) := by
      rw [hz]; field_simp; nlinarith
    have e : sqrt (1 + z ^ 2) * sqrt (1 + z ^ 2) = 2 / (1 + c) := by
      rw [mul_self_sqrt (by positivity), hz2]
    have hp : 0 < sqrt (1 + z ^ 2) := sqrt_pos.2 (by positivity)
    have : 2 * (z / sqrt (1 + z ^ 2)) * (1 / sqrt (1 + z ^ 2)) = 2 * z / (sqrt (1 + z ^ 2) * sqrt (1 + z ^ 2)) := by
      field_simp
    rw [this, e, hz]
    field_simp
  · rw [cos_two_mul, cos_arctan]
    have hz2 : 1 + z ^ 2 = 2 / (1 + c) := by
      rw [hz]; field_simp; nlinarith
    rw [div_pow, hz2, sq_sqrt (by positivity)]
    field_simp
    ring


/-- The region of the Einstein static universe `ℝ × S³` mapped to Minkowski space: `|η| < π`, `p` on the unit sphere
of `ℝ × ℝ³`, and `ω > 0`. It contains the axis `p = (1, 0)`. -/
def cartRegion : Set (ℝ × ℝ × EuclideanSpace ℝ (Fin 3)) :=
  {q | |q.1| < π ∧ q.2.1 ^ 2 + ‖q.2.2‖ ^ 2 = 1 ∧ 0 < cartOmega q.1 q.2.1}

/-- The embedding `(η, p₀, p⃗) ↦ (t, x⃗)`. -/
def cartMap (q : ℝ × ℝ × EuclideanSpace ℝ (Fin 3)) : ℝ × EuclideanSpace ℝ (Fin 3) :=
  (cartT q.1 q.2.1, cartX q.1 q.2.1 q.2.2)

/-- The quantity `uv = (t² - ρ²)/4` (`u = (t + ρ)/2`, `v = (t - ρ)/2`) of Carroll (7.88). -/
def cartUV (t ρ : ℝ) : ℝ := (t ^ 2 - ρ ^ 2) / 4

/-- The quantity `(1 + u²)(1 + v²) = (1 + uv)² + ρ²`, the inverse square of the conformal factor. -/
def cartD (t ρ : ℝ) : ℝ := (1 + cartUV t ρ) ^ 2 + ρ ^ 2

/-- On the region, `ω (1 + uv) = p₀` and `ω² (1 + u²)(1 + v²) = 1`. -/
theorem cart_key {s c p₀ n : ℝ} (hs : s ^ 2 + c ^ 2 = 1) (hp : p₀ ^ 2 + n ^ 2 = 1)
    (hω : 0 < (c + p₀) / 2) :
    (c + p₀) / 2 * (1 + cartUV (s / ((c + p₀) / 2)) (n / ((c + p₀) / 2))) = p₀ ∧
    ((c + p₀) / 2) ^ 2 * cartD (s / ((c + p₀) / 2)) (n / ((c + p₀) / 2)) = 1 := by
  set w := (c + p₀) / 2 with hw
  have hw0 : w ≠ 0 := hω.ne'
  have h1 : w * (1 + cartUV (s / w) (n / w)) = p₀ := by
    unfold cartUV
    field_simp
    have : c = 2 * w - p₀ := by rw [hw]; ring
    have hs' : s ^ 2 = 1 - c ^ 2 := by linarith
    have hn' : n ^ 2 = 1 - p₀ ^ 2 := by linarith
    rw [hs', hn', this]; ring
  refine ⟨h1, ?_⟩
  unfold cartD
  have e1 : (1 + cartUV (s / w) (n / w)) = p₀ / w := by
    rw [← h1]; field_simp
  rw [e1]
  field_simp
  linarith

/-- The Cartesian embedding is injective on the region. -/
theorem injOn_cartMap : Set.InjOn cartMap cartRegion := by
  rintro ⟨η, p₀, p⟩ ⟨hη, hp, hω⟩ ⟨η', p₀', p'⟩ ⟨hη', hp', hω'⟩ h
  simp only [cartMap, Prod.mk.injEq] at h
  obtain ⟨ht, hx⟩ := h
  simp only at hη hp hω hη' hp' hω'
  set w := cartOmega η p₀ with hwdef
  set w' := cartOmega η' p₀' with hwdef'
  have hwe : (cos η + p₀) / 2 = w := rfl
  have hwe' : (cos η' + p₀') / 2 = w' := rfl
  have hρ : ‖cartX η p₀ p‖ = ‖p‖ / w := by
    simp only [cartX, norm_smul, norm_inv, ← hwdef, Real.norm_eq_abs, abs_of_pos hω]; ring
  have hρ' : ‖cartX η' p₀' p'‖ = ‖p'‖ / w' := by
    simp only [cartX, norm_smul, norm_inv, ← hwdef', Real.norm_eq_abs, abs_of_pos hω']; ring
  obtain ⟨k1, k2⟩ := cart_key (sin_sq_add_cos_sq η) hp (by rw [hwe]; exact hω)
  obtain ⟨k1', k2'⟩ := cart_key (sin_sq_add_cos_sq η') hp' (by rw [hwe']; exact hω')
  rw [hwe] at k1 k2
  rw [hwe'] at k1' k2'
  have hρ2 : ‖p'‖ / w' = ‖p‖ / w := by rw [← hρ, ← hρ', hx]
  have hT2 : sin η' / w' = sin η / w := by
    have e1 : cartT η p₀ = sin η / w := rfl
    have e2 : cartT η' p₀' = sin η' / w' := rfl
    rw [← e1, ← e2, ht]
  rw [hρ2, hT2] at k1' k2'
  have hD : cartD (sin η / w) (‖p‖ / w) ≠ 0 := by
    intro h0; rw [h0] at k2; simp at k2
  have hww : w = w' := by
    have : w ^ 2 = w' ^ 2 := by
      apply mul_right_cancel₀ hD; rw [k2, k2']
    exact (sq_eq_sq₀ hω.le hω'.le).1 this
  have hp0 : p₀ = p₀' := by rw [← k1, ← k1', hww]
  have hs : sin η = sin η' := by
    have : sin η / w = sin η' / w := by
      have h3 := hT2
      rw [← hww] at h3
      exact h3.symm
    exact (div_left_inj' hω.ne').1 this
  have hc : cos η = cos η' := by
    have : 2 * w - p₀ = 2 * w' - p₀' := by rw [hww, hp0]
    have e1 : cos η = 2 * w - p₀ := by linarith [hwe]
    have e2 : cos η' = 2 * w' - p₀' := by linarith [hwe']
    rw [e1, e2, this]
  have hη2 : η = η' := eta_unique hη hη' hs hc
  have hpp : p = p' := by
    have e1 : p = w • cartX η p₀ p := by
      show p = w • (w⁻¹ • p)
      rw [smul_smul, mul_inv_cancel₀ hω.ne', one_smul]
    have e2 : p' = w' • cartX η' p₀' p' := by
      show p' = w' • (w'⁻¹ • p')
      rw [smul_smul, mul_inv_cancel₀ hω'.ne', one_smul]
    rw [e1, e2, hx, hww]
  rw [hη2, hp0, hpp]

/-- **Minkowski space is the region `ω > 0` of the Einstein static universe, axis included** (Carroll (7.91)–(7.99)
in Cartesian form): `(η, p₀, p⃗) ↦ (t, x⃗)` is a bijection from `cartRegion` onto `ℝ × ℝ³`. -/
theorem bijOn_cartMap : Set.BijOn cartMap cartRegion Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, injOn_cartMap, ?_⟩
  rintro ⟨t, x⟩ -
  set ρ := ‖x‖ with hρ
  set m := cartUV t ρ with hm
  have hm' : 4 * m = t ^ 2 - ρ ^ 2 := by simp only [hm, cartUV]; ring
  have hDpos : 0 < cartD t ρ := by
    unfold cartD
    rw [← hm]
    by_contra hneg
    have h1 : (1 + m) ^ 2 + ρ ^ 2 ≤ 0 := not_lt.1 hneg
    have hρ0 : ρ = 0 := by nlinarith [sq_nonneg (1 + m), sq_nonneg ρ]
    have hm0 : 0 ≤ m := by nlinarith [sq_nonneg t]
    nlinarith [sq_nonneg (1 + m), sq_nonneg ρ]
  set D := cartD t ρ with hD
  have hDe : D = (1 + m) ^ 2 + ρ ^ 2 := rfl
  set w := (sqrt D)⁻¹ with hw
  have hwpos : 0 < w := inv_pos.2 (sqrt_pos.2 hDpos)
  have hw2 : w ^ 2 * D = 1 := by
    rw [hw, inv_pow, sq_sqrt hDpos.le]; field_simp
  set s := w * t with hs
  set c := w * (1 - m) with hc
  have hsc : s ^ 2 + c ^ 2 = 1 := by
    have : t ^ 2 + (1 - m) ^ 2 = D := by rw [hDe]; nlinarith
    calc s ^ 2 + c ^ 2 = w ^ 2 * (t ^ 2 + (1 - m) ^ 2) := by rw [hs, hc]; ring
      _ = 1 := by rw [this, hw2]
  have hc1 : -1 < c := by
    by_cases ht : t = 0
    · have : 0 < 1 - m := by nlinarith [sq_nonneg ρ]
      have : 0 < c := by rw [hc]; positivity
      linarith
    · have hs0 : 0 < s ^ 2 := by rw [hs]; positivity
      have hcle : c ≤ 1 := by nlinarith
      by_contra hneg
      have : c ≤ -1 := not_lt.1 hneg
      nlinarith
  obtain ⟨η, hη, hsη, hcη⟩ := exists_eta hsc hc1
  set p₀ := w * (1 + m) with hp₀
  set p : EuclideanSpace ℝ (Fin 3) := w • x with hp
  have hpn : p₀ ^ 2 + ‖p‖ ^ 2 = 1 := by
    have : ‖p‖ = w * ρ := by
      rw [hp, norm_smul, Real.norm_eq_abs, abs_of_pos hwpos]
    rw [this]
    calc p₀ ^ 2 + (w * ρ) ^ 2 = w ^ 2 * ((1 + m) ^ 2 + ρ ^ 2) := by rw [hp₀]; ring
      _ = 1 := by rw [← hDe, hw2]
  have hωη : cartOmega η p₀ = w := by
    unfold cartOmega
    rw [hcη, hc, hp₀]; ring
  refine ⟨(η, p₀, p), ⟨hη, hpn, by rw [show (η, p₀, p).2.1 = p₀ from rfl, hωη]; exact hwpos⟩, ?_⟩
  have hωη' : cartOmega (η, p₀, p).1 (η, p₀, p).2.1 = w := hωη
  refine Prod.ext ?_ ?_
  · show cartT η p₀ = t
    unfold cartT
    rw [hωη, hsη, hs]; field_simp
  · show cartX η p₀ p = x
    unfold cartX
    rw [hωη, hp, smul_smul, inv_mul_cancel₀ hwpos.ne', one_smul]

end Lightlike
