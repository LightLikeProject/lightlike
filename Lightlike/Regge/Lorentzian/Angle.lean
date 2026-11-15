import Mathlib
import Lightlike.Regge.Winding

/-!
# Sorkin's complex angles in a Minkowski plane

Lorentzian Regge calculus (Sorkin 1975) needs angles between vectors of a two-dimensional
Minkowski plane, where a wedge can contain light rays. This file defines the complex angle of
Sorkin (arXiv:1908.10022) in the form of Asante–Dittrich–Padua-Argüelles (ADP, arXiv:2104.00485,
Appendix B, eqs. B1–B2) and proves the properties that Lorentzian Regge calculus rests on.

Signature `(−,+)`: a vector `a` is spacelike if `η(a,a) > 0` and timelike if `η(a,a) < 0`. The
angle of the convex wedge spanned by two non-null vectors `a`, `b` is a function of
`aa = η(a,a)`, `bb = η(b,b)` and `ab = η(a,b)`:

  `sorkinAngle aa bb ab = boostPart aa bb ab − (π/2) · lightRays aa bb ab · i`,

where `lightRays` counts the light rays (null half-lines) inside the wedge and `boostPart` is the
boost parameter (rapidity difference). The five cases of ADP are `sorkinAngle_ss_pos`,
`sorkinAngle_ss_neg`, `sorkinAngle_st`, `sorkinAngle_tt_neg` and `sorkinAngle_tt_pos`.

## Main results

* `sorkinAngle_null`: **the null-frame formula.** In null coordinates `u = x + t`, `v = x − t` of
  an orthonormal frame, so that `η(P, P') = (u v' + u' v)/2`, and for a positively oriented pair,
  the angle is `rapidity P' − rapidity P − (π/2) · N · i`, with `rapidity = ½ log |u/v|` and `N`
  the number of sign changes of `u` and of `v`.
* `sorkinAngle_add`: angles are additive: the wedge `(a, c)` split by a vector `b` inside it.
* `sum_sorkinAngle_eq`: **the full turn.** Wedges around a point that do not overlap, with
  non-null bounding vectors, have angles adding up to `−2πi` (four light rays, real parts
  cancelling).
* `sorkinAngle_comm`, `sorkinAngle_scale`, `sorkinAngle_div`: symmetry and scale invariance.

Null vectors are excluded by hypotheses; for them the definition returns the junk value `0`.
-/

open Real Finset

namespace Lightlike.ReggeLor

/-! ## Definition -/

/-- The **boost part** (real part) of Sorkin's angle between two non-null vectors `a`, `b` of a
Minkowski plane, from `aa = η(a,a)`, `bb = η(b,b)`, `ab = η(a,b)`. For vectors of the same causal
type (`aa * bb > 0`) it is `arcosh κ` if `ab > 0` and `-arcosh (-κ)` if `ab < 0`, with
`κ = ab / √(aa bb)`; for one spacelike and one timelike vector (`aa * bb < 0`) it is
`arsinh (ab / √(-aa bb))`. For a null vector it is the junk value `0`. -/
noncomputable def boostPart (aa bb ab : ℝ) : ℝ :=
  if 0 < aa * bb then
    (if 0 < ab then arcosh (ab / √(aa * bb)) else -arcosh (-ab / √(aa * bb)))
  else if aa * bb < 0 then arsinh (ab / √(-(aa * bb))) else 0

/-- The **number of light rays** inside the convex wedge spanned by two non-null vectors `a`,
`b`. Two spacelike vectors in the same quadrant (`ab > 0`), or two timelike vectors in the same
cone (`ab < 0`), enclose none; in opposite quadrants or cones they enclose two; a spacelike and a
timelike vector enclose one. In terms of the inner products: `0` if `aa * bb > 0` and
`aa * ab > 0`, `2` if `aa * bb > 0` and `aa * ab ≤ 0`, `1` if `aa * bb < 0`, and the junk value `0`
for a null vector. -/
noncomputable def lightRays (aa bb ab : ℝ) : ℕ :=
  if 0 < aa * bb then (if 0 < aa * ab then 0 else 2) else if aa * bb < 0 then 1 else 0

/-- **Sorkin's complex angle** of the convex wedge spanned by two non-null vectors `a`, `b` of a
Minkowski plane, from `aa = η(a,a)`, `bb = η(b,b)`, `ab = η(a,b)` (Sorkin, arXiv:1908.10022;
ADP, arXiv:2104.00485, eqs. B1–B2): the boost part minus `π/2 · i` for every light ray inside the
wedge. -/
noncomputable def sorkinAngle (aa bb ab : ℝ) : ℂ :=
  (boostPart aa bb ab : ℂ) - ((π / 2 * (lightRays aa bb ab : ℝ) : ℝ) : ℂ) * Complex.I

/-- The real part of Sorkin's angle is its boost part. -/
@[simp] theorem sorkinAngle_re (aa bb ab : ℝ) : (sorkinAngle aa bb ab).re = boostPart aa bb ab := by
  simp [sorkinAngle]

/-- The imaginary part of Sorkin's angle is `−π/2` per light ray. -/
@[simp] theorem sorkinAngle_im (aa bb ab : ℝ) :
    (sorkinAngle aa bb ab).im = -(π / 2 * (lightRays aa bb ab : ℝ)) := by
  simp [sorkinAngle]

/-! ## The five cases of ADP (eqs. B1–B2) -/

section Cases

variable {aa bb ab : ℝ}

/-- Two spacelike vectors in the same quadrant: `arcosh κ` (ADP `θ₁`). -/
theorem sorkinAngle_ss_pos (ha : 0 < aa) (hb : 0 < bb) (hab : 0 < ab) :
    sorkinAngle aa bb ab = (arcosh (ab / √(aa * bb)) : ℂ) := by
  have h1 : 0 < aa * bb := mul_pos ha hb
  simp [sorkinAngle, boostPart, lightRays, h1, hab, mul_pos ha hab]

/-- Two spacelike vectors in opposite quadrants: `-arcosh (-κ) - π i` (ADP `θ₂`). -/
theorem sorkinAngle_ss_neg (ha : 0 < aa) (hb : 0 < bb) (hab : ab < 0) :
    sorkinAngle aa bb ab = (-arcosh (-ab / √(aa * bb)) : ℂ) - π * Complex.I := by
  have h1 : 0 < aa * bb := mul_pos ha hb
  have h2 : ¬ 0 < aa * ab := not_lt.2 (mul_neg_of_pos_of_neg ha hab).le
  simp only [sorkinAngle, boostPart, lightRays, h1, h2, not_lt.2 hab.le, ↓reduceIte]
  push_cast
  ring

/-- A spacelike and a timelike vector: `arsinh κ - (π/2) i` (ADP `θ₃`). -/
theorem sorkinAngle_st (h : aa * bb < 0) :
    sorkinAngle aa bb ab = (arsinh (ab / √(-(aa * bb))) : ℂ) - π / 2 * Complex.I := by
  simp only [sorkinAngle, boostPart, lightRays, not_lt.2 h.le, h, ↓reduceIte]
  push_cast
  ring

/-- Two timelike vectors in the same cone: `-arcosh (-κ)` (ADP `θ₄`). -/
theorem sorkinAngle_tt_neg (ha : aa < 0) (hb : bb < 0) (hab : ab < 0) :
    sorkinAngle aa bb ab = (-arcosh (-ab / √(aa * bb)) : ℂ) := by
  have h1 : 0 < aa * bb := mul_pos_of_neg_of_neg ha hb
  simp [sorkinAngle, boostPart, lightRays, h1, not_lt.2 hab.le, mul_pos_of_neg_of_neg ha hab]

/-- Two timelike vectors in opposite cones: `arcosh κ - π i` (ADP `θ₅`). -/
theorem sorkinAngle_tt_pos (ha : aa < 0) (hb : bb < 0) (hab : 0 < ab) :
    sorkinAngle aa bb ab = (arcosh (ab / √(aa * bb)) : ℂ) - π * Complex.I := by
  have h1 : 0 < aa * bb := mul_pos_of_neg_of_neg ha hb
  have h2 : ¬ 0 < aa * ab := not_lt.2 (mul_neg_of_neg_of_pos ha hab).le
  simp only [sorkinAngle, boostPart, lightRays, h1, h2, hab, ↓reduceIte]
  push_cast
  ring

end Cases

/-! ## Symmetry and scale invariance -/

/-- The angle of the wedge `(a, b)` is the angle of `(b, a)`. -/
theorem sorkinAngle_comm (aa bb ab : ℝ) : sorkinAngle bb aa ab = sorkinAngle aa bb ab := by
  have hl : lightRays bb aa ab = lightRays aa bb ab := by
    unfold lightRays
    rw [mul_comm bb aa]
    by_cases h1 : 0 < aa * bb
    · have h : 0 < bb * ab ↔ 0 < aa * ab := by
        rcases mul_pos_iff.1 h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [mul_pos_iff_of_pos_left ha, mul_pos_iff_of_pos_left hb]
        · constructor <;> intro h2
          · have : ab < 0 := by nlinarith
            exact mul_pos_of_neg_of_neg ha this
          · have : ab < 0 := by nlinarith
            exact mul_pos_of_neg_of_neg hb this
      simp only [h1, h, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
  simp only [sorkinAngle, boostPart, mul_comm bb aa, hl]

/-- Sorkin's angle depends only on the directions of `a` and `b`: rescaling `a` by `p > 0` and
`b` by `q > 0` leaves it unchanged. -/
theorem sorkinAngle_scale {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (aa bb ab : ℝ) :
    sorkinAngle (p ^ 2 * aa) (q ^ 2 * bb) (p * q * ab) = sorkinAngle aa bb ab := by
  have hc : 0 < (p * q) ^ 2 := by positivity
  have hpq : 0 < p * q := mul_pos hp hq
  have hd : 0 < p ^ 3 * q := by positivity
  have e1 : p ^ 2 * aa * (q ^ 2 * bb) = (p * q) ^ 2 * (aa * bb) := by ring
  have e2 : p ^ 2 * aa * (p * q * ab) = p ^ 3 * q * (aa * ab) := by ring
  have e3 : -((p * q) ^ 2 * (aa * bb)) = (p * q) ^ 2 * -(aa * bb) := by ring
  have hs : ∀ x, √((p * q) ^ 2 * x) = p * q * √x := fun x => by
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq hpq.le]
  have hr : ∀ x y, p * q * x / (p * q * y) = x / y := fun x y => mul_div_mul_left x y hpq.ne'
  have hr' : ∀ x y, -(p * q * x) / (p * q * y) = -x / y := fun x y => by
    rw [← mul_neg, mul_div_mul_left _ _ hpq.ne']
  have hn : ∀ x, (p * q) ^ 2 * x < 0 ↔ x < 0 := fun x => by
    constructor <;> intro h <;> nlinarith
  simp only [sorkinAngle, boostPart, lightRays, e1, e2, e3, hs, hr, hr',
    mul_pos_iff_of_pos_left hc, mul_pos_iff_of_pos_left hd, mul_pos_iff_of_pos_left hpq, hn]

/-- Sorkin's angle is unchanged when all three inner products are divided by `c > 0`. -/
theorem sorkinAngle_div {c : ℝ} (hc : 0 < c) (aa bb ab : ℝ) :
    sorkinAngle (aa / c) (bb / c) (ab / c) = sorkinAngle aa bb ab := by
  have hs : 0 < (√c)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc)
  have e : ∀ x, x / c = (√c)⁻¹ ^ 2 * x := fun x => by
    rw [inv_pow, Real.sq_sqrt hc.le, div_eq_inv_mul]
  have e' : ∀ x, x / c = (√c)⁻¹ * (√c)⁻¹ * x := fun x => by rw [e x, sq]
  rw [e aa, e bb, e' ab, sorkinAngle_scale hs hs]

/-! ## The null-frame formula -/

/-- `1` if `x` and `y` have opposite signs, else `0`. -/
noncomputable def signFlip (x y : ℝ) : ℕ := if x * y < 0 then 1 else 0

/-- The **rapidity** of a non-null vector with null coordinates `u = x + t`, `v = x − t`:
`½ log |u/v|`, i.e. `artanh (t/x)` for a spacelike and `artanh (x/t)` for a timelike vector. -/
noncomputable def rapidity (u v : ℝ) : ℝ := Real.log |u / v| / 2

/-- For `a, b > 0`: `arcosh ((a² + b²)/(2ab)) = |log b − log a|`. -/
theorem arcosh_sq_add_sq_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    arcosh ((a ^ 2 + b ^ 2) / (2 * a * b)) = |Real.log b - Real.log a| := by
  have h : (a ^ 2 + b ^ 2) / (2 * a * b) = cosh (Real.log b - Real.log a) := by
    rw [← Real.log_div hb.ne' ha.ne', Real.cosh_log (div_pos hb ha)]
    field_simp
    ring
  rw [h, ← Real.cosh_abs, Real.arcosh_cosh (abs_nonneg _)]

/-- For `a, b > 0`: `arsinh ((b² − a²)/(2ab)) = log b − log a`. -/
theorem arsinh_sq_sub_sq_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    arsinh ((b ^ 2 - a ^ 2) / (2 * a * b)) = Real.log b - Real.log a := by
  have h : (b ^ 2 - a ^ 2) / (2 * a * b) = sinh (Real.log b - Real.log a) := by
    rw [← Real.log_div hb.ne' ha.ne', Real.sinh_log (div_pos hb ha)]
    field_simp
  rw [h, Real.arsinh_sinh]

/-- The boost part with `aa * bb = X * Y` and `ab = (X + Y)/2`, for `X ≤ Y`, is
`½ (log |Y| − log |X|)`. -/
theorem boostPart_XY {X Y : ℝ} (hX : X ≠ 0) (hY : Y ≠ 0) (hXY : X ≤ Y) :
    boostPart X Y ((X + Y) / 2) = (Real.log |Y| - Real.log |X|) / 2 := by
  rcases lt_or_gt_of_ne hX with hX | hX <;> rcases lt_or_gt_of_ne hY with hY | hY
  · -- `X ≤ Y < 0`: two vectors of the same type, `ab < 0`
    obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ X = -a ^ 2 :=
      ⟨√(-X), Real.sqrt_pos.2 (by linarith), by rw [Real.sq_sqrt (by linarith)]; ring⟩
    obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ Y = -b ^ 2 :=
      ⟨√(-Y), Real.sqrt_pos.2 (by linarith), by rw [Real.sq_sqrt (by linarith)]; ring⟩
    have hba : b ≤ a := by nlinarith
    have hP : 0 < -a ^ 2 * -b ^ 2 := by nlinarith [mul_pos ha hb]
    have hs : √(-a ^ 2 * -b ^ 2) = a * b := by
      rw [show -a ^ 2 * -b ^ 2 = (a * b) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
    have hn : ¬ 0 < (-a ^ 2 + -b ^ 2) / 2 := by nlinarith
    have harg : -((-a ^ 2 + -b ^ 2) / 2) / (a * b) = (a ^ 2 + b ^ 2) / (2 * a * b) := by
      field_simp; ring
    simp only [boostPart, hP, hn, ↓reduceIte, hs, harg, arcosh_sq_add_sq_div ha hb,
      Real.log_abs, Real.log_neg_eq_log, Real.log_pow]
    rw [abs_of_nonpos (by linarith [Real.log_le_log hb hba])]
    push_cast
    ring
  · -- `X < 0 < Y`: a spacelike and a timelike vector
    obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ X = -a ^ 2 :=
      ⟨√(-X), Real.sqrt_pos.2 (by linarith), by rw [Real.sq_sqrt (by linarith)]; ring⟩
    obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ Y = b ^ 2 :=
      ⟨√Y, Real.sqrt_pos.2 hY, by rw [Real.sq_sqrt hY.le]⟩
    have hP : -a ^ 2 * b ^ 2 < 0 := by nlinarith [mul_pos ha hb]
    have hs : √(-(-a ^ 2 * b ^ 2)) = a * b := by
      rw [show -(-a ^ 2 * b ^ 2) = (a * b) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
    have harg : (-a ^ 2 + b ^ 2) / 2 / (a * b) = (b ^ 2 - a ^ 2) / (2 * a * b) := by
      field_simp; ring
    simp only [boostPart, not_lt.2 hP.le, hP, ↓reduceIte, hs, harg,
      arsinh_sq_sub_sq_div ha hb, Real.log_abs, Real.log_neg_eq_log, Real.log_pow]
    push_cast
    ring
  · linarith
  · -- `0 < X ≤ Y`: two vectors of the same type, `ab > 0`
    obtain ⟨a, ha, rfl⟩ : ∃ a, 0 < a ∧ X = a ^ 2 :=
      ⟨√X, Real.sqrt_pos.2 hX, by rw [Real.sq_sqrt hX.le]⟩
    obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ Y = b ^ 2 :=
      ⟨√Y, Real.sqrt_pos.2 hY, by rw [Real.sq_sqrt hY.le]⟩
    have hab : a ≤ b := by nlinarith
    have hP : 0 < a ^ 2 * b ^ 2 := by positivity
    have hs : √(a ^ 2 * b ^ 2) = a * b := by
      rw [show a ^ 2 * b ^ 2 = (a * b) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
    have hpos : 0 < (a ^ 2 + b ^ 2) / 2 := by positivity
    have harg : (a ^ 2 + b ^ 2) / 2 / (a * b) = (a ^ 2 + b ^ 2) / (2 * a * b) := by
      field_simp
    simp only [boostPart, hP, hpos, ↓reduceIte, hs, harg, arcosh_sq_add_sq_div ha hb,
      Real.log_abs, Real.log_pow]
    rw [abs_of_nonneg (by linarith [Real.log_le_log ha hab])]
    push_cast
    ring

/-- Boost part in null coordinates: for a positively oriented pair (`u₁ v₂ ≤ u₂ v₁`), the boost
part is the rapidity difference. -/
theorem boostPart_null {u₁ v₁ u₂ v₂ : ℝ} (hu₁ : u₁ ≠ 0) (hv₁ : v₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hv₂ : v₂ ≠ 0) (hor : u₁ * v₂ ≤ u₂ * v₁) :
    boostPart (u₁ * v₁) (u₂ * v₂) ((u₁ * v₂ + u₂ * v₁) / 2) =
      rapidity u₂ v₂ - rapidity u₁ v₁ := by
  have hP : u₁ * v₁ * (u₂ * v₂) = u₁ * v₂ * (u₂ * v₁) := by ring
  have hB : boostPart (u₁ * v₁) (u₂ * v₂) ((u₁ * v₂ + u₂ * v₁) / 2) =
      boostPart (u₁ * v₂) (u₂ * v₁) ((u₁ * v₂ + u₂ * v₁) / 2) := by
    simp only [boostPart, hP]
  rw [hB, boostPart_XY (mul_ne_zero hu₁ hv₂) (mul_ne_zero hu₂ hv₁) hor]
  simp only [rapidity, Real.log_abs]
  rw [Real.log_div hu₂ hv₂, Real.log_div hu₁ hv₁, Real.log_mul hu₂ hv₁, Real.log_mul hu₁ hv₂]
  ring

/-- A non-zero real is `a` or `-a` for some `a > 0`. -/
theorem exists_pos_eq_or_eq_neg {x : ℝ} (hx : x ≠ 0) : ∃ a, 0 < a ∧ (x = a ∨ x = -a) := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact ⟨-x, by linarith, Or.inr (by ring)⟩
  · exact ⟨x, h, Or.inl rfl⟩

/-- Light rays in null coordinates: the wedge contains one light ray for every sign change of
`u` and one for every sign change of `v`. -/
theorem lightRays_null {u₁ v₁ u₂ v₂ : ℝ} (hu₁ : u₁ ≠ 0) (hv₁ : v₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hv₂ : v₂ ≠ 0) :
    lightRays (u₁ * v₁) (u₂ * v₂) ((u₁ * v₂ + u₂ * v₁) / 2) = signFlip u₁ u₂ + signFlip v₁ v₂ := by
  obtain ⟨a, ha, rfl | rfl⟩ := exists_pos_eq_or_eq_neg hu₁ <;>
  obtain ⟨b, hb, rfl | rfl⟩ := exists_pos_eq_or_eq_neg hv₁ <;>
  obtain ⟨c, hc, rfl | rfl⟩ := exists_pos_eq_or_eq_neg hu₂ <;>
  obtain ⟨d, hd, rfl | rfl⟩ := exists_pos_eq_or_eq_neg hv₂ <;>
  · have h1 := mul_pos (mul_pos ha hb) (mul_pos hc hd)
    have h2 := mul_pos (mul_pos ha hb) (mul_pos ha hd)
    have h3 := mul_pos (mul_pos ha hb) (mul_pos hc hb)
    have h4 := mul_pos ha hc
    have h5 := mul_pos hb hd
    simp only [lightRays, signFlip]
    split_ifs <;> first | rfl | (exfalso; linarith)

/-- **The null-frame formula.** Let `(u₁, v₁)` and `(u₂, v₂)` be the null coordinates
(`u = x + t`, `v = x − t`) of two non-null vectors, positively oriented (`u₁ v₂ ≤ u₂ v₁`, i.e.
`x₁ t₂ − x₂ t₁ ≥ 0`). Then Sorkin's angle is the rapidity difference minus `π/2 · i` for every
sign change of `u` and of `v`. -/
theorem sorkinAngle_null {u₁ v₁ u₂ v₂ : ℝ} (hu₁ : u₁ ≠ 0) (hv₁ : v₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hv₂ : v₂ ≠ 0) (hor : u₁ * v₂ ≤ u₂ * v₁) :
    sorkinAngle (u₁ * v₁) (u₂ * v₂) ((u₁ * v₂ + u₂ * v₁) / 2) =
      ((rapidity u₂ v₂ - rapidity u₁ v₁ : ℝ) : ℂ) -
        ((π / 2 * ((signFlip u₁ u₂ + signFlip v₁ v₂ : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I := by
  rw [sorkinAngle, boostPart_null hu₁ hv₁ hu₂ hv₂ hor, lightRays_null hu₁ hv₁ hu₂ hv₂]

/-! ## Additivity -/

/-- Sign changes add along a positive combination: if `y = l x + m z` with `l, m > 0`, then `x`
and `z` have opposite signs exactly when one of the pairs `(x, y)`, `(y, z)` has. -/
theorem signFlip_add {x y z l m : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hl : 0 < l)
    (hm : 0 < m) (h : y = l * x + m * z) : signFlip x z = signFlip x y + signFlip y z := by
  rcases lt_or_gt_of_ne hx with hx | hx <;> rcases lt_or_gt_of_ne hy with hy | hy <;>
    rcases lt_or_gt_of_ne hz with hz | hz <;>
  · simp only [signFlip]
    split_ifs <;> first | rfl | (exfalso; nlinarith)

/-- Additivity for a positively oriented wedge (`u_a v_c ≤ u_c v_a`); see `sorkinAngle_add`. -/
theorem sorkinAngle_add_of_le {ua va ub vb uc vc l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hu : ub = l * ua + m * uc) (hv : vb = l * va + m * vc)
    (hua : ua ≠ 0) (hva : va ≠ 0) (hub : ub ≠ 0) (hvb : vb ≠ 0) (huc : uc ≠ 0) (hvc : vc ≠ 0)
    (hor : ua * vc ≤ uc * va) :
    sorkinAngle (ua * va) (uc * vc) ((ua * vc + uc * va) / 2) =
      sorkinAngle (ua * va) (ub * vb) ((ua * vb + ub * va) / 2) +
        sorkinAngle (ub * vb) (uc * vc) ((ub * vc + uc * vb) / 2) := by
  have h1 : ua * vb ≤ ub * va := by rw [hu, hv]; nlinarith
  have h2 : ub * vc ≤ uc * vb := by rw [hu, hv]; nlinarith
  rw [sorkinAngle_null hua hva huc hvc hor, sorkinAngle_null hua hva hub hvb h1,
    sorkinAngle_null hub hvb huc hvc h2, signFlip_add hua hub huc hl hm hu,
    signFlip_add hva hvb hvc hl hm hv]
  push_cast
  ring

/-- **Additivity of Sorkin's angles.** Let `a`, `b`, `c` be non-null vectors with null
coordinates `(u_a, v_a)`, `(u_b, v_b)`, `(u_c, v_c)`, and `b = l a + m c` with `l, m > 0` (so `b`
lies inside the wedge spanned by `a` and `c`). Then the angle of the wedge `(a, c)` is the sum of
the angles of `(a, b)` and `(b, c)`, imaginary parts (light rays) included. -/
theorem sorkinAngle_add {ua va ub vb uc vc l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (hu : ub = l * ua + m * uc) (hv : vb = l * va + m * vc)
    (hua : ua ≠ 0) (hva : va ≠ 0) (hub : ub ≠ 0) (hvb : vb ≠ 0) (huc : uc ≠ 0) (hvc : vc ≠ 0) :
    sorkinAngle (ua * va) (uc * vc) ((ua * vc + uc * va) / 2) =
      sorkinAngle (ua * va) (ub * vb) ((ua * vb + ub * va) / 2) +
        sorkinAngle (ub * vb) (uc * vc) ((ub * vc + uc * vb) / 2) := by
  rcases le_total (ua * vc) (uc * va) with hor | hor
  · exact sorkinAngle_add_of_le hl hm hu hv hua hva hub hvb huc hvc hor
  · have h := sorkinAngle_add_of_le hm hl (by rw [hu]; ring) (by rw [hv]; ring)
      huc hvc hub hvb hua hva hor
    have e1 : sorkinAngle (ua * va) (uc * vc) ((ua * vc + uc * va) / 2) =
        sorkinAngle (uc * vc) (ua * va) ((uc * va + ua * vc) / 2) := by
      rw [add_comm (uc * va), sorkinAngle_comm]
    rw [e1, h, add_comm]
    congr 1 <;> rw [sorkinAngle_comm] <;> congr 1 <;> ring

/-! ## The full turn -/

/-- Rescaling both arguments by `c > 0` does not change whether they have opposite signs. -/
theorem signFlip_mul_left {c : ℝ} (hc : 0 < c) (x y : ℝ) :
    signFlip (c * x) (c * y) = signFlip x y := by
  have h : c * x * (c * y) < 0 ↔ x * y < 0 := by
    rw [show c * x * (c * y) = c ^ 2 * (x * y) by ring]
    have : 0 < c ^ 2 := by positivity
    constructor <;> intro h <;> nlinarith
  simp only [signFlip, h]

/-- Between two angles less than `π` apart at which `sin` does not vanish, `sin` changes sign
exactly when `⌊B/π⌋` increases (it increases by at most one). -/
theorem signFlip_sin {B B' : ℝ} (hB : sin B ≠ 0) (hB' : sin B' ≠ 0) (h1 : B < B')
    (h2 : B' < B + π) : (signFlip (sin B) (sin B') : ℤ) = ⌊B' / π⌋ - ⌊B / π⌋ := by
  have hπ := pi_pos
  have hfl : ∀ x : ℝ, (⌊x / π⌋ : ℝ) * π ≤ x ∧ x < ((⌊x / π⌋ : ℝ) + 1) * π := fun x =>
    ⟨by have := Int.floor_le (x / π); rwa [le_div_iff₀ hπ] at this,
      by have := Int.lt_floor_add_one (x / π); rwa [div_lt_iff₀ hπ] at this⟩
  have hs : ∀ (j : ℤ) (x : ℝ), (j : ℝ) * π ≤ x → x < (j + 1) * π → sin x ≠ 0 →
      0 < (-1 : ℝ) ^ j * sin x := by
    intro j x hj1 hj2 hx
    rw [← sin_sub_int_mul_pi]
    apply sin_pos_of_pos_of_lt_pi
    · rcases hj1.lt_or_eq with h | h
      · linarith
      · exact absurd (by rw [← h, sin_int_mul_pi]) hx
    · linarith
  have hkk : ⌊B / π⌋ ≤ ⌊B' / π⌋ := Int.floor_mono (div_le_div_of_nonneg_right h1.le hπ.le)
  have hkk' : ⌊B' / π⌋ ≤ ⌊B / π⌋ + 1 := by
    rw [← Int.floor_add_one]
    apply Int.floor_mono
    rw [div_add_one hπ.ne', div_le_div_iff_of_pos_right hπ]
    linarith
  have hsB := hs _ B (hfl B).1 (hfl B).2 hB
  have hsB' := hs _ B' (hfl B').1 (hfl B').2 hB'
  have hσ : (-1 : ℝ) ^ ⌊B / π⌋ = 1 ∨ (-1 : ℝ) ^ ⌊B / π⌋ = -1 := by
    rcases Int.even_or_odd ⌊B / π⌋ with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  rcases (show ⌊B' / π⌋ = ⌊B / π⌋ ∨ ⌊B' / π⌋ = ⌊B / π⌋ + 1 by omega) with he | he
  · rw [he] at hsB'
    have hp : 0 < sin B * sin B' := by
      rcases hσ with h | h <;> rw [h] at hsB hsB' <;> nlinarith
    simp only [signFlip, not_lt.2 hp.le, ↓reduceIte, he, sub_self, Nat.cast_zero]
  · rw [he, zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)] at hsB'
    have hn : sin B * sin B' < 0 := by
      rcases hσ with h | h <;> rw [h] at hsB hsB' <;> nlinarith
    simp only [signFlip, hn, ↓reduceIte, he]
    push_cast
    ring

/-- Along angles `B 0 < B 1 < ⋯ < B n = B 0 + 2π` with steps less than `π` and `sin (B k) ≠ 0`,
`sin` changes sign exactly twice. -/
theorem sum_signFlip_sin {n : ℕ} (B : ℕ → ℝ) (hB : ∀ k ≤ n, sin (B k) ≠ 0)
    (hst : ∀ i < n, B i < B (i + 1) ∧ B (i + 1) < B i + π) (hw : B n = B 0 + 2 * π) :
    ∑ i ∈ range n, signFlip (sin (B i)) (sin (B (i + 1))) = 2 := by
  have h : ((∑ i ∈ range n, signFlip (sin (B i)) (sin (B (i + 1))) : ℕ) : ℤ) = 2 := by
    push_cast
    rw [sum_congr rfl fun i hi => signFlip_sin (hB i (mem_range.1 hi).le)
      (hB (i + 1) (mem_range.1 hi)) (hst i (mem_range.1 hi)).1 (hst i (mem_range.1 hi)).2,
      sum_range_sub (fun k => ⌊B k / π⌋), hw,
      show (B 0 + 2 * π) / π = B 0 / π + ((2 : ℤ) : ℝ) by push_cast; field_simp,
      Int.floor_add_intCast]
    ring
  exact_mod_cast h

/-- The full turn for unit vectors `(cos α, sin α)` with a positively turning first wedge; see
`sum_sorkinAngle_eq`. -/
theorem sum_sorkinAngle_unit_of_pos {n : ℕ} (hn : 0 < n) (α : ℕ → ℝ)
    (hnull : ∀ k ≤ n, cos (2 * α k) ≠ 0)
    (hnd : ∀ i < n, sin (α (i + 1) - α i) ≠ 0)
    (hclose : cos (α n) = cos (α 0) ∧ sin (α n) = sin (α 0))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, Lightlike.Regge.InWedge (α i) (α (i + 1)) τ →
      ¬ Lightlike.Regge.InWedge (α j) (α (j + 1)) τ)
    (h0 : 0 < sin (α 1 - α 0)) :
    ∑ i ∈ range n, sorkinAngle (cos (2 * α i)) (cos (2 * α (i + 1))) (cos (α i + α (i + 1))) =
      -(2 * π) * Complex.I := by
  obtain ⟨A, hAdir, hAst, hw⟩ := Lightlike.Regge.exists_lift_of_pos hn α hnd hclose hdisj h0
  set u : ℕ → ℝ := fun k => cos (A k) + sin (A k) with hu
  set v : ℕ → ℝ := fun k => cos (A k) - sin (A k) with hv
  have h2 : ∀ k, cos (2 * α k) = u k * v k := fun k => by
    simp only [hu, hv]
    rw [cos_two_mul, ← (hAdir k).1]
    linear_combination sin_sq_add_cos_sq (A k)
  have hadd : ∀ k, cos (α k + α (k + 1)) = (u k * v (k + 1) + u (k + 1) * v k) / 2 := fun k => by
    simp only [hu, hv]
    rw [cos_add, ← (hAdir k).1, ← (hAdir k).2, ← (hAdir (k + 1)).1, ← (hAdir (k + 1)).2]
    ring
  have hor : ∀ i < n, u i * v (i + 1) ≤ u (i + 1) * v i := by
    intro i hi
    have h := sin_pos_of_pos_of_lt_pi (by linarith [(hAst i hi).1] : 0 < A (i + 1) - A i)
      (by linarith [(hAst i hi).2])
    rw [sin_sub] at h
    simp only [hu, hv]
    nlinarith
  have hne : ∀ k ≤ n, u k ≠ 0 ∧ v k ≠ 0 := fun k hk => by
    have h := hnull k hk
    rw [h2] at h
    exact ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
  have hθ : ∀ i ∈ range n,
      sorkinAngle (cos (2 * α i)) (cos (2 * α (i + 1))) (cos (α i + α (i + 1))) =
        ((rapidity (u (i + 1)) (v (i + 1)) - rapidity (u i) (v i) : ℝ) : ℂ) -
          ((π / 2 * ((signFlip (u i) (u (i + 1)) + signFlip (v i) (v (i + 1)) : ℕ) : ℝ) : ℝ) :
            ℂ) * Complex.I := by
    intro i hi
    have hi := mem_range.1 hi
    rw [h2, h2, hadd]
    exact sorkinAngle_null (hne i hi.le).1 (hne i hi.le).2 (hne (i + 1) hi).1 (hne (i + 1) hi).2
      (hor i hi)
  have hAn : A n = A 0 + 2 * π := by linarith
  have hre : ∑ i ∈ range n, (rapidity (u (i + 1)) (v (i + 1)) - rapidity (u i) (v i)) = 0 := by
    rw [sum_range_sub (fun k => rapidity (u k) (v k))]
    simp only [hu, hv, hAn, cos_add_two_pi, sin_add_two_pi, sub_self]
  have hs2 : √2 * (√2 / 2) = 1 := by
    rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hsu : ∀ k, u k = √2 * sin (A k + π / 4) := fun k => by
    simp only [hu]
    rw [sin_add, sin_pi_div_four, cos_pi_div_four]
    linear_combination (-(sin (A k) + cos (A k))) * hs2
  have hsv : ∀ k, v k = √2 * sin (A k + π / 4 + π / 2) := fun k => by
    simp only [hv]
    rw [sin_add_pi_div_two, cos_add, sin_pi_div_four, cos_pi_div_four]
    linear_combination (-(cos (A k) - sin (A k))) * hs2
  have h2pos : (0 : ℝ) < √2 := by positivity
  have hU : ∑ i ∈ range n, signFlip (u i) (u (i + 1)) = 2 := by
    simp only [hsu, signFlip_mul_left h2pos]
    refine sum_signFlip_sin (fun k => A k + π / 4) (fun k hk => ?_)
      (fun i hi => ⟨by linarith [(hAst i hi).1], by linarith [(hAst i hi).2]⟩) (by simp [hAn]; ring)
    have h := (hne k hk).1
    rw [hsu] at h
    exact right_ne_zero_of_mul h
  have hV : ∑ i ∈ range n, signFlip (v i) (v (i + 1)) = 2 := by
    simp only [hsv, signFlip_mul_left h2pos]
    refine sum_signFlip_sin (fun k => A k + π / 4 + π / 2) (fun k hk => ?_)
      (fun i hi => ⟨by linarith [(hAst i hi).1], by linarith [(hAst i hi).2]⟩) (by simp [hAn]; ring)
    have h := (hne k hk).2
    rw [hsv] at h
    exact right_ne_zero_of_mul h
  rw [sum_congr rfl hθ, sum_sub_distrib, ← sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
    hre, ← mul_sum, ← Nat.cast_sum, sum_add_distrib, hU, hV]
  push_cast
  ring

/-- **Non-overlapping wedges around a point add up to `−2πi`.** Let `P k = r k (cos α k, sin α k)`
(`k = 0, …, n`, `n ≥ 1`) be non-null vectors of a Minkowski plane in an orthonormal frame
`(e_x, e_t)`, so that `η(P k, P l) = r k r l cos (α k + α l)`, with `P n` in the direction of `P 0`,
no two consecutive ones parallel and the open wedges between consecutive vectors pairwise
disjoint (the hypotheses of `Lightlike.Regge.sum_arccos_cos_eq_two_pi`). Then Sorkin's angles of the
wedges add up to `−2πi`: the boost parts cancel and the wedges contain four light rays. -/
theorem sum_sorkinAngle_eq {n : ℕ} (hn : 0 < n) (α r : ℕ → ℝ) (hr : ∀ k ≤ n, 0 < r k)
    (hnull : ∀ k ≤ n, cos (2 * α k) ≠ 0)
    (hnd : ∀ i < n, sin (α (i + 1) - α i) ≠ 0)
    (hclose : cos (α n) = cos (α 0) ∧ sin (α n) = sin (α 0))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, Lightlike.Regge.InWedge (α i) (α (i + 1)) τ →
      ¬ Lightlike.Regge.InWedge (α j) (α (j + 1)) τ) :
    ∑ i ∈ range n, sorkinAngle (r i ^ 2 * cos (2 * α i)) (r (i + 1) ^ 2 * cos (2 * α (i + 1)))
      (r i * r (i + 1) * cos (α i + α (i + 1))) = -(2 * π) * Complex.I := by
  have hs : ∀ i ∈ range n,
      sorkinAngle (r i ^ 2 * cos (2 * α i)) (r (i + 1) ^ 2 * cos (2 * α (i + 1)))
        (r i * r (i + 1) * cos (α i + α (i + 1))) =
      sorkinAngle (cos (2 * α i)) (cos (2 * α (i + 1))) (cos (α i + α (i + 1))) := by
    intro i hi
    have := mem_range.1 hi
    exact sorkinAngle_scale (hr i (by omega)) (hr (i + 1) (by omega)) _ _ _
  rw [sum_congr rfl hs]
  rcases lt_or_gt_of_ne (hnd 0 hn) with hneg | hpos
  · -- reflect `t ↦ -t`: apply the positive case to `-α`; the inner products do not change
    have h := sum_sorkinAngle_unit_of_pos hn (fun i => -α i)
      (fun k hk => by rw [mul_neg, cos_neg]; exact hnull k hk)
      (fun i hi => by
        rw [show -α (i + 1) - -α i = -(α (i + 1) - α i) by ring, sin_neg, neg_ne_zero]
        exact hnd i hi)
      (by simp only [cos_neg, sin_neg, hclose.1, hclose.2, and_self])
      (fun i hi j hj hij τ h1 h2 => hdisj i hi j hj hij (-τ)
        (by simpa using h1.neg) (by simpa using h2.neg))
      (by rw [show -α (0 + 1) - -α 0 = -(α 1 - α 0) by simp; ring, sin_neg]; linarith)
    simpa only [mul_neg, cos_neg, ← neg_add] using h
  · exact sum_sorkinAngle_unit_of_pos hn α hnull hnd hclose hdisj (by simpa using hpos)

end Lightlike.ReggeLor
