import Mathlib

/-!
# The Rindler wedge of 1+1 Minkowski space and its boost group

Row G1-049 (milestone SC1, the Unruh effect in coordinates).  Points of `ℝ × ℝ` are `(t, x)` with the
interval `t² - x²`.  The right Rindler wedge is `{x > |t|}`; Rindler coordinates `(η, ξ)` with
acceleration parameter `a > 0` are
`t = (e^{aξ}/a) sinh (aη)`, `x = (e^{aξ}/a) cosh (aη)`
(the line `ξ = 0` is the uniformly accelerated observer with proper acceleration `a`, and `η` is its proper
time).  We prove that this map is onto the wedge, that the wedge is invariant under the boost group, and that
translating `η` by `s / a` is the boost of rapidity `s` (the wedge boost group of SC2).

## Main statements

* `rindlerMap_mem_wedge`, `exists_rindlerMap_eq`: Rindler coordinates cover exactly the wedge.
* `boost_rindlerMap`: the boost of rapidity `s` is the `η`-translation by `s / a`.
* `boost_mem_wedge`, `boost_add`, `boost_interval`: the boosts form a group of the wedge's isometries.
-/

namespace Lightlike.Rows.G1_049

open Real

/-- The right Rindler wedge `{(t, x) | |t| < x}` of 1+1 Minkowski space. -/
def rindlerWedge : Set (ℝ × ℝ) := {p | |p.1| < p.2}

/-- **Rindler coordinates** `(η, ξ) ↦ (t, x)` with acceleration parameter `a`:
`t = (e^{aξ}/a) sinh (aη)`, `x = (e^{aξ}/a) cosh (aη)`. -/
noncomputable def rindlerMap (a η ξ : ℝ) : ℝ × ℝ :=
  (exp (a * ξ) / a * sinh (a * η), exp (a * ξ) / a * cosh (a * η))

/-- The Lorentz boost of rapidity `s` on `(t, x)`. -/
noncomputable def boost (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * cosh s + p.2 * sinh s, p.2 * cosh s + p.1 * sinh s)

/-- The Minkowski interval `x² - t²` (positive inside the wedge). -/
def interval (p : ℝ × ℝ) : ℝ := p.2 ^ 2 - p.1 ^ 2

/-- Rindler coordinates land in the wedge when `a > 0`. -/
theorem rindlerMap_mem_wedge {a : ℝ} (ha : 0 < a) (η ξ : ℝ) : rindlerMap a η ξ ∈ rindlerWedge := by
  have hp : 0 < exp (a * ξ) / a := div_pos (exp_pos _) ha
  show |exp (a * ξ) / a * sinh (a * η)| < exp (a * ξ) / a * cosh (a * η)
  rw [abs_mul, abs_of_pos hp]
  refine mul_lt_mul_of_pos_left (abs_lt_of_sq_lt_sq ?_ (cosh_pos _).le) hp
  nlinarith [cosh_sq (a * η)]

/-- The interval of a point with Rindler coordinates is `(e^{aξ}/a)²`. -/
theorem interval_rindlerMap {a : ℝ} (η ξ : ℝ) :
    interval (rindlerMap a η ξ) = (exp (a * ξ) / a) ^ 2 := by
  unfold interval rindlerMap
  have := cosh_sq (a * η)
  simp only
  linear_combination (exp (a * ξ) / a) ^ 2 * this

/-- **Rindler coordinates cover exactly the wedge**: every point of the wedge has Rindler coordinates. -/
theorem exists_rindlerMap_eq {a : ℝ} (ha : 0 < a) {p : ℝ × ℝ} (hp : p ∈ rindlerWedge) :
    ∃ η ξ : ℝ, rindlerMap a η ξ = p := by
  obtain ⟨t, x⟩ := p
  have hx : |t| < x := hp
  have hx0 : 0 < x := lt_of_le_of_lt (abs_nonneg t) hx
  have hsq : t ^ 2 < x ^ 2 := by simpa [sq_abs] using (sq_lt_sq' (by linarith [neg_abs_le t]) (by linarith [le_abs_self t]))
  have hd : 0 < x ^ 2 - t ^ 2 := by linarith
  set r := Real.sqrt (x ^ 2 - t ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hd
  have hr2 : r ^ 2 = x ^ 2 - t ^ 2 := Real.sq_sqrt hd.le
  refine ⟨arsinh (t / r) / a, Real.log (a * r) / a, ?_⟩
  have h1 : a * (arsinh (t / r) / a) = arsinh (t / r) := by field_simp
  have h2 : a * (Real.log (a * r) / a) = Real.log (a * r) := by field_simp
  have hch : cosh (arsinh (t / r)) = x / r := by
    rw [cosh_arsinh]
    have : 1 + (t / r) ^ 2 = (x / r) ^ 2 := by
      field_simp
      linarith
    rw [this]
    exact Real.sqrt_sq (div_pos hx0 hr0).le
  unfold rindlerMap
  rw [h1, h2, sinh_arsinh, hch, Real.exp_log (mul_pos ha hr0)]
  ext
  · simp only
    field_simp
  · simp only
    field_simp

/-- A boost of rapidity `s` preserves the interval. -/
theorem boost_interval (s : ℝ) (p : ℝ × ℝ) : interval (boost s p) = interval p := by
  unfold interval boost
  have := cosh_sq s
  simp only
  linear_combination (p.2 ^ 2 - p.1 ^ 2) * this

/-- Boosts compose by adding rapidities: they form a one-parameter group. -/
theorem boost_add (s r : ℝ) (p : ℝ × ℝ) : boost s (boost r p) = boost (s + r) p := by
  unfold boost
  ext
  · simp only [cosh_add, sinh_add]
    ring
  · simp only [cosh_add, sinh_add]
    ring

/-- The boost of rapidity `0` is the identity. -/
theorem boost_zero (p : ℝ × ℝ) : boost 0 p = p := by
  simp [boost]

/-- **The boost of rapidity `s` is the translation `η ↦ η + s / a` in Rindler coordinates.** -/
theorem boost_rindlerMap {a : ℝ} (ha : a ≠ 0) (s η ξ : ℝ) :
    boost s (rindlerMap a η ξ) = rindlerMap a (η + s / a) ξ := by
  have h : a * (η + s / a) = a * η + s := by field_simp
  unfold boost rindlerMap
  rw [h]
  ext
  · simp only [sinh_add]
    ring
  · simp only [cosh_add]
    ring

/-- The wedge is invariant under every boost. -/
theorem boost_mem_wedge {a : ℝ} (ha : 0 < a) (s : ℝ) {p : ℝ × ℝ} (hp : p ∈ rindlerWedge) :
    boost s p ∈ rindlerWedge := by
  obtain ⟨η, ξ, rfl⟩ := exists_rindlerMap_eq ha hp
  rw [boost_rindlerMap ha.ne']
  exact rindlerMap_mem_wedge ha _ _

end Lightlike.Rows.G1_049
