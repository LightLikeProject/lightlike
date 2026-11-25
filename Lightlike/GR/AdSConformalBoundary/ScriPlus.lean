import Lightlike.GR.ConformalPoincare

/-!
# Future null infinity of Minkowski space and the time translation on it

In the compactified coordinates `(T, R, θ, φ)` of `compactify` (`ũ± = T ± R = arctan (t ± r)`), future null infinity
`I⁺` is the set `ũ₊ = π/2`, `|ũ₋| < π/2` (`scriPlus`), parametrised by the retarded time `u = tan ũ₋`
and the angles (`scriPoint`). Outgoing null rays `t - r = u` converge to `scriPoint u θ φ`
(`compactify_tendsto_scriPoint`), the conformal factor `cos² ũ₊ cos² ũ₋` of `compactMetric` vanishes on `I⁺`
(`scriFactor_scriPlus`), and the time translation `t ↦ t + a` extends to `I⁺` as the translation `u ↦ u + a` of
retarded time (`scriTimeShift_scriPoint`).

Gap row GE7 (null infinity of Minkowski space and the action of the isometry group on it). Sources read: D. Harlow,
*Jerusalem Lectures on Black Holes and Quantum Information*, arXiv:1409.1231, section 2.3 (the coordinates
`T ± R = arctan (t ± r)`); Aharony-Gubser-Maldacena-Ooguri-Oz, arXiv:hep-th/9905111, section 2.2 (`u± = tan ũ±`).
-/

open Matrix Real Filter Topology

noncomputable section

namespace Lightlike

/-- Future null infinity `I⁺` of Minkowski space in the compactified coordinates `(T, R, θ, φ)`:
`T + R = π/2` and `|T - R| < π/2` (the angles `θ, φ` are unrestricted). -/
def scriPlus : Set (Fin 4 → ℝ) := {p | p 0 + p 1 = π / 2 ∧ |p 0 - p 1| < π / 2}

/-- The point of `I⁺` of retarded time `u` and angles `(θ, φ)`: `T + R = π/2`, `T - R = arctan u`. -/
def scriPoint (u θ φ : ℝ) : Fin 4 → ℝ := ![(π / 2 + arctan u) / 2, (π / 2 - arctan u) / 2, θ, φ]

/-- The conformal factor `cos²(T + R) cos²(T - R)` as a function on the compactified space. -/
def scriFactor (p : Fin 4 → ℝ) : ℝ := cos (p 0 + p 1) ^ 2 * cos (p 0 - p 1) ^ 2

/-- Every `scriPoint` lies on `I⁺`. -/
theorem scriPoint_mem (u θ φ : ℝ) : scriPoint u θ φ ∈ scriPlus := by
  have h1 := Real.neg_pi_div_two_lt_arctan u
  have h2 := Real.arctan_lt_pi_div_two u
  refine ⟨by simp [scriPoint]; ring, ?_⟩
  simp only [scriPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [abs_lt]; constructor <;> linarith

/-- `I⁺` is exactly the set of the points `scriPoint u θ φ`: every point of `I⁺` is `scriPoint` of its
retarded time `u = tan (T - R)` and its angles. -/
theorem scriPlus_eq_range : scriPlus = Set.range (fun x : ℝ × ℝ × ℝ => scriPoint x.1 x.2.1 x.2.2) := by
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    rw [abs_lt] at h2
    refine ⟨(tan (p 0 - p 1), p 2, p 3), ?_⟩
    simp only
    have ha : arctan (tan (p 0 - p 1)) = p 0 - p 1 :=
      Real.arctan_tan (by linarith [h2.1]) (by linarith [h2.2])
    ext i
    fin_cases i
    · simp [scriPoint, ha]; linarith
    · simp [scriPoint, ha]; linarith
    · simp [scriPoint]
    · simp [scriPoint]
  · rintro ⟨x, rfl⟩
    exact scriPoint_mem _ _ _

/-- **The conformal factor vanishes on future null infinity.** -/
theorem scriFactor_scriPlus {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) : scriFactor p = 0 := by
  simp [scriFactor, hp.1]

/-- On the image of `compactify` the factor `scriFactor` is the conformal factor `conformalFactor` of the
compactification. -/
theorem scriFactor_compactify (y : Fin 4 → ℝ) : scriFactor (compactify y) = conformalFactor y := by
  have hp : compactify y 0 + compactify y 1 = arctan (y 0 + y 1) := by simp [compactify]; ring
  have hm : compactify y 0 - compactify y 1 = arctan (y 0 - y 1) := by simp [compactify]; ring
  have key : ∀ x : ℝ, cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) := fun x => by
    rw [Real.cos_arctan, div_pow, Real.sq_sqrt (by positivity)]; simp
  rw [scriFactor, hp, hm, key, key, conformalFactor, one_div_mul_one_div]

/-- **Outgoing null rays reach null infinity**: along the ray `t - r = u`, `r → ∞`, with fixed angles, the point
`compactify (u + r, r, θ, φ)` converges to the point `scriPoint u θ φ` of `I⁺`. -/
theorem compactify_tendsto_scriPoint (u θ φ : ℝ) :
    Tendsto (fun r : ℝ => compactify ![u + r, r, θ, φ]) atTop (𝓝 (scriPoint u θ φ)) := by
  have h2 : Tendsto (fun r : ℝ => arctan (u + 2 * r)) atTop (𝓝 (π / 2)) := by
    have : Tendsto (fun r : ℝ => u + 2 * r) atTop atTop :=
      tendsto_atTop_add_const_left _ u (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    exact Real.tendsto_arctan_atTop.comp this |>.mono_right nhdsWithin_le_nhds
  have e : ∀ r : ℝ, arctan (u + r + r) = arctan (u + 2 * r) := fun r => by ring_nf
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · have := (h2.add_const (arctan u)).div_const 2
    simpa [compactify, scriPoint, e] using this
  · have := (h2.sub_const (arctan u)).div_const 2
    simpa [compactify, scriPoint, e, sub_eq_add_neg] using this
  · simp [compactify, scriPoint]
  · simp [compactify, scriPoint]

/-- The time translation `t ↦ t + a` acting on the compactified coordinates of `I⁺`: it moves the retarded
null coordinate `ũ₋ = T - R` by `timeShift a` and fixes `ũ₊ = π/2` and the angles. -/
def scriTimeShift (a : ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(π / 2 + timeShift a (p 0 - p 1)) / 2, (π / 2 - timeShift a (p 0 - p 1)) / 2, p 2, p 3]

/-- **The time translation acts on `I⁺` by translating the retarded time**: `u ↦ u + a`. -/
theorem scriTimeShift_scriPoint (a u θ φ : ℝ) :
    scriTimeShift a (scriPoint u θ φ) = scriPoint (u + a) θ φ := by
  have h : (scriPoint u θ φ) 0 - (scriPoint u θ φ) 1 = arctan u := by simp [scriPoint]; ring
  have h2 : timeShift a (arctan u) = arctan (u + a) := by
    unfold timeShift; rw [Real.tan_arctan]
  unfold scriTimeShift
  rw [h, h2]
  simp [scriPoint]

/-- The time translation maps `I⁺` into itself. -/
theorem scriTimeShift_mem {a : ℝ} {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) : scriTimeShift a p ∈ scriPlus := by
  rw [scriPlus_eq_range] at hp ⊢
  obtain ⟨x, rfl⟩ := hp
  exact ⟨(x.1 + a, x.2), (scriTimeShift_scriPoint a _ _ _).symm⟩

end Lightlike
