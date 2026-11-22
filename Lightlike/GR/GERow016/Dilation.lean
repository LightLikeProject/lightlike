import Lightlike.GR.GERow016.ScriPlus
import Lightlike.GR.GERow016.Similarity

/-!
# Dilations act on future null infinity by rescaling retarded time

Pass-4 extension of gap row GE7. In the spherical chart `(t, r, θ, φ)` the dilation `x ↦ c x` of Minkowski space is
`sphDilate c : (t, r, θ, φ) ↦ (c t, c r, θ, φ)` (`sph_sphDilate`). On the null coordinates
`ũ± = arctan (t ± r)` of `compactify` it acts as `ũ ↦ arctan (c tan ũ)` (`compactify_sphDilate`). It extends to
`I⁺` as `scriDilate c`, which is the rescaling `u ↦ c u` of retarded time (`scriDilate_scriPoint`); this is an
action of the multiplicative monoid (`scriDilate_comp`, `scriDilate_one`), it preserves `I⁺`
(`scriDilate_mem`), and it is compatible with outgoing null rays (`compactify_sphDilate_tendsto_scriPoint`).

Sources read: Aharony-Gubser-Maldacena-Ooguri-Oz, arXiv:hep-th/9905111, section 2.2.
-/

open Matrix Real Filter Topology

noncomputable section

namespace Lightlike

/-- The dilation `x ↦ c x` in the spherical chart `(t, r, θ, φ)`: it scales `t` and `r` and fixes the angles. -/
def sphDilate (c : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![c * y 0, c * y 1, y 2, y 3]

/-- The chart `sph` intertwines `sphDilate c` with the Cartesian dilation `x ↦ c x`. -/
theorem sph_sphDilate (c : ℝ) (y : Fin 4 → ℝ) : sph (sphDilate c y) = c • sph y := by
  ext i
  fin_cases i <;> simp [sph, sphDilate] <;> ring

/-- The action of the dilation on a null coordinate: `ũ ↦ arctan (c tan ũ)`. -/
def dilAng (c u : ℝ) : ℝ := arctan (c * tan u)

/-- **The dilation on the null coordinates of the compactification**: `ũ± = T ± R` is sent to
`arctan (c tan ũ±)`. -/
theorem compactify_sphDilate (c : ℝ) (y : Fin 4 → ℝ) :
    compactify (sphDilate c y) 0 + compactify (sphDilate c y) 1 =
        dilAng c (compactify y 0 + compactify y 1) ∧
      compactify (sphDilate c y) 0 - compactify (sphDilate c y) 1 =
        dilAng c (compactify y 0 - compactify y 1) := by
  have hp : ∀ z : Fin 4 → ℝ, compactify z 0 + compactify z 1 = arctan (z 0 + z 1) := fun z => by
    simp [compactify]; ring
  have hm : ∀ z : Fin 4 → ℝ, compactify z 0 - compactify z 1 = arctan (z 0 - z 1) := fun z => by
    simp [compactify]; ring
  constructor
  · rw [hp, hp, dilAng, Real.tan_arctan]; simp [sphDilate]; ring_nf
  · rw [hm, hm, dilAng, Real.tan_arctan]; simp [sphDilate]; ring_nf

/-- The dilation acting on the compactified coordinates of `I⁺`: it moves `ũ₋ = T - R` to `dilAng c ũ₋` and fixes
`ũ₊ = π/2` and the angles. -/
def scriDilate (c : ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(π / 2 + dilAng c (p 0 - p 1)) / 2, (π / 2 - dilAng c (p 0 - p 1)) / 2, p 2, p 3]

/-- **Dilations act on `I⁺` by rescaling the retarded time**: `u ↦ c u`. -/
theorem scriDilate_scriPoint (c u θ φ : ℝ) :
    scriDilate c (scriPoint u θ φ) = scriPoint (c * u) θ φ := by
  have h : (scriPoint u θ φ) 0 - (scriPoint u θ φ) 1 = arctan u := by simp [scriPoint]; ring
  unfold scriDilate
  rw [h, dilAng, Real.tan_arctan]
  simp [scriPoint]

/-- The dilation maps `I⁺` into itself. -/
theorem scriDilate_mem {c : ℝ} {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) : scriDilate c p ∈ scriPlus := by
  rw [scriPlus_eq_range] at hp ⊢
  obtain ⟨x, rfl⟩ := hp
  exact ⟨(c * x.1, x.2), (scriDilate_scriPoint c _ _ _).symm⟩

/-- **Group law**: `scriDilate c ∘ scriDilate d = scriDilate (c d)` on `I⁺`. -/
theorem scriDilate_comp (c d : ℝ) {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) :
    scriDilate c (scriDilate d p) = scriDilate (c * d) p := by
  rw [scriPlus_eq_range] at hp
  obtain ⟨x, rfl⟩ := hp
  rw [scriDilate_scriPoint, scriDilate_scriPoint, scriDilate_scriPoint, mul_assoc]

/-- The dilation by `1` is the identity on `I⁺`. -/
theorem scriDilate_one {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) : scriDilate 1 p = p := by
  rw [scriPlus_eq_range] at hp
  obtain ⟨x, rfl⟩ := hp
  rw [scriDilate_scriPoint, one_mul]

/-- For `c > 0`, the dilation is a bijection of `I⁺` with inverse `scriDilate c⁻¹`. -/
theorem scriDilate_inv {c : ℝ} (hc : c ≠ 0) {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) :
    scriDilate c⁻¹ (scriDilate c p) = p := by
  rw [scriDilate_comp _ _ hp, inv_mul_cancel₀ hc, scriDilate_one hp]

/-- **The dilation is compatible with null rays**: for `c > 0` the dilated outgoing ray `t - r = u`
(i.e. `(c(u + r), c r, θ, φ)`) converges to the point `scriPoint (c u) θ φ = scriDilate c (scriPoint u θ φ)`
of `I⁺`. -/
theorem compactify_sphDilate_tendsto_scriPoint {c : ℝ} (hc : 0 < c) (u θ φ : ℝ) :
    Tendsto (fun r : ℝ => compactify (sphDilate c ![u + r, r, θ, φ])) atTop
      (𝓝 (scriDilate c (scriPoint u θ φ))) := by
  rw [scriDilate_scriPoint]
  have h := (compactify_tendsto_scriPoint (c * u) θ φ).comp
    (tendsto_id.const_mul_atTop hc : Tendsto (fun r : ℝ => c * r) atTop atTop)
  refine h.congr (fun r => ?_)
  simp only [Function.comp, sphDilate]
  congr 1
  ext i
  fin_cases i
  · simp; ring
  all_goals simp

end Lightlike
