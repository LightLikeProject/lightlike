import Lightlike.GR.GERow016.ScriPlus

/-!
# Rotations about the polar axis act on future null infinity by `φ ↦ φ + α`

Pass-4 extension of gap row GE7. In the spherical chart `(t, r, θ, φ)` the rotation about the `x₃`-axis by the
angle `α` is `sphRotate α : φ ↦ φ + α`. It commutes with `compactify` (`compactify_sphRotate`), extends to
`I⁺` as `scriRotate α` (`scriRotate_scriPoint`: it fixes the retarded time and shifts `φ`), preserves `I⁺`
(`scriRotate_mem`), is a group action (`scriRotate_comp`, `scriRotate_zero`) and is compatible with outgoing
null rays (`compactify_sphRotate_tendsto_scriPoint`).

Sources read: Aharony-Gubser-Maldacena-Ooguri-Oz, arXiv:hep-th/9905111, section 2.2.
-/

open Matrix Real Filter Topology

noncomputable section

namespace Lightlike

/-- Rotation about the polar axis by `α` in the spherical chart `(t, r, θ, φ)`: `φ ↦ φ + α`. -/
def sphRotate (α : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ := ![y 0, y 1, y 2, y 3 + α]

/-- `compactify` intertwines the rotation with the shift of the last compactified coordinate. -/
theorem compactify_sphRotate (α : ℝ) (y : Fin 4 → ℝ) :
    compactify (sphRotate α y) = ![compactify y 0, compactify y 1, compactify y 2, compactify y 3 + α] := by
  ext i
  fin_cases i <;> simp [compactify, sphRotate]

/-- The rotation acting on the compactified coordinates of `I⁺`: it shifts `φ` and fixes the other coordinates. -/
def scriRotate (α : ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℝ := ![p 0, p 1, p 2, p 3 + α]

/-- **Rotations act on `I⁺` by shifting the azimuth**: the retarded time and `θ` are fixed. -/
theorem scriRotate_scriPoint (α u θ φ : ℝ) :
    scriRotate α (scriPoint u θ φ) = scriPoint u θ (φ + α) := by
  ext i
  fin_cases i <;> simp [scriRotate, scriPoint]

/-- The rotation maps `I⁺` into itself. -/
theorem scriRotate_mem {α : ℝ} {p : Fin 4 → ℝ} (hp : p ∈ scriPlus) : scriRotate α p ∈ scriPlus := by
  obtain ⟨h1, h2⟩ := hp
  exact ⟨by simpa [scriRotate] using h1, by simpa [scriRotate] using h2⟩

/-- **Group law**: `scriRotate α ∘ scriRotate β = scriRotate (α + β)`. -/
theorem scriRotate_comp (α β : ℝ) (p : Fin 4 → ℝ) :
    scriRotate α (scriRotate β p) = scriRotate (β + α) p := by
  ext i
  fin_cases i
  all_goals simp [scriRotate]
  ring

/-- The rotation by `0` is the identity. -/
theorem scriRotate_zero (p : Fin 4 → ℝ) : scriRotate 0 p = p := by
  ext i
  fin_cases i <;> simp [scriRotate]

/-- **The rotation is compatible with null rays**: the rotated outgoing ray `(u + r, r, θ, φ + α)` converges to
`scriRotate α (scriPoint u θ φ)`. -/
theorem compactify_sphRotate_tendsto_scriPoint (α u θ φ : ℝ) :
    Tendsto (fun r : ℝ => compactify (sphRotate α ![u + r, r, θ, φ])) atTop
      (𝓝 (scriRotate α (scriPoint u θ φ))) := by
  rw [scriRotate_scriPoint]
  have h := compactify_tendsto_scriPoint u θ (φ + α)
  refine h.congr (fun r => ?_)
  congr 1

end Lightlike
