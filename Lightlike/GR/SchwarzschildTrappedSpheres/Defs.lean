import Lightlike.GR.Schwarzschild
import Lightlike.Spacetime.RaychaudhuriCoord

/-!
# Trapped coordinate spheres (row G1-011)

Coordinate-level definitions for "closed trapped surface" (milestone GE4, Penrose's theorem), for a
metric `g` on `ℝ⁴` in a chart `(y 0, y 1, y 2, y 3)` and a round sphere `{y 0 = t₀, y 1 = r₀}`
whose tangent directions are `∂₂, ∂₃` (`0 < y 2 < π`; the two poles lie in another chart).

* `Trapped.bil g y u v = g_{μν}(y) uᵘ vᵛ`.
* `Trapped.nullExpansion g k y`: the expansion of the null vector field `k` along the sphere,
  `θ_k = hᴬᴮ g(∇_A k, e_B)` with `h` the induced metric, `∇_A kᵘ = ∂_A kᵘ + Γᵘ_{Ac} kᶜ`.
* `Trapped.IsFutureNullNormal g T k y`: `k(y)` is nonzero, null, orthogonal to `∂₂, ∂₃`, and
  future directed for the time-orientation vector `T` (`g(k, T) < 0`).
* `Trapped.IsTrappedSphere g T t₀ r₀`: both future null normals have negative expansion.
-/

open Matrix Real

noncomputable section

namespace Lightlike
namespace Trapped

/-- The bilinear form `g_{μν}(y) uᵘ vᵛ`. -/
def bil (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (y u v : Fin 4 → ℝ) : ℝ :=
  ∑ μ, ∑ ν, u μ * g y μ ν * v ν

/-- The two tangent coordinate directions `∂₂, ∂₃` of the coordinate sphere. -/
def tan : Fin 2 → Fin 4 := ![2, 3]

/-- The induced metric `h_{AB} = g_{tan A, tan B}` on the sphere. -/
def sphereMetric (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun A B => g y (tan A) (tan B)

/-- The null expansion `θ_k = hᴬᴮ g(∇_A k, e_B)` of a vector field `k` along the coordinate sphere. -/
def nullExpansion (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (k : (Fin 4 → ℝ) → Fin 4 → ℝ)
    (y : Fin 4 → ℝ) : ℝ :=
  ∑ A, ∑ B, (sphereMetric g y)⁻¹ A B *
    ∑ μ, g y μ (tan B) * covD g k μ (tan A) y

/-- `k(y)` is a future-directed null normal of the coordinate sphere through `y`, the future being
that of the time-orientation vector `T`: nonzero, null, orthogonal to `∂₂, ∂₃`, and `g(k, T) < 0`. -/
def IsFutureNullNormal (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (T : Fin 4 → ℝ)
    (k : Fin 4 → ℝ) (y : Fin 4 → ℝ) : Prop :=
  k ≠ 0 ∧ bil g y k k = 0 ∧ (∀ A, bil g y k (Pi.single (tan A) 1) = 0) ∧ bil g y k T < 0

/-- The coordinate sphere `{y 0 = t₀, y 1 = r₀, 0 < y 2 < π}`. -/
def sphere (t₀ r₀ : ℝ) : Set (Fin 4 → ℝ) := {y | y 0 = t₀ ∧ y 1 = r₀ ∧ 0 < y 2 ∧ y 2 < π}

/-- The coordinate sphere `(t₀, r₀)` is **trapped** for the time orientation `T`: every vector field
`k`, future-directed null normal along the sphere, has negative expansion on it. -/
def IsTrappedSphere (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (T : Fin 4 → ℝ) (t₀ r₀ : ℝ) :
    Prop :=
  ∀ k : (Fin 4 → ℝ) → Fin 4 → ℝ, (∀ y ∈ sphere t₀ r₀, IsFutureNullNormal g T (k y) y) →
    ∀ y ∈ sphere t₀ r₀, nullExpansion g k y < 0

end Trapped
end Lightlike
