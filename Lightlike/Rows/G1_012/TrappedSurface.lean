import Lightlike.Rows.G1_012.NullGeodCausal
import Lightlike.Spacetime.Connection

/-!
# Closed trapped surfaces on a manifold (G1-012)

A **closed trapped surface** `S` in a space-time `(M, g)` with Levi-Civita connection `∇` and time orientation `T`
(Penrose 1965; Hawking–Ellis 1973, §8.1; Senovilla–Garfinkle 2015, §2): a compact spacelike surface of codimension
two whose two families of future null normals both converge, `θ < 0`.

**Weaker than the textbook "embedded submanifold"** (difference approved as `weaker`): `S` is a **regular level
set** `S = f⁻¹(0)` of a smooth map `f : M → ℝ²` with surjective derivative along `S`, so that `T_x S = ker df_x`
has dimension `n - 2` with no submanifold theory. A regular level set has a trivial normal bundle, so this covers
a proper subclass of the closed embedded codimension-two surfaces (those with trivial normal bundle, for example
the round spheres of a Schwarzschild slice). The expansion of a null normal field `k` along `S` is
`θ_k(x) = Σᵢ g(∇_{eᵢ} k, eᵢ)` for a `g`-orthonormal basis `(eᵢ)` of `T_x S` (independent of the basis); as for
`Trapped.IsTrappedSphere` (G1-011) the surface is trapped if **every** smooth future null normal field has `θ_k < 0`
on `S` (both families at once, since both are future null normal fields). Spacelikeness of `S` is not a separate
clause: an orthonormal basis of `T_x S` is required to exist at each point.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- `k x` is a **future-directed null normal** of the level set `{f = 0}` at `x`: non-zero, null, orthogonal to
`ker df_x`, and `g(k, T) < 0`. -/
def IsFutureNullNormalAt (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (T : Causal.TimeOrientation g)
    (f : M → Fin 2 → ℝ) (x : M) (k : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) : Prop :=
  k ≠ 0 ∧ g.g x k k = 0 ∧ (∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 →
    g.g x k v = 0) ∧ g.g x k (T.X x) < 0

/-- The **expansion** `Σᵢ g(∇_{eᵢ} k, eᵢ)` of the field `k` along an orthonormal frame `e` of `T_x S`. -/
def frameExpansion (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)
    (k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (x : M) (e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x) : ℝ :=
  ∑ i, g.g x (cov k x (e i)) (e i)

/-- **Closed trapped surface** `S`: compact, a regular level set `f⁻¹(0)` of a smooth `f : M → ℝ²`, and every smooth
field that is a future null normal along `S` has negative expansion along every `g`-orthonormal frame of `T_x S` at
every `x ∈ S`. -/
def IsClosedTrappedSurface (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (cov : Connection 𝓘(ℝ, Fin n → ℝ) M)
    (T : Causal.TimeOrientation g) (S : Set M) : Prop :=
  IsCompact S ∧ S.Nonempty ∧ ∃ f : M → Fin 2 → ℝ,
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f ∧ S = f ⁻¹' {0} ∧
    (∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x)) ∧
    ∀ k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p,
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) →
      (∀ x ∈ S, IsFutureNullNormalAt g T f x (k x)) →
      ∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
        (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) →
        frameExpansion g cov k x e < 0

end Lightlike.Penrose
