import Lightlike.Spacetime.PenroseSingularity.TrappedSurface

/-!
# Closed trapped spacelike surfaces (G1-012)

`IsClosedTrappedSurface` (in `TrappedSurface.lean`) is vacuous at the points `x ∈ S` where `T_x S = ker df_x`
is not spacelike: its expansion clause only constrains `g`-orthonormal `(n-2)`-frames of `T_x S`, and
there is none if `T_x S` contains a null or timelike vector. The textbook notion (Penrose 1965;
Senovilla–Garfinkle 2015, §2) is a closed **spacelike** surface. `IsClosedTrappedSpacelikeSurface` adds
that clause, with the same defining map `f`; the old definition is kept unchanged.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

/-- **Closed trapped spacelike surface**: `IsClosedTrappedSurface` (same `f`, same expansion clause) with the
additional clause that `T_x S = ker df_x` is spacelike at every `x ∈ S`. -/
def IsClosedTrappedSpacelikeSurface (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    (cov : Connection 𝓘(ℝ, Fin n → ℝ) M) (T : Causal.TimeOrientation g) (S : Set M) : Prop :=
  IsCompact S ∧ S.Nonempty ∧ ∃ f : M → Fin 2 → ℝ,
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f ∧ S = f ⁻¹' {0} ∧
    (∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x)) ∧
    (∀ x ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x v = 0 → v ≠ 0 → 0 < g.g x v v) ∧
    ∀ k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p,
      ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
        (fun q : M => (⟨q, k q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) →
      (∀ x ∈ S, IsFutureNullNormalAt g T f x (k x)) →
      ∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
        (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) →
        frameExpansion g cov k x e < 0

/-- A closed trapped spacelike surface is a closed trapped surface. -/
theorem IsClosedTrappedSpacelikeSurface.toIsClosedTrappedSurface
    {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} {cov : Connection 𝓘(ℝ, Fin n → ℝ) M}
    {T : Causal.TimeOrientation g} {S : Set M} (h : IsClosedTrappedSpacelikeSurface g cov T S) :
    IsClosedTrappedSurface g cov T S := by
  obtain ⟨hc, hne, f, hf, hS, hsub, -, hk⟩ := h
  exact ⟨hc, hne, f, hf, hS, hsub, hk⟩

end Lightlike.Penrose
