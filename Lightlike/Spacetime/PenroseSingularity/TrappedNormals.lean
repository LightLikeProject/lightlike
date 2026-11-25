import Lightlike.Spacetime.PenroseSingularity.NullNormalField

/-!
# The two global null normal fields of a closed trapped spacelike surface (G1-012, step D2)

For `S` a closed trapped spacelike surface there are two smooth global fields `k₁, k₂` on `M` which are
future null normals along `S`, every future null normal at a point of `S` is a positive multiple of one of
them, and both have negative expansion on `S` (the trapped hypothesis applied to them).
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [T2Space M]
  [SecondCountableTopology M]

open Lightlike.Causal NullNormal in
/-- **The null normals of a closed trapped spacelike surface.** -/
theorem exists_null_normal_pair {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} {T : TimeOrientation g} {S : Set M}
    (h : IsClosedTrappedSpacelikeSurface g cov T S) :
    ∃ f : M → Fin 2 → ℝ, ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) ∞ f ∧ S = f ⁻¹' {0} ∧
      (∀ x ∈ S, Function.Surjective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x)) ∧
      ∃ k₁ k₂ : (x : M) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
        ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
          (fun q : M => (⟨q, k₁ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧
        ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
          (fun q : M => (⟨q, k₂ q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) ∧
        (∀ x ∈ S, IsFutureNullNormalAt g T f x (k₁ x) ∧ IsFutureNullNormalAt g T f x (k₂ x)) ∧
        (∀ x ∈ S, ∀ ν : TangentSpace 𝓘(ℝ, Fin n → ℝ) x, IsFutureNullNormalAt g T f x ν →
          (∃ μ : ℝ, 0 < μ ∧ ν = μ • k₁ x) ∨ ∃ μ : ℝ, 0 < μ ∧ ν = μ • k₂ x) ∧
        (∀ x ∈ S, ∀ e : Fin (n - 2) → TangentSpace 𝓘(ℝ, Fin n → ℝ) x,
          (∀ i, mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin 2 → ℝ) f x (e i) = 0) →
          (∀ i j, g.g x (e i) (e j) = if i = j then 1 else 0) →
          frameExpansion g cov k₁ x e < 0 ∧ frameExpansion g cov k₂ x e < 0) := by
  classical
  obtain ⟨hc, hne, f, hf, hS, hsub, hsp, hk⟩ := h
  refine ⟨f, hf, hS, hsub, ?_⟩
  -- the two fields from the two signs
  obtain ⟨X, hXs, hX⟩ := exists_smooth_field T
  obtain ⟨k₁, hk₁s, hk₁n, hk₁e⟩ :=
    exists_global_null_normal T hc hf hS hsub hsp hXs hX 1 (by norm_num)
  obtain ⟨k₂, hk₂s, hk₂n, hk₂e⟩ :=
    exists_global_null_normal T hc hf hS hsub hsp hXs hX (-1) (by norm_num)
  refine ⟨k₁, k₂, hk₁s, hk₂s, fun x hx => ⟨hk₁n x hx, hk₂n x hx⟩, ?_, ?_⟩
  · intro x hx ν hν
    obtain ⟨s, hs, μ, hμ, hνk⟩ := nullField_classify T hf (hsub x hx) (hsp x hx) (hX x).1 (hX x).2 hν
    have hs' : s = 1 ∨ s = -1 := by
      have : (s - 1) * (s + 1) = 0 := by linear_combination hs
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    rcases hs' with rfl | rfl
    · left; exact ⟨μ, hμ, by rw [hνk, hk₁e x hx]⟩
    · right; exact ⟨μ, hμ, by rw [hνk, hk₂e x hx]⟩
  · intro x hx e he1 he2
    exact ⟨hk k₁ hk₁s (fun y hy => hk₁n y hy) x hx e he1 he2,
      hk k₂ hk₂s (fun y hy => hk₂n y hy) x hx e he1 he2⟩

end Lightlike.Penrose
