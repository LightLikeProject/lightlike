import Lightlike.Spacetime.PenroseSingularity.FocalBound
import Lightlike.Spacetime.PenroseSingularity.PenroseFocal

/-!
# Penrose's singularity theorem from focusing (G1-012)

`penrose_of_focal_chron` is Penrose's theorem for a closed trapped spacelike surface, assuming the second
variation fact `FocalImpliesChron` and the null energy condition in charts `ChartNEC`. The uniform bound on the
normalised expansion of the two null normal fields over the compact surface is proved
(`exists_expansion_bound`).
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- A bound by `Λ` is a bound by any larger number. -/
theorem ExpansionBound.mono {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n}
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} {T : Causal.TimeOrientation g} {S : Set M} {f : M → Fin 2 → ℝ}
    {k : Π p : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) p} {Λ Λ' : ℝ} (h : ExpansionBound g cov T S f k Λ)
    (hΛ : Λ ≤ Λ') : ExpansionBound g cov T S f k Λ' :=
  fun x hx e he ho => (h x hx e he ho).trans hΛ

/-- **Penrose's theorem, modulo `FocalImpliesChron` and `ChartNEC`.** -/
theorem penrose_of_focal_chron (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)
    {cov : Connection 𝓘(ℝ, Fin n → ℝ) M} [LocallySmoothConnection cov]
    (hLC : cov.IsLeviCivita g.toNondegMetric) (T : Causal.TimeOrientation g)
    (hGH : Causal.IsGloballyHyperbolic T) (hn : 3 ≤ n) {S : Set M} (hS : IsCompact S)
    (htrap : IsClosedTrappedSpacelikeSurface g cov T S) (Sig : Set M)
    (hCS : Causal.IsCauchySurface T Sig) [ConnectedSpace Sig] [NoncompactSpace Sig]
    (hKne : (frontier (Causal.causalFutureSet T S)).Nonempty) (hChron : FocalImpliesChron g T S)
    (hNEC : ChartNEC g) : NullGeodesicallyIncomplete g := by
  obtain ⟨hc, hne, f, hf, hSf, hsub, hsp, hexp⟩ := htrap
  obtain ⟨k₁, k₂, hk₁, hk₂, hkN, hcls⟩ := exists_null_normal_fields T hc hf hSf hsub hsp
  obtain ⟨Λ₁, h10, hΛ₁⟩ := exists_expansion_bound g hLC T hn hc hf hSf hsub hsp hk₁
    (fun x hx => (hkN x hx).1) (fun x hx e he ho => hexp k₁ hk₁ (fun y hy => (hkN y hy).1) x hx e he ho)
  obtain ⟨Λ₂, h20, hΛ₂⟩ := exists_expansion_bound g hLC T hn hc hf hSf hsub hsp hk₂
    (fun x hx => (hkN x hx).2) (fun x hx e he ho => hexp k₂ hk₂ (fun y hy => (hkN y hy).2) x hx e he ho)
  exact penrose_of_focal_bound g T hGH hS Sig hCS hKne (le_trans h10 (le_max_left Λ₁ Λ₂))
    (normalisedFocalBound_of_chron g hLC T hn hf hSf hsub hsp hexp hk₁ hk₂ hkN hcls hChron hNEC
      (hΛ₁.mono (le_max_left _ _)) (hΛ₂.mono (le_max_right _ _)))

end Lightlike.Penrose
