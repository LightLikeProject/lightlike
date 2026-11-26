import Lightlike.Spacetime.PenroseSingularity.VariationJets
import Lightlike.Spacetime.PenroseSingularity.QuotientSq
import Lightlike.Spacetime.PenroseSingularity.StartIdentity

/-!
# Matching the start of the variation with a curve in the surface (G1-012, step D4)

If `x (s)` is a `C²` chart curve with `x (0) = γc 0` and `x' (0) = W 0`, then `varA (s, 0) - x (s) = s² d s` with `d`
continuous at `0` and `d 0 = Z 0 - (1/2)(x'' (0) + Γ(W 0, W 0))`.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}
  {Θ : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ} {D : Set ((Fin n → ℝ) × (Fin n → ℝ))}
  {γc W Z : ℝ → Fin n → ℝ} {V : Set (ℝ × ℝ)}

/-- **The second-order quotient at the start.** -/
theorem start_quotient (hV : IsOpen V) (hD0 : IsOpen D) (hΘ : ContDiffOn ℝ ∞ Θ D)
    (hA : ContDiffOn ℝ 3 (varA Θ γc W Z) V)
    (j0 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → Θ (q, 0) = q)
    (j1 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ Θ (q, 0) (0, w) = w)
    (j2 : ∀ q, (q, (0 : Fin n → ℝ)) ∈ D → ∀ w, fderiv ℝ (fderiv ℝ Θ) (q, 0) (0, w) (0, w) =
      Lightlike.Geodesic.accel g q w)
    (hVD : ∀ p ∈ V, (γc p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2) ∈ D) (hp : ((0 : ℝ), (0 : ℝ)) ∈ V)
    (hpD : (γc 0, (0 : Fin n → ℝ)) ∈ D)
    {x x1 : ℝ → Fin n → ℝ} {x2 : Fin n → ℝ} (hxd : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt x (x1 s) s)
    (hx1d : HasDerivAt x1 x2 0) (hx0 : x 0 = γc 0) (hx10 : x1 0 = W 0) :
    ∃ d : ℝ → Fin n → ℝ, (∀ s, varA Θ γc W Z (s, 0) - x s = s ^ 2 • d s) ∧ ContinuousAt d 0 ∧
      d 0 = Z 0 - (1 / 2 : ℝ) • (x2 + Lightlike.Geodesic.gammaApply g (γc 0) (W 0) (W 0)) := by
  have hvals := varA_values (gc := g) hV hD0 hΘ hA j0 j1 j2 hVD hp hpD
  have hJ := hasDerivAt_jets hV hA hp
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ), ((s, (0 : ℝ)) : ℝ × ℝ) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
  obtain ⟨d, hd, hdc, hd0⟩ := exists_continuousAt_quot_sq
    (h := fun s => varA Θ γc W Z (s, 0) - x s) (h' := fun s => jetC1 (varA Θ γc W Z) (s, 0) - x1 s)
    (c := jetC2 (varA Θ γc W Z) (0, 0) - x2)
    (by
      filter_upwards [hmem, hxd] with s hs hxs
      exact ((hasDerivAt_jets hV hA hs).1).sub hxs)
    (by simp [hvals.1, hx0])
    (by simp [hvals.2.1, hx10])
    ((hJ.2.1).sub hx1d)
  refine ⟨d, hd, hdc, ?_⟩
  rw [hd0, hvals.2.2, Lightlike.Geodesic.accel_eq_neg_gammaApply]
  funext i
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

end Lightlike.Penrose
