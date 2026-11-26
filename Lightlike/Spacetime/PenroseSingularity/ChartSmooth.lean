import Lightlike.Spacetime.PenroseSingularity.ChartFocal
import Lightlike.Spacetime.PenroseSingularity.StartIdentity
import Lightlike.Spacetime.PenroseSingularity.VariationJets

/-!
# Smoothness of the chart Jacobi data (G1-012, step D4)

For a smooth chart family `H (t, σ)` with Jacobi fields `J_i = ∂_{σ_i} H` and covariant derivatives `P_i`, `P_i` is
given by the explicit smooth expression `∂_t ∂_{σ_i} H + Γ(w, J_i)`.
-/

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Lightlike.Penrose

open Lightlike.Geodesic

variable {n m : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- **The covariant derivative of a chart Jacobi field is explicit.** -/
theorem jacobi_P_eq {H : ℝ × (Fin m → ℝ) → Fin n → ℝ} {W : Set (ℝ × (Fin m → ℝ))} (hWo : IsOpen W)
    (hH : ContDiffOn ℝ 3 H W) {σ : Fin m → ℝ} {I : Set ℝ} {P : ℝ → Fin n → ℝ} {i : Fin m}
    (hJ : IsJacobiOn g (fun s => H (s, σ)) (fun s => fderiv ℝ H (s, σ) (1, 0))
      (fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) P I)
    (hIW : ∀ s ∈ I, ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W) {s : ℝ} (hs : s ∈ I) :
    P s = fderiv ℝ (fderiv ℝ H) (s, σ) (0, Pi.single i 1) (1, 0) +
      gammaApply g (H (s, σ)) (fderiv ℝ H (s, σ) (1, 0)) (fderiv ℝ H (s, σ) (0, Pi.single i 1)) := by
  have hC : ∀ q ∈ W, ContDiffAt ℝ 3 H q := fun q hq => hH.contDiffAt (hWo.mem_nhds hq)
  have hq := hIW s hs
  have hd1 : DifferentiableAt ℝ (fderiv ℝ H) (s, σ) :=
    ((hC _ hq).fderiv_right (m := 2) (by norm_num)).differentiableAt (by simp)
  have hcurveT : HasDerivAt (fun r : ℝ => ((r, σ) : ℝ × (Fin m → ℝ))) ((1 : ℝ), (0 : Fin m → ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s σ)
  have h1 := hJ.deriv_field s hs
  have h2 := hasDerivAt_fderiv_comp' (f := H) (q := fun r : ℝ => ((r, σ) : ℝ × (Fin m → ℝ))) (r := s)
    (by simpa using hd1) hcurveT (0, Pi.single i 1)
  have h3 := h1.unique (by simpa using h2)
  have hH2 : ContDiffAt ℝ 2 H (s, σ) := (hC _ hq).of_le (by norm_num)
  have hsymm := hH2.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have e3 : fderiv ℝ (fderiv ℝ H) (s, σ) (1, 0) (0, Pi.single i 1) =
      fderiv ℝ (fderiv ℝ H) (s, σ) (0, Pi.single i 1) (1, 0) := hsymm _ _
  rw [e3] at h3
  rw [← h3]; abel

/-- The Christoffel contraction of smooth curves is smooth. -/
theorem contDiffOn_gammaApply (hg : Lightlike.IsCoordMetric g U) {γ u v : ℝ → Fin n → ℝ} {I : Set ℝ} {k : ℕ∞}
    (hγ : ContDiffOn ℝ k γ I) (hu : ContDiffOn ℝ k u I) (hv : ContDiffOn ℝ k v I)
    (hU : ∀ t ∈ I, γ t ∈ U) : ContDiffOn ℝ k (fun t => gammaApply g (γ t) (u t) (v t)) I := by
  refine contDiffOn_pi.2 fun i => ?_
  simp only [gammaApply]
  refine ContDiffOn.sum fun j _ => ContDiffOn.sum fun l _ => ?_
  have hch : ContDiffOn ℝ k (fun t => Lightlike.christoffel g i j l (γ t)) I :=
    ((hg.contDiffOn_christoffel i j l).of_le (by exact_mod_cast le_top)).comp hγ hU
  exact (hch.mul ((contDiffOn_pi.1 hu) j)).mul ((contDiffOn_pi.1 hv) l)

/-- **Smoothness of the chart Jacobi data.** `J_i`, `w` and `P_i` are smooth on the interval. -/
theorem chart_data_smooth (hg : Lightlike.IsCoordMetric g U) {H : ℝ × (Fin m → ℝ) → Fin n → ℝ}
    {W : Set (ℝ × (Fin m → ℝ))} (hWo : IsOpen W) (hH : ContDiffOn ℝ ∞ H W) {σ : Fin m → ℝ} {I : Set ℝ}
    (hIo : IsOpen I) (hIW : ∀ s ∈ I, ((s, σ) : ℝ × (Fin m → ℝ)) ∈ W) (hUW : ∀ q ∈ W, H q ∈ U)
    (i : Fin m) :
    ContDiffOn ℝ ∞ (fun s => H (s, σ)) I ∧ ContDiffOn ℝ ∞ (fun s => fderiv ℝ H (s, σ) (1, 0)) I ∧
      ContDiffOn ℝ ∞ (fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) I ∧
      ContDiffOn ℝ ∞ (fun s => fderiv ℝ (fderiv ℝ H) (s, σ) (0, Pi.single i 1) (1, 0) +
        gammaApply g (H (s, σ)) (fderiv ℝ H (s, σ) (1, 0)) (fderiv ℝ H (s, σ) (0, Pi.single i 1))) I := by
  have hcurve : ContDiffOn ℝ ∞ (fun s : ℝ => ((s, σ) : ℝ × (Fin m → ℝ))) I :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hmaps : Set.MapsTo (fun s : ℝ => ((s, σ) : ℝ × (Fin m → ℝ))) I W := fun s hs => hIW s hs
  have h0 : ContDiffOn ℝ ∞ (fun s => H (s, σ)) I := hH.comp hcurve hmaps
  have hH1 : ContDiffOn ℝ ∞ (fderiv ℝ H) W := hH.fderiv_of_isOpen hWo (by simp)
  have hH2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ H)) W := hH1.fderiv_of_isOpen hWo (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun s => fderiv ℝ H (s, σ)) I := hH1.comp hcurve hmaps
  have h2 : ContDiffOn ℝ ∞ (fun s => fderiv ℝ (fderiv ℝ H) (s, σ)) I := hH2.comp hcurve hmaps
  have hw : ContDiffOn ℝ ∞ (fun s => fderiv ℝ H (s, σ) (1, 0)) I := h1.clm_apply contDiffOn_const
  have hJ : ContDiffOn ℝ ∞ (fun s => fderiv ℝ H (s, σ) (0, Pi.single i 1)) I := h1.clm_apply contDiffOn_const
  refine ⟨h0, hw, hJ, ?_⟩
  refine ContDiffOn.add ((h2.clm_apply contDiffOn_const).clm_apply contDiffOn_const) ?_
  exact contDiffOn_gammaApply hg h0 hw hJ (fun s hs => hUW _ (hIW s hs))

end Lightlike.Penrose
