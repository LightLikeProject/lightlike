import Lightlike.Spacetime.PenroseSingularity.FocalFields
import Lightlike.Spacetime.PenroseSingularity.ChartFocal

/-!
# The broken field and its correction function in a chart (G1-012, step D4)

In the chart, `Ĵ = Σ vᵢ Jᵢ - (c t / a) w` is a Jacobi field with covariant derivative `P̂ = Σ vᵢ Pᵢ - (c / a) w`;
for a field `η` orthogonal to `w`, the field `W = Ĵ + ε η` has covariant derivative `P̂ + ε Dη` orthogonal to `w`, and the
function `φ = ½ g(P̂, Ĵ) + ε g(P̂, η) + ½ ε² K + κ t + c₀` has derivative `½ bQ(W, DW) + κ`.
-/

open Set Filter Topology

noncomputable section

namespace Lightlike.Penrose

open Lightlike.Geodesic

variable {n m : ℕ} {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} {U : Set (Fin n → ℝ)}

/-- The corrected Jacobi field `Ĵ`. -/
def Jhat (Jf : Fin m → ℝ → Fin n → ℝ) (wf : ℝ → Fin n → ℝ) (v : Fin m → ℝ) (c a : ℝ) (t : ℝ) : Fin n → ℝ :=
  ∑ i, v i • Jf i t - ((c / a) * t) • wf t

/-- The corrected covariant derivative `P̂`. -/
def Phat (Pf : Fin m → ℝ → Fin n → ℝ) (wf : ℝ → Fin n → ℝ) (v : Fin m → ℝ) (c a : ℝ) (t : ℝ) : Fin n → ℝ :=
  ∑ i, v i • Pf i t - (c / a) • wf t

/-- `Ĵ` is a Jacobi field with covariant derivative `P̂`. -/
theorem isJacobiOn_Jhat {γ wf : ℝ → Fin n → ℝ} {I : Set ℝ} {Jf Pf : Fin m → ℝ → Fin n → ℝ}
    (hγ : IsGeodesicOn g γ wf I) (hJ : ∀ i, IsJacobiOn g γ wf (Jf i) (Pf i) I) (v : Fin m → ℝ) (c a : ℝ) :
    IsJacobiOn g γ wf (Jhat Jf wf v c a) (Phat Pf wf v c a) I := by
  have h := IsJacobiOn.add (IsJacobiOn.sum_smul hγ hJ v)
    (IsJacobiOn.smul (IsJacobiOn.affine_w hγ 0 (c / a)) (-1))
  convert h using 1
  · funext t
    simp [Jhat, sub_eq_add_neg]
  · funext t
    simp [Phat, sub_eq_add_neg]

variable {γ wf : ℝ → Fin n → ℝ} {I : Set ℝ} {Jf Pf : Fin m → ℝ → Fin n → ℝ}

/-- **The chart identities of the broken field.** -/
theorem chart_piece (hg : Lightlike.IsCoordMetric g U) (hγ : IsGeodesicOn g γ wf I)
    (hJ : ∀ i, IsJacobiOn g γ wf (Jf i) (Pf i) I) (hγU : ∀ t ∈ I, γ t ∈ U)
    (hIo : IsOpen I) (hnullw : ∀ t ∈ I, gpairAt g (γ t) (wf t) (wf t) = 0)
    (hperpJ : ∀ t ∈ I, ∀ i, gpairAt g (γ t) (wf t) (Jf i t) = 0) (v : Fin m → ℝ) (c a ε κ c₀ : ℝ)
    {ηc η' : ℝ → Fin n → ℝ} (hη : ∀ t ∈ I, HasDerivAt ηc (η' t) t)
    (hηperp : ∀ t ∈ I, gpairAt g (γ t) (wf t) (ηc t) = 0) {K : ℝ → ℝ}
    (hK : ∀ t ∈ I, HasDerivAt K (bQ g (γ t) (wf t) (ηc t) (η' t + gammaApply g (γ t) (wf t) (ηc t))) t)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => Jhat Jf wf v c a s + ε • ηc s)
      (Phat Pf wf v c a t - gammaApply g (γ t) (wf t) (Jhat Jf wf v c a t) + ε • η' t) t ∧
    gpairAt g (γ t) (Phat Pf wf v c a t + ε • (η' t + gammaApply g (γ t) (wf t) (ηc t))) (wf t) = 0 ∧
    HasDerivAt (fun s => (1 / 2 : ℝ) * gpairAt g (γ s) (Phat Pf wf v c a s) (Jhat Jf wf v c a s) +
        ε * gpairAt g (γ s) (Phat Pf wf v c a s) (ηc s) + (1 / 2 : ℝ) * ε ^ 2 * K s + κ * s + c₀)
      ((1 / 2 : ℝ) * bQ g (γ t) (wf t) (Jhat Jf wf v c a t + ε • ηc t)
        (Phat Pf wf v c a t + ε • (η' t + gammaApply g (γ t) (wf t) (ηc t))) + κ) t := by
  have hJh := isJacobiOn_Jhat hγ hJ v c a
  refine ⟨((hJh.deriv_field t ht).add ((hη t ht).const_smul ε)), ?_, ?_⟩
  · -- orthogonality of the covariant derivative
    have hperpv : ∀ s ∈ I, gpairAt g (γ s) (wf s) (Jhat Jf wf v c a s) = 0 := by
      intro s hs
      have h1 : gpairAt g (γ s) (wf s) (∑ i, v i • Jf i s) = 0 := by
        rw [gpairAt_symm hg (hγU s hs), gpairAt_sum_smul_left]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [gpairAt_symm hg (hγU s hs), hperpJ s hs i]; ring
      have h2 : gpairAt g (γ s) (wf s) (((c / a) * s) • wf s) = 0 := by
        rw [gpairAt_symm hg (hγU s hs)]
        have h0 : gpairAt g (γ s) 0 (wf s) = 0 := by simp [gpairAt]
        have := gpairAt_add_smul_left g (γ s) 0 (wf s) (wf s) ((c / a) * s)
        simp only [zero_add, h0] at this
        rw [this, hnullw s hs]; ring
      have : gpairAt g (γ s) (wf s) (Jhat Jf wf v c a s) =
          gpairAt g (γ s) (wf s) (∑ i, v i • Jf i s) - gpairAt g (γ s) (wf s) (((c / a) * s) • wf s) := by
        unfold Jhat
        rw [gpairAt_symm hg (hγU s hs), gpairAt_sub_left, gpairAt_symm hg (hγU s hs) (∑ i, v i • Jf i s),
          gpairAt_symm hg (hγU s hs) (((c / a) * s) • wf s)]
      rw [this, h1, h2]; ring
    have hPhw := IsJacobiOn.pair_P_w hg hJh hIo hγU hperpv ht
    -- `g(η, w) = 0` identically, so `g(Dη, w) = 0`
    have hDη : gpairAt g (γ t) (η' t + gammaApply g (γ t) (wf t) (ηc t)) (wf t) = 0 := by
      have hγd : HasDerivAt γ (wf t) t := hγ.1 t ht
      have hwd : HasDerivAt wf (accel g (γ t) (wf t)) t := hγ.2 t ht
      have h := hasDerivAt_gpair hg hγd (hγU t ht) (hη t ht) hwd
      have h0 : HasDerivAt (fun s => gpairAt g (γ s) (ηc s) (wf s)) 0 t :=
        (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (by
          filter_upwards [hIo.mem_nhds ht] with s hs
          rw [gpairAt_symm hg (hγU s hs), hηperp s hs])
      have := h.unique h0
      rw [covDAlong_eq_add, covDAlong_eq_add, accel_eq_neg_gammaApply] at this
      have e1 : (-gammaApply g (γ t) (wf t) (wf t) + gammaApply g (γ t) (wf t) (wf t)) = 0 := by abel
      rw [e1] at this
      have h3 : gpairAt g (γ t) (ηc t) 0 = 0 := by simp [gpairAt]
      rw [h3, add_zero] at this
      exact this
    have hsm : gpairAt g (γ t) (ε • (η' t + gammaApply g (γ t) (wf t) (ηc t))) (wf t) = 0 := by
      have h0 : gpairAt g (γ t) 0 (wf t) = 0 := by simp [gpairAt]
      have := gpairAt_add_smul_left g (γ t) 0 (η' t + gammaApply g (γ t) (wf t) (ηc t)) (wf t) ε
      simp only [zero_add, h0] at this
      rw [this, hDη]; ring
    rw [gpairAt_add_left, hsm, add_zero]
    exact hPhw
  · exact hasDerivAt_phi hg hJh hγU ht (hη t ht) ε κ c₀ (hK t ht)

end Lightlike.Penrose
