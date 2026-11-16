import Lightlike.Regge.Conv3.CurvatureEta
import Lightlike.Regge.Conv3.DihedralTaylor2

/-!
# The curvature density of `1 + η h` expands to second order in `η`, uniformly on compact sets of jets

The function `Feta` of `CurvatureEta` is smooth on the open set of jets `(η, h, ∂h, ∂∂h)` with `det (1 + η h) > 0`, and it
vanishes at `η = 0`. By the uniform Taylor expansion `taylor3_uniform` there are `M` and `r > 0` such that for every jet
`J = (h, ∂h, ∂∂h)` of a compact set and every `|η| ≤ r`,
`|Feta (η, J) - η F₁ J - (η² / 2) F₂ J| ≤ M |η|³` (`feta_expansion`), where `F₁ J` and `F₂ J` are the first and second
derivatives of `η ↦ Feta (η, J)` at `0`, written as derivatives of `Feta` along the first coordinate of the jet space.

## Main results

* `F1`, `F2`: the first and second `η`-derivatives of `Feta` at `η = 0`.
* `feta_expansion`: the expansion with a cubic remainder, uniform on compact sets of jets.
* `feta_expansion_dom`: the same, together with membership of `(η, J)` in the domain of `Feta`.

**Limits.** Dimension 3; the coefficients `F1`, `F2` are only defined here as derivatives, not computed (their explicit
polynomial form is the next step); nothing about integrals or periodic fields.
-/

open Matrix Finset Real
open scoped ContDiff
namespace Lightlike.Regge.Conv3

/-- The jets `(h, ∂h, ∂∂h)` without `η`. -/
abbrev Jet3 := (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)

/-- The direction of the `η`-axis in the jet space. -/
def etaDir : JetE := ((1 : ℝ), (0 : Jet3))

/-- The first `η`-derivative of `Feta` at `η = 0`, at the jet `J`. -/
noncomputable def F1 (J : Jet3) : ℝ := fderiv ℝ Feta ((0 : ℝ), J) etaDir

/-- The second `η`-derivative of `Feta` at `η = 0`, at the jet `J`. -/
noncomputable def F2 (J : Jet3) : ℝ := fderiv ℝ (fderiv ℝ Feta) ((0 : ℝ), J) etaDir etaDir

theorem isOpen_posJ : IsOpen posJ :=
  isOpen_lt continuous_const (contDiff_det_mat gJ contDiff_gJ).continuous

theorem norm_etaDir_smul (η : ℝ) : ‖η • etaDir‖ = |η| := by
  simp [etaDir, Prod.norm_def]

/-- **Second-order expansion in `η`, uniform on compact sets of jets.** -/
theorem feta_expansion {K : Set Jet3} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ J ∈ K, ∀ η : ℝ, |η| ≤ r →
      |Feta (η, J) - η * F1 J - η ^ 2 / 2 * F2 J| ≤ M * |η| ^ 3 := by
  have hKc : IsCompact ((fun J : Jet3 => ((0 : ℝ), J)) '' K) :=
    hK.image (continuous_const.prodMk continuous_id)
  have hKV : ((fun J : Jet3 => ((0 : ℝ), J)) '' K) ⊆ posJ := by
    rintro _ ⟨J, _, rfl⟩
    exact zero_mem_posJ _ _ _
  obtain ⟨M, r, hr, h⟩ := taylor3_uniform isOpen_posJ (contDiffOn_Feta.of_le (by simp))
    hKc hKV
  refine ⟨M, r, hr, fun J hJ η hη => ?_⟩
  have h1 := h ((0 : ℝ), J) ⟨J, hJ, rfl⟩ (η • etaDir) (by rw [norm_etaDir_smul]; exact hη)
  have e1 : ((0 : ℝ), J) + η • etaDir = (η, J) := by simp [etaDir]
  have e0 : Feta ((0 : ℝ), J) = 0 := Feta_flat _ _ _
  rw [e1, e0, norm_etaDir_smul] at h1
  have e2 : (fderiv ℝ Feta ((0 : ℝ), J)) (η • etaDir) = η * F1 J := by
    rw [map_smul, smul_eq_mul]; rfl
  have e3 : (fderiv ℝ (fderiv ℝ Feta) ((0 : ℝ), J)) (η • etaDir) (η • etaDir) = η ^ 2 * F2 J := by
    simp only [map_smul, _root_.smul_apply, smul_eq_mul, F2]; ring
  rw [e2, e3] at h1
  convert h1 using 2
  ring

/-- **The expansion stays in the domain.** For `|η|` small, `(η, J)` lies in the domain `posJ` for every jet `J` of a
compact set, and the second-order expansion of `Feta` holds with a cubic remainder. -/
theorem feta_expansion_dom {K : Set Jet3} (hK : IsCompact K) :
    ∃ M r : ℝ, 0 < r ∧ ∀ J ∈ K, ∀ η : ℝ, |η| ≤ r →
      (η, J) ∈ posJ ∧ |Feta (η, J) - η * F1 J - η ^ 2 / 2 * F2 J| ≤ M * |η| ^ 3 := by
  have hKc : IsCompact ((fun J : Jet3 => ((0 : ℝ), J)) '' K) :=
    hK.image (continuous_const.prodMk continuous_id)
  have hKV : ((fun J : Jet3 => ((0 : ℝ), J)) '' K) ⊆ posJ := by
    rintro _ ⟨J, _, rfl⟩
    exact zero_mem_posJ _ _ _
  obtain ⟨ρ, hρ, hρV⟩ := hKc.exists_cthickening_subset_open isOpen_posJ hKV
  obtain ⟨M, r, hr, h⟩ := taylor3_uniform isOpen_posJ (contDiffOn_Feta.of_le (by simp)) hKc hKV
  refine ⟨M, min r ρ, lt_min hr hρ, fun J hJ η hη => ⟨?_, ?_⟩⟩
  · apply hρV
    refine Metric.mem_cthickening_of_dist_le (η, J) ((0 : ℝ), J) ρ _ ⟨J, hJ, rfl⟩ ?_
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
    simpa using (hη.trans (min_le_right _ _))
  · have hη' : |η| ≤ r := hη.trans (min_le_left _ _)
    have h1 := h ((0 : ℝ), J) ⟨J, hJ, rfl⟩ (η • etaDir) (by rw [norm_etaDir_smul]; exact hη')
    have e1 : ((0 : ℝ), J) + η • etaDir = (η, J) := by simp [etaDir]
    have e0 : Feta ((0 : ℝ), J) = 0 := Feta_flat _ _ _
    rw [e1, e0, norm_etaDir_smul] at h1
    have e2 : (fderiv ℝ Feta ((0 : ℝ), J)) (η • etaDir) = η * F1 J := by
      rw [map_smul, smul_eq_mul]; rfl
    have e3 : (fderiv ℝ (fderiv ℝ Feta) ((0 : ℝ), J)) (η • etaDir) (η • etaDir) = η ^ 2 * F2 J := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul, F2]; ring
    rw [e2, e3] at h1
    convert h1 using 2
    ring

end Lightlike.Regge.Conv3
