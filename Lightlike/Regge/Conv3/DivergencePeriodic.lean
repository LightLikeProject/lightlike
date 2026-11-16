import Lightlike.Regge.Conv3.LatticeSum

/-!
# The divergence of a periodic field integrates to zero over the unit cube

For a family `T i` (`i : Fin 3`) of `C¹` functions on `ℝ³` that are invariant under integer translations, the integral over the
unit cube `[0, 1]³` of the divergence `Σ_i ∂_i T_i` is zero (`integral_div_periodic`): the divergence theorem of Mathlib on the box,
the contributions of the opposite faces cancelling because the fields are periodic. It is the integration by parts on the torus
that identifies the Saint-Venant and Fierz–Pauli forms of the `η²` coefficient of the integrated curvature density.

## Main results

* `integral_div_periodic`: `∫_{[0,1]³} Σ_i ∂_i T_i = 0` for periodic `C¹` fields.

**Limits.** The unit cube of `ℝ³` and periods in the integer lattice; `C¹` fields.
-/

open MeasureTheory Set Real
namespace Lightlike.Regge.Conv3

/-- **The integral of the divergence of a periodic `C¹` field over the unit cube vanishes.** The divergence theorem on the
box `[0,1]³`, the contributions of opposite faces cancelling by periodicity. -/
theorem integral_div_periodic (T : Fin 3 → (Fin 3 → ℝ) → ℝ) (hT : ∀ i, ContDiff ℝ 1 (T i))
    (hper : ∀ i (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), T i (p + fun j => (e j : ℝ)) = T i p) :
    ∫ x in unitCube, ∑ i, fderiv ℝ (T i) x (Pi.single i 1) = 0 := by
  have hbox : unitCube = Set.Icc (0 : Fin 3 → ℝ) 1 := by
    unfold unitCube; rw [Set.pi_univ_Icc]; rfl
  rw [hbox]
  have := integral_divergence_of_hasFDerivAt_off_countable' (n := 2) (E := ℝ) (0 : Fin 3 → ℝ) 1
    (by intro i; simp) T (fun i x => fderiv ℝ (T i) x) ∅ countable_empty
    (fun i => (hT i).continuous.continuousOn)
    (fun x _ i => ((hT i).differentiable (by norm_num) x).hasFDerivAt)
    (by
      have : Continuous fun x : Fin 3 → ℝ => ∑ i, fderiv ℝ (T i) x (Pi.single i 1) := by
        refine continuous_finset_sum _ fun i _ => ?_
        exact ((hT i).continuous_fderiv (by norm_num)).clm_apply continuous_const
      exact this.continuousOn.integrableOn_Icc)
  rw [this]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [sub_eq_zero]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
  show T i (Fin.insertNth i ((1 : Fin 3 → ℝ) i) y) = T i (Fin.insertNth i ((0 : Fin 3 → ℝ) i) y)
  have : (Fin.insertNth i ((1 : Fin 3 → ℝ) i) y : Fin 3 → ℝ) =
      (Fin.insertNth i (((0 : Fin 3 → ℝ)) i) y : Fin 3 → ℝ) + fun j => (((Pi.single i (1 : ℤ) : Fin 3 → ℤ) j : ℤ) : ℝ) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      simp [Fin.insertNth_apply_succAbove, hj]
  rw [this, hper]

end Lightlike.Regge.Conv3
