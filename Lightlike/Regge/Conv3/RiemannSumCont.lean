import Lightlike.Regge.Conv3.LatticeSum

/-!
# Riemann sums of a continuous function with sample points anywhere in the cells

`LatticeSum.lean` compares lattice sums of Lipschitz functions sampled at the lower corners of the cells with
the integral. Here the function is only continuous on the unit cube and the sample point of each cell is any
point of the cell (`riemann_sum_modulus`: the error is the modulus of continuity at distance `1/N`). Hence the
sums `Σ f (s N x) / N³` converge to `∫ f` (`riemann_sum_tendsto`).

## Main results

* `riemann_sum_modulus`: the error of a cell-sampled Riemann sum.
* `riemann_sum_tendsto`: convergence to the integral.

**Limits.** The unit cube of `Fin 3 → ℝ` only; no rate, only convergence.
-/

open MeasureTheory Set
namespace Lightlike.Regge.Conv3

/-- **Riemann sums of a continuous function with sample points anywhere in the cells.** If `f` is
continuous on the unit cube and varies by at most `η` over distances at most `1/N`, then every sum
`Σ f (s x) / N³` with `s x` in the cell `x` differs from `∫ f` by at most `η`. -/
theorem riemann_sum_modulus {f : (Fin 3 → ℝ) → ℝ} (hfc : ContinuousOn f unitCube) {η : ℝ} (hη : 0 ≤ η)
    {N : ℕ} (hN : 0 < N)
    (hf : ∀ x ∈ unitCube, ∀ y ∈ unitCube, ‖x - y‖ ≤ 1 / (N : ℝ) → |f x - f y| ≤ η)
    (s : (Fin 3 → Fin N) → (Fin 3 → ℝ)) (hs : ∀ x, s x ∈ latticeCell N x) :
    |(∑ x : Fin 3 → Fin N, f (s x)) * (1 / (N : ℝ)) ^ 3 - ∫ y in unitCube, f y| ≤ η := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcomp : IsCompact unitCube := isCompact_univ_pi fun _ => isCompact_Icc
  have hint : IntegrableOn f unitCube := hfc.integrableOn_compact hcomp
  have hsub : Set.pi univ (fun _ => Ico (0 : ℝ) 1) ⊆ unitCube :=
    Set.pi_mono fun _ _ => Ico_subset_Icc_self
  have hae : Set.pi univ (fun _ => Ico (0 : ℝ) 1) =ᵐ[volume] unitCube := by
    refine ae_eq_of_subset_of_measure_ge hsub ?_
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico).nullMeasurableSet
      hcomp.measure_lt_top.ne
    have h1 : volume unitCube = 1 := by
      unfold unitCube; rw [volume_pi_pi]; simp [Real.volume_Icc]
    have h2 : volume (Set.pi (univ : Set (Fin 3)) (fun _ => Ico (0 : ℝ) 1)) = 1 := by
      rw [volume_pi_pi]; simp [Real.volume_Ico]
    rw [h1, h2]
  have hcell_sub : ∀ x, latticeCell N x ⊆ unitCube := fun x =>
    (subset_iUnion (latticeCell N) x).trans ((latticeCell_iUnion hN).le.trans hsub)
  have hsplit : ∫ y in unitCube, f y = ∑ x : Fin 3 → Fin N, ∫ y in latticeCell N x, f y := by
    rw [← setIntegral_congr_set hae, ← latticeCell_iUnion hN]
    exact integral_iUnion_fintype (latticeCell_measurable N) (latticeCell_disjoint hN)
      fun x => hint.mono_set (hcell_sub x)
  have hcell : ∀ x : Fin 3 → Fin N,
      |f (s x) * (1 / (N : ℝ)) ^ 3 - ∫ y in latticeCell N x, f y| ≤ η * (1 / (N : ℝ)) ^ 3 := by
    intro x
    have hvol : volume.real (latticeCell N x) = (1 / (N : ℝ)) ^ 3 := latticeCell_volume x
    have hfin : volume (latticeCell N x) < ⊤ :=
      (measure_mono (hcell_sub x)).trans_lt hcomp.measure_lt_top
    have hI : IntegrableOn f (latticeCell N x) := hint.mono_set (hcell_sub x)
    have e1 : f (s x) * (1 / (N : ℝ)) ^ 3 - ∫ y in latticeCell N x, f y
        = ∫ y in latticeCell N x, (f (s x) - f y) := by
      rw [integral_sub (integrableOn_const hfin.ne) hI, setIntegral_const, hvol, smul_eq_mul, mul_comm]
    rw [e1]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := latticeCell N x)
      (f := fun y => f (s x) - f y) (C := η) hfin (fun y hy => by
        rw [Real.norm_eq_abs]
        refine hf _ (hcell_sub x (hs x)) y (hcell_sub x hy) ?_
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
        have hy' := hy i (mem_univ _)
        have hs' := hs x i (mem_univ _)
        simp only [mem_Ico] at hy' hs'
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        rw [abs_le]
        constructor <;> linarith [hy'.1, hy'.2, hs'.1, hs'.2])
    rwa [hvol, Real.norm_eq_abs] at this
  have hcard : (Fintype.card (Fin 3 → Fin N) : ℝ) = (N : ℝ) ^ 3 := by simp
  rw [hsplit, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _x : Fin 3 → Fin N, η * (1 / (N : ℝ)) ^ 3 := Finset.sum_le_sum fun x _ => hcell x
    _ = η := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; field_simp


/-- **Riemann sums with sample points in the cells converge to the integral.** For `f` continuous on the
unit cube and sample points `s N x` in the cells of the lattice of mesh `1/N`,
`Σ_x f (s N x) / N³ → ∫ f` as `N → ∞`. -/
theorem riemann_sum_tendsto {f : (Fin 3 → ℝ) → ℝ} (hfc : ContinuousOn f unitCube)
    (s : ∀ N : ℕ, (Fin 3 → Fin N) → (Fin 3 → ℝ)) (hs : ∀ N x, s N x ∈ latticeCell N x) :
    Filter.Tendsto (fun N : ℕ => (∑ x : Fin 3 → Fin N, f (s N x)) * (1 / (N : ℝ)) ^ 3)
      Filter.atTop (nhds (∫ y in unitCube, f y)) := by
  have hcomp : IsCompact unitCube := isCompact_univ_pi fun _ => isCompact_Icc
  have huc := hcomp.uniformContinuousOn_of_continuous hfc
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 huc (η / 2) (half_pos hη)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / δ)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNN : (N0 : ℝ) < N := by exact_mod_cast (by omega : N0 < N)
  have h1N : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hN']
    have : 1 / δ < N := hN0.trans hNN
    rw [div_lt_iff₀ hδ] at this
    linarith
  have := riemann_sum_modulus hfc (half_pos hη).le hNpos
    (fun x hx y hy hxy => by
      have := hδf x hx y hy (by rw [dist_eq_norm]; exact lt_of_le_of_lt hxy h1N)
      rw [Real.dist_eq] at this
      exact this.le) (s N) (hs N)
  rw [Real.dist_eq]
  linarith

end Lightlike.Regge.Conv3
