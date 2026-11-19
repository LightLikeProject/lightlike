import Lightlike.Spacetime.FLRWCoord
import Lightlike.Spacetime.Corners.EinsteinChart
import Lightlike.Spacetime.SchwarzschildManifold
import Lightlike.Spacetime.Corners.ChartConnection
import Lightlike.Spacetime.Corners.ChartCovariant
import Lightlike.Spacetime.Corners.Coordinates
import Lightlike.Spacetime.Corners.Curvature
import Lightlike.Spacetime.Corners.EinsteinEquations
import Lightlike.Spacetime.Corners.LeviCivitaSmooth

/-!
# Friedmann's equations on `I × S³` (CO30, attempt 1)

`flrwSphere_einsteinEq_leviCivita_iff_friedmann`: for `a` smooth and positive on an open interval (or open set) `J ⊆ ℝ`, the Lorentzian metric
`-dt² + a(t)² h` on the manifold `↥J × S³` (`h` the round metric of the unit sphere; `FLRWModel.lean`), the Levi-Civita connection, and the comoving perfect fluid
`T = (ρ + p) u ⊗ u + p g`, `u = ∂_t` (`flrwFluid`), the Einstein equations `G + Λ g = 8πG_N T` hold iff Friedmann's first and second equations hold with
spatial curvature `k = 1` at every `t ∈ J` (`Cosmology.FirstFriedmann`, `Cosmology.SecondFriedmann`). The proof is chartwise: `einsteinEq_iff_chartW`
(`EinsteinChart.lean`), the coordinate components of the metric and of the fluid in every chart (`coordMetric_flrw`, `flrwFluid_chart`), and the coordinate result
`Cosmology.flrw_einstein_iff_friedmann`. The point sets of the charts cover the coordinate domain of the FLRW chart because the stereographic charts of the
sphere have target all of `ℝ³` (so `k = 1` is covered with no missing point, unlike the chart-domain statement for `k > 0`).

**Trust check** (`closedDeSitter_einsteinEq`): `a = cosh(Ht)/H`, `ρ = p = 0`, `Λ = 3H²` solve Friedmann's equations with `k = 1`, so closed de Sitter space on `ℝ × S³` satisfies the Einstein equations (the statement is not vacuous).

**Comparison with the source** (Carroll, *Lecture Notes on General Relativity* (1997), ch. 8, read at (8.3), (8.7), (8.17), (8.29)-(8.31), (8.33)-(8.36), pp. 218-224; see
`docs/notes/co30-carroll-comparison.md`): the equations match; the metric is `-dt² + a² h` with `h` of unit radius (`k = 1`), on the whole of `S³`; the fluid is
comoving with `ρ, p` depending on `t` only; units `c = 1`; `J` is an open subset of `ℝ` (an interval for the physical case).

**Limits.** Manifold `J × S³` modelled on `Fin 4 → ℝ` by transporting the product model; `C²` structure and a locally smooth connection (the Levi-Civita connection).
-/

open Manifold Metric Bundle TopologicalSpace Set
open scoped ContDiff
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace Lightlike

theorem mem_target_opens (J : Opens ℝ) (t₀ : J) (s : ℝ) : s ∈ (extChartAt 𝓘(ℝ, ℝ) t₀).target ↔ s ∈ (J : Set ℝ) := by
  simp [extChartAt, Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def]

theorem target_sphere_chart (x : S3) : (extChartAt (𝓡 3) x).target = Set.univ := by
  simp [extChartAt]
  exact stereographic'_target (n := 3) (-x)

theorem mem_target_I4 (J : Opens ℝ) (x : ↥J × S3) (y : Fin 4 → ℝ) : y ∈ (extChartAt I4 x).target ↔ y 0 ∈ (J : Set ℝ) := by
  have h : y ∈ (extChartAt I4 x).target ↔ modelEquiv.symm y ∈ (extChartAt IJS x).target := by
    simp only [I4, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage]
  rw [h, extChartAt_IJS]
  show (modelEquiv.symm y) ∈ (extChartAt 𝓘(ℝ, ℝ) x.1).target ×ˢ (extChartAt (𝓡 3) x.2).target ↔ _
  rw [Set.mem_prod, target_sphere_chart, mem_target_opens]
  simp [modelEquiv_symm_apply]


instance : I4.Boundaryless := ⟨range_I4⟩

/-- the coordinate field of the chart is the derivative of the chart inverse on the basis vector -/
theorem coordField_eq_mfderiv (J : Opens ℝ) (x : ↥J × S3) {y : Fin 4 → ℝ} (hy : y ∈ (extChartAt I4 x).target) (i : Fin 4) :
    coordFieldW (I := I4) x i ((extChartAt I4 x).symm y) =
      mfderivWithin 𝓘(ℝ, Fin 4 → ℝ) I4 (extChartAt I4 x).symm (range I4) y (Pi.single i 1) := by
  rw [coordField_applyW x i hy, coordBasis_applyW, ← mfderiv_extChartAt_symm_eqW x hy]
  rfl


/-- **The time coordinate field of the chart is `∂_t`**, the vector `(1, 0)` of the product, i.e. `e₀` in the model `Fin 4 → ℝ`. -/
theorem coordField_zero (J : Opens ℝ) (x : ↥J × S3) {y : Fin 4 → ℝ} (hy : y ∈ (extChartAt I4 x).target) :
    coordFieldW (I := I4) x 0 ((extChartAt I4 x).symm y) = (Pi.single 0 1 : Fin 4 → ℝ) := by
  have hz : modelEquiv.symm y ∈ (extChartAt IJS x).target := by
    have := hy
    simp only [I4, ModelWithCorners.extChartAt_transContinuousLinearEquiv_target, Set.mem_preimage] at this
    exact this
  rw [coordField_eq_mfderiv J x hy]
  apply modelEquiv.symm.injective
  rw [mfderiv_I4_chart_symm J x hy, modelEquiv_symm_single0]
  obtain ⟨h1, h2⟩ := chart_symm_deriv J x hz ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))
  have h2' : dcoe ((extChartAt IJS x).symm (modelEquiv.symm y)).2
      (mfderivWithin 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 3)) IJS (extChartAt IJS x).symm (range IJS) (modelEquiv.symm y)
        ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3)))).2 = 0 := by
    rw [h2]; simp
  have h3 := (injective_mvfderiv_subtypeVal_sphere (E := E4) ((extChartAt IJS x).symm (modelEquiv.symm y)).2)
    (h2'.trans (map_zero _).symm)
  exact Prod.ext h1 h3


/-- **A comoving perfect fluid on `J × S³`**: `T = (ρ + p) u ⊗ u + p g` with `u = ∂_t` (as a form `g(∂_t, ·)`), `ρ` and `p` functions of `t`. -/
def flrwFluid (J : Opens ℝ) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t) (ρ p : ℝ → ℝ) (x : ↥J × S3) :
    TangentSpace I4 x →L[ℝ] TangentSpace I4 x →L[ℝ] ℝ :=
  (ρ (x.1 : ℝ) + p (x.1 : ℝ)) •
      ((flrwMetric4 J ha hpos).toNondegMetric.g x (Pi.single 0 1)).smulRight
        ((flrwMetric4 J ha hpos).toNondegMetric.g x (Pi.single 0 1)) +
    p (x.1 : ℝ) • (flrwMetric4 J ha hpos).toNondegMetric.g x

/-- **The chart components of the fluid are `perfectFluid`** of the coordinate FLRW metric. -/
theorem flrwFluid_chart (J : Opens ℝ) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t) (ρ p : ℝ → ℝ)
    (x : ↥J × S3) {y : Fin 4 → ℝ} (hy : y ∈ (extChartAt I4 x).target) (μ ν : Fin 4) :
    flrwFluid J ha hpos ρ p ((extChartAt I4 x).symm y) (coordFieldW (I := I4) x μ ((extChartAt I4 x).symm y))
        (coordFieldW (I := I4) x ν ((extChartAt I4 x).symm y)) =
      Cosmology.perfectFluid ρ p (Cosmology.flrwMetric a 1) μ ν y := by
  have hu := coordField_zero J x hy
  have hg := fun i j => g_coordFieldW (flrwMetric4 J ha hpos).toNondegMetric x i j hy
  have hc := coordMetric_flrw J ha hpos x hy
  unfold flrwFluid Cosmology.perfectFluid
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  rw [← hu, hg 0 μ, hg 0 ν, hg μ ν, hc, val_chart_symm J x hy]
  have hs : ∀ i j, Cosmology.flrwMetric a 1 y i j = Cosmology.flrwMetric a 1 y j i := fun i j => by
    simp only [Cosmology.flrwMetric, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  rw [hs 0 μ, hs 0 ν]
  ring


/-- the coordinate FLRW metric with `k = 1` is a coordinate metric on its chart domain (the proof of `flrw_einstein_iff_friedmann`) -/
theorem isCoordMetric_flrw {I : Set ℝ} (hI : IsOpen I) {a : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a I) (hpos : ∀ t ∈ I, 0 < a t) :
    IsCoordMetric (Cosmology.flrwMetric a 1) (Cosmology.flrwDomain I 1) := by
  have hU : IsOpen (Cosmology.flrwDomain I 1) := by
    have h1 : IsOpen {x : Fin 4 → ℝ | x 0 ∈ I} := hI.preimage (continuous_apply 0)
    have h2 : IsOpen {x : Fin 4 → ℝ | 0 < 1 + 1 * Cosmology.spatialNormSq x / 4} :=
      isOpen_lt continuous_const (by unfold Cosmology.spatialNormSq; fun_prop)
    exact h1.inter h2
  have hDn : ∀ x ∈ Cosmology.flrwDomain I 1, Cosmology.Dn 1 x ≠ 0 := fun x hx => (show 0 < Cosmology.Dn 1 x from hx.2).ne'
  refine isCoordMetric_diagonal (Cosmology.dF a 1) hU ?_ ?_
  · intro i
    by_cases hi : i = 0
    · simp only [Cosmology.dF, hi, ite_true]; exact contDiffOn_const
    · simp only [Cosmology.dF, hi, ite_false]
      have hs : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => 1 + 1 * Cosmology.spatialNormSq y / 4) := by
        unfold Cosmology.spatialNormSq; fun_prop
      have ha0 : ContDiffOn ℝ ∞ (fun y : Fin 4 → ℝ => a (y 0)) (Cosmology.flrwDomain I 1) :=
        ha.comp (by fun_prop : ContDiff ℝ ∞ (fun y : Fin 4 → ℝ => y 0)).contDiffOn (fun y hy => hy.1)
      exact (ha0.div hs.contDiffOn (fun y hy => hDn y hy)).pow 2
  · intro x hx i
    unfold Cosmology.dF; split_ifs
    · norm_num
    · exact pow_ne_zero 2 (div_ne_zero (hpos _ hx.1).ne' (hDn x hx))


/-- **Einstein's equations on `J × S³` with the comoving perfect fluid are Friedmann's equations with `k = 1`** (CO30): for the Levi-Civita
connection of `-dt² + a(t)² h` on `↥J × S³`, `G + Λ g = 8πG_N T` holds iff the first and second Friedmann equations hold at every `t ∈ J`. -/
theorem flrwSphere_einsteinEq_iff_friedmann (J : Opens ℝ) {a ρ p : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J) (hpos : ∀ t ∈ J, 0 < a t)
    (cov : Connection I4 (↥J × S3)) [LocallySmoothConnectionW cov] (h : cov.IsLeviCivita (flrwMetric4 J ha hpos).toNondegMetric)
    (Λ Gn : ℝ) :
    (flrwMetric4 J ha hpos).toNondegMetric.EinsteinEqW cov Λ (8 * Real.pi * Gn) (fun x v w => flrwFluid J ha hpos ρ p x v w) ↔
      ∀ t ∈ (J : Set ℝ), Cosmology.FirstFriedmann a ρ 1 Λ Gn t ∧ Cosmology.SecondFriedmann a ρ p Λ Gn t := by
  rw [← Cosmology.flrw_einstein_iff_friedmann (ρ := ρ) (p := p) J.isOpen ha hpos 1 Λ Gn]
  have hmem : ∀ (x₀ : ↥J × S3) (y : Fin 4 → ℝ), y ∈ (extChartAt I4 x₀).target ↔ y ∈ Cosmology.flrwDomain (J : Set ℝ) 1 := by
    intro x₀ y
    rw [mem_target_I4]
    refine ⟨fun hy => ⟨hy, ?_⟩, fun hy => hy.1⟩
    have : 0 ≤ Cosmology.spatialNormSq y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  rw [einsteinEq_iff_chartW cov (flrwMetric4 J ha hpos) h Λ (8 * Real.pi * Gn) (fun x => flrwFluid J ha hpos ρ p x)]
  have hconv : ∀ (x₀ : ↥J × S3) (y : Fin 4 → ℝ), y ∈ (extChartAt I4 x₀).target → ∀ μ ν : Fin 4,
      (einsteinTensorW (range I4) ((flrwMetric4 J ha hpos).toNondegMetric.coordMetricW x₀) μ ν y +
        Λ * (flrwMetric4 J ha hpos).toNondegMetric.coordMetricW x₀ y μ ν =
          8 * Real.pi * Gn * flrwFluid J ha hpos ρ p ((extChartAt I4 x₀).symm y)
            (coordFieldW (I := I4) x₀ μ ((extChartAt I4 x₀).symm y)) (coordFieldW (I := I4) x₀ ν ((extChartAt I4 x₀).symm y))) ↔
        (einsteinTensor (Cosmology.flrwMetric a 1) μ ν y + Λ * Cosmology.flrwMetric a 1 y μ ν =
          8 * Real.pi * Gn * Cosmology.perfectFluid ρ p (Cosmology.flrwMetric a 1) μ ν y) := by
    intro x₀ y hy μ ν
    have hc := coordMetric_flrw J ha hpos x₀ hy
    have hopen : IsOpen (extChartAt I4 x₀).target := isOpen_extChartAt_target x₀
    have hcongr : ∀ z ∈ (extChartAt I4 x₀).target,
        (flrwMetric4 J ha hpos).toNondegMetric.coordMetricW x₀ z = Cosmology.flrwMetric a 1 z :=
      fun z hz => coordMetric_flrw J ha hpos x₀ hz
    rw [range_I4, einsteinTensorW_univ, einsteinTensor_congr_on hopen hcongr hy, hc, flrwFluid_chart J ha hpos ρ p x₀ hy]
  constructor
  · intro H
    refine ⟨isCoordMetric_flrw J.isOpen ha hpos, fun x hx μ ν => ?_⟩
    let s0 : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
    let x₀ : ↥J × S3 := (⟨x 0, hx.1⟩, s0)
    exact (hconv x₀ x ((hmem x₀ x).2 hx) μ ν).1 (H x₀ x ((hmem x₀ x).2 hx) μ ν)
  · intro H x₀ y hy μ ν
    exact (hconv x₀ y hy μ ν).2 (H.2 y ((hmem x₀ y).1 hy) μ ν)


/-- **CO30, for the Levi-Civita connection**: the Einstein equations with the comoving perfect fluid on `↥J × S³` hold iff the Friedmann equations with `k = 1`
hold at every `t ∈ J`. -/
theorem flrwSphere_einsteinEq_leviCivita_iff_friedmann (J : Opens ℝ) {a ρ p : ℝ → ℝ} (ha : ContDiffOn ℝ ∞ a J)
    (hpos : ∀ t ∈ J, 0 < a t) (Λ Gn : ℝ) :
    (flrwMetric4 J ha hpos).toNondegMetric.EinsteinEqW (leviCivita (flrwMetric4 J ha hpos).toNondegMetric) Λ (8 * Real.pi * Gn)
        (fun x v w => flrwFluid J ha hpos ρ p x v w) ↔
      ∀ t ∈ (J : Set ℝ), Cosmology.FirstFriedmann a ρ 1 Λ Gn t ∧ Cosmology.SecondFriedmann a ρ p Λ Gn t :=
  flrwSphere_einsteinEq_iff_friedmann J ha hpos _ ⟨leviCivita_torsion _, leviCivita_compat _⟩ Λ Gn

/-- **Trust check: closed de Sitter space.** `a(t) = cosh(H t) / H`, `k = 1`, `ρ = p = 0`, `Λ = 3H²` solve Friedmann's equations. -/
theorem closedDeSitter_friedmann {H : ℝ} (hH : 0 < H) (Gn : ℝ) (t : ℝ) :
    Cosmology.FirstFriedmann (fun t => Real.cosh (H * t) / H) (fun _ => 0) 1 (3 * H ^ 2) Gn t ∧
      Cosmology.SecondFriedmann (fun t => Real.cosh (H * t) / H) (fun _ => 0) (fun _ => 0) (3 * H ^ 2) Gn t := by
  have hd : ∀ s, HasDerivAt (fun t => Real.cosh (H * t) / H) (Real.sinh (H * s)) s := fun s => by
    have h1 : HasDerivAt (fun t => H * t) H s := by simpa using (hasDerivAt_id s).const_mul H
    have h2 := (Real.hasDerivAt_cosh (H * s)).comp s h1
    have h3 := h2.div_const H
    exact h3.congr_deriv (by field_simp)
  have hd1 : deriv (fun t => Real.cosh (H * t) / H) = fun s => Real.sinh (H * s) := funext fun s => (hd s).deriv
  have hd2 : ∀ s, deriv (fun s => Real.sinh (H * s)) s = H * Real.cosh (H * s) := fun s => by
    have h1 : HasDerivAt (fun t => H * t) H s := by simpa using (hasDerivAt_id s).const_mul H
    have h2 := (Real.hasDerivAt_sinh (H * s)).comp s h1
    have := h2.deriv
    simpa [Function.comp_def, mul_comm] using this
  have hc : 0 < Real.cosh (H * t) := Real.cosh_pos _
  simp only [Cosmology.FirstFriedmann, Cosmology.SecondFriedmann, hd1, hd2]
  constructor
  · field_simp
    have := Real.cosh_sq (H * t)
    nlinarith [this]
  · field_simp
    ring


/-- **Non-vacuity of CO30: closed de Sitter space is a solution.** On `ℝ × S³` the metric `−dt² + (cosh(Ht)/H)² h` with `Λ = 3H²` and no matter satisfies the
Einstein equations for its Levi-Civita connection (the fluid has `ρ = p = 0`). -/
theorem closedDeSitter_einsteinEq {H : ℝ} (hH : 0 < H) (Gn : ℝ) :
    let a : ℝ → ℝ := fun t => Real.cosh (H * t) / H
    ∃ (ha : ContDiffOn ℝ ∞ a (⊤ : Opens ℝ)) (hpos : ∀ t ∈ (⊤ : Opens ℝ), 0 < a t),
      (flrwMetric4 ⊤ ha hpos).toNondegMetric.EinsteinEqW (leviCivita (flrwMetric4 ⊤ ha hpos).toNondegMetric) (3 * H ^ 2)
        (8 * Real.pi * Gn) (fun x v w => flrwFluid ⊤ ha hpos (fun _ => 0) (fun _ => 0) x v w) := by
  intro a
  have ha : ContDiffOn ℝ ∞ a (⊤ : Opens ℝ) :=
    (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).div_const H |>.contDiffOn
  have hpos : ∀ t ∈ (⊤ : Opens ℝ), 0 < a t := fun t _ => div_pos (Real.cosh_pos _) hH
  refine ⟨ha, hpos, ?_⟩
  rw [flrwSphere_einsteinEq_leviCivita_iff_friedmann ⊤ ha hpos (ρ := fun _ => 0) (p := fun _ => 0)]
  intro t _
  exact closedDeSitter_friedmann hH Gn t


/-- **Trust check, the sign of `Λ`: closed de Sitter space does not solve the Einstein equations with `Λ = −3H²`.** With the wrong sign of the
cosmological constant the radius `1/H` of the spatial sphere at the time of symmetry is wrong (Friedmann's first equation at `t = 0`). -/
theorem closedDeSitter_wrong_sign {H : ℝ} (hH : 0 < H) (Gn : ℝ) :
    let a : ℝ → ℝ := fun t => Real.cosh (H * t) / H
    ∀ (ha : ContDiffOn ℝ ∞ a (⊤ : Opens ℝ)) (hpos : ∀ t ∈ (⊤ : Opens ℝ), 0 < a t),
      ¬ (flrwMetric4 ⊤ ha hpos).toNondegMetric.EinsteinEqW (leviCivita (flrwMetric4 ⊤ ha hpos).toNondegMetric) (-(3 * H ^ 2))
        (8 * Real.pi * Gn) (fun x v w => flrwFluid ⊤ ha hpos (fun _ => 0) (fun _ => 0) x v w) := by
  intro a ha hpos h
  rw [flrwSphere_einsteinEq_leviCivita_iff_friedmann ⊤ ha hpos (ρ := fun _ => 0) (p := fun _ => 0)] at h
  have h1 := (h 0 (Set.mem_univ _)).1
  have hd : ∀ s, HasDerivAt a (Real.sinh (H * s)) s := fun s => by
    have h1 : HasDerivAt (fun t => H * t) H s := by simpa using (hasDerivAt_id s).const_mul H
    have h2 := (Real.hasDerivAt_cosh (H * s)).comp s h1
    exact (h2.div_const H).congr_deriv (by field_simp)
  simp only [Cosmology.FirstFriedmann, (hd 0).deriv] at h1
  simp [a] at h1
  field_simp at h1
  nlinarith [sq_nonneg H]

end Lightlike
