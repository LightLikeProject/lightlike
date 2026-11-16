import Lightlike.Regge.Conv3.HingeTerm
import Lightlike.Regge.Conv3.RiemannSumCont
import Lightlike.Regge.Conv3.ChartChangeGeneral

/-!
# The 3D Regge action of the Kuhn grid converges to half the Einstein–Hilbert action

For a Riemannian metric `g` on an open set `U ⊆ ℝ³` containing the cube `[0, 2]³`, the Kuhn triangulation of
the grid of mesh `1/N` has seven classes of edges (`dirs k`); the hinge of class `k` with lower corner `z / N`
has midpoint `hingeMid N k z`. `reggeAction3 g U N` is the sum over the classes and over the hinges with
lower corner in `[0, 1)³` of `ℓ δ`, with `ℓ` the geodesic length of the hinge (`hingeLen`) and
`δ = 2π - Σ dihedral angles` its deficit angle computed from the true geodesic lengths of the tetrahedra of its star
(`hingeDef`).

`regge3d_tendsto`: `reggeAction3 g U N → ∫_{[0,1]³} (R/2) √det g` as `N → ∞`. The proof assembles the hinge term
`ℓ δ = -ε³ √(g(w, w)) c₂ + O(ε⁴)` (`hinge_term`), the identity `Σ_k classDensity = (R/2) √det g` at every point
(`sum_classDensity`, from the jet-level star identity `jetStarCore_of_chart`), and the convergence of Riemann
sums of a continuous function with sample points in the cells (`riemann_sum_tendsto`).

## Main results

* `reggeAction3`: the Regge action of the grid of mesh `1/N`.
* `regge_class_tendsto`: one edge class converges to the integral of its density.
* `sum_classDensity`: the seven densities add up to `(R/2) √det g`.
* `regge3d_tendsto`: the Regge action of the Kuhn grid converges to `∫ (R/2) √det g` over the unit cube.

**Limits.** This is convergence, not a rate: the proof uses continuity of the densities only, so no
`O(1/N)` bound is claimed (a rate would need Lipschitz bounds for the second-order coefficient `c₂`, i.e. a
derivative of the jet in the base point). The grid is the standard cubical Kuhn triangulation in one chart;
the sum is over the hinges whose lower corner lies in `[0, 1)³` (hinges near the boundary have stars
reaching into `[0, 2]³ ⊆ U`); the lengths are geodesic distances of `g` in `U`; Riemannian signature only. It
is not Cheeger–Müller–Schrader's theorem for arbitrary fine triangulations of a manifold.
-/

open Real Matrix Lightlike Filter Topology Metric Set MeasureTheory
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)}

/-- The geodesic length of the hinge of class `k` with midpoint `v` at scale `ε`. -/
noncomputable def hingeLen (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Fin 3 → ℝ))
    (v : Fin 3 → ℝ) (ε : ℝ) (k : Fin 7) : ℝ :=
  Geodesic.dist g U (v - (ε / 2) • dirs k) (v + (ε / 2) • dirs k)

/-- The deficit angle `2π - Σ dihedral angles` of the hinge of class `k` with midpoint `v` at scale `ε`,
from the true geodesic lengths of the tetrahedra of its star. -/
noncomputable def hingeDef (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Fin 3 → ℝ))
    (v : Fin 3 → ℝ) (ε : ℝ) (k : Fin 7) : ℝ :=
  2 * π - clsSum (dirs k) (fun σ h => Dsq (trueLen g U v ε σ h))

/-- The midpoint of the hinge of class `k` whose lower corner is the lattice point `z / N`. -/
noncomputable def hingeMid (N : ℕ) (k : Fin 7) (z : Fin 3 → Fin N) : Fin 3 → ℝ :=
  fun i => ((z i : ℝ) + dirs k i / 2) / N

/-- **The Regge action of the Kuhn grid of mesh `1/N`.** The sum over the seven edge classes and over the
hinges whose lower corner `z / N` lies in the half-open cube `[0, 1)³` of the product `ℓ δ` of the geodesic length of
the hinge and its deficit angle, computed from the true geodesic lengths of the tetrahedra around it. -/
noncomputable def reggeAction3 (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (U : Set (Fin 3 → ℝ))
    (N : ℕ) : ℝ :=
  ∑ k : Fin 7, ∑ z : Fin 3 → Fin N,
    hingeLen g U (hingeMid N k z) (1 / (N : ℝ)) k * hingeDef g U (hingeMid N k z) (1 / (N : ℝ)) k

/-- The hinge midpoints lie in the cell of their lower corner. -/
theorem hingeMid_mem_cell {N : ℕ} (hN : 0 < N) (k : Fin 7) (z : Fin 3 → Fin N) :
    hingeMid N k z ∈ latticeCell N z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  intro i _
  have h0 : 0 ≤ dirs k i := by fin_cases k <;> fin_cases i <;> simp [dirs]
  have h1 : dirs k i ≤ 1 := by fin_cases k <;> fin_cases i <;> simp [dirs]
  simp only [hingeMid, mem_Ico]
  constructor
  · rw [div_le_div_iff_of_pos_right hN']; linarith
  · rw [← add_div, div_lt_div_iff_of_pos_right hN']; linarith

/-- The density of one edge class: minus the hinge length divided by `ε`, times the second-order
coefficient of the class angle sum. -/
noncomputable def classDensity (g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (k : Fin 7)
    (y : Fin 3 → ℝ) : ℝ := -(√(edgeQ g y (dirs k)) * clsSum (dirs k) (angC2 g y))

/-- The hinge midpoints with lower corner in the cube lie in `[0, 2]³`. -/
theorem hingeMid_mem_box {N : ℕ} (hN : 0 < N) (k : Fin 7) (z : Fin 3 → Fin N) :
    hingeMid N k z ∈ Set.pi univ (fun _ => Icc (0 : ℝ) 2) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := hingeMid_mem_cell hN k z
  have hsub : latticeCell N z ⊆ unitCube := by
    intro y hy i hi
    have h := hy i hi
    simp only [mem_Ico] at h
    have h2 : (z i : ℝ) + 1 ≤ N := by exact_mod_cast (z i).2
    refine ⟨le_trans (by positivity) h.1, ?_⟩
    have : (z i : ℝ) / N + 1 / N ≤ 1 := by rw [← add_div, div_le_one hN']; exact h2
    linarith [h.2]
  intro i hi
  have := hsub hc i hi
  exact ⟨this.1, this.2.trans (by norm_num)⟩

/-- The unit cube lies in the box `[0, 2]³`. -/
theorem unitCube_subset_box : unitCube ⊆ Set.pi univ (fun _ => Icc (0 : ℝ) 2) :=
  Set.pi_mono fun _ _ => Icc_subset_Icc le_rfl (by norm_num)

/-- **One edge class of the Regge action converges.** For a Riemannian metric `g` on `U` with
`[0, 2]³ ⊆ U`, the sum over the hinges of class `k` of the grid of mesh `1/N` of `ℓ δ` converges, as
`N → ∞`, to the integral over the unit cube of the class density. -/
theorem regge_class_tendsto (hg : IsRiemMetric g U)
    (hQU : Set.pi univ (fun _ => Icc (0 : ℝ) 2) ⊆ U) (k : Fin 7) :
    Tendsto (fun N : ℕ => ∑ z : Fin 3 → Fin N, hingeLen g U (hingeMid N k z) (1 / (N : ℝ)) k *
        hingeDef g U (hingeMid N k z) (1 / (N : ℝ)) k) atTop
      (𝓝 (∫ y in unitCube, classDensity g k y)) := by
  have hK : IsCompact (Set.pi univ (fun _ : Fin 3 => Icc (0 : ℝ) 2)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, r, hr, hbd⟩ := hinge_term hg hK hQU k
  have hFc : ContinuousOn (classDensity g k) unitCube := by
    unfold classDensity
    have h1 : ContinuousOn (fun v => √(edgeQ g v (dirs k))) U :=
      Real.continuous_sqrt.comp_continuousOn (continuousOn_edgeQ hg.coord (dirs k))
    exact ((h1.mul (continuousOn_clsAngC2 hg (dirs k))).neg).mono
      (unitCube_subset_box.trans hQU)
  have hpos : ∀ {N : ℕ} (z : Fin 3 → Fin N), 0 < N := fun z => Fin.pos (z 0)
  have hA := riemann_sum_tendsto hFc (fun N z => hingeMid N k z) (fun N z => hingeMid_mem_cell (hpos z) k z)
  -- the difference tends to zero
  have hdiff : Tendsto (fun N : ℕ => (∑ z : Fin 3 → Fin N, hingeLen g U (hingeMid N k z) (1 / (N : ℝ)) k *
        hingeDef g U (hingeMid N k z) (1 / (N : ℝ)) k) -
      (∑ z : Fin 3 → Fin N, classDensity g k (hingeMid N k z)) * (1 / (N : ℝ)) ^ 3) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat M)
    obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / r)
    filter_upwards [eventually_ge_atTop (N0 + 1)] with N hN
    have hNpos : 0 < N := by omega
    have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hε : 1 / (N : ℝ) ≤ r := by
      have : 1 / r < N := hN0.trans (by exact_mod_cast (by omega : N0 < N))
      rw [div_lt_iff₀ hr] at this
      rw [div_le_iff₀ hN']; nlinarith
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ z : Fin 3 → Fin N, |hingeLen g U (hingeMid N k z) (1 / (N : ℝ)) k *
        hingeDef g U (hingeMid N k z) (1 / (N : ℝ)) k -
        classDensity g k (hingeMid N k z) * (1 / (N : ℝ)) ^ 3| ≤ M * (1 / (N : ℝ)) ^ 4 := by
      intro z
      have := hbd (hingeMid N k z) (hingeMid_mem_box hNpos k z) (1 / (N : ℝ)) (by positivity) hε
      unfold hingeLen hingeDef classDensity
      convert this using 2
      ring
    calc ∑ z : Fin 3 → Fin N, |_| ≤ ∑ z : Fin 3 → Fin N, M * (1 / (N : ℝ)) ^ 4 :=
          Finset.sum_le_sum fun z _ => hterm z
      _ = M / N := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp
        field_simp
  have := hA.add hdiff
  simpa using (hdiff.add hA).congr (fun N => by ring)

/-- **The classes add up to half the scalar curvature times the volume density.** At every point of `U`,
the sum of the class densities is `(R/2) √det g`. -/
theorem sum_classDensity (hg : IsRiemMetric g U) {y : Fin 3 → ℝ} (hy : y ∈ U) :
    ∑ k : Fin 7, classDensity g k y = scalarCurvature g y / 2 * √((g y).det) := by
  have := (jetStarCore_of_chart hg hy).curvature
  unfold classDensity
  rw [Finset.sum_neg_distrib, this]
  ring

/-- **The 3D Regge action of the Kuhn grid converges to half the Einstein–Hilbert action.** For a
Riemannian metric `g` on `U` with `[0, 2]³ ⊆ U`, the Regge action `reggeAction3 g U N` of the Kuhn grid of mesh
`1/N` (hinge lengths and deficit angles from the geodesic distance of `g`) converges, as `N → ∞`, to
`∫_{[0,1]³} (R/2) √det g`, with `R` the scalar curvature. -/
theorem regge3d_tendsto (hg : IsRiemMetric g U)
    (hQU : Set.pi univ (fun _ => Icc (0 : ℝ) 2) ⊆ U) :
    Tendsto (fun N : ℕ => reggeAction3 g U N) atTop
      (𝓝 (∫ y in unitCube, scalarCurvature g y / 2 * √((g y).det))) := by
  have hcomp : IsCompact unitCube := isCompact_univ_pi fun _ => isCompact_Icc
  have hsubU : unitCube ⊆ U := unitCube_subset_box.trans hQU
  have hint : ∀ k : Fin 7, IntegrableOn (classDensity g k) unitCube := fun k => by
    unfold classDensity
    have h1 : ContinuousOn (fun v => √(edgeQ g v (dirs k))) U :=
      Real.continuous_sqrt.comp_continuousOn (continuousOn_edgeQ hg.coord (dirs k))
    exact (((h1.mul (continuousOn_clsAngC2 hg (dirs k))).neg).mono hsubU).integrableOn_compact hcomp
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin 7)) fun k _ => regge_class_tendsto hg hQU k
  have hlim : ∑ k : Fin 7, ∫ y in unitCube, classDensity g k y =
      ∫ y in unitCube, scalarCurvature g y / 2 * √((g y).det) := by
    rw [← integral_finset_sum _ (fun k _ => hint k)]
    exact setIntegral_congr_fun hcomp.measurableSet (fun y hy => sum_classDensity hg (hsubU hy))
  rw [hlim] at hsum
  refine hsum.congr' (Eventually.of_forall fun N => ?_)
  simp only [reggeAction3]

end Lightlike.Regge.Conv3
