import Mathlib

/-!
# Lattice Riemann sums on the unit cube of `Fin 3 → ℝ`

A sum over the cubical lattice of mesh `1/N` of a function with a uniform `C/N` error against a
sup-norm Lipschitz limit differs from the integral of the limit by at most `(C + Lf)/N`.
-/

open MeasureTheory Set
namespace Lightlike.Regge.Conv3

/-- The unit cube `[0,1]³` in `Fin 3 → ℝ`. -/
def unitCube : Set (Fin 3 → ℝ) := Set.pi univ (fun _ => Icc 0 1)

/-- The lattice point `x / N` of the cubical lattice of mesh `1/N`. -/
noncomputable def latticePt (N : ℕ) (x : Fin 3 → Fin N) : Fin 3 → ℝ := fun i => (x i : ℝ) / N

/-- The half-open cell of the lattice of mesh `1/N` with lower corner `x / N`. -/
def latticeCell (N : ℕ) (x : Fin 3 → Fin N) : Set (Fin 3 → ℝ) :=
  Set.pi univ (fun i => Ico ((x i : ℝ) / N) ((x i : ℝ) / N + 1 / N))

/-- Lattice cells are measurable. -/
theorem latticeCell_measurable (N : ℕ) (x : Fin 3 → Fin N) : MeasurableSet (latticeCell N x) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- A lattice cell of mesh `1/N` has volume `(1/N)³`. -/
theorem latticeCell_volume {N : ℕ} (x : Fin 3 → Fin N) :
    (volume (latticeCell N x)).toReal = (1 / (N : ℝ)) ^ 3 := by
  unfold latticeCell
  rw [Real.volume_pi_Ico_toReal (fun i => by
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith)]
  simp

/-- Distinct lattice cells are disjoint. -/
theorem latticeCell_disjoint {N : ℕ} (hN : 0 < N) :
    Pairwise (Function.onFun Disjoint (latticeCell N)) := by
  intro x y hxy
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Function.onFun, Set.disjoint_left]
  intro z hzx hzy
  apply hxy
  funext i
  have h1 := hzx i (mem_univ _)
  have h2 := hzy i (mem_univ _)
  simp only [mem_Ico] at h1 h2
  have e1 : (y i : ℝ) < x i + 1 := by
    have := lt_of_le_of_lt h2.1 h1.2
    have h3 : (y i : ℝ) / N < ((x i : ℝ) + 1) / N := by rw [add_div]; linarith
    rw [div_lt_div_iff_of_pos_right hN'] at h3; exact h3
  have e2 : (x i : ℝ) < y i + 1 := by
    have := lt_of_le_of_lt h1.1 h2.2
    have h3 : (x i : ℝ) / N < ((y i : ℝ) + 1) / N := by rw [add_div]; linarith
    rw [div_lt_div_iff_of_pos_right hN'] at h3; exact h3
  apply Fin.ext
  have e1' : (y i : ℕ) < x i + 1 := by exact_mod_cast e1
  have e2' : (x i : ℕ) < y i + 1 := by exact_mod_cast e2
  omega

/-- The lattice cells tile the half-open unit cube. -/
theorem latticeCell_iUnion {N : ℕ} (hN : 0 < N) :
    (⋃ x : Fin 3 → Fin N, latticeCell N x) = Set.pi univ (fun _ => Ico (0 : ℝ) 1) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  ext y
  simp only [mem_iUnion, latticeCell, mem_pi, mem_univ, true_implies, mem_Ico]
  constructor
  · rintro ⟨x, hx⟩ i
    obtain ⟨h1, h2⟩ := hx i
    have hxi : (x i : ℝ) + 1 ≤ N := by exact_mod_cast (x i).2
    refine ⟨le_trans (by positivity) h1, lt_of_lt_of_le h2 ?_⟩
    rw [← add_div, div_le_one hN']; exact hxi
  · intro hy
    refine ⟨fun i => ⟨⌊y i * N⌋₊, ?_⟩, fun i => ?_⟩
    · have := (hy i).2
      have h4 : y i * N < N := by nlinarith [(hy i).1]
      exact (Nat.floor_lt (mul_nonneg (hy i).1 hN'.le)).2 (by exact_mod_cast h4)
    · have h0 : 0 ≤ y i * N := mul_nonneg (hy i).1 hN'.le
      have f1 := Nat.floor_le h0
      have f2 := Nat.lt_floor_add_one (y i * N)
      simp only
      constructor
      · rw [div_le_iff₀ hN']; exact f1
      · rw [← add_div, lt_div_iff₀ hN']; exact f2

/-- **Riemann sum on the cubical lattice.** If `f` is Lipschitz with constant `Lf` for the sup norm
on the unit cube, the left-corner Riemann sum of mesh `1/N` differs from the integral by at most
`Lf / N`. -/
theorem riemann_sum_lipschitz {f : (Fin 3 → ℝ) → ℝ} {Lf : ℝ} (hL : 0 ≤ Lf)
    (hf : ∀ x ∈ unitCube, ∀ y ∈ unitCube, |f x - f y| ≤ Lf * ‖x - y‖)
    {N : ℕ} (hN : 0 < N) :
    |(∑ x : Fin 3 → Fin N, f (latticePt N x)) * (1 / (N : ℝ)) ^ 3 - ∫ y in unitCube, f y|
      ≤ Lf / N := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hcomp : IsCompact unitCube := isCompact_univ_pi fun _ => isCompact_Icc
  have hlip : LipschitzOnWith Lf.toNNReal f unitCube := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
    exact hf x hx y hy
  have hint : IntegrableOn f unitCube := hlip.continuousOn.integrableOn_compact hcomp
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
  have hcorner : ∀ x, latticePt N x ∈ latticeCell N x := fun x i _ =>
    ⟨le_rfl, by simp [latticePt]; positivity⟩
  have hcell : ∀ x : Fin 3 → Fin N,
      |f (latticePt N x) * (1 / (N : ℝ)) ^ 3 - ∫ y in latticeCell N x, f y|
        ≤ Lf / N * (1 / (N : ℝ)) ^ 3 := by
    intro x
    have hvol : volume.real (latticeCell N x) = (1 / (N : ℝ)) ^ 3 := latticeCell_volume x
    have hfin : volume (latticeCell N x) < ⊤ :=
      (measure_mono (hcell_sub x)).trans_lt hcomp.measure_lt_top
    have hI : IntegrableOn f (latticeCell N x) := hint.mono_set (hcell_sub x)
    have e1 : f (latticePt N x) * (1 / (N : ℝ)) ^ 3 - ∫ y in latticeCell N x, f y
        = ∫ y in latticeCell N x, (f (latticePt N x) - f y) := by
      rw [integral_sub (integrableOn_const hfin.ne) hI, setIntegral_const, hvol, smul_eq_mul, mul_comm]
    rw [e1]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := latticeCell N x)
      (f := fun y => f (latticePt N x) - f y) (C := Lf / N) hfin (fun y hy => by
        rw [Real.norm_eq_abs]
        refine (hf _ (hcell_sub x (hcorner x)) y (hcell_sub x hy)).trans ?_
        rw [div_eq_mul_one_div]
        refine mul_le_mul_of_nonneg_left ?_ hL
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
        have hy' := hy i (mem_univ _)
        simp only [mem_Ico] at hy'
        simp only [Pi.sub_apply, latticePt, Real.norm_eq_abs]
        rw [abs_of_nonpos (by linarith [hy'.1])]
        linarith [hy'.2])
    rwa [hvol, Real.norm_eq_abs] at this
  have hcard : (Fintype.card (Fin 3 → Fin N) : ℝ) = (N : ℝ) ^ 3 := by simp
  rw [hsplit, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _x : Fin 3 → Fin N, Lf / N * (1 / (N : ℝ)) ^ 3 := Finset.sum_le_sum fun x _ => hcell x
    _ = Lf / N := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; field_simp

/-- A lattice point of mesh  lies in the unit cube. -/
theorem latticePt_mem {N : ℕ} (hN : 0 < N) (x : Fin 3 → Fin N) : latticePt N x ∈ unitCube := by
  intro i _
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by unfold latticePt; positivity, ?_⟩
  unfold latticePt
  rw [div_le_one hN']
  exact_mod_cast (x i).2.le

/-- **From a uniform per-vertex expansion to the integral.** If the vertex densities `ρ N` agree
with a sup-norm Lipschitz limit `F` up to `C / N` on the lattice, the normalised lattice sum of
`ρ N` is within `(C + Lf) / N` of the integral of `F`. Used with `F = -(R/2) √det g`.
-/
theorem lattice_sum_converges {ρ : ℕ → (Fin 3 → ℝ) → ℝ} {F : (Fin 3 → ℝ) → ℝ} {C Lf : ℝ}
    (hL : 0 ≤ Lf)
    (hF : ∀ x ∈ unitCube, ∀ y ∈ unitCube, |F x - F y| ≤ Lf * ‖x - y‖)
    {N : ℕ} (hN : 0 < N)
    (hρ : ∀ x : Fin 3 → Fin N, |ρ N (latticePt N x) - F (latticePt N x)| ≤ C / N) :
    |(∑ x : Fin 3 → Fin N, ρ N (latticePt N x)) * (1 / (N : ℝ)) ^ 3 - ∫ y in unitCube, F y|
      ≤ (C + Lf) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hR := riemann_sum_lipschitz hL hF hN
  have hcard : (Fintype.card (Fin 3 → Fin N) : ℝ) = (N : ℝ) ^ 3 := by simp
  have h1 : |(∑ x : Fin 3 → Fin N, (ρ N (latticePt N x) - F (latticePt N x))) * (1 / (N : ℝ)) ^ 3|
      ≤ C / N := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < (1 / (N : ℝ)) ^ 3)]
    have := Finset.abs_sum_le_sum_abs (fun x : Fin 3 → Fin N => ρ N (latticePt N x) - F (latticePt N x)) Finset.univ
    have h2 : ∑ x : Fin 3 → Fin N, |ρ N (latticePt N x) - F (latticePt N x)| ≤ (N : ℝ) ^ 3 * (C / N) := by
      calc _ ≤ ∑ _x : Fin 3 → Fin N, C / (N : ℝ) := Finset.sum_le_sum (fun x _ => hρ x)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    calc |∑ x : Fin 3 → Fin N, (ρ N (latticePt N x) - F (latticePt N x))| * (1 / (N : ℝ)) ^ 3
        ≤ ((N : ℝ) ^ 3 * (C / N)) * (1 / (N : ℝ)) ^ 3 :=
          mul_le_mul_of_nonneg_right (this.trans h2) (by positivity)
      _ = C / N := by field_simp
  have h3 : (∑ x : Fin 3 → Fin N, ρ N (latticePt N x)) * (1 / (N : ℝ)) ^ 3 - ∫ y in unitCube, F y
      = (∑ x : Fin 3 → Fin N, (ρ N (latticePt N x) - F (latticePt N x))) * (1 / (N : ℝ)) ^ 3
        + ((∑ x : Fin 3 → Fin N, F (latticePt N x)) * (1 / (N : ℝ)) ^ 3 - ∫ y in unitCube, F y) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [h3]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ C / N + Lf / N := add_le_add h1 hR
    _ = (C + Lf) / N := by ring

end Lightlike.Regge.Conv3
