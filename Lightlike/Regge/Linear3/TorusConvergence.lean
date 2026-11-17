import Lightlike.Regge.Linear3.TorusBridgeLengths
import Lightlike.Regge.Conv3.HingeTerm

/-!
# The Regge action of the periodic Kuhn complex of the torus converges to half the Einstein–Hilbert action

For a Riemannian metric `g` on `ℝ³` invariant under integer translations, the periodic Kuhn complex
`torusComplex N` of the torus `(ℝ/ℤ)³` (a closed simplicial 3-complex, `N³` cubes and `6 N³` tetrahedra) with
the geodesic lengths of `g` has Regge action tending to `∫_{[0,1]³} (R/2) √det g`. This is
`Conv3.regge3d_tendsto` (a sum of hinge terms of the lattice) transported to the actual simplicial
complex by `reggeAction_torus_eq`; on the torus there is no boundary layer. The remaining hypothesis of
`reggeAction_torus_eq`, that the geodesic length of every hinge is positive, holds for large `N`
(`hpos_large`): a short edge of direction `dirs k` has length `ε √(g(w, w)) + O(ε³)` uniformly in the
starting point (`dist_pos_dir`, from `Conv3.hinge_length`, the periodicity of `g`).

## Main results

* `dist_pos_dir`, `hpos_large`: the hinges of a fine complex have positive geodesic length.
* `torus_regge_converges`: the convergence to `∫ (R/2) √det g`.

**Limits.** Convergence only, no rate; one periodic metric, the standard cubical Kuhn triangulation of the
torus; Riemannian signature. It is not Cheeger–Müller–Schrader's theorem for arbitrary fine triangulations
of a manifold, and it does not cover the sphere (no triangulation of a closed surface other than the torus).
-/

open Real Finset Filter Topology
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3 Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}

theorem dirs_nonneg (k : Fin 7) (i : Fin 3) : 0 ≤ dirs k i := by
  rw [← dirsN_cast]; positivity

theorem dirs_le_one (k : Fin 7) (i : Fin 3) : dirs k i ≤ 1 := by
  rw [← dirsN_cast]; exact_mod_cast dirsN_le k i

/-- **Positivity of the geodesic length of a short edge of direction `dirs k`**, uniformly in the
starting point, for a metric invariant under integer translations. -/
theorem dist_pos_dir (hg : IsRiemMetric g Set.univ)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), g (p + fun i => (e i : ℝ)) = g p) (k : Fin 7) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ x : Fin 3 → ℝ,
      0 < Geodesic.dist g Set.univ x (x + ε • dirs k) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 3 => Set.Icc (0 : ℝ) 2) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, r, hr, hb⟩ := hinge_length hg hK (Set.subset_univ _) (dirs_ne_zero k) (dirs_norm_le k)
  -- a positive lower bound of `edgeQ` on the box
  have hne : (Set.pi Set.univ fun _ : Fin 3 => Set.Icc (0 : ℝ) 2).Nonempty :=
    ⟨fun _ => 0, fun i _ => ⟨le_rfl, by norm_num⟩⟩
  obtain ⟨v0, hv0, hmin⟩ := hK.exists_isMinOn hne
    ((continuousOn_edgeQ hg.coord (dirs k)).mono (Set.subset_univ _))
  have hq : 0 < edgeQ g v0 (dirs k) := by
    have := (hg.posDef v0 (Set.mem_univ _)).dotProduct_mulVec_pos (dirs_ne_zero k)
    simpa [edgeQ] using this
  set q := edgeQ g v0 (dirs k) with hqdef
  have hsq : 0 < √q := Real.sqrt_pos.2 hq
  have hCq : ∀ ε : ℝ, 0 < ε → ε ≤ √(√q / (|C| + 1)) → C * ε ^ 2 < √q := by
    intro ε he hed
    have hε2 : ε ^ 2 ≤ √q / (|C| + 1) := by
      rw [← Real.sq_sqrt (by positivity : 0 ≤ √q / (|C| + 1))]
      exact pow_le_pow_left₀ he.le hed 2
    have h1 : C * ε ^ 2 ≤ |C| * ε ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h2 : |C| * ε ^ 2 ≤ |C| * (√q / (|C| + 1)) := mul_le_mul_of_nonneg_left hε2 (abs_nonneg C)
    have h3 : |C| * (√q / (|C| + 1)) < √q := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]
    linarith
  refine ⟨min (min r 1) (√(√q / (|C| + 1))), lt_min (lt_min hr one_pos) (by positivity),
    fun ε he hed x => ?_⟩
  have hεr : ε ≤ r := (hed.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (hed.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hεs : ε ≤ √(√q / (|C| + 1)) := hed.trans (min_le_right _ _)
  set e : Fin 3 → ℤ := fun i => -⌊x i⌋ with he_def
  set x' : Fin 3 → ℝ := x + fun i => (e i : ℝ) with hx'
  set v : Fin 3 → ℝ := x' + (ε / 2) • dirs k with hv
  have hx'mem : ∀ i, 0 ≤ x' i ∧ x' i < 1 := fun i => by
    simp only [hx', Pi.add_apply, he_def, Int.cast_neg]
    constructor
    · linarith [Int.floor_le (x i)]
    · linarith [Int.lt_floor_add_one (x i)]
  have hvK : v ∈ Set.pi Set.univ fun _ : Fin 3 => Set.Icc (0 : ℝ) 2 := by
    intro i _
    have h0 := dirs_nonneg k i
    have h1 := dirs_le_one k i
    have := hx'mem i
    simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> nlinarith [this.1, this.2]
  have hb' := hb v hvK ε he hεr
  have hQ : q ≤ edgeQ g v (dirs k) := hmin hvK
  have hlow : √q ≤ √(edgeQ g v (dirs k)) := Real.sqrt_le_sqrt hQ
  have hpos : 0 < Geodesic.dist g Set.univ (v - (ε / 2) • dirs k) (v + (ε / 2) • dirs k) := by
    have h1 := (abs_le.1 hb').1
    have h2 : 0 < ε * (√q - C * ε ^ 2) := mul_pos he (by linarith [hCq ε he hεs])
    nlinarith [mul_le_mul_of_nonneg_left hlow he.le]
  have h1 : v - (ε / 2) • dirs k = x' := by simp [hv]
  have h2 : v + (ε / 2) • dirs k = x' + ε • dirs k := by
    funext i; simp [hv]; ring
  rw [h1, h2] at hpos
  have := Geodesic.dist_translate_univ (g := g) (fun i => (e i : ℝ)) (hper · e) x (x + ε • dirs k)
  have e2 : (x + ε • dirs k) + (fun i => (e i : ℝ)) = x' + ε • dirs k := by
    funext i; simp [hx']; ring
  rw [e2] at this
  rw [← this]
  exact hpos


theorem hinge_dir : ∀ σ h : Fin 6, ∃ k : Fin 7, ∀ i : Fin 3,
    koff (hQ h) (perms σ i) = koff (hP h) (perms σ i) + dirsN k i := by
  decide

/-- **The hinges of a fine periodic complex have positive length.** -/
theorem hpos_large (hg : IsRiemMetric g Set.univ)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), g (p + fun i => (e i : ℝ)) = g p) :
    ∃ N0 : ℕ, ∀ (N : ℕ) [NeZero N], N0 ≤ N → ∀ (ct : Fin 3 → ℤ) (σ h : Fin 6),
      0 < Geodesic.dist g Set.univ (cornerPt N ct σ (hP h)) (cornerPt N ct σ (hQ h)) := by
  choose! δ hδ using fun k => dist_pos_dir hg hper k
  have hmin : 0 < Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ δ :=
    (Finset.lt_inf'_iff _).2 fun k _ => (hδ k).1
  obtain ⟨N0, hN0⟩ := exists_nat_gt (1 / Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ δ)
  refine ⟨N0, fun N _ hN ct σ h => ?_⟩
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
    have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    have : 0 < 1 / Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ δ := by positivity
    linarith
  obtain ⟨k, hk⟩ := hinge_dir σ h
  have hε : 1 / (N : ℝ) ≤ δ k := by
    have h1 : 1 / (N : ℝ) ≤ Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ δ := by
      rw [div_le_iff₀ hNpos]
      have : 1 / Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ δ < N := by
        have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
      rw [div_lt_iff₀ hmin] at this
      linarith
    exact h1.trans (Finset.inf'_le _ (Finset.mem_univ k))
  have hQ : cornerPt N ct σ (hQ h) = cornerPt N ct σ (hP h) + (1 / (N : ℝ)) • dirs k := by
    funext i
    simp only [cornerPt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hk i]
    push_cast
    rw [dirsN_cast]
    field_simp
    ring
  rw [hQ]
  exact (hδ k).2 _ (by positivity) hε _


/-- **The Regge action of the periodic Kuhn complex of the torus converges to half the Einstein–Hilbert
action.** For a Riemannian metric `g` on `ℝ³` invariant under integer translations, the Regge action of
the Kuhn complex `torusComplex N` of the torus `(ℝ/ℤ)³` with the geodesic lengths of `g`
tends to `∫_{[0,1]³} (R/2) √det g` as `N → ∞`: for every `ε > 0` there is `N₀` such that for all `N ≥ N₀`
the difference is less than `ε`. -/
theorem torus_regge_converges (hg : IsRiemMetric g Set.univ)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), g (p + fun i => (e i : ℝ)) = g p) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ (N : ℕ) [NeZero N] (hN : 3 ≤ N), N0 ≤ N →
      |reggeAction (torusComplex N (by omega)) (lenD N (Geodesic.dist g Set.univ)) -
        ∫ y in unitCube, scalarCurvature g y / 2 * √((g y).det)| < ε := by
  intro ε hε
  have ht := regge3d_tendsto hg (Set.subset_univ _)
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 ht ε hε
  obtain ⟨N2, hN2⟩ := hpos_large hg hper
  refine ⟨max N1 N2, fun N _ hN hmax => ?_⟩
  have h1 : N1 ≤ N := (le_max_left _ _).trans hmax
  have h2 : N2 ≤ N := (le_max_right _ _).trans hmax
  rw [reggeAction_torus_eq N hN g hper (hN2 N h2)]
  have := hN1 N h1
  rwa [Real.dist_eq] at this

end Lightlike.Regge.Linear3
