import Lightlike.Regge.Conv3.JetContinuity
import Lightlike.Regge.Conv3.ChartChangeGeneral
import Lightlike.Regge.Conv3.ClassUniform
import Lightlike.Regge.Conv3.AngleClose

/-!
# The class angle sum of the true star at a hinge, uniformly on a compact set

For a Riemannian metric `g` on `U`, a compact set `K ⊆ U` of hinge midpoints and an edge class `k`, the sum of
the dihedral angles of the tetrahedra of the Kuhn star of a hinge at `v ∈ K`, computed with the true
geodesic squared lengths at scale `ε`, is `2π + ε² c₂(v) + O(ε³)` with the `O` constant independent of `v`
(`hinge_expansion_true`). `c₂(v)` is the second-order coefficient of the jet of `g` at `v`.

The constants are gathered once in `hinge_data` (compactness: a lower bound of the hinge lengths, bounds of
the first- and second-order parts, the Lipschitz radius of the dihedral angle, the `ε⁵` bound of the true
lengths, and the uniform class expansion); `hinge_expansion_true` assembles them with `dsq_close`.

## Main results

* `hinge_data`: the uniform constants.
* `hinge_expansion_true`: the uniform expansion of the class angle sum of the true star.

**Limits.** One edge class of the standard cubical Kuhn star at one scale `ε`; the constants are not
explicit and the statement is local in `ε` (`0 < ε ≤ r`).
-/

open Real Matrix Lightlike Filter Topology Metric Set
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)}

/-- `clsSum` commutes with subtraction. -/
theorem clsSum_sub (w : Fin 3 → ℝ) (A B : Fin 6 → Fin 6 → ℝ) :
    clsSum w (fun σ h => A σ h - B σ h) = clsSum w A - clsSum w B := by
  classical
  simp only [clsSum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun h _ => ?_
  split_ifs <;> ring

/-- **The uniform constants of the hinge expansion.** For a Riemannian metric `g` on `U`, a compact
`K ⊆ U` and an edge class `k`, there are constants valid for all hinge midpoints `v ∈ K`: a lower bound
`a > 0` of the hinge lengths, bounds `B` of the first- and second-order parts, a Lipschitz radius `δ ≤ a/2`
and constant `C0` of `Dsq` around the base lengths, the `ε⁵` bound of `trueLen_sub_incLen`, and the
uniform class expansion. -/
theorem hinge_data (hg : IsRiemMetric g U) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hne : K.Nonempty) (k : Fin 7) :
    ∃ (a B δ C0 C5 r5 M1 r1 : ℝ), 0 < a ∧ 0 ≤ B ∧ 0 < δ ∧ δ ≤ a / 2 ∧ 0 ≤ C0 ∧ 0 < r5 ∧ 0 < r1 ∧
      (∀ v ∈ K, ∀ σ h : Fin 6, a ≤ incQ g v σ h 0 ∧ ‖incC g v σ h‖ ≤ B ∧ ‖incR g v σ h‖ ≤ B) ∧
      (∀ v ∈ K, ∀ σ h : Fin 6, ∀ L L' : Fin 6 → ℝ, ‖L - incQ g v σ h‖ ≤ δ →
        ‖L' - incQ g v σ h‖ ≤ δ → |Dsq L' - Dsq L| ≤ C0 * ‖L' - L‖) ∧
      (∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r5 → ∀ σ h : Fin 6,
        ‖trueLen g U v ε σ h - incLen g v ε σ h‖ ≤ C5 * ε ^ 5) ∧
      (∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r1 →
        |clsSum (dirs k) (fun σ h => Dsq (incLen g v ε σ h)) - 2 * π
          - ε ^ 2 * clsSum (dirs k) (angC2 g v)| ≤ M1 * ε ^ 3) := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Nonempty K := hne.to_subtype
  have hP : ∀ p : K, (g p).PosDef := fun p => hg.posDef p (hKU p.2)
  have hqc : ∀ σ h, Continuous fun p : K => incQ g p σ h := fun σ h =>
    ((continuousOn_incQ hg.coord σ h).mono hKU).domRestrict
  have hcc : ∀ σ h, Continuous fun p : K => incC g p σ h := fun σ h =>
    ((continuousOn_incC hg.coord σ h).mono hKU).domRestrict
  have hρc : ∀ σ h, Continuous fun p : K => incR g p σ h := fun σ h =>
    ((continuousOn_incR hg.coord σ h).mono hKU).domRestrict
  have hv : ∀ p : K, ∀ σ h, Valid (incQ g p σ h) := fun p σ h => valid_incQ (hP p) σ h
  have hsum : ∀ p : K, clsSum (dirs k) (fun σ h => Dsq (incQ g p σ h)) = 2 * π := fun p =>
    jet_angle_sum (hP p) k
  have hfirst : ∀ p : K, clsSum (dirs k) (fun σ h => Dh (incQ g p σ h, incC g p σ h)) = 0 :=
    fun p => (jetStarCore_of_chart hg (hKU p.2)).first_order k
  obtain ⟨M1, r1, hr1, h1⟩ := class_sum_expansion_uniform (P := K) (dirs k) (fun p : K => incQ g p)
    (fun p : K => incC g p) (fun p : K => incR g p) hqc hcc hρc hv hsum hfirst
  have hQ : Continuous fun x : K × (Fin 6 × Fin 6) => incQ g x.1 x.2.1 x.2.2 :=
    continuous_prod_of_discrete_right.2 fun b => hqc b.1 b.2
  have hKQc : IsCompact (Set.range (fun x : K × (Fin 6 × Fin 6) => incQ g x.1 x.2.1 x.2.2)) :=
    isCompact_range hQ
  have hKQV : ∀ L ∈ Set.range (fun x : K × (Fin 6 × Fin 6) => incQ g x.1 x.2.1 x.2.2), Valid L := by
    rintro _ ⟨x, rfl⟩; exact hv x.1 x.2.1 x.2.2
  obtain ⟨δ0, C0, hδ0, hC0, hlip⟩ := Dsq_lipschitz_uniform hKQc hKQV
  have hQ0 : Continuous fun x : K × (Fin 6 × Fin 6) => incQ g x.1 x.2.1 x.2.2 0 :=
    (continuous_apply 0).comp hQ
  obtain ⟨x0, -, hx0'⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty (α := K × (Fin 6 × Fin 6))) hQ0.continuousOn
  have ha0 : 0 < incQ g x0.1 x0.2.1 x0.2.2 0 := (hv x0.1 x0.2.1 x0.2.2).1
  have hCont : Continuous fun x : K × (Fin 6 × Fin 6) =>
      ‖incC g x.1 x.2.1 x.2.2‖ + ‖incR g x.1 x.2.1 x.2.2‖ :=
    ((continuous_prod_of_discrete_right.2 fun b => hcc b.1 b.2).norm).add
      ((continuous_prod_of_discrete_right.2 fun b => hρc b.1 b.2).norm)
  obtain ⟨y0, -, hy0'⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty (α := K × (Fin 6 × Fin 6))) hCont.continuousOn
  obtain ⟨C5, r5, hr5, h5⟩ := trueLen_sub_incLen hg hK hKU
  have hamin : ∀ x : K × (Fin 6 × Fin 6),
      incQ g x0.1 x0.2.1 x0.2.2 0 ≤ incQ g x.1 x.2.1 x.2.2 0 := fun x => hx0' (Set.mem_univ x)
  have hbmax : ∀ x : K × (Fin 6 × Fin 6), ‖incC g x.1 x.2.1 x.2.2‖ + ‖incR g x.1 x.2.1 x.2.2‖ ≤
      ‖incC g y0.1 y0.2.1 y0.2.2‖ + ‖incR g y0.1 y0.2.1 y0.2.2‖ := fun x => hy0' (Set.mem_univ x)
  refine ⟨incQ g x0.1 x0.2.1 x0.2.2 0, ‖incC g y0.1 y0.2.1 y0.2.2‖ + ‖incR g y0.1 y0.2.1 y0.2.2‖,
    min δ0 (incQ g x0.1 x0.2.1 x0.2.2 0 / 2), C0, C5, r5, M1, r1, ha0, by positivity,
    lt_min hδ0 (half_pos ha0), min_le_right _ _, hC0, hr5, hr1, ?_, ?_, h5, ?_⟩
  · intro v hv' σ h
    refine ⟨hamin (⟨v, hv'⟩, (σ, h)), ?_, ?_⟩
    · exact le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hbmax (⟨v, hv'⟩, (σ, h)))
    · exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hbmax (⟨v, hv'⟩, (σ, h)))
  · intro v hv' σ h L L' hL hL'
    exact hlip (incQ g v σ h) ⟨(⟨v, hv'⟩, (σ, h)), rfl⟩ L L' (hL.trans (min_le_left _ _))
      (hL'.trans (min_le_left _ _))
  · intro v hv' ε hε hεr
    have := h1 ⟨v, hv'⟩ ε hε hεr
    have e : clsSum (dirs k) (angC2 g v) = clsSum (dirs k) (fun σ h => Dh (incQ g v σ h, incR g v σ h)
      + (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) (incQ g v σ h) (incC g v σ h) (incC g v σ h)) := rfl
    rw [e]
    simp only [incLen_eq]
    exact this

/-- **The class angle sum of the true star at a hinge, uniformly on a compact set of hinge midpoints.**
For a Riemannian metric `g` on `U`, a compact `K ⊆ U` and an edge class `k` there are `M` and `r > 0`
such that for every hinge midpoint `v ∈ K` and `0 < ε ≤ r`, the sum of the dihedral angles of the
tetrahedra of the star around the hinge with the true geodesic lengths is `2π + ε² c₂(v)` up to
`M ε³`, with `c₂(v)` the second-order coefficient `clsSum (dirs k) (angC2 g v)` of the jet at `v`. -/
theorem hinge_expansion_true (hg : IsRiemMetric g U) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) (k : Fin 7) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |clsSum (dirs k) (fun σ h => Dsq (trueLen g U v ε σ h)) - 2 * π
        - ε ^ 2 * clsSum (dirs k) (angC2 g v)| ≤ M * ε ^ 3 := by
  classical
  by_cases hne : K.Nonempty
  swap
  · exact ⟨0, 1, one_pos, fun v hv => absurd ⟨v, hv⟩ hne⟩
  obtain ⟨a, B, δ, C0, C5, r5, M1, r1, ha0, hB0, hδpos, hδa, hC0, hr5, hr1, hbd, hlip, h5, h1⟩ :=
    hinge_data hg hK hKU hne k
  set E : ℝ := 2 * B + |C5| + 1 with hE
  have hEpos : 0 < E := by positivity
  refine ⟨36 * C0 * |C5| + M1, min (min r1 r5) (min 1 (δ / (2 * E))), lt_min (lt_min hr1 hr5)
    (lt_min one_pos (by positivity)), fun v hv ε hε hεr => ?_⟩
  have hεr1 : ε ≤ r1 := hεr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεr5 : ε ≤ r5 := hεr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := hεr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ : ε ≤ δ / (2 * E) := hεr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεE : (2 * B + |C5| + 1) * ε ≤ δ / 2 := by
    calc (2 * B + |C5| + 1) * ε ≤ E * (δ / (2 * E)) := by gcongr
      _ = δ / 2 := by field_simp
  have hinc : ∀ σ h : Fin 6, |Dsq (trueLen g U v ε σ h) - Dsq (incLen g v ε σ h)| ≤
      C0 * |C5| * ε ^ 3 := fun σ h => by
    have hq := hbd v hv σ h
    have hincl := incLen_eq g v ε σ h
    rw [hincl]
    refine dsq_close (δ := δ) (a := a) (B := B) hε hε1 hq.1 ha0 hδa hδpos hC0 hq.2.1 hq.2.2 ?_ ?_ ?_
    · have h1' := h5 v hv ε hε hεr5 σ h
      rw [hincl] at h1'
      exact h1'.trans (mul_le_mul_of_nonneg_right (le_abs_self C5) (by positivity))
    · rw [abs_abs]; exact hεE
    · intro L L' hL hL'
      exact hlip v hv σ h L L' hL hL'
  have hdiff : |clsSum (dirs k) (fun σ h => Dsq (trueLen g U v ε σ h))
      - clsSum (dirs k) (fun σ h => Dsq (incLen g v ε σ h))| ≤ 36 * (C0 * |C5| * ε ^ 3) := by
    rw [← clsSum_sub]
    exact abs_clsSum_le (dirs k) _ (by positivity) hinc
  have h1p := h1 v hv ε hε hεr1
  calc _ ≤ |clsSum (dirs k) (fun σ h => Dsq (trueLen g U v ε σ h))
        - clsSum (dirs k) (fun σ h => Dsq (incLen g v ε σ h))|
        + |clsSum (dirs k) (fun σ h => Dsq (incLen g v ε σ h)) - 2 * π
          - ε ^ 2 * clsSum (dirs k) (angC2 g v)| := by
        refine le_trans (le_of_eq ?_) (abs_add_le _ _)
        congr 1; ring
    _ ≤ 36 * (C0 * |C5| * ε ^ 3) + M1 * ε ^ 3 := add_le_add hdiff h1p
    _ = (36 * C0 * |C5| + M1) * ε ^ 3 := by ring

end Lightlike.Regge.Conv3
