import Lightlike.Regge.Flat
import Lightlike.Regge.Manifold
import Lightlike.Regge.Embedded
import Lightlike.Regge.ReggeEquations
import Lightlike.Regge.Gradient
import Lightlike.Regge.FlatSolution
import Lightlike.Regge.CombManifold
import Lightlike.Regge.Disc

/-!
# Trust checks for 3D Regge calculus

Checks of the definitions in `Lightlike/Regge/Complex.lean`, `Manifold.lean` and `Embedded.lean`
against known values, and deliberately wrong models and inputs that must fail. Each check's
docstring says what it shows. With all lengths `1` every dihedral angle is `θ = arccos (1/3)`
(`dihedral_one`), and an edge in `n` tetrahedra has deficit `2π - n θ`; we prove `π/3 < θ < 2π/5`.

* **Flat triangulations of `ℝ³`, deficit zero:** the octahedron around its axis
  (`octahedron_deficit`) and the cube split into six Kuhn tetrahedra (`cube_deficit`).
* **Curved examples, deficit nonzero:** the boundary of the 4-simplex (`simplexBoundary`), five
  and six regular tetrahedra around an edge (`ring5_gap_mem`, `cube_deficit_unit`), and any
  complex with unit lengths (`deficit_unit_ne_zero`).
* **Wrong inputs and formulas:** a stretched cube, face angles, exterior angles (which go unnoticed
  on a four-valent edge, `octahedron_exterior_passes`), and all-zero lengths.
* **The manifold condition:** cycle and path links, and three tetrahedra sharing a triangle.
* **Geometric triangulations:** the octahedron (`octahedron_geometric`), and a double ring whose
  deficit `-2π` forces two tetrahedra to overlap (`doubleRing_overlap`).
* **Regge's equations:** the gradient of the regular tetrahedron's action is the exterior angle
  (`regularTet_gradient`); the regular 3-sphere is not stationary, the flat octahedron is
  (`octahedron_stationary`). `scripts/regge/regge_equations_check.py` compares finite differences
  of the action with the deficit angles on a perturbed 3-sphere (agreement to `10⁻⁸`).
* **Combinatorial 3-manifolds:** closed and with boundary, decided by the kernel, and the
  non-manifolds and wrong disc models they reject.
* **Bridge to Ponzano–Regge:** `reggeAction_singleTet`, the phase of the asymptotic formula.
-/

open Real Finset InnerProductSpace

namespace Lightlike.Regge.Tests

open Lightlike.PR (Complex3 dihedral cosDihedral)
open Lightlike.Regge

/-! ## The regular dihedral angle `arccos (1/3)` -/

/-- With all six lengths equal to `1` the dihedral angle is `arccos (1/3)`. -/
theorem dihedral_one : dihedral 1 1 1 1 1 1 = arccos (1 / 3) := by
  rw [dihedral, Lightlike.PR.cos_dihedral_regular one_pos]

/-- The regular dihedral angle exceeds `π/3`, because `cos (π/3) = 1/2 > 1/3`. -/
theorem pi_div_three_lt_arccos : π / 3 < arccos (1 / 3) := by
  have h := arccos_lt_arccos (x := 1 / 3) (y := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  rwa [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])] at h

/-- The regular dihedral angle is less than `2π/5`, because `cos (2π/5) = (√5 - 1)/4 < 1/3`. -/
theorem arccos_lt_two_pi_div_five : arccos (1 / 3) < 2 * π / 5 := by
  have hc : cos (2 * π / 5) = (√5 - 1) / 4 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, cos_two_mul, cos_pi_div_five]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have h5 : cos (2 * π / 5) < 1 / 3 := by
    rw [hc]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  calc arccos (1 / 3) < arccos (cos (2 * π / 5)) :=
        arccos_lt_arccos (neg_one_le_cos _) h5 (by norm_num)
    _ = 2 * π / 5 := arccos_cos (by positivity) (by linarith [pi_pos])

/-- The regular dihedral angle is less than `π/2`. -/
theorem arccos_lt_pi_div_two : arccos (1 / 3) < π / 2 := by
  rw [← arccos_zero]
  exact arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)

/-! ## The boundary of the 4-simplex -/

/-- The boundary of the 4-simplex: the five 4-element subsets of `Fin 5`, a triangulation of the
3-sphere. -/
def simplexBoundary : Complex3 (Fin 5) where
  tets := powersetCard 4 univ
  card_eq := fun _ ht => (mem_powersetCard.mp ht).2

/-- The boundary of the 4-simplex is closed: every triangle lies in two tetrahedra. -/
theorem simplexBoundary_bdryTris : bdryTris simplexBoundary = ∅ := by decide

/-- Its edges are the ten 2-element subsets of `Fin 5`. -/
theorem simplexBoundary_edges : simplexBoundary.edges = powersetCard 2 univ := by decide

/-- Every edge of the boundary of the 4-simplex lies in three tetrahedra. -/
theorem simplexBoundary_star_card :
    ∀ e ∈ simplexBoundary.edges, #(star simplexBoundary e) = 3 := by decide

/-- **Curved example.** With all lengths `1`, every edge of the boundary of the 4-simplex has
deficit angle `2π - 3 arccos (1/3)`, and this is positive. -/
theorem simplexBoundary_deficit {e : Finset (Fin 5)} (he : e ∈ simplexBoundary.edges) :
    deficit simplexBoundary (fun _ => 1) e = 2 * π - 3 * arccos (1 / 3) ∧
      0 < deficit simplexBoundary (fun _ => 1) e := by
  have he2 : #e = 2 := by
    rw [simplexBoundary_edges, mem_powersetCard] at he
    exact he.2
  rw [deficit_const _ _ he2, simplexBoundary_star_card e he, dihedral_one]
  push_cast
  exact ⟨rfl, by linarith [arccos_lt_pi_div_two, pi_pos]⟩

/-- **The Regge action of the regular 3-sphere** with unit edges is `10 (2π - 3 arccos (1/3))`,
which is positive. -/
theorem simplexBoundary_reggeAction :
    reggeAction simplexBoundary (fun _ => 1) = 10 * (2 * π - 3 * arccos (1 / 3)) ∧
      0 < reggeAction simplexBoundary (fun _ => 1) := by
  have h : reggeAction simplexBoundary (fun _ => 1) = 10 * (2 * π - 3 * arccos (1 / 3)) := by
    rw [reggeAction_of_bdryTris_eq_empty simplexBoundary_bdryTris,
      sum_congr rfl fun e he => by rw [one_mul, (simplexBoundary_deficit he).1], sum_const,
      simplexBoundary_edges]
    simp only [card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show Nat.choose 5 2 = 10 by decide]
    push_cast
    ring
  exact ⟨h, by rw [h]; linarith [arccos_lt_pi_div_two, pi_pos]⟩

/-- **A certified enclosure of the regular dihedral angle**: `1.2308 < arccos (1/3) < 1.2311`,
from `cos θ = sin (π/2 - θ)`, Mathlib's bounds `3.141592 < π < 3.141593` and the Taylor bound
`|sin y - (y - y³/6)| ≤ |y|⁵/100`. -/
theorem arccos_one_third_mem : 1.2308 < arccos (1 / 3) ∧ arccos (1 / 3) < 1.2311 := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hcos : ∀ a : ℝ, cos a = sin (π / 2 - a) := fun a => by
    rw [← Real.cos_pi_div_two_sub, sub_sub_cancel]
  constructor
  · -- `cos 1.2308 > 1/3`
    set y := π / 2 - 1.2308 with hy
    have y0 : 0.339996 < y := by rw [hy]; linarith
    have y1 : y < 0.3399965 := by rw [hy]; linarith
    have hb := Real.sin_bound (x := y) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [abs_of_pos (by linarith : (0 : ℝ) < y)] at hb
    have h3 : y ^ 3 < 0.3399965 ^ 3 := by gcongr
    have h5 : y ^ 5 < 0.3399965 ^ 5 := by gcongr
    have hs : 1 / 3 < sin y := by
      have := (abs_le.mp hb).1
      nlinarith
    have := arccos_lt_arccos (x := 1 / 3) (y := cos 1.2308) (by norm_num) (by rw [hcos]; exact hs)
      (cos_le_one _)
    rwa [arccos_cos (by norm_num) (by linarith)] at this
  · -- `cos 1.2311 < 1/3`
    set y := π / 2 - 1.2311 with hy
    have y0 : 0.339696 < y := by rw [hy]; linarith
    have y1 : y < 0.3396965 := by rw [hy]; linarith
    have hb := Real.sin_bound (x := y) (by rw [abs_of_pos (by linarith)]; linarith)
    rw [abs_of_pos (by linarith : (0 : ℝ) < y)] at hb
    have h3 : 0.339696 ^ 3 < y ^ 3 := by gcongr
    have h5 : y ^ 5 < 0.3396965 ^ 5 := by gcongr
    have hs : sin y < 1 / 3 := by
      have := (abs_le.mp hb).2
      nlinarith
    have := arccos_lt_arccos (x := cos 1.2311) (y := 1 / 3) (neg_one_le_cos _)
      (by rw [hcos]; exact hs) (by norm_num)
    rwa [arccos_cos (by norm_num) (by linarith)] at this

/-- **The gap left by five regular tetrahedra around an edge**, certified:
`0.1276 < 2π - 5 arccos (1/3) < 0.1292` radians, i.e. between `7.31°` and `7.41°` (numerically
`0.12839 ≈ 7.356°`). -/
theorem ring5_gap_mem :
    0.1276 < 2 * π - 5 * arccos (1 / 3) ∧ 2 * π - 5 * arccos (1 / 3) < 0.1292 ∧
      7.31 < (2 * π - 5 * arccos (1 / 3)) * 180 / π ∧
      (2 * π - 5 * arccos (1 / 3)) * 180 / π < 7.41 := by
  obtain ⟨h1, h2⟩ := arccos_one_third_mem
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hpos : 0 < π := pi_pos
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]
    nlinarith
  · rw [div_lt_iff₀ hpos]
    nlinarith

/-! ## Five and six regular tetrahedra around an edge -/

/-- Five tetrahedra `{0, 1, i, i+1}` around the edge `{0, 1}`, with link `2, 3, 4, 5, 6, 2`. -/
def ring5 : Complex3 (Fin 7) where
  tets := {{0, 1, 2, 3}, {0, 1, 3, 4}, {0, 1, 4, 5}, {0, 1, 5, 6}, {0, 1, 6, 2}}
  card_eq := by decide +kernel

set_option maxRecDepth 100000 in
/-- The edge `{0, 1}` of `ring5` is interior and lies in all five tetrahedra. -/
theorem ring5_edge : ({0, 1} : Finset (Fin 7)) ∈ intEdges ring5 ∧ #(star ring5 {0, 1}) = 5 := by
  decide +kernel

/-- **Five regular tetrahedra around an edge leave a gap**: the deficit `2π - 5 arccos (1/3)`
(about `7.36°`) is positive, so they cannot close up flat. -/
theorem ring5_deficit :
    deficit ring5 (fun _ => 1) {0, 1} = 2 * π - 5 * arccos (1 / 3) ∧
      0 < deficit ring5 (fun _ => 1) {0, 1} := by
  rw [deficit_const _ _ (by decide +kernel), ring5_edge.2, dihedral_one]
  push_cast
  exact ⟨rfl, by linarith [arccos_lt_two_pi_div_five]⟩

/-! ## Flat example 1: the octahedron, through the general flatness theorem

The octahedron with vertices `-e₃, e₃` (labels `0, 1`) and `e₁, e₂, -e₁, -e₂` (labels `2, 3, 4, 5`),
split into four tetrahedra around its axis `{0, 1}`. The general theorem `deficit_eq_zero_of_cyl`
applies, which also shows that its hypotheses can be met. -/

/-- The octahedron split into four tetrahedra around the axis `{0, 1}`. -/
def octahedron : Complex3 (Fin 6) where
  tets := {{0, 1, 2, 3}, {0, 1, 3, 4}, {0, 1, 4, 5}, {0, 1, 5, 2}}
  card_eq := by decide +kernel

/-- The vertices of the octahedron in `ℝ³`. -/
noncomputable def octPos : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[0, 0, -1], !₂[0, 0, 1], !₂[1, 0, 0], !₂[0, 1, 0], !₂[-1, 0, 0], !₂[0, -1, 0]]

/-- The link of the axis, `2, 3, 4, 5, 2`, as a sequence. -/
def octLink (i : ℕ) : Fin 6 := ⟨i % 4 + 2, by omega⟩

/-- The edge lengths of the octahedron placed in `ℝ³`. -/
noncomputable def octLen : Finset (Fin 6) → ℝ := ofDist fun u v => dist (octPos u) (octPos v)

/-- The axis `{0, 1}` lies in all four tetrahedra. -/
theorem octahedron_star : #(star octahedron {0, 1}) = 4 := by decide +kernel

/-- **Flat example (general theorem).** The axis of the octahedron placed in `ℝ³` has deficit
angle zero; obtained from `deficit_eq_zero_of_cyl` with link angles `0, π/2, π, 3π/2, 2π`. -/
theorem octahedron_deficit : deficit octahedron octLen {0, 1} = 0 := by
  have horth : Orthonormal ℝ
      ![(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[1, 0, 0], !₂[0, 1, 0]] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.norm_eq]
  refine deficit_eq_zero_of_cyl octahedron octPos 4 octLink ?_ ?_ ?_ horth (L := 2) (by norm_num) ?_
    (fun _ => 1) (fun _ => 1) (fun i => (i : ℝ) * (π / 2)) (fun _ _ => one_pos) ?_ ?_ ?_
  · decide +kernel
  · intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide +kernel)
  · decide +kernel
  · ext k
    fin_cases k <;> simp [octPos]
    norm_num
  · intro i hi
    interval_cases i
    · ext k; fin_cases k <;> simp [octPos, octLink]
    · ext k; fin_cases k <;> simp [octPos, octLink]
    · rw [show ((2 : ℕ) : ℝ) * (π / 2) = π by push_cast; ring]
      ext k; fin_cases k <;> simp [octPos, octLink]
    · rw [show ((3 : ℕ) : ℝ) * (π / 2) = π / 2 + π by push_cast; ring]
      ext k; fin_cases k <;> simp [octPos, octLink, cos_add_pi, sin_add_pi]
    · rw [show ((4 : ℕ) : ℝ) * (π / 2) = 2 * π by push_cast; ring]
      ext k; fin_cases k <;> simp [octPos, octLink]
  · intro i _
    push_cast
    constructor <;> nlinarith [pi_pos]
  · push_cast
    ring

/-! ## Flat example 2: the unit cube, by direct computation

The unit cube `[0,1]³` with vertex `v` at the binary digits of `v` (bit 0 = `x`, bit 1 = `y`,
bit 2 = `z`), split into the six Kuhn (Freudenthal) tetrahedra `0 → e_a → e_a + e_b → 7` around
the main diagonal `{0, 7}`. Each has dihedral angle `π/3` at the diagonal, computed here directly
from the lengths `√3, 1, √2, √2, 1, 1`, independently of the general theorem. -/

/-- The unit cube split into the six Kuhn tetrahedra around its diagonal `{0, 7}`. -/
def cube : Complex3 (Fin 8) where
  tets := {{0, 1, 3, 7}, {0, 1, 5, 7}, {0, 2, 3, 7}, {0, 2, 6, 7}, {0, 4, 5, 7}, {0, 4, 6, 7}}
  card_eq := by decide +kernel

/-- The vertices of the unit cube in `ℝ³`. -/
noncomputable def cubePos : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[0, 0, 0], !₂[1, 0, 0], !₂[0, 1, 0], !₂[1, 1, 0], !₂[0, 0, 1], !₂[1, 0, 1], !₂[0, 1, 1],
    !₂[1, 1, 1]]

/-- The edge lengths of the cube placed in `ℝ³`. -/
noncomputable def cubeLen : Finset (Fin 8) → ℝ := ofDist fun u v => dist (cubePos u) (cubePos v)

/-- The length of an edge of the cube complex, in coordinates. -/
theorem cubeLen_pair {u v : Fin 8} (h : u ≠ v) :
    cubeLen {u, v} = √(∑ i : Fin 3, (cubePos u i - cubePos v i) ^ 2) := by
  rw [cubeLen, ofDist_pair (d := fun u v => dist (cubePos u) (cubePos v))
    (fun u => dist_self (cubePos u)) (fun u v => dist_comm (cubePos u) (cubePos v)) h,
    EuclideanSpace.dist_eq]
  simp [Real.dist_eq, sq_abs]

/-- The lengths of the edges of the six Kuhn tetrahedra: the diagonal `√3`, and `1` or `√2`. -/
theorem cubeLen_values :
    cubeLen {0, 7} = √3 ∧
    cubeLen {0, 1} = 1 ∧ cubeLen {0, 2} = 1 ∧ cubeLen {0, 4} = 1 ∧
    cubeLen {7, 1} = √2 ∧ cubeLen {7, 2} = √2 ∧ cubeLen {7, 4} = √2 ∧
    cubeLen {0, 3} = √2 ∧ cubeLen {0, 5} = √2 ∧ cubeLen {0, 6} = √2 ∧
    cubeLen {7, 3} = 1 ∧ cubeLen {7, 5} = 1 ∧ cubeLen {7, 6} = 1 ∧
    cubeLen {1, 3} = 1 ∧ cubeLen {1, 5} = 1 ∧ cubeLen {2, 3} = 1 ∧ cubeLen {2, 6} = 1 ∧
    cubeLen {4, 5} = 1 ∧ cubeLen {4, 6} = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [cubeLen_pair (by decide)]
    simp [cubePos, Fin.sum_univ_three]
    try norm_num

/-- The diagonal `{0, 7}` is an interior edge of the cube complex. -/
theorem cube_interior : ({0, 7} : Finset (Fin 8)) ∈ intEdges cube := by decide +kernel

/-- All six tetrahedra contain the diagonal. -/
theorem cube_star : star cube {0, 7} = cube.tets := by decide +kernel

/-- A sum over the tetrahedra of the cube, written out, each tetrahedron listed as
`{0, 7, e_a, e_a + e_b}`. -/
theorem cube_sum (G : Finset (Fin 8) → ℝ) :
    ∑ t ∈ cube.tets, G t = G {0, 7, 1, 3} + G {0, 7, 1, 5} + G {0, 7, 2, 3} + G {0, 7, 2, 6} +
      G {0, 7, 4, 5} + G {0, 7, 4, 6} := by
  rw [show cube.tets = {{0, 7, 1, 3}, {0, 7, 1, 5}, {0, 7, 2, 3}, {0, 7, 2, 6}, {0, 7, 4, 5},
      {0, 7, 4, 6}} by decide +kernel,
    sum_insert (by decide +kernel), sum_insert (by decide +kernel), sum_insert (by decide +kernel),
    sum_insert (by decide +kernel), sum_insert (by decide +kernel), sum_singleton]
  ring

/-- Any angle formula on a Kuhn-type tetrahedron `{0, 7, a, b}` at the edge `{0, 7}` of length
`d`, with the other lengths those of the cube. -/
theorem kuhn_angleAvg (F : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (ℓ : Finset (Fin 8) → ℝ) {a b : Fin 8}
    {d : ℝ} (hne : (0 : Fin 8) ≠ a ∧ (0 : Fin 8) ≠ b ∧ (7 : Fin 8) ≠ a ∧ (7 : Fin 8) ≠ b ∧ a ≠ b)
    (h0 : ℓ {0, 7} = d) (h1 : ℓ {0, a} = 1) (h2 : ℓ {7, a} = √2) (h3 : ℓ {0, b} = √2)
    (h4 : ℓ {7, b} = 1) (h5 : ℓ {a, b} = 1) :
    angleAvg F ℓ {0, 7, a, b} {0, 7} =
      (F d 1 (√2) (√2) 1 1 + F d (√2) 1 1 (√2) 1 + F d (√2) 1 1 (√2) 1 + F d 1 (√2) (√2) 1 1) /
        4 := by
  rw [angleAvg_eq F ℓ (by decide) hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2, h0, h1, h2,
    h3, h4, h5]

/-- The dihedral angle of a Kuhn-type tetrahedron `{0, 7, a, b}` at the edge `{0, 7}` of
length `d ≠ 0`. -/
theorem kuhn_dihedralAt (ℓ : Finset (Fin 8) → ℝ) {a b : Fin 8} {d : ℝ} (hd : d ≠ 0)
    (hne : (0 : Fin 8) ≠ a ∧ (0 : Fin 8) ≠ b ∧ (7 : Fin 8) ≠ a ∧ (7 : Fin 8) ≠ b ∧ a ≠ b)
    (h0 : ℓ {0, 7} = d) (h1 : ℓ {0, a} = 1) (h2 : ℓ {7, a} = √2) (h3 : ℓ {0, b} = √2)
    (h4 : ℓ {7, b} = 1) (h5 : ℓ {a, b} = 1) :
    dihedralAt ℓ {0, 7, a, b} {0, 7} = dihedral d 1 (√2) (√2) 1 1 := by
  rw [dihedralAt_eq ℓ (by decide) hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2
    (by rw [h0]; exact hd), h0, h1, h2, h3, h4, h5]

/-- A Kuhn tetrahedron has cosine `1/2` at the diagonal. -/
theorem cosDihedral_kuhn : cosDihedral (√3) 1 (√2) (√2) 1 1 = 1 / 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : √3 ≠ 0 := by positivity
  have hru : ((1 : ℝ) ^ 2 + √3 ^ 2 - √2 ^ 2) / (2 * √3) = 1 / √3 := by
    rw [h3, h2]; field_simp; norm_num
  have hsu : (√2 ^ 2 + √3 ^ 2 - (1 : ℝ) ^ 2) / (2 * √3) = 2 / √3 := by
    rw [h3, h2]; field_simp; norm_num
  simp only [cosDihedral, hru, hsu]
  have hr : ((1 : ℝ) ^ 2 - (1 / √3) ^ 2) * (√2 ^ 2 - (2 / √3) ^ 2) = (2 / 3) ^ 2 := by
    rw [div_pow, div_pow, h3, h2]; norm_num
  rw [hr, Real.sqrt_sq (by norm_num), h2, show (1 : ℝ) / √3 * (2 / √3) = 2 / √3 ^ 2 by ring, h3]
  norm_num

/-- A Kuhn tetrahedron has dihedral angle `π/3` at the diagonal of the cube. -/
theorem dihedral_kuhn : dihedral (√3) 1 (√2) (√2) 1 1 = π / 3 := by
  rw [dihedral, cosDihedral_kuhn, ← cos_pi_div_three,
    arccos_cos (by positivity) (by linarith [pi_pos])]

/-- **Flat example (direct computation).** The diagonal of the unit cube, surrounded by the six
Kuhn tetrahedra, has deficit angle `2π - 6 · π/3 = 0`. -/
theorem cube_deficit : deficit cube cubeLen {0, 7} = 0 := by
  obtain ⟨d07, d01, d02, d04, d71, d72, d74, d03, d05, d06, d73, d75, d76, d13, d15, d23, d26,
    d45, d46⟩ := cubeLen_values
  have hd : √3 ≠ 0 := by positivity
  rw [deficit, angleSum, cube_star, cube_sum,
    kuhn_dihedralAt cubeLen hd (by decide) d07 d01 d71 d03 d73 d13,
    kuhn_dihedralAt cubeLen hd (by decide) d07 d01 d71 d05 d75 d15,
    kuhn_dihedralAt cubeLen hd (by decide) d07 d02 d72 d03 d73 d23,
    kuhn_dihedralAt cubeLen hd (by decide) d07 d02 d72 d06 d76 d26,
    kuhn_dihedralAt cubeLen hd (by decide) d07 d04 d74 d05 d75 d45,
    kuhn_dihedralAt cubeLen hd (by decide) d07 d04 d74 d06 d76 d46, dihedral_kuhn]
  ring

/-! ## Wrong inputs and wrong formulas must fail -/

/-- The cube's lengths with the diagonal stretched from `√3` to `2`. These are not the distances
of any placement of the cube complex in `ℝ³` with the other lengths kept. -/
noncomputable def cubeLenStretched (e : Finset (Fin 8)) : ℝ := if e = {0, 7} then 2 else cubeLen e

/-- Away from the diagonal the stretched lengths are the cube's. -/
theorem cubeLenStretched_of_ne {e : Finset (Fin 8)} (h : e ≠ {0, 7}) :
    cubeLenStretched e = cubeLen e := by
  simp [cubeLenStretched, h]

/-- The stretched Kuhn tetrahedron has cosine `1/7` at the diagonal. -/
theorem cosDihedral_stretched : cosDihedral 2 1 (√2) (√2) 1 1 = 1 / 7 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [cosDihedral, h2]
  have hr : ((1 : ℝ) ^ 2 - ((1 ^ 2 + 2 ^ 2 - 2) / (2 * 2)) ^ 2) *
      (2 - ((2 + 2 ^ 2 - 1 ^ 2) / (2 * 2)) ^ 2) = (7 / 16) ^ 2 := by norm_num
  rw [hr, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Wrong input fails.** Stretching the cube's diagonal to `2` gives each tetrahedron the
dihedral angle `arccos (1/7) > π/3` at the diagonal, so the deficit is negative, not zero. -/
theorem cubeStretched_deficit :
    deficit cube cubeLenStretched {0, 7} = 2 * π - 6 * arccos (1 / 7) ∧
      deficit cube cubeLenStretched {0, 7} < 0 := by
  obtain ⟨_, d01, d02, d04, d71, d72, d74, d03, d05, d06, d73, d75, d76, d13, d15, d23, d26,
    d45, d46⟩ := cubeLen_values
  have s : ∀ {e : Finset (Fin 8)} {x : ℝ}, e ≠ {0, 7} → cubeLen e = x → cubeLenStretched e = x :=
    fun h h' => by rw [cubeLenStretched_of_ne h, h']
  have d07 : cubeLenStretched {0, 7} = 2 := by simp [cubeLenStretched]
  have hd : (2 : ℝ) ≠ 0 := two_ne_zero
  have h : deficit cube cubeLenStretched {0, 7} = 2 * π - 6 * arccos (1 / 7) := by
    rw [deficit, angleSum, cube_star, cube_sum,
      kuhn_dihedralAt _ hd (by decide) d07 (s (by decide) d01) (s (by decide) d71)
        (s (by decide) d03) (s (by decide) d73) (s (by decide) d13),
      kuhn_dihedralAt _ hd (by decide) d07 (s (by decide) d01) (s (by decide) d71)
        (s (by decide) d05) (s (by decide) d75) (s (by decide) d15),
      kuhn_dihedralAt _ hd (by decide) d07 (s (by decide) d02) (s (by decide) d72)
        (s (by decide) d03) (s (by decide) d73) (s (by decide) d23),
      kuhn_dihedralAt _ hd (by decide) d07 (s (by decide) d02) (s (by decide) d72)
        (s (by decide) d06) (s (by decide) d76) (s (by decide) d26),
      kuhn_dihedralAt _ hd (by decide) d07 (s (by decide) d04) (s (by decide) d74)
        (s (by decide) d05) (s (by decide) d75) (s (by decide) d45),
      kuhn_dihedralAt _ hd (by decide) d07 (s (by decide) d04) (s (by decide) d74)
        (s (by decide) d06) (s (by decide) d76) (s (by decide) d46), dihedral,
      cosDihedral_stretched]
    ring
  refine ⟨h, ?_⟩
  have hlt : π / 3 < arccos (1 / 7) := by
    have := arccos_lt_arccos (x := 1 / 7) (y := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    rwa [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])] at this
  rw [h]
  linarith

/-- The deficit computed with an angle formula `F` in place of the dihedral angle, by the same
averaging and summation as `deficit` (`deficitWith_dihedral`). -/
noncomputable def deficitWith {V : Type*} [DecidableEq V] (F : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (K : Complex3 V) (ℓ : Finset V → ℝ) (e : Finset V) : ℝ :=
  2 * π - ∑ t ∈ star K e, angleAvg F ℓ t e

/-- With the dihedral angle as the formula, `deficitWith` is `deficit`. -/
theorem deficitWith_dihedral {V : Type*} [DecidableEq V] (K : Complex3 V) (ℓ : Finset V → ℝ)
    (e : Finset V) : deficitWith dihedral K ℓ e = deficit K ℓ e := rfl

/-- **Wrong formula: exterior angles.** Using `π - θ` instead of `θ` at an edge in `n`
tetrahedra reports `(4 - n) π - δ`. At a flat edge it is zero exactly when `n = 4`, so a flatness
test on a four-valent edge (`octahedron_exterior_passes`) cannot detect this mistake. -/
theorem deficitWith_exterior {V : Type*} [DecidableEq V] (K : Complex3 V) (ℓ : Finset V → ℝ)
    {e : Finset V} (he : #e = 2) :
    deficitWith (fun a b c d f g => π - dihedral a b c d f g) K ℓ e =
      (4 - #(star K e)) * π - deficit K ℓ e := by
  have h : ∀ t ∈ star K e,
      angleAvg (fun a b c d f g => π - dihedral a b c d f g) ℓ t e = π - dihedralAt ℓ t e := by
    intro t ht
    simp only [star, mem_filter] at ht
    rw [angleAvg_sub (fun _ _ _ _ _ _ => π) dihedral,
      angleAvg_const π ℓ he (by rw [card_sdiff_of_subset ht.2, K.card_eq t ht.1, he]), dihedralAt]
  rw [deficitWith, sum_congr rfl h, sum_sub_distrib, sum_const, deficit, angleSum, nsmul_eq_mul]
  ring

/-- The exterior-angle mistake goes unnoticed on the octahedron's axis (four tetrahedra). -/
theorem octahedron_exterior_passes :
    deficitWith (fun a b c d f g => π - dihedral a b c d f g) octahedron octLen {0, 1} = 0 := by
  rw [deficitWith_exterior _ _ (by decide), octahedron_deficit, octahedron_star]
  push_cast
  ring

/-- **Wrong formula fails: exterior angles on the cube.** The six Kuhn tetrahedra report
`-2π` instead of `0`. -/
theorem cube_exterior_fails :
    deficitWith (fun a b c d f g => π - dihedral a b c d f g) cube cubeLen {0, 7} = -2 * π := by
  rw [deficitWith_exterior _ _ (by decide), cube_deficit, cube_star,
    show #cube.tets = 6 by decide +kernel]
  push_cast
  ring

/-- A wrong angle formula: the angle at the vertex `p` of the face `prs`, by the law of cosines.
This is the angle between two edges, not between two faces. -/
noncomputable def faceAngle (_pq pr _qr ps _qs rs : ℝ) : ℝ :=
  arccos ((pr ^ 2 + ps ^ 2 - rs ^ 2) / (2 * pr * ps))

/-- **Wrong formula fails: face angles on the cube.** Each Kuhn tetrahedron reports `π/4`, so
the six of them give `2π - 6 · π/4 = π/2` instead of `0`. -/
theorem cube_faceAngle_fails : deficitWith faceAngle cube cubeLen {0, 7} = π / 2 := by
  obtain ⟨d07, d01, d02, d04, d71, d72, d74, d03, d05, d06, d73, d75, d76, d13, d15, d23, d26,
    d45, d46⟩ := cubeLen_values
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hq : arccos (1 / √2) = π / 4 := by
    rw [← arccos_cos (x := π / 4) (by positivity) (by linarith [pi_pos]), cos_pi_div_four]
    congr 1
    field_simp
    rw [h2]
  have f1 : faceAngle (√3) 1 (√2) (√2) 1 1 = π / 4 := by
    rw [faceAngle, h2, ← hq]
    congr 1
    field_simp
    norm_num
  have f2 : faceAngle (√3) (√2) 1 1 (√2) 1 = π / 4 := by
    rw [faceAngle, h2, ← hq]
    congr 1
    field_simp
    norm_num
  rw [deficitWith, cube_star, cube_sum,
    kuhn_angleAvg faceAngle cubeLen (by decide) d07 d01 d71 d03 d73 d13,
    kuhn_angleAvg faceAngle cubeLen (by decide) d07 d01 d71 d05 d75 d15,
    kuhn_angleAvg faceAngle cubeLen (by decide) d07 d02 d72 d03 d73 d23,
    kuhn_angleAvg faceAngle cubeLen (by decide) d07 d02 d72 d06 d76 d26,
    kuhn_angleAvg faceAngle cubeLen (by decide) d07 d04 d74 d05 d75 d45,
    kuhn_angleAvg faceAngle cubeLen (by decide) d07 d04 d74 d06 d76 d46, f1, f2]
  ring

/-! ## Junk values: degenerate lengths fake flatness

With all lengths `0`, Lean's `0 / 0 = 0` makes every "dihedral angle" `arccos 0 = π/2`, so four
degenerate tetrahedra around an edge report deficit `0`. A zero deficit is therefore no evidence
of flatness by itself; `deficit_eq_zero_of_cyl` assumes a non-degenerate placement (`L > 0`,
`ρ_i > 0`). -/

/-- With all lengths zero the length formula returns the junk angle `π/2`. -/
theorem dihedral_zero : dihedral 0 0 0 0 0 0 = π / 2 := by
  simp [dihedral, cosDihedral, arccos_zero]

/-- **Junk check.** All-zero lengths on the octahedron give the axis deficit `0`, a degenerate
"flatness" that the theorems of this library exclude by their hypotheses. -/
theorem octahedron_deficit_zero_lengths : deficit octahedron (fun _ => 0) {0, 1} = 0 := by
  rw [deficit_const _ _ (by decide), octahedron_star, dihedral_zero]
  push_cast
  ring

/-! ## More regular examples -/

/-- With unit lengths the octahedron's axis lies in four regular tetrahedra: deficit
`2π - 4 arccos (1/3) > 0` (the edge valence of the 16-cell). -/
theorem octahedron_deficit_unit : 0 < deficit octahedron (fun _ => 1) {0, 1} := by
  rw [deficit_const _ _ (by decide), octahedron_star, dihedral_one]
  push_cast
  linarith [arccos_lt_pi_div_two]

/-- **Six regular tetrahedra around an edge overlap**: with unit lengths the cube complex's
diagonal has deficit `2π - 6 arccos (1/3) < 0`. -/
theorem cube_deficit_unit :
    deficit cube (fun _ => 1) {0, 7} = 2 * π - 6 * arccos (1 / 3) ∧
      deficit cube (fun _ => 1) {0, 7} < 0 := by
  rw [deficit_const _ _ (by decide), cube_star, show #cube.tets = 6 by decide +kernel,
    dihedral_one]
  push_cast
  exact ⟨rfl, by linarith [pi_div_three_lt_arccos]⟩

/-- **Regular tetrahedra never fit flat around an edge.** In any complex, with all lengths `1`,
every edge has nonzero deficit: positive if it lies in at most five tetrahedra, negative if in six
or more, since `π/3 < arccos (1/3) < 2π/5`. -/
theorem deficit_unit_ne_zero {V : Type*} [DecidableEq V] (K : Complex3 V) {e : Finset V}
    (he : #e = 2) : deficit K (fun _ => 1) e ≠ 0 := by
  rw [deficit_const _ _ he, dihedral_one]
  have hθ0 : 0 ≤ arccos (1 / 3) := arccos_nonneg _
  rcases Nat.lt_or_ge #(star K e) 6 with h | h
  · have h5 : (#(star K e) : ℝ) ≤ 5 := by exact_mod_cast Nat.lt_succ_iff.mp h
    have := mul_le_mul_of_nonneg_right h5 hθ0
    linarith [arccos_lt_two_pi_div_five]
  · have h6 : (6 : ℝ) ≤ #(star K e) := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_right h6 hθ0
    linarith [pi_div_three_lt_arccos]

/-! ## One tetrahedron: the Regge action of `Lightlike/PonzanoRegge/Asymptotics.lean`

For a single tetrahedron every edge is a boundary edge, and the Regge action is
`Σ_e ℓ_e (π - θ_e)`, the phase of the Ponzano–Regge asymptotic formula (`Lightlike.PR.reggeAction`). -/

/-- One tetrahedron `ABCD = {0, 1, 2, 3}`. -/
def singleTet : Complex3 (Fin 4) where
  tets := {univ}
  card_eq := by decide

/-- The lengths of `singleTet` from the six lengths `l = (AB, BC, CA, CD, AD, BD)` used by
`Lightlike.PR.reggeAction`, with `A, B, C, D = 0, 1, 2, 3`. -/
noncomputable def tetLen (l : Fin 6 → ℝ) : Finset (Fin 4) → ℝ :=
  ofDist ![![0, l 0, l 2, l 4], ![l 0, 0, l 1, l 5], ![l 2, l 1, 0, l 3], ![l 4, l 5, l 3, 0]]

/-- The length of an edge of `singleTet`. -/
theorem tetLen_pair (l : Fin 6 → ℝ) {u v : Fin 4} (h : u ≠ v) :
    tetLen l {u, v} =
      ![![0, l 0, l 2, l 4], ![l 0, 0, l 1, l 5], ![l 2, l 1, 0, l 3], ![l 4, l 5, l 3, 0]] u v :=
  ofDist_pair (fun a => by fin_cases a <;> rfl) (fun a b => by fin_cases a <;> fin_cases b <;> rfl) h

/-- The single tetrahedron has no interior edge, and all six edges are on the boundary. -/
theorem singleTet_edges :
    intEdges singleTet = ∅ ∧
      bdryEdges singleTet = {{0, 1}, {1, 2}, {2, 0}, {2, 3}, {0, 3}, {1, 3}} := by
  decide +kernel

/-- Each edge of the single tetrahedron lies in the one tetrahedron. -/
theorem singleTet_star (e : Finset (Fin 4)) : star singleTet e = {univ} := by
  simp [star, singleTet, filter_singleton, subset_univ]

/-- **Bridge to Ponzano–Regge.** For nonzero lengths, the Regge action of a single tetrahedron
(boundary term only) is the phase `Lightlike.PR.reggeAction` of the Ponzano–Regge asymptotic formula. -/
theorem reggeAction_singleTet (l : Fin 6 → ℝ) (hl : ∀ i, l i ≠ 0) :
    reggeAction singleTet (tetLen l) = Lightlike.PR.reggeAction l := by
  have hL : ∀ u v : Fin 4, u ≠ v → tetLen l {u, v} =
      ![![0, l 0, l 2, l 4], ![l 0, 0, l 1, l 5], ![l 2, l 1, 0, l 3], ![l 4, l 5, l 3, 0]] u v :=
    fun u v h => tetLen_pair l h
  have hθ : ∀ e : Finset (Fin 4), angleSum singleTet (tetLen l) e = dihedralAt (tetLen l) univ e :=
    fun e => by rw [angleSum, singleTet_star, sum_singleton]
  rw [reggeAction, singleTet_edges.1, singleTet_edges.2, sum_empty, zero_add,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp only [bdryAngle, hθ]
  rw [show (univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide,
    dihedralAt_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hL 0 1 (by decide)]; exact hl 0)]
  rw [show ({0, 1, 2, 3} : Finset (Fin 4)) = {1, 2, 0, 3} by decide,
    dihedralAt_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hL 1 2 (by decide)]; exact hl 1)]
  rw [show ({1, 2, 0, 3} : Finset (Fin 4)) = {2, 0, 1, 3} by decide,
    dihedralAt_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hL 2 0 (by decide)]; exact hl 2)]
  rw [show ({2, 0, 1, 3} : Finset (Fin 4)) = {2, 3, 0, 1} by decide,
    dihedralAt_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hL 2 3 (by decide)]; exact hl 3)]
  rw [show ({2, 3, 0, 1} : Finset (Fin 4)) = {0, 3, 1, 2} by decide,
    dihedralAt_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hL 0 3 (by decide)]; exact hl 4)]
  rw [show ({0, 3, 1, 2} : Finset (Fin 4)) = {1, 3, 0, 2} by decide,
    dihedralAt_eq _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hL 1 3 (by decide)]; exact hl 5)]
  simp only [hL _ _ (by decide : (0 : Fin 4) ≠ 1), hL _ _ (by decide : (0 : Fin 4) ≠ 2),
    hL _ _ (by decide : (0 : Fin 4) ≠ 3), hL _ _ (by decide : (1 : Fin 4) ≠ 0),
    hL _ _ (by decide : (1 : Fin 4) ≠ 2), hL _ _ (by decide : (1 : Fin 4) ≠ 3),
    hL _ _ (by decide : (2 : Fin 4) ≠ 0), hL _ _ (by decide : (2 : Fin 4) ≠ 1),
    hL _ _ (by decide : (2 : Fin 4) ≠ 3), hL _ _ (by decide : (3 : Fin 4) ≠ 0),
    hL _ _ (by decide : (3 : Fin 4) ≠ 1), hL _ _ (by decide : (3 : Fin 4) ≠ 2)]
  simp [Lightlike.PR.reggeAction, Lightlike.PR.extAngles, Fin.sum_univ_six]
  ring

/-! ## The manifold condition at edges

The examples are edge-manifolds where expected, and a complex with a branching triangle is not. -/

/-- The link of the cube's diagonal: the hexagon `1, 3, 2, 6, 4, 5`, repeated. -/
def cubeLink (i : ℕ) : Fin 8 := ![1, 3, 2, 6, 4, 5] ⟨i % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The cube's diagonal has a cycle link (a hexagon), so it is interior. -/
theorem cube_diagonal_cycleLink : IsCycleLink cube 0 7 6 cubeLink where
  ne := by decide
  three_le := by norm_num
  ne_a := by decide
  ne_b := by decide
  inj := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  closed := rfl
  star_eq := by decide +kernel

/-- The link of the cube edge `{0, 1}`: the path `3, 7, 5`. -/
def cubeEdgeLink : ℕ → Fin 8
  | 0 => 3
  | 1 => 7
  | _ => 5

/-- The cube edge `{0, 1}` has a path link (two tetrahedra), so it is a boundary edge. -/
theorem cube_edge_pathLink : IsPathLink cube 0 1 2 cubeEdgeLink where
  ne := by decide
  one_le := by norm_num
  ne_a := by decide
  ne_b := by decide
  inj := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  star_eq := by decide +kernel

/-- The octahedron's axis has a cycle link (a square). -/
theorem octahedron_axis_cycleLink : IsCycleLink octahedron 0 1 4 octLink where
  ne := by decide
  three_le := by norm_num
  ne_a := by decide
  ne_b := by decide
  inj := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  closed := rfl
  star_eq := by decide +kernel

/-- The link of the edge `{0, 1}` of the boundary of the 4-simplex: the triangle `2, 3, 4`. -/
def simplexLink (i : ℕ) : Fin 5 := ⟨i % 3 + 2, by omega⟩

/-- In the boundary of the 4-simplex the edge `{0, 1}` has a cycle link (a triangle). -/
theorem simplexBoundary_cycleLink : IsCycleLink simplexBoundary 0 1 3 simplexLink where
  ne := by decide
  three_le := le_refl 3
  ne_a := by decide
  ne_b := by decide
  inj := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  closed := rfl
  star_eq := by decide +kernel

/-- Three tetrahedra sharing the triangle `{0, 1, 2}`: not a manifold. -/
def tripleBook : Complex3 (Fin 6) where
  tets := {{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 2, 5}}
  card_eq := by decide +kernel

/-- **Non-manifold check.** The link of the edge `{0, 1}` of `tripleBook` is a star with three
arms (all three tetrahedra contain the vertex `2`), neither a cycle nor a path, so `tripleBook`
is not an edge-manifold. -/
theorem tripleBook_not_edgeManifold : ¬ IsEdgeManifold tripleBook := by
  intro hK
  obtain ⟨a, b, n, w, he, hc | hp⟩ := hK {0, 1} (by decide +kernel)
  all_goals
    have h2 : ∀ t ∈ star tripleBook {a, b}, (2 : Fin 6) ∈ t := by
      rw [← he]
      decide +kernel
    have hab : a ≠ 2 ∧ b ≠ 2 := by
      have ha : a ∈ ({0, 1} : Finset (Fin 6)) := by rw [he]; simp
      have hb : b ∈ ({0, 1} : Finset (Fin 6)) := by rw [he]; simp
      simp only [mem_insert, mem_singleton] at ha hb
      constructor <;> rintro rfl <;> simp at ha hb
  · have h3 := hc.three_le
    have mem2 : ∀ i < n, w i = 2 ∨ w (cycSucc n i) = 2 := by
      intro i hi
      have := h2 _ (by rw [hc.star_eq]; exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
      rw [hc.w_succ hi] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h | h
      · exact absurd h.symm hab.1
      · exact absurd h.symm hab.2
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have s0 : cycSucc n 0 = 1 := by unfold cycSucc; split_ifs <;> omega
    have s1 : cycSucc n 1 = 2 := by unfold cycSucc; split_ifs <;> omega
    have s2 : cycSucc n 2 ≠ 1 := by unfold cycSucc; split_ifs <;> omega
    have hs2 : cycSucc n 2 < n := cycSucc_lt (by omega)
    rcases mem2 0 (by omega) with h0 | h0 <;> rw [s0] at * <;>
      rcases mem2 1 (by omega) with h1 | h1 <;> rw [s1] at * <;>
      rcases mem2 2 (by omega) with h2' | h2'
    all_goals first
      | exact absurd (hc.w_inj (by omega) (by omega) (h0.trans h1.symm)) (by omega)
      | exact absurd (hc.w_inj (by omega) (by omega) (h1.trans h2'.symm)) (by omega)
  · have hn : 3 ≤ n := by
      have := card_image_le (s := range n) (f := fun i => ({a, b, w i, w (i + 1)} : Finset (Fin 6)))
      rw [← hp.star_eq, ← he, show #(star tripleBook {0, 1}) = 3 by decide +kernel,
        card_range] at this
      exact this
    have mem2 : ∀ i < n, w i = 2 ∨ w (i + 1) = 2 := by
      intro i hi
      have := h2 _ (by rw [hp.star_eq]; exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h | h
      · exact absurd h.symm hab.1
      · exact absurd h.symm hab.2
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have inj : ∀ i j, i ≤ n → j ≤ n → w i = w j → i = j := fun i j hi hj h =>
      hp.inj (by simp only [coe_range, Set.mem_Iio]; omega)
        (by simp only [coe_range, Set.mem_Iio]; omega) h
    rcases mem2 0 (by omega) with h0 | h0 <;> rcases mem2 2 (by omega) with h2' | h2'
    · exact absurd (inj 0 2 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)
    · exact absurd (inj 0 3 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)
    · exact absurd (inj 1 2 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)
    · exact absurd (inj 1 3 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)

/-! ## Geometric triangulations (`Lightlike/Regge/Embedded.lean`)

The octahedron placed in `ℝ³` is a geometric triangulation, so the general theorem gives its axis
deficit zero. A ring of eight tetrahedra winding twice around an axis meets every hypothesis except
disjointness, and has deficit `-2π`; so the theorem forces its tetrahedra to overlap. -/

/-- The standard frame `e₃, e₁, e₂` of `ℝ³` is orthonormal. -/
theorem stdFrame_orthonormal :
    Orthonormal ℝ ![(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)), !₂[1, 0, 0], !₂[0, 1, 0]] := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.norm_eq]

/-- A tetrahedron of the octahedron with link vertices at angles `α, α + π/2` is non-degenerate. -/
theorem oct_linIndep {r s : Fin 6} {α : ℝ}
    (hr : octPos r - octPos 0 = (1 : ℝ) • (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) +
      (1 : ℝ) • (cos α • !₂[1, 0, 0] + sin α • !₂[0, 1, 0]))
    (hs : octPos s - octPos 0 = (1 : ℝ) • (!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3)) +
      (1 : ℝ) • (cos (α + π / 2) • !₂[1, 0, 0] + sin (α + π / 2) • !₂[0, 1, 0])) :
    LinearIndependent ℝ ![octPos 1 - octPos 0, octPos r - octPos 0, octPos s - octPos 0] :=
  cyl_linIndep stdFrame_orthonormal (L := 2) two_ne_zero one_ne_zero one_ne_zero
    (by rw [show α + π / 2 - α = π / 2 by ring, sin_pi_div_two]; exact one_ne_zero)
    (by ext k; fin_cases k <;> simp [octPos]; norm_num) hr hs

/-- The four tetrahedra of the octahedron placed in `ℝ³` are non-degenerate. -/
theorem octahedron_nondeg : ∀ t ∈ octahedron.tets, AffineIndependent ℝ fun v : t => octPos v := by
  intro t ht
  simp only [octahedron, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · refine affIndep_of_linIndep octPos (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (oct_linIndep (α := 0) ?_ ?_)
    · ext k; fin_cases k <;> simp [octPos]
    · ext k; fin_cases k <;> simp [octPos]
  · refine affIndep_of_linIndep octPos (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (oct_linIndep (α := π / 2) ?_ ?_)
    · ext k; fin_cases k <;> simp [octPos]
    · rw [show π / 2 + π / 2 = π by ring]; ext k; fin_cases k <;> simp [octPos]
  · refine affIndep_of_linIndep octPos (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (oct_linIndep (α := π) ?_ ?_)
    · ext k; fin_cases k <;> simp [octPos]
    · ext k; fin_cases k <;> simp [octPos, cos_add_pi_div_two, sin_add_pi_div_two]
  · refine affIndep_of_linIndep octPos (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (oct_linIndep (α := -(π / 2)) ?_ ?_)
    · ext k; fin_cases k <;> simp [octPos]
    · rw [show -(π / 2) + π / 2 = 0 by ring]; ext k; fin_cases k <;> simp [octPos]

/-- The open simplices of the octahedron's tetrahedra lie in the four open quadrants of the
`xy`-plane: `x > 0` iff the tetrahedron contains the vertex `2` (at `e₁`), `y > 0` iff it
contains `3` (at `e₂`). -/
theorem octahedron_region : ∀ t ∈ octahedron.tets, ∀ y ∈ openHull octPos t,
    ((2 : Fin 6) ∈ t → 0 < y 0) ∧ ((2 : Fin 6) ∉ t → y 0 < 0) ∧
    ((3 : Fin 6) ∈ t → 0 < y 1) ∧ ((3 : Fin 6) ∉ t → y 1 < 0) := by
  intro t ht
  simp only [octahedron, mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> rintro y ⟨c, hc, -, rfl⟩ <;>
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  · refine ⟨fun _ => ?_, fun h => absurd (by decide) h, fun _ => ?_, fun h => absurd (by decide) h⟩
    · simp [octPos]; linarith [hc 2 (by decide)]
    · simp [octPos]; linarith [hc 3 (by decide)]
  · refine ⟨fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd (by decide) h⟩
    · simp [octPos]; linarith [hc 4 (by decide)]
    · simp [octPos]; linarith [hc 3 (by decide)]
  · refine ⟨fun h => absurd h (by decide), fun _ => ?_, fun h => absurd h (by decide), fun _ => ?_⟩
    · simp [octPos]; linarith [hc 4 (by decide)]
    · simp [octPos]; linarith [hc 5 (by decide)]
  · refine ⟨fun _ => ?_, fun h => absurd (by decide) h, fun h => absurd h (by decide), fun _ => ?_⟩
    · simp [octPos]; linarith [hc 2 (by decide)]
    · simp [octPos]; linarith [hc 5 (by decide)]

/-- Distinct tetrahedra of the octahedron placed in `ℝ³` have disjoint interiors. -/
theorem octahedron_disjoint : ∀ t ∈ octahedron.tets, ∀ t' ∈ octahedron.tets, t ≠ t' →
    Disjoint (openHull octPos t) (openHull octPos t') := by
  intro t ht t' ht' hne
  rw [Set.disjoint_left]
  intro y hy hy'
  obtain ⟨a1, a2, a3, a4⟩ := octahedron_region t ht y hy
  obtain ⟨b1, b2, b3, b4⟩ := octahedron_region t' ht' y hy'
  simp only [octahedron, mem_insert, mem_singleton] at ht ht'
  rcases ht with rfl | rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl | rfl <;>
    first
    | exact hne rfl
    | linarith [a1 (by decide), b2 (by decide)]
    | linarith [a2 (by decide), b1 (by decide)]
    | linarith [a3 (by decide), b4 (by decide)]
    | linarith [a4 (by decide), b3 (by decide)]

/-- **The octahedron placed in `ℝ³` is a geometric triangulation**: its four tetrahedra are
non-degenerate, and the interiors of their convex hulls (by `openHull_eq_interior`, their open
simplices) lie in the four open quadrants `±x > 0, ±y > 0`. -/
theorem octahedron_geometric : IsGeometric octahedron octPos :=
  ⟨octahedron_nondeg, fun t ht t' ht' hne => by
    rw [← openHull_eq_interior finrank_euclideanSpace_fin octPos ht (octahedron_nondeg t ht),
      ← openHull_eq_interior finrank_euclideanSpace_fin octPos ht' (octahedron_nondeg t' ht')]
    exact octahedron_disjoint t ht t' ht' hne⟩

/-- **Flat example (geometric triangulation).** The octahedron's axis has deficit zero, now from
`IsGeometric.deficit_eq_zero_of_cycleLink`: no winding hypothesis is assumed. -/
theorem octahedron_deficit_geometric : deficit octahedron octLen {0, 1} = 0 :=
  octahedron_geometric.deficit_eq_zero_of_cycleLink finrank_euclideanSpace_fin
    octahedron_axis_cycleLink

/-- Eight tetrahedra `{0, 1, w k, w (k+1)}` around the edge `{0, 1}`, link `2, 3, …, 9, 2`. -/
def doubleRing : Complex3 (Fin 10) where
  tets := {{0, 1, 2, 3}, {0, 1, 3, 4}, {0, 1, 4, 5}, {0, 1, 5, 6}, {0, 1, 6, 7}, {0, 1, 7, 8},
    {0, 1, 8, 9}, {0, 1, 9, 2}}
  card_eq := by decide +kernel

/-- The link of the edge `{0, 1}` of `doubleRing`. -/
def dwLink (k : ℕ) : Fin 10 := ⟨k % 8 + 2, by omega⟩

/-- The edge `{0, 1}` of `doubleRing` has a cycle link of length eight. -/
theorem doubleRing_cycleLink : IsCycleLink doubleRing 0 1 8 dwLink where
  ne := by decide
  three_le := by norm_num
  ne_a := by decide
  ne_b := by decide
  inj := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  closed := rfl
  star_eq := by decide +kernel

/-- A placement winding twice around the axis: the link vertices `2, …, 5` at distance `1` and
`6, …, 9` at distance `2`, at angles `0, π/2, π, 3π/2` each time. -/
noncomputable def dwPos : Fin 10 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[0, 0, -1], !₂[0, 0, 1], !₂[1, 0, 0], !₂[0, 1, 0], !₂[-1, 0, 0], !₂[0, -1, 0],
    !₂[2, 0, 0], !₂[0, 2, 0], !₂[-2, 0, 0], !₂[0, -2, 0]]

/-- The radii of the link vertices of `doubleRing` in `dwPos`. -/
noncomputable def dwRad (k : ℕ) : ℝ := if 4 ≤ k ∧ k < 8 then 2 else 1

/-- The link vertices of `doubleRing` in cylindrical coordinates: height `1` above `x 0`, radius
`dwRad k`, angle `k π/2`. -/
theorem dwPos_cyl : ∀ k ≤ 8, dwPos (dwLink k) = dwPos 0 + (1 : ℝ) • !₂[0, 0, 1] +
    dwRad k • (cos ((k : ℝ) * (π / 2)) • !₂[1, 0, 0] + sin ((k : ℝ) * (π / 2)) • !₂[0, 1, 0]) := by
  intro k hk
  interval_cases k
  · ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad]
  · ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad]
  · rw [show ((2 : ℕ) : ℝ) * (π / 2) = π by push_cast; ring]
    ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad]
  · rw [show ((3 : ℕ) : ℝ) * (π / 2) = π / 2 + π by push_cast; ring]
    ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad, cos_add_pi, sin_add_pi]
  · rw [show ((4 : ℕ) : ℝ) * (π / 2) = 0 + 2 * π by push_cast; ring]
    ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad]
  · rw [show ((5 : ℕ) : ℝ) * (π / 2) = π / 2 + 2 * π by push_cast; ring]
    ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad, cos_add_two_pi, sin_add_two_pi]
  · rw [show ((6 : ℕ) : ℝ) * (π / 2) = π + 2 * π by push_cast; ring]
    ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad, cos_add_two_pi, sin_add_two_pi]
  · rw [show ((7 : ℕ) : ℝ) * (π / 2) = π / 2 + π + 2 * π by push_cast; ring]
    ext i; fin_cases i <;>
      simp [dwPos, dwLink, dwRad, cos_add_two_pi, sin_add_two_pi, cos_add_pi, sin_add_pi]
  · rw [show ((8 : ℕ) : ℝ) * (π / 2) = 0 + 2 * π + 2 * π by push_cast; ring]
    ext i; fin_cases i <;> simp [dwPos, dwLink, dwRad, cos_add_two_pi, sin_add_two_pi]

/-- **A placement winding twice has deficit `-2π`.** The eight tetrahedra around the edge `{0, 1}`
turn by `4π` in total. -/
theorem doubleRing_deficit :
    deficit doubleRing (ofDist fun u v => dist (dwPos u) (dwPos v)) {0, 1} = -(2 * π) := by
  have hc := doubleRing_cycleLink
  rw [deficit_eq_of_cyl doubleRing dwPos 8 dwLink hc.star_eq hc.injOn_tet
    (fun i hi => hc.tet_distinct hi) stdFrame_orthonormal (L := 2) two_pos
    (by ext i; fin_cases i <;> simp [dwPos]; norm_num) (fun _ => 1) dwRad
    (fun k => (k : ℝ) * (π / 2)) (fun k _ => by unfold dwRad; split_ifs <;> norm_num) dwPos_cyl
    (fun i _ => by push_cast; constructor <;> nlinarith [pi_pos]) (T := 4 * π)
    (by push_cast; ring)]
  ring

/-- **Disjoint interiors are necessary.** In the double ring every tetrahedron around the edge is
non-degenerate and the link is a cycle, but the deficit is `-2π ≠ 0`; so by
`deficit_eq_zero_of_embedded` some two of the open tetrahedra must overlap. -/
theorem doubleRing_overlap : ¬ ∀ i < 8, ∀ j < 8, i ≠ j →
    Disjoint (openTet (dwPos 0) (dwPos 1) (dwPos (dwLink i)) (dwPos (dwLink (i + 1))))
      (openTet (dwPos 0) (dwPos 1) (dwPos (dwLink j)) (dwPos (dwLink (j + 1)))) := by
  intro hdisj
  have hnd : ∀ i < 8, LinearIndependent ℝ
      ![dwPos 1 - dwPos 0, dwPos (dwLink i) - dwPos 0, dwPos (dwLink (i + 1)) - dwPos 0] := by
    intro i hi
    have hr := dwPos_cyl i hi.le
    have hs := dwPos_cyl (i + 1) hi
    refine cyl_linIndep stdFrame_orthonormal (L := 2) (z := 1) (z' := 1) (ρ := dwRad i)
      (ρ' := dwRad (i + 1)) (α := (i : ℝ) * (π / 2)) (α' := ((i + 1 : ℕ) : ℝ) * (π / 2)) two_ne_zero
      (by unfold dwRad; split_ifs <;> norm_num) (by unfold dwRad; split_ifs <;> norm_num)
      (by rw [show ((i + 1 : ℕ) : ℝ) * (π / 2) - (i : ℝ) * (π / 2) = π / 2 by push_cast; ring,
        sin_pi_div_two]; exact one_ne_zero)
      (by ext k; fin_cases k <;> simp [dwPos]; norm_num) (by rw [hr]; abel) (by rw [hs]; abel)
  have h0 := deficit_eq_zero_of_embedded finrank_euclideanSpace_fin doubleRing dwPos
    doubleRing_cycleLink hnd hdisj
  rw [doubleRing_deficit] at h0
  linarith [pi_pos]

/-! ## Regge's equations (`Lightlike/Regge/Schlaefli.lean`, `Lightlike/Regge/ReggeEquations.lean`)
-/

/-- The regular tetrahedron with unit edges is non-degenerate. -/
theorem tetNondeg_one : TetNondeg fun _ => 1 := by
  refine ⟨fun _ => one_pos, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [heron, Lightlike.PR.vol2]

/-- **The gradient of the regular tetrahedron's action** is the exterior dihedral angle
`π - arccos (1/3)` in every edge. -/
theorem regularTet_gradient (v : Fin 6 → ℝ) :
    HasDerivAt (fun τ => Lightlike.PR.reggeAction fun i => 1 + τ * v i)
      (∑ e, v e * (π - arccos (1 / 3))) 0 := by
  refine (hasDerivAt_reggeAction_tet (fun _ => 1) v tetNondeg_one).congr_deriv ?_
  refine sum_congr rfl fun e _ => ?_
  congr 1
  fin_cases e <;> simp [Lightlike.PR.extAngles, dihedral_one]

/-- **Sign check**: the gradient of the action is the exterior angle, not the interior angle
`arccos (1/3)`; the two differ because `arccos (1/3) ≠ π/2`. -/
theorem regularTet_gradient_ne_interior : π - arccos (1 / 3) ≠ arccos (1 / 3) := by
  intro h
  linarith [arccos_lt_pi_div_two]

/-- Unit edge lengths on the boundary of the 4-simplex are non-degenerate. -/
theorem simplexBoundary_lengthsNondeg : LengthsNondeg simplexBoundary fun _ => 1 :=
  lengthsNondeg_const _ one_pos

/-- **Regge's equations on the regular 3-sphere.** Along every direction `v`, the derivative of the
Regge action of the boundary of the 4-simplex at unit edges is `Σ_e v_e (2π - 3 arccos (1/3))`,
the deficit at every edge. -/
theorem simplexBoundary_reggeEquations (v : Finset (Fin 5) → ℝ) :
    HasDerivAt (fun τ => reggeAction simplexBoundary fun e => 1 + τ * v e)
      (∑ e ∈ simplexBoundary.edges, v e * (2 * π - 3 * arccos (1 / 3))) 0 := by
  have h := hasDerivAt_reggeAction simplexBoundary_lengthsNondeg v
  have hb : bdryEdges simplexBoundary = ∅ := by simp [bdryEdges, simplexBoundary_bdryTris]
  rw [hb, sum_empty, add_zero, intEdges_of_bdryTris_eq_empty simplexBoundary_bdryTris] at h
  refine h.congr_deriv (sum_congr rfl fun e he => ?_)
  rw [(simplexBoundary_deficit he).1]

/-- **The regular 3-sphere does not solve Regge's equations**: its deficit angles are positive, so
the action is not stationary. -/
theorem simplexBoundary_not_stationary :
    ¬ ∀ e ∈ intEdges simplexBoundary, deficit simplexBoundary (fun _ => 1) e = 0 := by
  intro h
  have he : ({0, 1} : Finset (Fin 5)) ∈ intEdges simplexBoundary := by
    rw [intEdges_of_bdryTris_eq_empty simplexBoundary_bdryTris]
    decide
  have := (simplexBoundary_deficit (by
    rw [← intEdges_of_bdryTris_eq_empty simplexBoundary_bdryTris]; exact he)).2
  linarith [h _ he]

/-- **The gradient of the regular 3-sphere's action.** The Regge action of the boundary of the
4-simplex is differentiable at unit edges, with gradient `v ↦ Σ_e v_e (2π - 3 arccos (1/3))`. -/
theorem simplexBoundary_gradient :
    HasFDerivAt (reggeAction simplexBoundary) (reggeGradient simplexBoundary fun _ => 1)
        (fun _ => 1) ∧
      ∀ v, reggeGradient simplexBoundary (fun _ => 1) v =
        ∑ e ∈ simplexBoundary.edges, v e * (2 * π - 3 * arccos (1 / 3)) := by
  refine ⟨hasFDerivAt_reggeAction simplexBoundary_lengthsNondeg, fun v => ?_⟩
  have hb : bdryEdges simplexBoundary = ∅ := by simp [bdryEdges, simplexBoundary_bdryTris]
  rw [reggeGradient_apply, hb, sum_empty, add_zero,
    intEdges_of_bdryTris_eq_empty simplexBoundary_bdryTris]
  exact sum_congr rfl fun e he => by rw [(simplexBoundary_deficit he).1]

/-! ## Combinatorial 3-manifolds (`Lightlike/Regge/CombManifold.lean`)

The boundary of the 4-simplex is a closed combinatorial 3-manifold in the sense of the core
(`Lightlike.PR.IsCombManifold`: every vertex link is a combinatorial 2-sphere), hence an edge-manifold by
`IsCombManifold.isEdgeManifold`. The other examples, which have boundary, are edge-manifolds by the
decision procedure. Two 3-spheres glued at a vertex form a closed edge-manifold that is not a
combinatorial 3-manifold. -/

/-- **The boundary of the 4-simplex is a closed combinatorial 3-manifold**: the link of each
vertex is the boundary of the tetrahedron on the other four vertices. -/
theorem simplexBoundary_isCombManifold : Lightlike.PR.IsCombManifold simplexBoundary := by
  intro v _
  fin_cases v
  · show Lightlike.PR.IsSphere2 (simplexBoundary.link 0)
    rw [show simplexBoundary.link 0 = Lightlike.PR.bdry 1 2 3 4 by decide +kernel]
    exact Lightlike.PR.isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · show Lightlike.PR.IsSphere2 (simplexBoundary.link 1)
    rw [show simplexBoundary.link 1 = Lightlike.PR.bdry 0 2 3 4 by decide +kernel]
    exact Lightlike.PR.isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · show Lightlike.PR.IsSphere2 (simplexBoundary.link 2)
    rw [show simplexBoundary.link 2 = Lightlike.PR.bdry 0 1 3 4 by decide +kernel]
    exact Lightlike.PR.isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · show Lightlike.PR.IsSphere2 (simplexBoundary.link 3)
    rw [show simplexBoundary.link 3 = Lightlike.PR.bdry 0 1 2 4 by decide +kernel]
    exact Lightlike.PR.isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · show Lightlike.PR.IsSphere2 (simplexBoundary.link 4)
    rw [show simplexBoundary.link 4 = Lightlike.PR.bdry 0 1 2 3 by decide +kernel]
    exact Lightlike.PR.isSphere2_bdry (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)

/-- The boundary of the 4-simplex is an edge-manifold, by the general theorem
`IsCombManifold.isEdgeManifold`. -/
theorem simplexBoundary_edgeManifold : IsEdgeManifold simplexBoundary :=
  IsCombManifold.isEdgeManifold simplexBoundary_isCombManifold

set_option maxRecDepth 100000 in
/-- The single tetrahedron is an edge-manifold (every edge has an arc as link). -/
theorem singleTet_edgeManifold : IsEdgeManifold singleTet :=
  isEdgeManifold_of_check _ (finLinkWitness singleTet) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The octahedron split around its axis is an edge-manifold. -/
theorem octahedron_edgeManifold : IsEdgeManifold octahedron :=
  isEdgeManifold_of_check _ (finLinkWitness octahedron) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The cube split into the six Kuhn tetrahedra is an edge-manifold. -/
theorem cube_edgeManifold : IsEdgeManifold cube :=
  isEdgeManifold_of_check _ (finLinkWitness cube) (by decide +kernel)

/-- Two copies of the boundary of the 4-simplex, on `{0, 1, 2, 3, 4}` and `{0, 5, 6, 7, 8}`,
glued at the vertex `0`. -/
def doubleSphere : Complex3 (Fin 9) where
  tets := {{0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4},
    {0, 5, 6, 7}, {0, 5, 6, 8}, {0, 5, 7, 8}, {0, 6, 7, 8}, {5, 6, 7, 8}}
  card_eq := by decide +kernel

set_option maxRecDepth 100000 in
/-- The two glued 3-spheres form a closed edge-manifold: every edge has a triangle as link. -/
theorem doubleSphere_edgeManifold : IsEdgeManifold doubleSphere :=
  isEdgeManifold_of_check _ (finLinkWitness doubleSphere) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **The vertex condition is not implied by the edge condition**: the link of the shared vertex
of the two glued 3-spheres is two disjoint 2-spheres, not connected, so the complex is not a
combinatorial 3-manifold. -/
theorem doubleSphere_not_isCombManifold : ¬ Lightlike.PR.IsCombManifold doubleSphere := by
  intro h
  have hc := (h 0 (by decide +kernel)).isSurfaceSphere.connected 1 (by decide +kernel) 5
    (by decide +kernel)
  -- the vertices `1, 2, 3, 4` of the link of `0` are closed under its edges
  have hclosed : ∀ e ∈ Lightlike.PR.edges2 (doubleSphere.link 0), ∀ x ∈ e, ∀ y ∈ e,
      x ∈ ({1, 2, 3, 4} : Finset (Fin 9)) → y ∈ ({1, 2, 3, 4} : Finset (Fin 9)) := by
    decide +kernel
  have key : ∀ y, Relation.ReflTransGen
      (fun x y => ({x, y} : Finset (Fin 9)) ∈ Lightlike.PR.edges2 (doubleSphere.link 0)) 1 y →
      y ∈ ({1, 2, 3, 4} : Finset (Fin 9)) := by
    intro y hy
    induction hy with
    | refl => decide
    | tail _ hbc ih => exact hclosed _ hbc _ (by simp) _ (by simp) ih
  exact absurd (key 5 hc) (by decide)

/-- Two tetrahedra sharing only the vertex `0`. -/
def bowtie : Complex3 (Fin 7) where
  tets := {{0, 1, 2, 3}, {0, 4, 5, 6}}
  card_eq := by decide +kernel

set_option maxRecDepth 100000 in
/-- Two tetrahedra sharing only a vertex form an edge-manifold (with boundary). -/
theorem bowtie_edgeManifold : IsEdgeManifold bowtie :=
  isEdgeManifold_of_check _ (finLinkWitness bowtie) (by decide +kernel)

/-- **Flat space solves Regge's equations (example).** The octahedron placed in `ℝ³` is a geometric
triangulation and an edge-manifold, so its Regge action is stationary under every
variation of the lengths that fixes the boundary lengths. -/
theorem octahedron_stationary (v : Finset (Fin 6) → ℝ) (hv : ∀ e ∈ bdryEdges octahedron, v e = 0) :
    HasDerivAt (fun τ => reggeAction octahedron fun e => octLen e + τ * v e) 0 0 :=
  octahedron_geometric.reggeAction_stationary finrank_euclideanSpace_fin
    octahedron_edgeManifold v hv

/-! ## Combinatorial 3-manifolds with boundary (`Lightlike/Regge/Disc.lean`) -/

section Discs

open Lightlike.PR (edges2 verts2 lk2 euler2 IsConnEdges IsConnected2 IsLinkConn)

set_option maxRecDepth 100000 in
/-- The single tetrahedron is a combinatorial 3-manifold with boundary: every vertex link is a
triangle, a disc. -/
theorem singleTet_isCombManifoldBd : IsCombManifoldBd singleTet :=
  isCombManifoldBd_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The octahedron split around its axis is a combinatorial 3-manifold with boundary. -/
theorem octahedron_isCombManifoldBd : IsCombManifoldBd octahedron :=
  isCombManifoldBd_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The cube split into the six Kuhn tetrahedra is a combinatorial 3-manifold with boundary. -/
theorem cube_isCombManifoldBd : IsCombManifoldBd cube :=
  isCombManifoldBd_of_check (by decide +kernel)

/-- The cube is an edge-manifold by the general theorem `IsCombManifoldBd.isEdgeManifold`, without
computing any edge link. -/
theorem cube_edgeManifold_of_isCombManifoldBd : IsEdgeManifold cube :=
  cube_isCombManifoldBd.isEdgeManifold

set_option maxRecDepth 100000 in
/-- The link of the corner `0` of the cube is the hexagon of six triangles around `7`, a disc with
an interior vertex. -/
theorem cube_link_isDisc2 : IsDisc2 (cube.link 0) :=
  isDisc2_iff_isSurfaceDisc.mpr (isSurfaceDisc_of_check (by decide +kernel))

/-- The boundary of the 4-simplex, a closed combinatorial 3-manifold, is a combinatorial
3-manifold with (empty) boundary. -/
theorem simplexBoundary_isCombManifoldBd : IsCombManifoldBd simplexBoundary :=
  IsCombManifold.isCombManifoldBd simplexBoundary_isCombManifold

set_option maxRecDepth 100000 in
/-- **The vertex condition is stronger than the edge condition, also with boundary.** Two
tetrahedra sharing only a vertex form an edge-manifold (`bowtie_edgeManifold`), but the link of the
shared vertex is two disjoint triangles, neither a sphere nor a disc. -/
theorem bowtie_not_isCombManifoldBd : ¬ IsCombManifoldBd bowtie := by
  intro h
  have hnot := not_reach_of_closed (S := Lightlike.PR.edges2 (bowtie.link 0))
    (A := ({1, 2, 3} : Finset (Fin 7))) (by decide +kernel) (u := 1) (w := 4) (by decide)
    (by decide)
  rcases h 0 (by decide +kernel) with hS | hD
  · exact hnot (hS.isSurfaceSphere.connected 1 (by decide +kernel) 4 (by decide +kernel))
  · exact hnot ((isDisc2_iff_isSurfaceDisc.mp hD).connected 1 (by decide +kernel) 4
      (by decide +kernel))

/-- Three tetrahedra sharing a triangle are not a combinatorial 3-manifold with boundary: by the
general theorem they would be an edge-manifold. -/
theorem tripleBook_not_isCombManifoldBd : ¬ IsCombManifoldBd tripleBook :=
  fun h => tripleBook_not_edgeManifold h.isEdgeManifold

set_option maxRecDepth 100000 in
/-- Two 3-spheres glued at a vertex are not a combinatorial 3-manifold with boundary either: the
link of the shared vertex is two disjoint spheres. -/
theorem doubleSphere_not_isCombManifoldBd : ¬ IsCombManifoldBd doubleSphere := by
  intro h
  have hnot := not_reach_of_closed (S := Lightlike.PR.edges2 (doubleSphere.link 0))
    (A := ({1, 2, 3, 4} : Finset (Fin 9))) (by decide +kernel) (u := 1) (w := 5) (by decide)
    (by decide)
  rcases h 0 (by decide +kernel) with hS | hD
  · exact hnot (hS.isSurfaceSphere.connected 1 (by decide +kernel) 5 (by decide +kernel))
  · exact hnot ((isDisc2_iff_isSurfaceDisc.mp hD).connected 1 (by decide +kernel) 5
      (by decide +kernel))

/-- A projective plane (its six-vertex triangulation, on `0, …, 5`) with the triangle `{0, 6, 7}`
attached at the vertex `0`. -/
def pinchedDisc : Finset (Finset (Fin 8)) :=
  {{0, 1, 2}, {0, 2, 3}, {0, 3, 4}, {0, 4, 5}, {0, 5, 1}, {1, 2, 4}, {2, 3, 5}, {1, 3, 4},
    {2, 4, 5}, {1, 3, 5}, {0, 6, 7}}

set_option maxRecDepth 100000 in
/-- **Recognising discs needs connected vertex links (wrong model).** The pinched complex meets
every other condition of `IsSurfaceDisc`: its triangles have three vertices, every edge lies in at
most two triangles, it is connected, its boundary is the single circle `0, 6, 7`, and its Euler
characteristic is `1`. -/
theorem pinchedDisc_passes :
    (∀ τ ∈ pinchedDisc, #τ = 3) ∧ (∀ f ∈ edges2 pinchedDisc, #(pinchedDisc.filter (f ⊆ ·)) ≤ 2) ∧
      IsConnected2 pinchedDisc ∧ (bdryEdges2 pinchedDisc).Nonempty ∧
      (∀ x ∈ verts2 (bdryEdges2 pinchedDisc), #((bdryEdges2 pinchedDisc).filter (x ∈ ·)) = 2) ∧
      IsConnEdges (bdryEdges2 pinchedDisc) ∧ euler2 pinchedDisc = 1 :=
  ⟨by decide +kernel, by decide +kernel,
    reach_of_connCheck (fun _ he => card_of_mem_edges2 he) (by decide +kernel), by decide +kernel,
    by decide +kernel, reach_of_connCheck (fun _ he => card_of_mem_bdryEdges2 he) (by decide +kernel),
    by decide +kernel⟩

set_option maxRecDepth 100000 in
/-- The pinched complex is not a disc: the link of `0` is a 5-cycle and the separate edge
`{6, 7}`. (Its cone completion is a projective plane and a sphere glued at a point.) -/
theorem pinchedDisc_not_isDisc2 : ¬ IsDisc2 pinchedDisc := by
  intro h
  have hl := (isDisc2_iff_isSurfaceDisc.mp h).link 0 (by decide +kernel) 6 (by decide +kernel) 1
    (by decide +kernel)
  exact not_reach_of_closed (S := lk2 pinchedDisc 0) (A := {6, 7}) (by decide +kernel) (by decide)
    (by decide) hl

/-- The five-vertex Möbius band: the triangles `{i, i+1, i+2}`, indices mod `5`. -/
def moebius : Finset (Finset (Fin 5)) := {{0, 1, 2}, {1, 2, 3}, {2, 3, 4}, {0, 3, 4}, {0, 1, 4}}

set_option maxRecDepth 100000 in
/-- **Recognising discs needs the Euler characteristic (wrong model).** The Möbius band meets
every other condition of `IsSurfaceDisc`; its boundary is the single circle `0, 2, 4, 1, 3`. -/
theorem moebius_passes :
    (∀ τ ∈ moebius, #τ = 3) ∧ (∀ f ∈ edges2 moebius, #(moebius.filter (f ⊆ ·)) ≤ 2) ∧
      IsLinkConn moebius ∧ IsConnected2 moebius ∧ (bdryEdges2 moebius).Nonempty ∧
      (∀ x ∈ verts2 (bdryEdges2 moebius), #((bdryEdges2 moebius).filter (x ∈ ·)) = 2) ∧
      IsConnEdges (bdryEdges2 moebius) := by
  have hc : ∀ τ ∈ moebius, #τ = 3 := by decide +kernel
  have hl : ∀ v ∈ verts2 moebius, connCheck (lk2 moebius v) (verts2 (lk2 moebius v)) := by
    decide +kernel
  exact ⟨hc, by decide +kernel,
    fun v hv => reach_of_connCheck (fun _ he => card_of_mem_lk2 hc he) (hl v hv),
    reach_of_connCheck (fun _ he => card_of_mem_edges2 he) (by decide +kernel), by decide +kernel,
    by decide +kernel, reach_of_connCheck (fun _ he => card_of_mem_bdryEdges2 he) (by decide +kernel)⟩

/-- The Möbius band has Euler characteristic `0`, so it is not a disc. -/
theorem moebius_not_isDisc2 : euler2 moebius = 0 ∧ ¬ IsDisc2 moebius := by
  have he : euler2 moebius = 0 := by decide +kernel
  refine ⟨he, fun h => ?_⟩
  have := (isDisc2_iff_isSurfaceDisc.mp h).euler
  rw [he] at this
  exact absurd this (by norm_num)

end Discs

end Lightlike.Regge.Tests
