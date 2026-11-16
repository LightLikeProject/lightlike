import Lightlike.Regge.D4.FlatSolution
import Lightlike.Regge.D4.Gradient

/-!
# Trust checks for 4D Regge calculus

Checks of the definitions in `Regge/D4/` against known values, and deliberately wrong formulas and
inputs shown to fail.

**Flat.**

* `flatRing`: three 4-simplices `{0, 1, 2, w, w'}` around the triangle `{0, 1, 2}`, placed in `ℝ⁴`
  with the link vertices at `e₀ + e₂`, `e₀ + e₃`, `e₀ - e₂ - e₃` (`ringPos`). It is a geometric
  triangulation (`flatRing_geometric`), so the general theorem gives deficit `0`
  (`flatRing_deficit`). The dihedral angles are `π/2, 3π/4, 3π/4` (`flatRing_dihedral`), checked
  from the lengths.
* `cone5`: a 4-simplex in `ℝ⁴` subdivided from its centroid (the 1-5 move), a geometric
  triangulation (`cone5_geometric`) with ten interior triangles and five interior edges
  (`cone5_interior`). Every interior deficit is `0` (`cone5_deficit`), and varying the length of
  an interior edge leaves the action stationary (`cone5_stationary`): flat space solves Regge's
  equations.

**Curved.**

* `sphere5`: the boundary of the 5-simplex (six 4-simplices, the smallest triangulation of the
  4-sphere). With unit lengths every triangle lies in three 4-simplices and has deficit
  `2π - 3 arccos(1/4) > 0` (`sphere5_deficit`); the action is `20 (√3/4)(2π - 3 arccos(1/4))`
  (`sphere5_reggeAction`); it is not stationary (`sphere5_not_stationary`).
* `regular_never_flat`: `n` regular 4-simplices never close up flat around a triangle:
  `4 arccos(1/4) < 2π < 5 arccos(1/4)`.

**Wrong formulas and inputs.**

* `flatRing_exterior`: the exterior angle `π - θ` instead of the dihedral angle reports deficit
  `π` on the flat ring.
* `flatRing_noSqrt`: forgetting the square root in `cos θ = mixed / √(gram3 gram3)` reports
  deficit `π/6`.
* `ring4_zero`: with all lengths `0` (Lean junk values) a triangle in four 4-simplices shows a fake
  deficit `0`.
* `tripleBook4_not_isTriManifold`: three 4-simplices sharing a tetrahedron violate the manifold
  condition at triangles.

**One 4-simplex.**

* `simplex5_reggeAction`: for one regular 4-simplex the action is the boundary term
  `10 (√3/4)(π - arccos(1/4))`.
-/

open Real Finset InnerProductSpace Module

namespace Lightlike.Regge4.Tests

open Lightlike.FourD (Complex4)
open Lightlike.Regge4
open Lightlike.Regge (ofDist ofDist_pair)
open Lightlike.FourD.Complex4 (card_of_mem_faces)

/-! ## A flat ring of three 4-simplices around a triangle -/

/-- Three 4-simplices `{0, 1, 2, 3, 4}`, `{0, 1, 2, 4, 5}`, `{0, 1, 2, 5, 3}` around the triangle
`{0, 1, 2}`. -/
def flatRing : Complex4 (Fin 6) where
  simps := {{0, 1, 2, 3, 4}, {0, 1, 2, 4, 5}, {0, 1, 2, 5, 3}}
  card_eq := by decide +kernel

/-- The link of the triangle `{0, 1, 2}` of `flatRing`: `3, 4, 5, 3, …`. -/
def ringLink (i : ℕ) : Fin 6 := ⟨i % 3 + 3, by omega⟩

/-- The triangle `{0, 1, 2}` of `flatRing` has a cycle link of length three. -/
theorem flatRing_cycleLink : IsCycleLink4 flatRing 0 1 2 3 ringLink where
  ne_ab := by decide
  ne_ac := by decide
  ne_bc := by decide
  three_le := le_refl 3
  ne_a := by decide
  ne_b := by decide
  ne_c := by decide
  inj := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    interval_cases i <;> interval_cases j <;> first | rfl | exact absurd h (by decide)
  closed := rfl
  star_eq := by decide +kernel

/-- The placement of `flatRing` in `ℝ⁴`: the triangle at `0, e₀, e₁`, the link vertices at
`e₀ + e₂`, `e₀ + e₃`, `e₀ - e₂ - e₃` (tilted out of the normal plane, which the dihedral angle
must ignore). -/
noncomputable def ringPos : Fin 6 → EuclideanSpace ℝ (Fin 4) :=
  ![!₂[0, 0, 0, 0], !₂[1, 0, 0, 0], !₂[0, 1, 0, 0], !₂[1, 0, 1, 0], !₂[1, 0, 0, 1],
    !₂[1, 0, -1, -1]]

/-- The edge lengths of `ringPos`. -/
noncomputable def ringLen : Finset (Fin 6) → ℝ := ofDist fun u v => dist (ringPos u) (ringPos v)

/-- `ringLen` gives each edge its Euclidean length. -/
theorem ringLen_eq (u v : Fin 6) (h : u ≠ v) : ringLen {u, v} = dist (ringPos u) (ringPos v) :=
  ofDist_pair (d := fun u v => dist (ringPos u) (ringPos v)) (fun _ => dist_self _)
    (fun _ _ => dist_comm _ _) h

/-- Four vectors `e₀, e₁, a, b` of `ℝ⁴` are linearly independent when the components of `a, b`
in the `e₂ e₃`-plane are. -/
theorem linIndep_e01 {x₀ x₁ a₂ a₃ y₀ y₁ b₂ b₃ : ℝ} (hd : a₂ * b₃ - a₃ * b₂ ≠ 0) :
    LinearIndependent ℝ ![(!₂[1, 0, 0, 0] : EuclideanSpace ℝ (Fin 4)), !₂[0, 1, 0, 0],
      !₂[x₀, x₁, a₂, a₃], !₂[y₀, y₁, b₂, b₃]] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have c : ∀ k, (∑ i, g i • ![(!₂[1, 0, 0, 0] : EuclideanSpace ℝ (Fin 4)), !₂[0, 1, 0, 0],
      !₂[x₀, x₁, a₂, a₃], !₂[y₀, y₁, b₂, b₃]] i) k = 0 := fun k => by rw [hg]; rfl
  have c0 := c 0
  have c1 := c 1
  have c2 := c 2
  have c3 := c 3
  simp [Fin.sum_univ_four] at c0 c1 c2 c3
  have e2 : g 2 = 0 := by
    have : g 2 * (a₂ * b₃ - a₃ * b₂) = 0 := by linear_combination b₃ * c2 - b₂ * c3
    exact (mul_eq_zero.mp this).resolve_right hd
  have e3 : g 3 = 0 := by
    have : g 3 * (a₂ * b₃ - a₃ * b₂) = 0 := by linear_combination a₂ * c3 - a₃ * c2
    exact (mul_eq_zero.mp this).resolve_right hd
  intro i
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [e2, e3] at c0
    linarith
  · simp only [Fin.mk_one]
    rw [e2, e3] at c1
    linarith
  · exact e2
  · exact e3

/-- The three 4-simplices of `flatRing` placed in `ℝ⁴` are non-degenerate. -/
theorem flatRing_nondeg : ∀ σ ∈ flatRing.simps, AffineIndependent ℝ fun v : σ => ringPos v := by
  intro σ hσ
  simp only [flatRing, mem_insert, mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl
  · refine affIndep_of_linIndep5 ringPos (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
    convert linIndep_e01 (x₀ := 1) (x₁ := 0) (a₂ := 1) (a₃ := 0) (y₀ := 1) (y₁ := 0) (b₂ := 0)
      (b₃ := 1) (by norm_num) using 1
    ext i k
    fin_cases i <;> fin_cases k <;> simp [ringPos]
  · refine affIndep_of_linIndep5 ringPos (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
    convert linIndep_e01 (x₀ := 1) (x₁ := 0) (a₂ := 0) (a₃ := 1) (y₀ := 1) (y₁ := 0) (b₂ := -1)
      (b₃ := -1) (by norm_num) using 1
    ext i k
    fin_cases i <;> fin_cases k <;> simp [ringPos]
  · refine affIndep_of_linIndep5 ringPos (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_
    convert linIndep_e01 (x₀ := 1) (x₁ := 0) (a₂ := -1) (a₃ := -1) (y₀ := 1) (y₁ := 0) (b₂ := 1)
      (b₃ := 0) (by norm_num) using 1
    ext i k
    fin_cases i <;> fin_cases k <;> simp [ringPos]

/-- The open simplex of `{0, 1, 2, 3, 4}` lies in `x₂ > 0, x₃ > 0`. -/
theorem ringRegion₁ {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Lightlike.Regge.openHull ringPos {0, 1, 2, 3, 4}) : 0 < y 2 ∧ 0 < y 3 := by
  obtain ⟨c, hc, -, rfl⟩ := hy
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp [ringPos]
  exact ⟨hc 3 (by decide), hc 4 (by decide)⟩

/-- The open simplex of `{0, 1, 2, 4, 5}` lies in `x₂ < 0, x₃ - x₂ > 0`. -/
theorem ringRegion₂ {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Lightlike.Regge.openHull ringPos {0, 1, 2, 4, 5}) : y 2 < 0 ∧ 0 < y 3 - y 2 := by
  obtain ⟨c, hc, -, rfl⟩ := hy
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp [ringPos]
  constructor <;> linarith [hc 4 (by decide), hc 5 (by decide)]

/-- The open simplex of `{0, 1, 2, 5, 3}` lies in `x₃ < 0, x₂ - x₃ > 0`. -/
theorem ringRegion₃ {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Lightlike.Regge.openHull ringPos {0, 1, 2, 5, 3}) : y 3 < 0 ∧ 0 < y 2 - y 3 := by
  obtain ⟨c, hc, -, rfl⟩ := hy
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp [ringPos]
  constructor <;> linarith [hc 3 (by decide), hc 5 (by decide)]

/-- **The flat ring placed in `ℝ⁴` is a geometric triangulation**: its 4-simplices are
non-degenerate, and the interiors of their convex hulls (their open simplices) lie in the three
regions `ringRegion₁`, `ringRegion₂`, `ringRegion₃`, which do not meet. -/
theorem flatRing_geometric : IsGeometric4 flatRing ringPos := by
  refine ⟨flatRing_nondeg, fun σ hσ σ' hσ' hne => ?_⟩
  rw [← openHull_eq_interior4 finrank_euclideanSpace_fin ringPos (flatRing.card_eq σ hσ)
      (flatRing_nondeg σ hσ),
    ← openHull_eq_interior4 finrank_euclideanSpace_fin ringPos (flatRing.card_eq σ' hσ')
      (flatRing_nondeg σ' hσ'), Set.disjoint_left]
  intro y hy hy'
  simp only [flatRing, mem_insert, mem_singleton] at hσ hσ'
  rcases hσ with rfl | rfl | rfl <;> rcases hσ' with rfl | rfl | rfl
  · exact hne rfl
  · linarith [(ringRegion₁ hy).1, (ringRegion₂ hy').1]
  · linarith [(ringRegion₁ hy).2, (ringRegion₃ hy').1]
  · linarith [(ringRegion₂ hy).1, (ringRegion₁ hy').1]
  · exact hne rfl
  · linarith [(ringRegion₂ hy).2, (ringRegion₃ hy').2]
  · linarith [(ringRegion₃ hy).1, (ringRegion₁ hy').2]
  · linarith [(ringRegion₃ hy).2, (ringRegion₂ hy').2]
  · exact hne rfl

/-- **Flat example.** The triangle `{0, 1, 2}` of the flat ring has deficit angle zero, by the
general theorem `IsGeometric4.deficit4_eq_zero_of_cycleLink`. -/
theorem flatRing_deficit : deficit4 flatRing ringLen {0, 1, 2} = 0 :=
  flatRing_geometric.deficit4_eq_zero_of_cycleLink finrank_euclideanSpace_fin flatRing_cycleLink

/-! ### The dihedral angles of the flat ring, from its lengths -/

/-- Inner products of edge vectors from the vertex `0` (at the origin). -/
theorem ringIp (a b : Fin 6) : ip ringLen 0 a b = ⟪ringPos a, ringPos b⟫_ℝ := by
  have h0 : ringPos 0 = 0 := by
    ext k
    fin_cases k <;> simp [ringPos]
  rw [ip_eq_inner ringPos ringLen_eq, h0, sub_zero, sub_zero]

/-- The mixed determinants and `gram3` of the flat ring at the triangle `{0, 1, 2}`. -/
theorem flatRing_values :
    mixed ringLen 0 1 2 3 4 = 0 ∧ mixed ringLen 0 1 2 4 5 = -1 ∧ mixed ringLen 0 1 2 5 3 = -1 ∧
      gram3 ringLen 0 1 2 3 = 1 ∧ gram3 ringLen 0 1 2 4 = 1 ∧ gram3 ringLen 0 1 2 5 = 2 := by
  simp only [mixed, gram3, det3, ringIp]
  simp only [ringPos, Matrix.cons_val, EuclideanSpace.inner_toLp_toLp, dotProduct,
    Fin.sum_univ_four, star_trivial]
  norm_num

/-- `arccos (-1/√2) = 3π/4`. -/
theorem arccos_neg_inv_sqrt_two : arccos (-1 / √2) = 3 * π / 4 := by
  have h : (1 : ℝ) / √2 = cos (π / 4) := by
    rw [cos_pi_div_four]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [neg_div, arccos_neg, h, arccos_cos (by positivity) (by linarith [pi_pos])]
  ring

/-- **The dihedral angles of the flat ring, from its lengths**: `π/2`, `3π/4`, `3π/4`, adding up to
`2π` (independently of the winding argument of `flatRing_deficit`). -/
theorem flatRing_dihedral :
    dihedral4 ringLen 0 1 2 3 4 = π / 2 ∧ dihedral4 ringLen 0 1 2 4 5 = 3 * π / 4 ∧
      dihedral4 ringLen 0 1 2 5 3 = 3 * π / 4 := by
  obtain ⟨m1, m2, m3, g3, g4, g5⟩ := flatRing_values
  refine ⟨?_, ?_, ?_⟩
  · rw [dihedral4, cosDihedral4, m1, zero_div, arccos_zero]
  · rw [dihedral4, cosDihedral4, m2, g4, g5, one_mul, arccos_neg_inv_sqrt_two]
  · rw [dihedral4, cosDihedral4, m3, g5, g3, mul_one, arccos_neg_inv_sqrt_two]

/-! ### Wrong formulas on the flat ring -/

/-- The deficit at `t` computed with an angle formula `F` (through the same averaging over
labellings as `dihedralAt4`). -/
noncomputable def deficitWith (F : (Finset (Fin 6) → ℝ) → Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℝ)
    (K : Complex4 (Fin 6)) (ℓ : Finset (Fin 6) → ℝ) (t : Finset (Fin 6)) : ℝ :=
  2 * π - ∑ σ ∈ K.star t, angleAvg4 F ℓ σ t

/-- The exterior angle `π - θ` instead of the dihedral angle. -/
noncomputable def extAngle4 (ℓ : Finset (Fin 6) → ℝ) (p q r s u : Fin 6) : ℝ :=
  π - dihedral4 ℓ p q r s u

/-- The cosine formula without its square root: `arccos (mixed / (gram3 · gram3))`. -/
noncomputable def noSqrt4 (ℓ : Finset (Fin 6) → ℝ) (p q r s u : Fin 6) : ℝ :=
  arccos (mixed ℓ p q r s u / (gram3 ℓ p q r s * gram3 ℓ p q r u))

/-- The exterior-angle formula is symmetric, so its average is the formula in any labelling. -/
theorem isSymm4_extAngle4 : IsSymm4 extAngle4 :=
  ⟨fun ℓ p q r s u => by simp only [extAngle4, dihedral4_swap_pq],
    fun ℓ p q r s u => by simp only [extAngle4, dihedral4_swap_qr],
    fun ℓ p q r s u => by simp only [extAngle4, dihedral4_swap_su]⟩

/-- The formula without the square root is symmetric. -/
theorem isSymm4_noSqrt4 : IsSymm4 noSqrt4 :=
  ⟨fun ℓ p q r s u => by simp only [noSqrt4, mixed_swap_pq, gram3_swap_pq],
    fun ℓ p q r s u => by simp only [noSqrt4, mixed_swap_qr, gram3_swap_qr],
    fun ℓ p q r s u => by simp only [noSqrt4, mixed_swap_su, mul_comm (gram3 ℓ p q r u)]⟩

/-- The sum over the ring of a symmetric formula, labelled. -/
theorem flatRing_sum {F : (Finset (Fin 6) → ℝ) → Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hF : IsSymm4 F) (ℓ : Finset (Fin 6) → ℝ) :
    ∑ σ ∈ flatRing.star {0, 1, 2}, angleAvg4 F ℓ σ {0, 1, 2} =
      F ℓ 0 1 2 3 4 + F ℓ 0 1 2 4 5 + F ℓ 0 1 2 5 3 := by
  rw [flatRing_cycleLink.star_eq, sum_image flatRing_cycleLink.injOn_simp]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [angleAvg4_eq hF ℓ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    angleAvg4_eq hF ℓ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    angleAvg4_eq hF ℓ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- **Wrong formula: the exterior angle.** Using `π - θ` instead of the dihedral angle reports the
deficit `π` on the flat ring (on a triangle in `n` 4-simplices it reports `(4 - n) π - δ`, so a
test needs a valence other than four). -/
theorem flatRing_exterior : deficitWith extAngle4 flatRing ringLen {0, 1, 2} = π := by
  obtain ⟨d1, d2, d3⟩ := flatRing_dihedral
  rw [deficitWith, flatRing_sum isSymm4_extAngle4]
  simp only [extAngle4, d1, d2, d3]
  ring

/-- `arccos (-1/2) = 2π/3`. -/
theorem arccos_neg_half : arccos (-1 / 2) = 2 * π / 3 := by
  rw [neg_div, arccos_neg, show (1 : ℝ) / 2 = cos (π / 3) by rw [cos_pi_div_three],
    arccos_cos (by positivity) (by linarith [pi_pos])]
  ring

/-- **Wrong formula: no square root.** `arccos (mixed / (gram3 · gram3))` reports the deficit `π/6`
on the flat ring. -/
theorem flatRing_noSqrt : deficitWith noSqrt4 flatRing ringLen {0, 1, 2} = π / 6 := by
  obtain ⟨m1, m2, m3, g3, g4, g5⟩ := flatRing_values
  rw [deficitWith, flatRing_sum isSymm4_noSqrt4]
  simp only [noSqrt4, m1, m2, m3, g3, g4, g5]
  rw [zero_div, arccos_zero, show (-1 : ℝ) / (1 * 2) = -1 / 2 by norm_num,
    show (-1 : ℝ) / (2 * 1) = -1 / 2 by norm_num, arccos_neg_half]
  ring

/-! ## The boundary of the 5-simplex: a curved closed 4-manifold -/

/-- The boundary of the 5-simplex on `Fin 6`: the six 4-simplices, a triangulated 4-sphere. -/
def sphere5 : Complex4 (Fin 6) := Lightlike.FourD.Complex4.sphere univ

/-- `sphere5` is closed. -/
theorem sphere5_bdryTets : sphere5.bdryTets = ∅ := by decide +kernel

/-- Every triangle of `sphere5` lies in three 4-simplices. -/
theorem sphere5_star_card : ∀ t ∈ sphere5.tris, #(sphere5.star t) = 3 := by decide +kernel

/-- `sphere5` has twenty triangles. -/
theorem sphere5_tris_card : #(sphere5.tris) = 20 := by decide +kernel

set_option maxRecDepth 100000 in
/-- `sphere5` satisfies the manifold condition at triangles (decided by the kernel). -/
theorem sphere5_isTriManifold : IsTriManifold sphere5 :=
  isTriManifold_of_check _ (finLinkWitness4 sphere5) (by decide +kernel)

/-- `arccos (1/4) < 2π/3`: three regular 4-simplices leave a gap around a triangle. -/
theorem arccos_quarter_lt : arccos (1 / 4) < 2 * π / 3 := by
  rw [← arccos_neg_half]
  exact arccos_lt_arccos (by norm_num) (by norm_num) (by norm_num)

/-- With all edge lengths `1` a triangle has area `√3/4`. -/
theorem area4_one {t : Finset (Fin 6)} (ht : #t = 3) : area4 (fun _ => (1 : ℝ)) t = √3 / 4 := by
  rw [area4, Lightlike.Regge.triH_const ht]
  norm_num

/-- **Curved example.** With unit lengths every triangle of the 4-sphere `sphere5` has deficit
`2π - 3 arccos(1/4)`, and this is positive. -/
theorem sphere5_deficit {t : Finset (Fin 6)} (ht : t ∈ sphere5.tris) :
    deficit4 sphere5 (fun _ => 1) t = 2 * π - 3 * arccos (1 / 4) ∧
      0 < deficit4 sphere5 (fun _ => 1) t := by
  have h : deficit4 sphere5 (fun _ => 1) t = 2 * π - 3 * arccos (1 / 4) := by
    rw [deficit4_const sphere5 one_ne_zero (card_of_mem_faces ht), sphere5_star_card t ht]
    norm_num
  exact ⟨h, by rw [h]; linarith [arccos_quarter_lt]⟩

/-- The Regge action of the unit 4-sphere `sphere5` is `20 (√3/4)(2π - 3 arccos(1/4)) > 0`. -/
theorem sphere5_reggeAction :
    reggeAction4 sphere5 (fun _ => 1) = 20 * (√3 / 4) * (2 * π - 3 * arccos (1 / 4)) := by
  have hterm : ∀ t ∈ sphere5.tris, area4 (fun _ => (1 : ℝ)) t * deficit4 sphere5 (fun _ => 1) t =
      √3 / 4 * (2 * π - 3 * arccos (1 / 4)) := fun t ht => by
    rw [area4_one (card_of_mem_faces ht), (sphere5_deficit ht).1]
  rw [reggeAction4_of_bdryTets_eq_empty sphere5_bdryTets, sum_congr rfl hterm, sum_const,
    sphere5_tris_card, nsmul_eq_mul]
  push_cast
  ring

/-- On `sphere5` with unit lengths every edge lies in four triangles, each with `∂A/∂ℓ = 1/(2√3)`,
so `∂S/∂ℓ_e = 4 (1/(2√3)) (2π - 3 arccos(1/4))`. -/
theorem sphere5_reggePartial {e : Finset (Fin 6)} (he : e ∈ sphere5.edges) :
    reggePartial4 sphere5 (fun _ => 1) e = 4 * (1 / (2 * √3)) * (2 * π - 3 * arccos (1 / 4)) := by
  have hint : intTris4 sphere5 = sphere5.tris := intTris4_of_bdryTets_eq_empty sphere5_bdryTets
  have hbd : bdryTris4 sphere5 = ∅ := by
    have := intTris4_union_bdryTris4 sphere5
    have hd := disjoint_intTris4_bdryTris4 sphere5
    rw [hint] at this hd
    exact disjoint_self_iff_empty _ |>.mp (by
      rw [disjoint_iff_ne] at hd ⊢
      intro a ha b hb
      exact hd a (this ▸ mem_union_right _ ha) b hb)
  have hcount : ∀ e ∈ sphere5.edges, #(sphere5.tris.filter (e ⊆ ·)) = 4 := by decide +kernel
  have hpart : ∀ t ∈ sphere5.tris.filter (e ⊆ ·),
      areaPartial (fun _ => (1 : ℝ)) t e * deficit4 sphere5 (fun _ => 1) t =
        1 / (2 * √3) * (2 * π - 3 * arccos (1 / 4)) := by
    intro t ht
    obtain ⟨ht', -⟩ := mem_filter.mp ht
    have h3 := card_of_mem_faces ht'
    rw [(sphere5_deficit ht').1, areaPartial, Lightlike.Regge.triH_const h3]
    simp only [one_pow, sum_const, card_powersetCard, h3, mul_one]
    norm_num
  rw [reggePartial4, hint, hbd, filter_empty, sum_empty, add_zero, sum_congr rfl hpart,
    sum_const, hcount e he, nsmul_eq_mul]
  push_cast
  ring

/-- **The unit 4-sphere is not a solution of Regge's equations**: varying the length of the edge
`{0, 1}` changes the action at the rate `∂S/∂ℓ = 4 (1/(2√3)) (2π - 3 arccos(1/4)) ≠ 0`. -/
theorem sphere5_not_stationary :
    ¬ HasDerivAt (fun τ => reggeAction4 sphere5
      (lineL (fun _ => 1) (fun f => if f = {0, 1} then 1 else 0) τ)) 0 0 := by
  intro h
  have hg := (hasDerivAt_reggeAction4_grad (lengthsNondeg4_const sphere5 one_ne_zero)
    fun f => if f = ({0, 1} : Finset (Fin 6)) then 1 else 0).unique h
  have he : ({0, 1} : Finset (Fin 6)) ∈ sphere5.edges := by decide +kernel
  rw [sum_eq_single ({0, 1} : Finset (Fin 6)) (fun f _ hf => by simp [hf])
      (fun hn => absurd he hn), ite_eq_left rfl, one_mul, sphere5_reggePartial he] at hg
  have h3 : 0 < √3 := by positivity
  have : 0 < 4 * (1 / (2 * √3)) * (2 * π - 3 * arccos (1 / 4)) := by
    have := arccos_quarter_lt
    have : 0 < 2 * π - 3 * arccos (1 / 4) := by linarith
    positivity
  linarith

/-! ## Regular 4-simplices never close up flat -/

/-- `arccos (1/4) > 2π/5`: five regular 4-simplices overlap around a triangle. -/
theorem two_pi_div_five_lt_arccos_quarter : 2 * π / 5 < arccos (1 / 4) := by
  have hc : cos (2 * π / 5) = (√5 - 1) / 4 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, cos_two_mul, cos_pi_div_five]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    ring
  have h5 : 2 < √5 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h5' : √5 < 5 := by
    rw [show (5 : ℝ) = √25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [← arccos_cos (show 0 ≤ 2 * π / 5 by positivity) (by linarith [pi_pos]), hc]
  exact arccos_lt_arccos (by norm_num) (by linarith) (by linarith)

/-- **Regular 4-simplices never close up flat around a triangle**: `n` of them leave a gap
(`n ≤ 4`) or overlap (`n ≥ 5`), since `4 arccos(1/4) < 2π < 5 arccos(1/4)`. -/
theorem regular_never_flat (n : ℕ) :
    (n ≤ 4 → 0 < 2 * π - n * arccos (1 / 4)) ∧ (5 ≤ n → 2 * π - n * arccos (1 / 4) < 0) := by
  have h1 := arccos_lt_pi_div_two.mpr (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 := two_pi_div_five_lt_arccos_quarter
  have h0 := arccos_nonneg (1 / 4 : ℝ)
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · have : (n : ℝ) ≤ 4 := by exact_mod_cast hn
    nlinarith [pi_pos]
  · have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pi_pos]

/-! ## Junk values -/

/-- Four 4-simplices around the triangle `{0, 1, 2}`. -/
def ring4 : Complex4 (Fin 7) where
  simps := {{0, 1, 2, 3, 4}, {0, 1, 2, 4, 5}, {0, 1, 2, 5, 6}, {0, 1, 2, 6, 3}}
  card_eq := by decide +kernel

/-- **Junk values fake flatness.** With all lengths `0` (degenerate), Lean's `0/0 = 0` makes every
dihedral angle `arccos 0 = π/2`, and a triangle in four 4-simplices shows deficit `0`. -/
theorem ring4_zero : deficit4 ring4 (fun _ => 0) {0, 1, 2} = 0 := by
  have hθ : ∀ σ ∈ ring4.star {0, 1, 2}, dihedralAt4 (fun _ => (0 : ℝ)) σ {0, 1, 2} = π / 2 := by
    intro σ hσ
    have hst := Lightlike.FourD.Complex4.mem_star.mp hσ
    refine angleAvg4_of_forall _ _ (by decide) ?_ fun p _ q _ r _ s _ u _ => ?_
    · rw [card_sdiff_of_subset hst.2, ring4.card_eq σ hst.1]
      decide
    · simp [dihedral4, cosDihedral4, mixed, det3, ip, sq]
  have hc : #(ring4.star {0, 1, 2}) = 4 := by decide +kernel
  rw [deficit4, angleSum4, sum_congr rfl hθ, sum_const, hc, nsmul_eq_mul]
  push_cast
  ring

/-! ## A non-manifold -/

/-- Three 4-simplices sharing the tetrahedron `{0, 1, 2, 3}`. -/
def tripleBook4 : Complex4 (Fin 7) where
  simps := {{0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 3, 6}}
  card_eq := by decide +kernel

/-- **Non-manifold check.** The link of the triangle `{0, 1, 2}` of `tripleBook4` is a star with
three arms (all three 4-simplices contain the vertex `3`), neither a cycle nor a path. -/
theorem tripleBook4_not_isTriManifold : ¬ IsTriManifold tripleBook4 := by
  intro hK
  obtain ⟨a, b, c, n, w, he, hc | hp⟩ := hK {0, 1, 2} (by decide +kernel)
  all_goals
    have h3 : ∀ σ ∈ tripleBook4.star {a, b, c}, (3 : Fin 7) ∈ σ := by
      rw [← he]
      decide +kernel
    have habc : a ≠ 3 ∧ b ≠ 3 ∧ c ≠ 3 := by
      have ha : a ∈ ({0, 1, 2} : Finset (Fin 7)) := by rw [he]; simp
      have hb : b ∈ ({0, 1, 2} : Finset (Fin 7)) := by rw [he]; simp
      have hc : c ∈ ({0, 1, 2} : Finset (Fin 7)) := by rw [he]; simp
      simp only [mem_insert, mem_singleton] at ha hb hc
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp at ha hb hc
  · have hn3 := hc.three_le
    have mem3 : ∀ i < n, w i = 3 ∨ w (Lightlike.Regge.cycSucc n i) = 3 := by
      intro i hi
      have := h3 _ (by rw [hc.star_eq]; exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
      rw [hc.w_succ hi] at this
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h | h | h
      · exact absurd h.symm habc.1
      · exact absurd h.symm habc.2.1
      · exact absurd h.symm habc.2.2
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have s0 : Lightlike.Regge.cycSucc n 0 = 1 := by unfold Lightlike.Regge.cycSucc; split_ifs <;> omega
    have s1 : Lightlike.Regge.cycSucc n 1 = 2 := by unfold Lightlike.Regge.cycSucc; split_ifs <;> omega
    have s2 : Lightlike.Regge.cycSucc n 2 ≠ 1 := by unfold Lightlike.Regge.cycSucc; split_ifs <;> omega
    have hs2 : Lightlike.Regge.cycSucc n 2 < n := Lightlike.Regge.cycSucc_lt (by omega)
    rcases mem3 0 (by omega) with h0 | h0 <;> rw [s0] at * <;>
      rcases mem3 1 (by omega) with h1 | h1 <;> rw [s1] at * <;>
      rcases mem3 2 (by omega) with h2' | h2'
    all_goals first
      | exact absurd (hc.w_inj (by omega) (by omega) (h0.trans h1.symm)) (by omega)
      | exact absurd (hc.w_inj (by omega) (by omega) (h1.trans h2'.symm)) (by omega)
  · have hn : 3 ≤ n := by
      have := card_image_le (s := range n)
        (f := fun i => ({a, b, c, w i, w (i + 1)} : Finset (Fin 7)))
      rw [← hp.star_eq, ← he, show #(tripleBook4.star {0, 1, 2}) = 3 by decide +kernel,
        card_range] at this
      exact this
    have mem3 : ∀ i < n, w i = 3 ∨ w (i + 1) = 3 := by
      intro i hi
      have := h3 _ (by rw [hp.star_eq]; exact mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)
      simp only [mem_insert, mem_singleton] at this
      rcases this with h | h | h | h | h
      · exact absurd h.symm habc.1
      · exact absurd h.symm habc.2.1
      · exact absurd h.symm habc.2.2
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    have inj : ∀ i j, i ≤ n → j ≤ n → w i = w j → i = j := fun i j hi hj h =>
      hp.inj (by simp only [coe_range, Set.mem_Iio]; omega)
        (by simp only [coe_range, Set.mem_Iio]; omega) h
    rcases mem3 0 (by omega) with h0 | h0 <;> rcases mem3 2 (by omega) with h2' | h2'
    · exact absurd (inj 0 2 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)
    · exact absurd (inj 0 3 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)
    · exact absurd (inj 1 2 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)
    · exact absurd (inj 1 3 (by omega) (by omega) (h0.trans h2'.symm)) (by omega)

/-! ## One 4-simplex -/

/-- The complex of one 4-simplex on `Fin 5`. -/
def simplex5 : Complex4 (Fin 5) := Lightlike.FourD.Complex4.simplex univ (by decide)

/-- **One regular 4-simplex**: every triangle is on the boundary, in one 4-simplex, and the Regge
action is the boundary term `10 (√3/4)(π - arccos(1/4))`. -/
theorem simplex5_reggeAction :
    reggeAction4 simplex5 (fun _ => 1) = 10 * (√3 / 4) * (π - arccos (1 / 4)) := by
  have hint : intTris4 simplex5 = ∅ := by decide +kernel
  have hbd : bdryTris4 simplex5 = simplex5.tris := by decide +kernel
  have hstar : ∀ t ∈ simplex5.tris, #(simplex5.star t) = 1 := by decide +kernel
  have hcard : #(simplex5.tris) = 10 := by decide +kernel
  have hterm : ∀ t ∈ simplex5.tris, area4 (fun _ => (1 : ℝ)) t * bdryAngle4 simplex5 (fun _ => 1) t =
      √3 / 4 * (π - arccos (1 / 4)) := by
    intro t ht
    have h3 := card_of_mem_faces ht
    have hθ : ∀ σ ∈ simplex5.star t, dihedralAt4 (fun _ => (1 : ℝ)) σ t = arccos (1 / 4) := by
      intro σ hσ
      obtain ⟨hσK, htσ⟩ := Lightlike.FourD.Complex4.mem_star.mp hσ
      exact dihedralAt4_const one_ne_zero (simplex5.card_eq σ hσK) h3 htσ
    rw [bdryAngle4, angleSum4, sum_congr rfl hθ, sum_const, hstar t ht, one_smul, area4,
      Lightlike.Regge.triH_const h3]
    norm_num
  rw [reggeAction4, hint, sum_empty, zero_add, hbd, sum_congr rfl hterm, sum_const, hcard,
    nsmul_eq_mul]
  push_cast
  ring

/-! ## A subdivided 4-simplex: flat, with interior triangles and edges -/

/-- The 4-simplex `{0, 1, 2, 3, 4}` subdivided from an interior vertex `5` (the 1-5 Pachner move):
the five 4-simplices `{5} ∪ (facet)`. -/
def cone5 : Complex4 (Fin 6) where
  simps := {{1, 2, 3, 4, 5}, {0, 2, 3, 4, 5}, {0, 1, 3, 4, 5}, {0, 1, 2, 4, 5}, {0, 1, 2, 3, 5}}
  card_eq := by decide +kernel

/-- The placement of `cone5`: the corners `0, e₀, e₁, e₂, e₃` and the centroid at `(1/5)(1,1,1,1)`. -/
noncomputable def conePos : Fin 6 → EuclideanSpace ℝ (Fin 4) :=
  ![!₂[0, 0, 0, 0], !₂[1, 0, 0, 0], !₂[0, 1, 0, 0], !₂[0, 0, 1, 0], !₂[0, 0, 0, 1],
    !₂[1 / 5, 1 / 5, 1 / 5, 1 / 5]]

/-- The edge lengths of `conePos`. -/
noncomputable def coneLen : Finset (Fin 6) → ℝ := ofDist fun u v => dist (conePos u) (conePos v)

/-- Linear independence of four explicit vectors of `ℝ⁴`, by solving the coordinate equations. -/
macro "linIndep4" : tactic =>
  `(tactic| (rw [Fintype.linearIndependent_iff]
             intro g hg
             have c0 := congrArg (fun y : EuclideanSpace ℝ (Fin 4) => y 0) hg
             have c1 := congrArg (fun y : EuclideanSpace ℝ (Fin 4) => y 1) hg
             have c2 := congrArg (fun y : EuclideanSpace ℝ (Fin 4) => y 2) hg
             have c3 := congrArg (fun y : EuclideanSpace ℝ (Fin 4) => y 3) hg
             simp [Fin.sum_univ_four, conePos] at c0 c1 c2 c3
             intro i
             fin_cases i <;> simp <;> linarith))

/-- The five 4-simplices of `cone5` are non-degenerate. -/
theorem cone5_nondeg : ∀ σ ∈ cone5.simps, AffineIndependent ℝ fun v : σ => conePos v := by
  intro σ hσ
  simp only [cone5, mem_insert, mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl <;>
    refine affIndep_of_linIndep5 conePos (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ <;>
    linIndep4

/-- The barycentric coordinate of `y` at the corner `k` of the big simplex. -/
noncomputable def bary (y : EuclideanSpace ℝ (Fin 4)) : Fin 5 → ℝ :=
  ![1 - y 0 - y 1 - y 2 - y 3, y 0, y 1, y 2, y 3]

/-- In the open simplex of the 4-simplex of `cone5` opposite the corner `k`, the barycentric
coordinate at `k` is the smallest. -/
theorem coneRegion {k : Fin 5} {σ : Finset (Fin 6)} (hσ : σ ∈ cone5.simps)
    (hk : (⟨k, by omega⟩ : Fin 6) ∉ σ) {y : EuclideanSpace ℝ (Fin 4)}
    (hy : y ∈ Lightlike.Regge.openHull conePos σ) : ∀ j : Fin 5, j ≠ k → bary y k < bary y j := by
  obtain ⟨c, hc, hsum, rfl⟩ := hy
  simp only [cone5, mem_insert, mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl <;> fin_cases k <;> simp at hk <;>
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq] at hc <;>
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
      sum_insert (by decide), sum_singleton] at hsum ⊢ <;>
    intro j hj <;> fin_cases j <;> simp at hj <;> simp [bary, conePos] <;>
    linarith [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]

/-- Each 4-simplex of `cone5` is the vertex set without one corner `k`. -/
theorem cone5_simps_eq {σ : Finset (Fin 6)} (hσ : σ ∈ cone5.simps) :
    ∃ k : Fin 5, σ = (univ : Finset (Fin 6)).erase ⟨k, by omega⟩ := by
  simp only [cone5, mem_insert, mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]

/-- **The subdivided 4-simplex placed in `ℝ⁴` is a geometric triangulation**: in the open
4-simplex opposite the corner `k` the barycentric coordinate at `k` is the smallest, so distinct
open 4-simplices do not meet. -/
theorem cone5_geometric : IsGeometric4 cone5 conePos := by
  refine ⟨cone5_nondeg, fun σ hσ σ' hσ' hne => ?_⟩
  rw [← openHull_eq_interior4 finrank_euclideanSpace_fin conePos (cone5.card_eq σ hσ)
      (cone5_nondeg σ hσ),
    ← openHull_eq_interior4 finrank_euclideanSpace_fin conePos (cone5.card_eq σ' hσ')
      (cone5_nondeg σ' hσ'), Set.disjoint_left]
  intro y hy hy'
  obtain ⟨k, rfl⟩ := cone5_simps_eq hσ
  obtain ⟨k', rfl⟩ := cone5_simps_eq hσ'
  have hkk : k ≠ k' := by
    rintro rfl
    exact hne rfl
  have h1 := coneRegion hσ (by simp) hy k' (Ne.symm hkk)
  have h2 := coneRegion hσ' (by simp) hy' k hkk
  linarith

set_option maxRecDepth 100000 in
/-- `cone5` satisfies the manifold condition at triangles (decided by the kernel). -/
theorem cone5_isTriManifold : IsTriManifold cone5 :=
  isTriManifold_of_check _ (finLinkWitness4 cone5) (by decide +kernel)

/-- `cone5` has ten interior triangles (those through the centre `5`) and five interior edges. -/
theorem cone5_interior :
    #(intTris4 cone5) = 10 ∧ intEdges4 cone5 = {{0, 5}, {1, 5}, {2, 5}, {3, 5}, {4, 5}} := by
  constructor <;> decide +kernel

/-- **Flat example with interior triangles.** All ten interior triangles of the subdivided
4-simplex have deficit zero (`IsGeometric4.deficit4_eq_zero`). -/
theorem cone5_deficit {t : Finset (Fin 6)} (ht : t ∈ intTris4 cone5) :
    deficit4 cone5 coneLen t = 0 :=
  cone5_geometric.deficit4_eq_zero finrank_euclideanSpace_fin cone5_isTriManifold ht

/-- **Flat space solves Regge's equations (example).** Moving the interior vertex `5` along the
edge `{0, 5}`, i.e. varying the length of that interior edge alone, leaves the Regge action of the
flat subdivided 4-simplex stationary. -/
theorem cone5_stationary :
    HasDerivAt (fun τ => reggeAction4 cone5
      (lineL coneLen (fun f => if f = {0, 5} then 1 else 0) τ)) 0 0 := by
  refine cone5_geometric.reggeAction4_stationary finrank_euclideanSpace_fin cone5_isTriManifold _
    fun e he => ?_
  have : e ≠ {0, 5} := by
    rintro rfl
    exact absurd he (by decide +kernel)
  simp [this]

end Lightlike.Regge4.Tests
