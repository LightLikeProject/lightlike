import Lightlike.Regge.Lorentzian.FlatSolution
import Lightlike.Regge.D4.Tests

/-!
# Trust checks for Lorentzian Regge calculus

Checks of `Lightlike/Regge/Lorentzian/` on a concrete triangulation: M12's flat ring
`Lightlike.Regge4.Tests.flatRing` (six vertices, three 4-simplices around the one interior triangle
`{0, 1, 2}`), with its vertices placed in Minkowski space in two inertial frames.

* **Integer coordinates.** `ipL_eq`, `gram2L_eq`, `gram3L_eq`, `mixedL_eq`: for vertices at
  integer points, every Gram determinant of the signed squared lengths `lorLen` is an integer,
  which the kernel evaluates (`decide +kernel`); `isNonNull4_of_check` turns a finite table into
  `IsNonNull4`.
* **Two frames.** `frameT` makes the triangle `{0, 1, 2}` timelike, `frameS` makes it spacelike.
  In `frameS` the edge `{4, 5}` is null (`L = 0`); null edges are allowed, only null triangles and
  tetrahedra are excluded.
* **Manifold and non-null.** `flatRing_isTriManifold`, `flatRing_intTris`, `nonNull_T`,
  `nonNull_S`: the hypotheses of the general theorems hold, checked by the kernel.
* **Known values, from the lengths alone.** Timelike frame: dihedral angles `π/2, 3π/4, 3π/4`,
  sum `2π` (`lorDihedral4_T`, `lorAngleSum_T`). Spacelike frame: `−iπ/2`,
  `arsinh(−1/√3) − iπ/2` and `arcosh(4/√12) − iπ` with `arcosh(4/√12) = arsinh(1/√3)`, sum
  `−2πi` (`lorDihedral4_S`, `lorAngleSum_S`). The deficit is `0` in both frames
  (`lorDeficit_T`, `lorDeficit_S`), independently of the winding argument of `Embedded.lean`.
* **Non-vacuity.** `flatRing_lorDeficit_T/S` obtain the same zero deficits from the general
  theorem `IsGeometric4.lorDeficit_eq_zero`, and `flatRing_lorReggeAction_T/S` reduce the action
  to its boundary term by `IsGeometric4.lorReggeAction_eq`, with every hypothesis met.
* **Regge equations, on a complex with interior edges.** M12's subdivided 4-simplex `cone5` in the
  frame `frameC` (`nonNull_C`) has five spacelike and five timelike interior triangles
  (`cone5_causal`). Its deficits vanish (`cone5_lorDeficit`), its action is stationary under a
  change of the timelike interior edge `{1, 5}` (`cone5_lorStationary`), the Lorentzian Regge
  equations hold at all five interior edges (`cone5_lorReggeEquations`), and the Lorentzian
  Schläfli identity applies to its 4-simplex `{1, 2, 3, 4, 5}` (`cone5_lorNondeg4`,
  `cone5_lorSchlaefli`).
* **Wrong models.** M12's Euclidean formula `arccos(+M/√(G_s G_u))` on the same Lorentzian data
  gives the deficit `π`, not `0` (`wrong_eucAngle_T`); the Euclidean flat value `2π` at a
  spacelike triangle gives `2π + 2πi` (`wrong_causalZ_S`); and no choice of real angles can
  cancel the spacelike flat value, whose imaginary part `−2π` remains (`wrong_realAngles_S`).
-/

open Real Finset Module

namespace Lightlike.ReggeLor.Tests

open Lightlike.FourD (Complex4)
open Lightlike.FourD.Complex4 (mem_faces)
open Lightlike.Regge4 (IsTriManifold intTris4 bdryTris4 intEdges4 isTriManifold_of_check finLinkWitness4
  det3 lineL)
open Lightlike.Regge4.Tests (flatRing ringLink ringPos flatRing_cycleLink flatRing_geometric cone5 conePos
  cone5_geometric cone5_isTriManifold)

/-! ## Integer coordinates

The checks place the vertices of a complex on six vertices at integer points of Minkowski space and
reduce every Gram determinant to an integer, which the kernel evaluates. -/

/-- The Minkowski form `diag(−1, 1, 1, 1)` on integer vectors. -/
def etaZ (y z : Fin 4 → ℤ) : ℤ := -(y 0 * z 0) + y 1 * z 1 + y 2 * z 2 + y 3 * z 3

/-- The Minkowski inner product of the edge vectors `a − o`, `b − o` of integer points `X`. -/
def ipZ (X : Fin 6 → Fin 4 → ℤ) (o a b : Fin 6) : ℤ := etaZ (X a - X o) (X b - X o)

/-- The Gram determinant of the triangle `pqr`, over the integers. -/
def gram2Z (X : Fin 6 → Fin 4 → ℤ) (p q r : Fin 6) : ℤ :=
  ipZ X p q q * ipZ X p r r - ipZ X p q r * ipZ X p r q

/-- A `3 × 3` determinant over the integers, expanded along the first row. -/
def det3Z (a b c d e f g h i : ℤ) : ℤ :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- The Gram determinant of the tetrahedron `pqrs`, over the integers. -/
def gram3Z (X : Fin 6 → Fin 4 → ℤ) (p q r s : Fin 6) : ℤ :=
  det3Z (ipZ X p q q) (ipZ X p q r) (ipZ X p q s) (ipZ X p r q) (ipZ X p r r) (ipZ X p r s)
    (ipZ X p s q) (ipZ X p s r) (ipZ X p s s)

/-- The mixed determinant at the triangle `pqr` of the 4-simplex `pqrsu`, over the integers. -/
def mixedZ (X : Fin 6 → Fin 4 → ℤ) (p q r s u : Fin 6) : ℤ :=
  det3Z (ipZ X p q q) (ipZ X p q r) (ipZ X p q u) (ipZ X p r q) (ipZ X p r r) (ipZ X p r u)
    (ipZ X p s q) (ipZ X p s r) (ipZ X p s u)

section Coordinates

variable (φ : EuclideanSpace ℝ (Fin 4) ≃ₗ[ℝ] (Fin 4 → ℝ)) {x : Fin 6 → EuclideanSpace ℝ (Fin 4)}
  {X : Fin 6 → Fin 4 → ℤ} (hX : ∀ v k, φ (x v) k = X v k)
include hX

/-- In inertial coordinates with integer vertices, `ipL` is the integer inner product. -/
theorem ipL_eq (o a b : Fin 6) : ipL (lorLen φ x) o a b = ipZ X o a b := by
  rw [ipL_eq_g (minkG_comm φ) x (lorLen_eq φ x), minkG_apply]
  simp only [map_sub, Pi.sub_apply, hX, ipZ, etaZ]
  push_cast
  ring

/-- `gram2L` is the integer Gram determinant. -/
theorem gram2L_eq (p q r : Fin 6) : gram2L (lorLen φ x) p q r = gram2Z X p q r := by
  simp only [gram2L, ipL_eq φ hX, gram2Z]
  push_cast
  ring

/-- `gram3L` is the integer Gram determinant. -/
theorem gram3L_eq (p q r s : Fin 6) : gram3L (lorLen φ x) p q r s = gram3Z X p q r s := by
  simp only [gram3L, det3, ipL_eq φ hX, gram3Z, det3Z]
  push_cast
  ring

/-- `mixedL` is the integer mixed determinant. -/
theorem mixedL_eq (p q r s u : Fin 6) :
    mixedL (lorLen φ x) p q r s u = mixedZ X p q r s u := by
  simp only [mixedL, det3, ipL_eq φ hX, mixedZ, det3Z]
  push_cast
  ring

/-- A complex on six vertices is non-null in these coordinates if no triangle with distinct
vertices and no tetrahedron of a 4-simplex has a vanishing integer Gram determinant (a finite
check). -/
theorem isNonNull4_of_check {K : Complex4 (Fin 6)}
    (h2 : ∀ p q r : Fin 6, p ≠ q → p ≠ r → q ≠ r → gram2Z X p q r ≠ 0)
    (h3 : ∀ σ ∈ K.simps, ∀ p ∈ σ, ∀ q ∈ σ, ∀ r ∈ σ, ∀ s ∈ σ,
      #({p, q, r, s} : Finset (Fin 6)) = 4 → gram3Z X p q r s ≠ 0) :
    IsNonNull4 K (lorLen φ x) where
  tri t ht := by
    obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ :=
      card_eq_three.mp (Lightlike.FourD.Complex4.card_of_mem_faces ht)
    rw [triHL_eq _ hpq hpr hqr, gram2L_eq φ hX]
    exact mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr (h2 p q r hpq hpr hqr))
  tet p q r s h := by
    obtain ⟨σ, hσ, hsub, hcard⟩ := mem_faces.mp h
    rw [gram3L_eq φ hX]
    exact Int.cast_ne_zero.mpr (h3 σ hσ p (hsub (by simp)) q (hsub (by simp)) r (hsub (by simp))
      s (hsub (by simp)) hcard)

end Coordinates

/-! ## Two inertial frames for the flat ring -/

/-- Inertial coordinates `(2 y₀, y₁, y₂, y₃)` on `ℝ⁴`: the triangle `{0, 1, 2}` of the flat ring
is timelike. -/
noncomputable def frameT : EuclideanSpace ℝ (Fin 4) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).trans
    { toFun := fun y => ![2 * y 0, y 1, y 2, y 3]
      invFun := fun z => ![z 0 / 2, z 1, z 2, z 3]
      map_add' := fun y z => by ext k; fin_cases k <;> simp; ring
      map_smul' := fun c y => by ext k; fin_cases k <;> simp; ring
      left_inv := fun y => by ext k; fin_cases k <;> simp
      right_inv := fun z => by ext k; fin_cases k <;> simp; ring }

/-- Inertial coordinates `(2 y₂, y₀, y₁, y₃)` on `ℝ⁴`: the triangle `{0, 1, 2}` of the flat ring
is spacelike. -/
noncomputable def frameS : EuclideanSpace ℝ (Fin 4) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).trans
    { toFun := fun y => ![2 * y 2, y 0, y 1, y 3]
      invFun := fun z => ![z 1, z 2, z 0 / 2, z 3]
      map_add' := fun y z => by ext k; fin_cases k <;> simp; ring
      map_smul' := fun c y => by ext k; fin_cases k <;> simp; ring
      left_inv := fun y => by ext k; fin_cases k <;> simp
      right_inv := fun z => by ext k; fin_cases k <;> simp; ring }

/-- The vertices of the flat ring in the coordinates `frameT`. -/
def posT : Fin 6 → Fin 4 → ℤ :=
  ![![0, 0, 0, 0], ![2, 0, 0, 0], ![0, 1, 0, 0], ![2, 0, 1, 0], ![2, 0, 0, 1], ![2, 0, -1, -1]]

/-- The vertices of the flat ring in the coordinates `frameS`. -/
def posS : Fin 6 → Fin 4 → ℤ :=
  ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 1, 0, 0], ![0, 1, 0, 1], ![-2, 1, 0, -1]]

/-- The vertices of the flat ring are at the integer points `posT` in the coordinates `frameT`. -/
theorem frameT_pos (v : Fin 6) (k : Fin 4) : frameT (ringPos v) k = posT v k := by
  fin_cases v <;> fin_cases k <;> simp [frameT, ringPos, posT]

/-- The vertices of the flat ring are at the integer points `posS` in the coordinates `frameS`. -/
theorem frameS_pos (v : Fin 6) (k : Fin 4) : frameS (ringPos v) k = posS v k := by
  fin_cases v <;> fin_cases k <;> simp [frameS, ringPos, posS]

/-- The signed squared lengths of the flat ring in the coordinates `frameT`. -/
local notation "LT" => lorLen frameT ringPos

/-- The signed squared lengths of the flat ring in the coordinates `frameS`. -/
local notation "LS" => lorLen frameS ringPos

/-! ## The flat ring is a non-null Lorentzian triangulation -/

set_option maxRecDepth 100000 in
/-- `flatRing` satisfies the manifold condition at triangles (decided by the kernel). -/
theorem flatRing_isTriManifold : IsTriManifold flatRing :=
  isTriManifold_of_check _ (finLinkWitness4 flatRing) (by decide +kernel)

/-- The only interior triangle of the flat ring is `{0, 1, 2}`. -/
theorem flatRing_intTris : intTris4 flatRing = {{0, 1, 2}} := by decide +kernel

/-- No triangle of `posT` is null. -/
theorem posT_tri : ∀ p q r : Fin 6, p ≠ q → p ≠ r → q ≠ r → gram2Z posT p q r ≠ 0 := by
  decide +kernel

/-- No tetrahedron of the flat ring at `posT` is null. -/
theorem posT_tet : ∀ σ ∈ flatRing.simps, ∀ p ∈ σ, ∀ q ∈ σ, ∀ r ∈ σ, ∀ s ∈ σ,
    #({p, q, r, s} : Finset (Fin 6)) = 4 → gram3Z posT p q r s ≠ 0 := by
  decide +kernel

/-- No triangle of `posS` is null. -/
theorem posS_tri : ∀ p q r : Fin 6, p ≠ q → p ≠ r → q ≠ r → gram2Z posS p q r ≠ 0 := by
  decide +kernel

/-- No tetrahedron of the flat ring at `posS` is null. -/
theorem posS_tet : ∀ σ ∈ flatRing.simps, ∀ p ∈ σ, ∀ q ∈ σ, ∀ r ∈ σ, ∀ s ∈ σ,
    #({p, q, r, s} : Finset (Fin 6)) = 4 → gram3Z posS p q r s ≠ 0 := by
  decide +kernel

/-- The flat ring in the coordinates `frameT` is non-null. -/
theorem nonNull_T : IsNonNull4 flatRing LT :=
  isNonNull4_of_check frameT frameT_pos posT_tri posT_tet

/-- The flat ring in the coordinates `frameS` is non-null. -/
theorem nonNull_S : IsNonNull4 flatRing LS :=
  isNonNull4_of_check frameS frameS_pos posS_tri posS_tet

/-! ## Known values: the dihedral angles of the flat ring, from its lengths -/

/-- The angle sum around `{0, 1, 2}`, labelled. -/
theorem flatRing_lorAngleSum (L : Finset (Fin 6) → ℝ) :
    lorAngleSum flatRing L {0, 1, 2} =
      lorDihedral4 L 0 1 2 3 4 + lorDihedral4 L 0 1 2 4 5 + lorDihedral4 L 0 1 2 5 3 := by
  rw [lorAngleSum_eq_of_cycleLink flatRing_cycleLink]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [lorDihedralAt_eq L (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    lorDihedralAt_eq L (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    lorDihedralAt_eq L (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
  rfl

/-- The Gram determinants of the timelike ring (`frameT`) at `{0, 1, 2}`. -/
theorem values_T :
    gram2L LT 0 1 2 = -4 ∧ gram3L LT 0 1 2 3 = -4 ∧ gram3L LT 0 1 2 4 = -4 ∧
      gram3L LT 0 1 2 5 = -8 ∧ mixedL LT 0 1 2 3 4 = 0 ∧ mixedL LT 0 1 2 4 5 = 4 ∧
      mixedL LT 0 1 2 5 3 = 4 := by
  simp only [gram2L_eq frameT frameT_pos, gram3L_eq frameT frameT_pos,
    mixedL_eq frameT frameT_pos]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [gram2Z, gram3Z, mixedZ, det3Z, ipZ, etaZ, posT]

/-- The Gram determinants of the spacelike ring (`frameS`) at `{0, 1, 2}`. -/
theorem values_S :
    gram2L LS 0 1 2 = 1 ∧ gram3L LS 0 1 2 3 = -4 ∧ gram3L LS 0 1 2 4 = 1 ∧
      gram3L LS 0 1 2 5 = -3 ∧ mixedL LS 0 1 2 3 4 = 0 ∧ mixedL LS 0 1 2 4 5 = -1 ∧
      mixedL LS 0 1 2 5 3 = 4 := by
  simp only [gram2L_eq frameS frameS_pos, gram3L_eq frameS frameS_pos,
    mixedL_eq frameS frameS_pos]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [gram2Z, gram3Z, mixedZ, det3Z, ipZ, etaZ, posS]

/-- `√32 = 4 √2`. -/
theorem sqrt_32 : √(32 : ℝ) = 4 * √2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
  linear_combination 16 * Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)

/-- `arccos (1/√2) = π/4`. -/
theorem arccos_inv_sqrt_two : arccos (1 / √2) = π / 4 := by
  have h : (1 : ℝ) / √2 = cos (π / 4) := by
    rw [cos_pi_div_four]
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- **Known values at a timelike triangle**: the dihedral angles of the flat ring in `frameT` are
the Euclidean angles `π/2, 3π/4, 3π/4` of the normal plane, from the lengths. -/
theorem lorDihedral4_T :
    lorDihedral4 LT 0 1 2 3 4 = ((π / 2 : ℝ) : ℂ) ∧
      lorDihedral4 LT 0 1 2 4 5 = ((3 * π / 4 : ℝ) : ℂ) ∧
      lorDihedral4 LT 0 1 2 5 3 = ((3 * π / 4 : ℝ) : ℂ) := by
  obtain ⟨g2, g3, g4, g5, m1, m2, m3⟩ := values_T
  have h1 : ¬ 0 < gram2L LT 0 1 2 := by rw [g2]; norm_num
  have h2 : gram2L LT 0 1 2 < 0 := by rw [g2]; norm_num
  simp only [lorDihedral4, h1, h2, ↓reduceIte, g3, g4, g5, m1, m2, m3]
  have h32 : (-4 : ℝ) / √32 = -1 / √2 := by
    rw [sqrt_32, div_eq_div_iff (by positivity) (by positivity)]
    ring
  refine ⟨?_, ?_, ?_⟩ <;> congr 1
  · norm_num
  · norm_num
    rw [h32, Lightlike.Regge4.Tests.arccos_neg_inv_sqrt_two]
  · norm_num
    rw [h32, Lightlike.Regge4.Tests.arccos_neg_inv_sqrt_two]

/-- `arcosh (4/√12) = arsinh (1/√3)`: the two boosts of the spacelike ring cancel. -/
theorem arcosh_eq_arsinh : arcosh (4 / √12) = arsinh (1 / √3) := by
  have h : (4 : ℝ) / √12 = √(1 + (1 / √3) ^ 2) := by
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity), div_pow,
      Real.sq_sqrt (by norm_num), div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [h, ← cosh_arsinh, arcosh_cosh (arsinh_nonneg_iff.mpr (by positivity))]

/-- **Known values at a spacelike triangle**: the dihedral angles of the flat ring in `frameS` are
Sorkin's angles of the normal Minkowski plane, from the lengths: a timelike and a spacelike
direction at right angles (`−iπ/2`, one light ray), a spacelike and a timelike direction
(`arsinh(−1/√3) − iπ/2`), and two timelike directions in opposite cones (`arcosh(4/√12) − iπ`,
two light rays). -/
theorem lorDihedral4_S :
    lorDihedral4 LS 0 1 2 3 4 = -(π / 2 * Complex.I) ∧
      lorDihedral4 LS 0 1 2 4 5 = (arsinh (-1 / √3) : ℂ) - π / 2 * Complex.I ∧
      lorDihedral4 LS 0 1 2 5 3 = (arcosh (4 / √12) : ℂ) - π * Complex.I := by
  obtain ⟨g2, g3, g4, g5, m1, m2, m3⟩ := values_S
  have h1 : 0 < gram2L LS 0 1 2 := by rw [g2]; norm_num
  simp only [lorDihedral4, h1, ↓reduceIte, g3, g4, g5, m1, m2, m3]
  refine ⟨?_, ?_, ?_⟩
  · rw [sorkinAngle_st (by norm_num)]
    simp
  · rw [sorkinAngle_st (by norm_num)]
    norm_num
  · rw [sorkinAngle_tt_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num

/-- **The flat value at a timelike triangle, from the lengths**: the angle sum is `2π`, computed
independently of the winding argument of `Embedded.lean`. -/
theorem lorAngleSum_T : lorAngleSum flatRing LT {0, 1, 2} = 2 * π := by
  obtain ⟨d1, d2, d3⟩ := lorDihedral4_T
  rw [flatRing_lorAngleSum, d1, d2, d3]
  push_cast
  ring

/-- **The flat value at a spacelike triangle, from the lengths**: the angle sum is `−2πi` (four
light rays, the boosts cancelling), computed independently of the winding argument. -/
theorem lorAngleSum_S : lorAngleSum flatRing LS {0, 1, 2} = -(2 * π * Complex.I) := by
  obtain ⟨d1, d2, d3⟩ := lorDihedral4_S
  rw [flatRing_lorAngleSum, d1, d2, d3, neg_div, arsinh_neg, ← arcosh_eq_arsinh]
  push_cast
  ring

/-- The triangle `{0, 1, 2}` is timelike in `frameT`: `Z = 1`. -/
theorem causalZ_T : causalZ LT {0, 1, 2} = 1 := by
  rw [causalZ, triHL_eq _ (by decide) (by decide) (by decide), values_T.1]
  norm_num

/-- The triangle `{0, 1, 2}` is spacelike in `frameS`: `Z = −i`. -/
theorem causalZ_S : causalZ LS {0, 1, 2} = -Complex.I := by
  rw [causalZ, triHL_eq _ (by decide) (by decide) (by decide), values_S.1]
  norm_num

/-- The deficit of the flat timelike ring is `0`, from the lengths. -/
theorem lorDeficit_T : lorDeficit flatRing LT {0, 1, 2} = 0 := by
  rw [lorDeficit, causalZ_T, lorAngleSum_T]
  ring

/-- The deficit of the flat spacelike ring is `0`, from the lengths. -/
theorem lorDeficit_S : lorDeficit flatRing LS {0, 1, 2} = 0 := by
  rw [lorDeficit, causalZ_S, lorAngleSum_S]
  ring

/-! ## Non-vacuity: the general theorems apply to the flat ring -/

/-- **`IsGeometric4.lorDeficit_eq_zero` applies**: every interior triangle of the flat ring has
deficit `0` in the frame `frameT`, with all its hypotheses met. -/
theorem flatRing_lorDeficit_T {t : Finset (Fin 6)} (ht : t ∈ intTris4 flatRing) :
    lorDeficit flatRing LT t = 0 :=
  IsGeometric4.lorDeficit_eq_zero frameT flatRing_geometric flatRing_isTriManifold nonNull_T ht

/-- **`IsGeometric4.lorDeficit_eq_zero` applies** in the frame `frameS`, where the interior
triangle is spacelike. -/
theorem flatRing_lorDeficit_S {t : Finset (Fin 6)} (ht : t ∈ intTris4 flatRing) :
    lorDeficit flatRing LS t = 0 :=
  IsGeometric4.lorDeficit_eq_zero frameS flatRing_geometric flatRing_isTriManifold nonNull_S ht

/-- **`IsGeometric4.lorReggeAction_eq` applies**: the Lorentzian action of the flat ring is its
boundary term. -/
theorem flatRing_lorReggeAction_T :
    lorReggeAction flatRing LT =
      ∑ t ∈ bdryTris4 flatRing, (lorArea LT t : ℂ) * lorBdryAngle flatRing LT t :=
  IsGeometric4.lorReggeAction_eq frameT flatRing_geometric flatRing_isTriManifold nonNull_T

/-- The same in the frame `frameS`. -/
theorem flatRing_lorReggeAction_S :
    lorReggeAction flatRing LS =
      ∑ t ∈ bdryTris4 flatRing, (lorArea LS t : ℂ) * lorBdryAngle flatRing LS t :=
  IsGeometric4.lorReggeAction_eq frameS flatRing_geometric flatRing_isTriManifold nonNull_S

/-! ## Flat Minkowski space solves the Lorentzian Regge equations: a subdivided 4-simplex

The flat ring has no interior edge, so the stationarity theorem would hold there vacuously. M12's
subdivided 4-simplex `cone5` has five interior edges and ten interior triangles. -/

/-- Inertial coordinates `(10 y₀, 5 y₁, 5 y₂, 15 y₃)` on `ℝ⁴`. In them `cone5` has integer
vertices, no null triangle or tetrahedron, five spacelike and five timelike interior triangles, and
interior edges of both causal types. -/
noncomputable def frameC : EuclideanSpace ℝ (Fin 4) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).trans
    { toFun := fun y => ![10 * y 0, 5 * y 1, 5 * y 2, 15 * y 3]
      invFun := fun z => ![z 0 / 10, z 1 / 5, z 2 / 5, z 3 / 15]
      map_add' := fun y z => by ext k; fin_cases k <;> simp <;> ring
      map_smul' := fun c y => by ext k; fin_cases k <;> simp <;> ring
      left_inv := fun y => by ext k; fin_cases k <;> simp
      right_inv := fun z => by ext k; fin_cases k <;> simp <;> ring }

/-- The vertices of `cone5` in the coordinates `frameC`; the centre `5` is at `(2, 1, 1, 3)`. -/
def posC : Fin 6 → Fin 4 → ℤ :=
  ![![0, 0, 0, 0], ![10, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 15], ![2, 1, 1, 3]]

/-- The vertices of `cone5` are at the integer points `posC` in the coordinates `frameC`. -/
theorem frameC_pos (v : Fin 6) (k : Fin 4) : frameC (conePos v) k = posC v k := by
  fin_cases v <;> fin_cases k <;> simp [frameC, conePos, posC] <;> norm_num

/-- The signed squared lengths of `cone5` in the coordinates `frameC`. -/
local notation "LC" => lorLen frameC conePos

/-- No triangle of `posC` is null. -/
theorem posC_tri : ∀ p q r : Fin 6, p ≠ q → p ≠ r → q ≠ r → gram2Z posC p q r ≠ 0 := by
  decide +kernel

/-- No tetrahedron of `cone5` at `posC` is null. -/
theorem posC_tet : ∀ σ ∈ cone5.simps, ∀ p ∈ σ, ∀ q ∈ σ, ∀ r ∈ σ, ∀ s ∈ σ,
    #({p, q, r, s} : Finset (Fin 6)) = 4 → gram3Z posC p q r s ≠ 0 := by
  decide +kernel

/-- `cone5` in the coordinates `frameC` is non-null. -/
theorem nonNull_C : IsNonNull4 cone5 LC :=
  isNonNull4_of_check frameC frameC_pos posC_tri posC_tet

/-- **Both causal types occur among the interior triangles**: `{0, 1, 5}` is timelike
(`gram2L = −1100`) and `{0, 2, 5}` is spacelike (`gram2L = 150`), so the theorems below use both
branches of the dihedral angle. -/
theorem cone5_causal :
    {0, 1, 5} ∈ intTris4 cone5 ∧ {0, 2, 5} ∈ intTris4 cone5 ∧
      causalZ LC {0, 1, 5} = 1 ∧ causalZ LC {0, 2, 5} = -Complex.I := by
  have h1 : triHL LC {0, 1, 5} = -4400 := by
    rw [triHL_eq _ (by decide) (by decide) (by decide), gram2L_eq frameC frameC_pos]
    norm_num [gram2Z, ipZ, etaZ, posC]
  have h2 : triHL LC {0, 2, 5} = 600 := by
    rw [triHL_eq _ (by decide) (by decide) (by decide), gram2L_eq frameC frameC_pos]
    norm_num [gram2Z, ipZ, etaZ, posC]
  refine ⟨by decide +kernel, by decide +kernel, ?_, ?_⟩
  · rw [causalZ, h1]
    norm_num
  · rw [causalZ, h2]
    norm_num

/-- **`IsGeometric4.lorDeficit_eq_zero` applies to `cone5`**: all ten interior triangles, five of
them spacelike and five timelike, have Lorentzian deficit `0`. -/
theorem cone5_lorDeficit {t : Finset (Fin 6)} (ht : t ∈ intTris4 cone5) :
    lorDeficit cone5 LC t = 0 :=
  IsGeometric4.lorDeficit_eq_zero frameC cone5_geometric cone5_isTriManifold nonNull_C ht

/-- **Flat Minkowski space solves the Lorentzian Regge equations (example).** Varying the signed
squared length of the timelike interior edge `{1, 5}` alone leaves the complex Lorentzian Regge
action of the flat subdivided 4-simplex stationary
(`IsGeometric4.lorReggeAction_stationary`). -/
theorem cone5_lorStationary :
    HasDerivAt (fun τ => lorReggeAction cone5
      (lineL LC (fun f => if f = {1, 5} then 1 else 0) τ)) 0 0 := by
  refine IsGeometric4.lorReggeAction_stationary frameC cone5_geometric cone5_isTriManifold
    nonNull_C _ fun e he => ?_
  have : e ≠ {1, 5} := by
    rintro rfl
    exact absurd he (by decide +kernel)
  simp [this]

/-- **The Lorentzian Regge equations hold** at the five interior edges of the flat `cone5`, each a
sum over the four interior triangles at that edge (`lorReggeAction_stationary_iff`). -/
theorem cone5_lorReggeEquations :
    ∀ e ∈ intEdges4 cone5,
      ∑ t ∈ (intTris4 cone5).filter (e ⊆ ·), (lorAreaPartial LC t e : ℂ) * lorDeficit cone5 LC t =
        0 :=
  (lorReggeAction_stationary_iff
    (IsGeometric4.lorLengthsNondeg4 frameC cone5_geometric nonNull_C)).mp
    (IsGeometric4.lorReggeAction_stationary frameC cone5_geometric cone5_isTriManifold nonNull_C)

/-- **The Lorentzian Schläfli identity applies**: the 4-simplex `{1, 2, 3, 4, 5}` of `cone5` in
`frameC` satisfies `LorNondeg4`; its triangles `{1, 2, 5}` and `{2, 3, 5}` are timelike and
spacelike. -/
theorem cone5_lorNondeg4 : LorNondeg4 LC 1 2 3 4 5 :=
  (IsGeometric4.lorLengthsNondeg4 frameC cone5_geometric nonNull_C).lorNondeg4 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide +kernel)

/-- **Schläfli's identity on a concrete Lorentzian 4-simplex**: along every line of signed squared
lengths, the area-weighted sum of the complex dihedral angles of `{1, 2, 3, 4, 5}` is
stationary. -/
theorem cone5_lorSchlaefli (v : Finset (Fin 6) → ℝ) :
    HasDerivAt (fun τ => ∑ t ∈ ({1, 2, 3, 4, 5} : Finset (Fin 6)).powersetCard 3,
      (lorArea LC t : ℂ) * lorDihedralAt (lineL LC v τ) {1, 2, 3, 4, 5} t) 0 0 :=
  lorSchlaefli4_finset LC v (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) cone5_lorNondeg4

/-! ## Wrong models -/

/-- M12's dihedral-angle formula `arccos (mixed / √(gram3 · gram3))`, written in squared
lengths. -/
noncomputable def eucAngleL (L : Finset (Fin 6) → ℝ) (p q r s u : Fin 6) : ℝ :=
  arccos (mixedL L p q r s u / √(gram3L L p q r s * gram3L L p q r u))

/-- On squared lengths `ℓ²`, `eucAngleL` is M12's `dihedral4 ℓ`. -/
theorem eucAngleL_sq (ℓ : Finset (Fin 6) → ℝ) :
    eucAngleL (fun e => ℓ e ^ 2) = Lightlike.Regge4.dihedral4 ℓ := rfl

/-- M12's formula is symmetric. -/
theorem isSymm4_eucAngleL : Lightlike.Regge4.IsSymm4 eucAngleL :=
  ⟨fun L p q r s u => by simp only [eucAngleL, mixedL_swap_pq, gram3L_swap_pq],
    fun L p q r s u => by simp only [eucAngleL, mixedL_swap_qr, gram3L_swap_qr],
    fun L p q r s u => by simp only [eucAngleL, mixedL_swap_su, mul_comm (gram3L L p q r u)]⟩

/-- **Wrong model: Euclidean angles on Lorentzian data.** M12's dihedral-angle formula applied
to the signed squared lengths of the flat timelike ring gives `π/2, π/4, π/4` instead of
`π/2, 3π/4, 3π/4` (at a timelike triangle `gram2 < 0` reverses the sign of the cosine) and reports
the deficit `π` on flat Minkowski space. -/
theorem wrong_eucAngle_T : Lightlike.Regge4.Tests.deficitWith eucAngleL flatRing LT {0, 1, 2} = π := by
  obtain ⟨g2, g3, g4, g5, m1, m2, m3⟩ := values_T
  rw [Lightlike.Regge4.Tests.deficitWith, Lightlike.Regge4.Tests.flatRing_sum isSymm4_eucAngleL]
  simp only [eucAngleL, g3, g4, g5, m1, m2, m3]
  have h32 : (4 : ℝ) / √32 = 1 / √2 := by
    rw [sqrt_32, div_eq_div_iff (by positivity) (by positivity)]
    ring
  norm_num
  rw [h32, arccos_inv_sqrt_two]
  ring

/-- **Wrong model: the Euclidean flat value at a spacelike triangle.** With `Z = 1` (flat value
`2π`) in place of Sorkin's `Z = −i`, the flat spacelike ring would report the deficit
`2π + 2πi`. -/
theorem wrong_causalZ_S :
    2 * π * 1 - lorAngleSum flatRing LS {0, 1, 2} = 2 * π + 2 * π * Complex.I := by
  rw [lorAngleSum_S]
  ring

/-- **Wrong model: real angles at a spacelike triangle.** With any real-valued angles, such as
M12's, the deficit of the flat spacelike triangle keeps the imaginary part `−2π` of its flat
value, so it is never zero: closing a spacelike hinge needs Sorkin's complex angles. -/
theorem wrong_realAngles_S (θ : Fin 3 → ℝ) :
    (2 * π * causalZ LS {0, 1, 2} - ∑ i, (θ i : ℂ)).im = -(2 * π) := by
  rw [causalZ_S]
  simp

end Lightlike.ReggeLor.Tests
