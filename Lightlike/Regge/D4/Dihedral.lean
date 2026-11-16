import Lightlike.Regge.Dihedral

/-!
# Dihedral angles of a 4-simplex from its edge lengths

In 4D Regge calculus curvature sits on triangles. Two tetrahedra of a 4-simplex meet in a triangle,
and the **dihedral angle** there is the angle between the two tetrahedra, measured in the plane
orthogonal to the triangle. This file computes it from the ten edge lengths and checks the formula
against Euclidean geometry.

Let the 4-simplex have vertices `p, q, r, s, u`, the triangle be `pqr`, and the tetrahedra `pqrs`
and `pqru`. With the edge vectors `a = q - p`, `b = r - p`, `c = s - p`, `d = u - p`, all inner
products follow from the squared lengths by polarization, `⟨i - o, j - o⟩ = (ℓ_oi² + ℓ_oj² -
ℓ_ij²)/2` (`ip`). The Gram determinants (`gram2`, `gram3`, `gram4`) are `(k!)²` times the squared
`k`-volumes, as in the Cayley–Menger formula: `gram2 = 4·area²`, `gram3 = 36·vol₃²`,
`gram4 = 576·vol₄²`. The **mixed determinant** `mixed` has rows `a, b, c` and columns `a, b, d`.
Then

  `cos θ = mixed / √(gram3(pqrs) · gram3(pqru))`.

## Main results

* `sq ℓ a b`: the squared length of the edge `ab` (zero for `a = b`), from lengths `ℓ` on
  2-element vertex sets as everywhere in `Regge/`.
* `ip ℓ o a b`, `gram2`, `gram3`, `gram4`, `mixed`: inner products and determinants.
* `cosDihedral4 ℓ p q r s u`, `dihedral4 ℓ p q r s u`: the dihedral angle at the triangle `pqr`
  between the tetrahedra `pqrs` and `pqru`.
* `perp2 a b c`: the component of `c` orthogonal to `a` and `b`.

* `mixed_swap_pq`, `mixed_swap_qr`, `mixed_swap_su`, `gram3_swap_pq`, `gram3_swap_qr`,
  `gram3_swap_rs`: the formulas are exactly symmetric, so `dihedral4` depends only on the
  triangle and the two opposite vertices (`dihedral4_swap_pq`, `dihedral4_swap_qr`,
  `dihedral4_swap_su`).
* `desnanot_jacobi`: `gram3(pqrs) · gram3(pqru) - mixed² = gram2(pqr) · gram4`, so
  `sin θ = √(gram2 · gram4) / √(gram3 · gram3)`.
* `cosDihedral4_dist`, `dihedral4_dist`: **the length formula is Euclidean**. For points of any
  real inner product space with a non-degenerate triangle `pqr`, `dihedral4` of their distances is
  the angle between the components of `s - p` and `u - p` orthogonal to the plane of the
  triangle (`perp2`, characterised by `perp2_mem_orthogonal` and `sub_perp2_mem_span`).
* `dihedral4_smul`: invariance under scaling all lengths.
* `cosDihedral4_regular`: the regular 4-simplex has `cos θ = 1/4`.

Symbolic checks of these identities (and of the facet identity used for Schläfli's identity):
`scripts/regge/regge4_check.py`.
-/

open Real InnerProductGeometry InnerProductSpace Finset

namespace Lightlike.Regge4

variable {V : Type*} [DecidableEq V]

/-! ## Inner products and determinants from lengths -/

/-- The determinant of the `3 × 3` matrix with rows `(a, b, c)`, `(d, e, f)`, `(g, h, i)`. -/
def det3 (a b c d e f g h i : ℝ) : ℝ :=
  a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)

/-- The squared length of the edge `ab`, from the lengths `ℓ` of 2-element vertex sets; zero for
`a = b`. -/
noncomputable def sq (ℓ : Finset V → ℝ) (a b : V) : ℝ := if a = b then 0 else ℓ {a, b} ^ 2

/-- The inner product `⟨a - o, b - o⟩` of two edge vectors from `o`, by polarization. -/
noncomputable def ip (ℓ : Finset V → ℝ) (o a b : V) : ℝ := (sq ℓ o a + sq ℓ o b - sq ℓ a b) / 2

/-- The Gram determinant of the edge vectors `q - p`, `r - p` of the triangle `pqr`: four times
its squared area. -/
noncomputable def gram2 (ℓ : Finset V → ℝ) (p q r : V) : ℝ :=
  ip ℓ p q q * ip ℓ p r r - ip ℓ p q r * ip ℓ p r q

/-- The Gram determinant of the edge vectors `q - p`, `r - p`, `s - p` of the tetrahedron `pqrs`:
`36` times its squared volume. -/
noncomputable def gram3 (ℓ : Finset V → ℝ) (p q r s : V) : ℝ :=
  det3 (ip ℓ p q q) (ip ℓ p q r) (ip ℓ p q s) (ip ℓ p r q) (ip ℓ p r r) (ip ℓ p r s)
    (ip ℓ p s q) (ip ℓ p s r) (ip ℓ p s s)

/-- The mixed determinant at the triangle `pqr` of the 4-simplex `pqrsu`: rows `q - p, r - p,
s - p`, columns `q - p, r - p, u - p` of the Gram matrix. -/
noncomputable def mixed (ℓ : Finset V → ℝ) (p q r s u : V) : ℝ :=
  det3 (ip ℓ p q q) (ip ℓ p q r) (ip ℓ p q u) (ip ℓ p r q) (ip ℓ p r r) (ip ℓ p r u)
    (ip ℓ p s q) (ip ℓ p s r) (ip ℓ p s u)

/-- The Gram determinant of the edge vectors `q - p, r - p, s - p, u - p` of the 4-simplex
`pqrsu` (expanded along the first row): `576` times its squared 4-volume. -/
noncomputable def gram4 (ℓ : Finset V → ℝ) (p q r s u : V) : ℝ :=
  ip ℓ p q q * det3 (ip ℓ p r r) (ip ℓ p r s) (ip ℓ p r u) (ip ℓ p s r) (ip ℓ p s s) (ip ℓ p s u)
      (ip ℓ p u r) (ip ℓ p u s) (ip ℓ p u u)
    - ip ℓ p q r * det3 (ip ℓ p r q) (ip ℓ p r s) (ip ℓ p r u) (ip ℓ p s q) (ip ℓ p s s)
      (ip ℓ p s u) (ip ℓ p u q) (ip ℓ p u s) (ip ℓ p u u)
    + ip ℓ p q s * det3 (ip ℓ p r q) (ip ℓ p r r) (ip ℓ p r u) (ip ℓ p s q) (ip ℓ p s r)
      (ip ℓ p s u) (ip ℓ p u q) (ip ℓ p u r) (ip ℓ p u u)
    - ip ℓ p q u * det3 (ip ℓ p r q) (ip ℓ p r r) (ip ℓ p r s) (ip ℓ p s q) (ip ℓ p s r)
      (ip ℓ p s s) (ip ℓ p u q) (ip ℓ p u r) (ip ℓ p u s)

/-- Cosine of the **dihedral angle** of the 4-simplex `pqrsu` at its triangle `pqr`, between the
tetrahedra `pqrs` and `pqru`. -/
noncomputable def cosDihedral4 (ℓ : Finset V → ℝ) (p q r s u : V) : ℝ :=
  mixed ℓ p q r s u / √(gram3 ℓ p q r s * gram3 ℓ p q r u)

/-- The **dihedral angle** of the 4-simplex `pqrsu` at its triangle `pqr`. -/
noncomputable def dihedral4 (ℓ : Finset V → ℝ) (p q r s u : V) : ℝ :=
  arccos (cosDihedral4 ℓ p q r s u)

/-! ## Symmetry -/

omit [DecidableEq V] in
/-- Squared lengths are symmetric. -/
theorem sq_comm [DecidableEq V] (ℓ : Finset V → ℝ) (a b : V) : sq ℓ a b = sq ℓ b a := by
  by_cases h : a = b
  · rw [h]
  · simp [sq, h, Ne.symm h, pair_comm]

/-- The squared length of a degenerate edge is zero. -/
@[simp] theorem sq_self (ℓ : Finset V → ℝ) (a : V) : sq ℓ a a = 0 := by simp [sq]

/-- The squared length of an edge `ab`, `a ≠ b`. -/
theorem sq_of_ne (ℓ : Finset V → ℝ) {a b : V} (h : a ≠ b) : sq ℓ a b = ℓ {a, b} ^ 2 := by
  simp [sq, h]

/-- Normalise squared lengths: remove `sq ℓ a a`, order the arguments, expand. -/
macro "sq_ring" : tactic =>
  `(tactic| (simp only [mixed, gram2, gram3, gram4, det3, ip, sq_self]
             simp only [sq_comm]
             ring))

/-- The mixed determinant is symmetric in the first two vertices of the triangle. -/
theorem mixed_swap_pq (ℓ : Finset V → ℝ) (p q r s u : V) :
    mixed ℓ q p r s u = mixed ℓ p q r s u := by sq_ring

/-- The mixed determinant is symmetric in the last two vertices of the triangle. -/
theorem mixed_swap_qr (ℓ : Finset V → ℝ) (p q r s u : V) :
    mixed ℓ p r q s u = mixed ℓ p q r s u := by sq_ring

/-- The mixed determinant is symmetric in the two opposite vertices. -/
theorem mixed_swap_su (ℓ : Finset V → ℝ) (p q r s u : V) :
    mixed ℓ p q r u s = mixed ℓ p q r s u := by sq_ring

/-- `gram3` is symmetric in its first two points. -/
theorem gram3_swap_pq (ℓ : Finset V → ℝ) (p q r s : V) :
    gram3 ℓ q p r s = gram3 ℓ p q r s := by sq_ring

/-- `gram3` is symmetric in its second and third points. -/
theorem gram3_swap_qr (ℓ : Finset V → ℝ) (p q r s : V) :
    gram3 ℓ p r q s = gram3 ℓ p q r s := by sq_ring

/-- `gram3` is symmetric in its last two points. -/
theorem gram3_swap_rs (ℓ : Finset V → ℝ) (p q r s : V) :
    gram3 ℓ p q s r = gram3 ℓ p q r s := by sq_ring

/-- `gram2` is symmetric in its first two points. -/
theorem gram2_swap_pq (ℓ : Finset V → ℝ) (p q r : V) : gram2 ℓ q p r = gram2 ℓ p q r := by
  sq_ring

/-- `gram2` is symmetric in its last two points. -/
theorem gram2_swap_qr (ℓ : Finset V → ℝ) (p q r : V) : gram2 ℓ p r q = gram2 ℓ p q r := by
  sq_ring

/-- The dihedral angle is symmetric in the first two vertices of the triangle. -/
theorem dihedral4_swap_pq (ℓ : Finset V → ℝ) (p q r s u : V) :
    dihedral4 ℓ q p r s u = dihedral4 ℓ p q r s u := by
  simp only [dihedral4, cosDihedral4, mixed_swap_pq, gram3_swap_pq]

/-- The dihedral angle is symmetric in the last two vertices of the triangle. -/
theorem dihedral4_swap_qr (ℓ : Finset V → ℝ) (p q r s u : V) :
    dihedral4 ℓ p r q s u = dihedral4 ℓ p q r s u := by
  simp only [dihedral4, cosDihedral4, mixed_swap_qr, gram3_swap_qr]

/-- The dihedral angle is symmetric in the two opposite vertices. -/
theorem dihedral4_swap_su (ℓ : Finset V → ℝ) (p q r s u : V) :
    dihedral4 ℓ p q r u s = dihedral4 ℓ p q r s u := by
  simp only [dihedral4, cosDihedral4, mixed_swap_su, mul_comm (gram3 ℓ p q r u)]

/-- **Desnanot–Jacobi**: `gram3(pqrs) · gram3(pqru) - mixed² = gram2(pqr) · gram4(pqrsu)`. Hence
`sin² θ = gram2 · gram4 / (gram3 · gram3)`. -/
theorem desnanot_jacobi (ℓ : Finset V → ℝ) (p q r s u : V) :
    gram3 ℓ p q r s * gram3 ℓ p q r u - mixed ℓ p q r s u ^ 2 =
      gram2 ℓ p q r * gram4 ℓ p q r s u := by sq_ring

/-! ## Scaling and the regular 4-simplex -/

/-- Scaling all lengths by `c` scales squared lengths by `c²`. -/
theorem sq_smul (ℓ : Finset V → ℝ) (c : ℝ) (a b : V) :
    sq (fun e => c * ℓ e) a b = c ^ 2 * sq ℓ a b := by
  unfold sq
  split_ifs <;> ring

/-- The cosine of the dihedral angle is invariant under scaling all lengths by `c ≠ 0`. -/
theorem cosDihedral4_smul (ℓ : Finset V → ℝ) {c : ℝ} (hc : c ≠ 0) (p q r s u : V) :
    cosDihedral4 (fun e => c * ℓ e) p q r s u = cosDihedral4 ℓ p q r s u := by
  have hm : mixed (fun e => c * ℓ e) p q r s u = (c ^ 2) ^ 3 * mixed ℓ p q r s u := by
    simp only [mixed, det3, ip, sq_smul]; ring
  have hg : ∀ s', gram3 (fun e => c * ℓ e) p q r s' = (c ^ 2) ^ 3 * gram3 ℓ p q r s' := by
    intro s'; simp only [gram3, det3, ip, sq_smul]; ring
  have hpos : 0 < (c ^ 2) ^ 3 := by positivity
  rw [cosDihedral4, cosDihedral4, hm, hg, hg,
    show (c ^ 2) ^ 3 * gram3 ℓ p q r s * ((c ^ 2) ^ 3 * gram3 ℓ p q r u) =
      ((c ^ 2) ^ 3) ^ 2 * (gram3 ℓ p q r s * gram3 ℓ p q r u) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hpos.le, mul_div_mul_left _ _ hpos.ne']

/-- The dihedral angle is invariant under scaling all lengths by `c ≠ 0`. -/
theorem dihedral4_smul (ℓ : Finset V → ℝ) {c : ℝ} (hc : c ≠ 0) (p q r s u : V) :
    dihedral4 (fun e => c * ℓ e) p q r s u = dihedral4 ℓ p q r s u := by
  rw [dihedral4, dihedral4, cosDihedral4_smul ℓ hc]

set_option linter.unusedSimpArgs false in
/-- **The regular 4-simplex**: with all edge lengths `a ≠ 0`, the dihedral angle has
`cos θ = 1/4`. -/
theorem cosDihedral4_regular {a : ℝ} (ha : a ≠ 0) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u) :
    cosDihedral4 (fun _ => a) p q r s u = 1 / 4 := by
  have hm : mixed (fun _ => a) p q r s u = (a ^ 2) ^ 3 / 8 := by
    simp only [mixed, det3, ip, sq, hpq, hpr, hps, hpu, hqr, hqs, hqu, hrs, hru, hsu,
      Ne.symm hpq, Ne.symm hpr, Ne.symm hps, Ne.symm hpu, Ne.symm hqr, Ne.symm hqs, Ne.symm hqu,
      Ne.symm hrs, Ne.symm hru, Ne.symm hsu, ite_true, ite_false]
    ring
  have hg : ∀ w, p ≠ w → q ≠ w → r ≠ w → gram3 (fun _ => a) p q r w = (a ^ 2) ^ 3 / 2 := by
    intro w hpw hqw hrw
    simp only [gram3, det3, ip, sq, hpq, hpr, hqr, hpw, hqw, hrw, Ne.symm hpq, Ne.symm hpr,
      Ne.symm hqr, Ne.symm hpw, Ne.symm hqw, Ne.symm hrw, ite_true, ite_false]
    ring
  have hpos : 0 < (a ^ 2) ^ 3 / 2 := by positivity
  rw [cosDihedral4, hm, hg s hps hqs hrs, hg u hpu hqu hru, ← pow_two, Real.sqrt_sq hpos.le]
  field_simp
  ring

/-! ## The length formula is Euclidean -/

section Euclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component of `c` orthogonal to `a` and `b`: `c` minus its orthogonal projection onto the
span of `a` and `b`, written with Cramer's rule (for linearly independent `a, b`). -/
noncomputable def perp2 (a b c : E) : E :=
  c - ((⟪c, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪c, b⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)) • a -
    ((⟪c, b⟫_ℝ * ⟪a, a⟫_ℝ - ⟪c, a⟫_ℝ * ⟪a, b⟫_ℝ) / (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2)) • b

variable {a b : E}

/-- `perp2 a b c` is orthogonal to `a`. -/
theorem inner_perp2_left (h : ⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2 ≠ 0) (c : E) :
    ⟪perp2 a b c, a⟫_ℝ = 0 := by
  simp only [perp2, inner_sub_left, real_inner_smul_left, real_inner_comm a b]
  linear_combination (-⟪c, a⟫_ℝ) * mul_inv_cancel₀ h

/-- `perp2 a b c` is orthogonal to `b`. -/
theorem inner_perp2_right (h : ⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2 ≠ 0) (c : E) :
    ⟪perp2 a b c, b⟫_ℝ = 0 := by
  simp only [perp2, inner_sub_left, real_inner_smul_left]
  linear_combination (-⟪c, b⟫_ℝ) * mul_inv_cancel₀ h

/-- A vector orthogonal to `a` and `b` has the same inner product with `perp2 a b d` as with
`d`. -/
theorem inner_perp2_of_orth {y : E} (ha : ⟪y, a⟫_ℝ = 0) (hb : ⟪y, b⟫_ℝ = 0) (d : E) :
    ⟪y, perp2 a b d⟫_ℝ = ⟪y, d⟫_ℝ := by
  simp only [perp2, inner_sub_right, real_inner_smul_right, ha, hb, mul_zero, sub_zero]

/-- `perp2 a b c` lies in the orthogonal complement of the span of `a` and `b`. -/
theorem perp2_mem_orthogonal (h : ⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2 ≠ 0) (c : E) :
    perp2 a b c ∈ (Submodule.span ℝ {a, b})ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro v hv
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, inner_perp2_left h,
    inner_perp2_right h, mul_zero, mul_zero, add_zero]

/-- `c - perp2 a b c` lies in the span of `a` and `b`; with `perp2_mem_orthogonal`, `perp2 a b c`
is the orthogonal projection of `c` onto the orthogonal complement of that span. -/
theorem sub_perp2_mem_span (c : E) : c - perp2 a b c ∈ Submodule.span ℝ {a, b} := by
  rw [Submodule.mem_span_pair]
  exact ⟨_, _, by simp only [perp2]; abel⟩

/-- The inner product of two orthogonal components is the mixed determinant divided by the Gram
determinant of `a, b`. -/
theorem inner_perp2_perp2 (h : ⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2 ≠ 0) (c d : E) :
    ⟪perp2 a b c, perp2 a b d⟫_ℝ =
      det3 ⟪a, a⟫_ℝ ⟪a, b⟫_ℝ ⟪a, d⟫_ℝ ⟪b, a⟫_ℝ ⟪b, b⟫_ℝ ⟪b, d⟫_ℝ ⟪c, a⟫_ℝ ⟪c, b⟫_ℝ ⟪c, d⟫_ℝ /
        (⟪a, a⟫_ℝ * ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ ^ 2) := by
  rw [inner_perp2_of_orth (inner_perp2_left h c) (inner_perp2_right h c)]
  simp only [perp2, det3, inner_sub_left, real_inner_smul_left, real_inner_comm a b]
  linear_combination (-⟪c, d⟫_ℝ) * mul_inv_cancel₀ h

variable (x : V → E) {ℓ : Finset V → ℝ}

omit [InnerProductSpace ℝ E] in
/-- For the lengths of a placement `x`, squared lengths are squared distances. -/
theorem sq_eq_norm (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) (a b : V) :
    sq ℓ a b = ‖x a - x b‖ ^ 2 := by
  by_cases h : a = b
  · simp [h]
  · rw [sq_of_ne ℓ h, hℓ a b h, dist_eq_norm]

/-- For the lengths of a placement `x`, `ip` is the inner product of the edge vectors. -/
theorem ip_eq_inner (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) (o a b : V) :
    ip ℓ o a b = ⟪x a - x o, x b - x o⟫_ℝ := by
  rw [ip, sq_eq_norm x hℓ, sq_eq_norm x hℓ, sq_eq_norm x hℓ,
    show x o - x a = -(x a - x o) by abel, show x o - x b = -(x b - x o) by abel,
    show x a - x b = (x a - x o) - (x b - x o) by abel, norm_neg, norm_neg,
    norm_sub_sq_real (x a - x o) (x b - x o)]
  ring

/-- For the lengths of a placement, `gram2` is the Gram determinant of the edge vectors. -/
theorem gram2_eq_inner (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) (p q r : V) :
    gram2 ℓ p q r = ⟪x q - x p, x q - x p⟫_ℝ * ⟪x r - x p, x r - x p⟫_ℝ -
      ⟪x q - x p, x r - x p⟫_ℝ ^ 2 := by
  rw [gram2, ip_eq_inner x hℓ, ip_eq_inner x hℓ, ip_eq_inner x hℓ, ip_eq_inner x hℓ,
    real_inner_comm (x q - x p) (x r - x p)]
  ring

/-- For the lengths of a placement, `gram2 ≥ 0` (Cauchy–Schwarz). -/
theorem gram2_nonneg (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) (p q r : V) :
    0 ≤ gram2 ℓ p q r := by
  rw [gram2_eq_inner x hℓ]
  nlinarith [real_inner_mul_inner_self_le (x q - x p) (x r - x p)]

/-- For the lengths of a placement with a non-degenerate triangle `pqr`, `gram3(pqrs)` is `gram2`
times the squared length of the component of `s - p` orthogonal to the triangle. -/
theorem gram3_eq_norm (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) {p q r : V}
    (h : gram2 ℓ p q r ≠ 0) (s : V) :
    gram3 ℓ p q r s = gram2 ℓ p q r * ‖perp2 (x q - x p) (x r - x p) (x s - x p)‖ ^ 2 := by
  have hG := h
  rw [gram2_eq_inner x hℓ] at hG
  rw [← real_inner_self_eq_norm_sq, inner_perp2_perp2 hG, gram2_eq_inner x hℓ,
    mul_div_cancel₀ _ hG]
  simp only [gram3, ip_eq_inner x hℓ]

/-- For the lengths of a placement with a non-degenerate triangle `pqr`, the mixed determinant is
`gram2` times the inner product of the components of `s - p` and `u - p` orthogonal to the
triangle. -/
theorem mixed_eq_inner (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) {p q r : V}
    (h : gram2 ℓ p q r ≠ 0) (s u : V) :
    mixed ℓ p q r s u = gram2 ℓ p q r * ⟪perp2 (x q - x p) (x r - x p) (x s - x p),
      perp2 (x q - x p) (x r - x p) (x u - x p)⟫_ℝ := by
  have hG := h
  rw [gram2_eq_inner x hℓ] at hG
  rw [inner_perp2_perp2 hG, gram2_eq_inner x hℓ, mul_div_cancel₀ _ hG]
  simp only [mixed, ip_eq_inner x hℓ]

/-- **The length formula is Euclidean.** For points of a real inner product space with a
non-degenerate triangle `pqr` (`gram2 ≠ 0`), `cosDihedral4` of their distances is the cosine of
the angle between the components of `s - p` and `u - p` orthogonal to the plane of the triangle. -/
theorem cosDihedral4_dist (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) {p q r : V}
    (h : gram2 ℓ p q r ≠ 0) (s u : V) :
    cosDihedral4 ℓ p q r s u =
      ⟪perp2 (x q - x p) (x r - x p) (x s - x p), perp2 (x q - x p) (x r - x p) (x u - x p)⟫_ℝ /
        (‖perp2 (x q - x p) (x r - x p) (x s - x p)‖ *
          ‖perp2 (x q - x p) (x r - x p) (x u - x p)‖) := by
  have hpos : 0 < gram2 ℓ p q r := lt_of_le_of_ne (gram2_nonneg x hℓ p q r) (Ne.symm h)
  rw [cosDihedral4, mixed_eq_inner x hℓ h, gram3_eq_norm x hℓ h, gram3_eq_norm x hℓ h,
    show ∀ G A B : ℝ, G * A ^ 2 * (G * B ^ 2) = (G * (A * B)) ^ 2 from fun G A B => by ring,
    Real.sqrt_sq (by positivity), mul_div_mul_left _ _ h]

/-- **The dihedral angle from lengths is the Euclidean dihedral angle**: the angle between the
components of `s - p` and `u - p` orthogonal to the plane of the triangle `pqr`. -/
theorem dihedral4_dist (hℓ : ∀ a b, a ≠ b → ℓ {a, b} = dist (x a) (x b)) {p q r : V}
    (h : gram2 ℓ p q r ≠ 0) (s u : V) :
    dihedral4 ℓ p q r s u = angle (perp2 (x q - x p) (x r - x p) (x s - x p))
      (perp2 (x q - x p) (x r - x p) (x u - x p)) := by
  rw [dihedral4, cosDihedral4_dist x hℓ h, angle]

end Euclid

end Lightlike.Regge4
