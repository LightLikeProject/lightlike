import Lightlike.Regge.Lorentzian.Angle
import Lightlike.Regge.D4.Dihedral

/-!
# Dihedral angles of a Lorentzian 4-simplex from its squared edge lengths

In Lorentzian Regge calculus (Sorkin 1975) the variables are the **signed squared lengths**
`L e = η(Δx, Δx)` of the edges, positive for spacelike and negative for timelike edges, in the
signature `(−,+,+,+)`. The inner products of edge vectors follow from them by polarization, which
holds for any symmetric bilinear form, so the Gram determinants of M12 (`Lightlike/Regge/D4/Dihedral.lean`)
are the same polynomials, now in `L` instead of `ℓ²` (`gram2L_sq`, …, `gram4L_sq`).

At the triangle `pqr` of the 4-simplex `pqrsu`, the components of `s - p` and `u - p` orthogonal
to the triangle have the inner products `G_s/G`, `G_u/G`, `M/G` (`g_perpL_perpL`), with
`G = gram2L(pqr)`, `G_s = gram3L(pqrs)`, `G_u = gram3L(pqru)` and `M = mixedL`. The dihedral angle
is the angle of the wedge they span in the plane orthogonal to the triangle (Asante, Dittrich,
Padua-Argüelles, arXiv:2104.00485, Appendix B, eqs. B4–B6):

* at a **spacelike** triangle (`G > 0`) the orthogonal plane is a Minkowski plane and the angle is
  Sorkin's complex angle `sorkinAngle G_s G_u M` (`Lightlike/Regge/Lorentzian/Angle.lean`);
* at a **timelike** triangle (`G < 0`) the orthogonal plane is Euclidean and the angle is
  `arccos(−M / √(G_s G_u))`. The sign is opposite to the Euclidean formula of M12 because `G < 0`.

## Main results

* `sqL L a b`, `ipL L o a b`, `gram2L`, `gram3L`, `mixedL`, `gram4L`: squared lengths, inner
  products and determinants from signed squared lengths.
* `lorDihedral4 L p q r s u`: the dihedral angle at the triangle `pqr` between the tetrahedra
  `pqrs` and `pqru`, a complex number (zero, a junk value, at null triangles).
* `perpL g a b c`: the component of `c` that is `g`-orthogonal to `a` and `b`, for a symmetric
  bilinear form `g`.

* `mixedL_swap_pq`, …, `lorDihedral4_swap_su`: the formulas depend only on the triangle and the
  two opposite vertices.
* `desnanot_jacobiL`: `G_s G_u − M² = G · gram4L`, the identity of M12 for signed squared lengths.
* `gram2L_sq`, `gram3L_sq`, `mixedL_sq`, `gram4L_sq`: for `L = ℓ²` the polynomials are those of
  M12.
* `ipL_eq_g`, `gram3L_eq_g`, `mixedL_eq_g`: for the squared lengths `L {a, b} = g(x b − x a,
  x b − x a)` of a placement in a space with a symmetric bilinear form `g`, the polynomials are
  the Gram determinants of `g`, and `gram3L`, `mixedL` are `G` times the `g`-inner products of the
  orthogonal components (Schur complements).
* `lorDihedral4_eq_of_pos`, `lorDihedral4_eq_of_neg`: **the length formula is the geometric
  angle**: at a spacelike triangle it is Sorkin's angle of the orthogonal components, at a
  timelike triangle the Euclidean angle between them.
-/

open Real Finset

namespace Lightlike.ReggeLor

open Lightlike.Regge4 (det3)

variable {V : Type*} [DecidableEq V]

/-! ## Inner products and determinants from signed squared lengths -/

/-- The signed squared length of the edge `ab`, from the values `L` on 2-element vertex sets;
zero for `a = b`. -/
noncomputable def sqL (L : Finset V → ℝ) (a b : V) : ℝ := if a = b then 0 else L {a, b}

/-- The inner product `η(a - o, b - o)` of two edge vectors from `o`, by polarization. -/
noncomputable def ipL (L : Finset V → ℝ) (o a b : V) : ℝ := (sqL L o a + sqL L o b - sqL L a b) / 2

/-- The Gram determinant of the edge vectors `q - p`, `r - p` of the triangle `pqr`: positive for
a spacelike, negative for a timelike triangle. -/
noncomputable def gram2L (L : Finset V → ℝ) (p q r : V) : ℝ :=
  ipL L p q q * ipL L p r r - ipL L p q r * ipL L p r q

/-- The Gram determinant of the edge vectors `q - p`, `r - p`, `s - p` of the tetrahedron
`pqrs`. -/
noncomputable def gram3L (L : Finset V → ℝ) (p q r s : V) : ℝ :=
  det3 (ipL L p q q) (ipL L p q r) (ipL L p q s) (ipL L p r q) (ipL L p r r) (ipL L p r s)
    (ipL L p s q) (ipL L p s r) (ipL L p s s)

/-- The mixed determinant at the triangle `pqr` of the 4-simplex `pqrsu`: rows `q - p, r - p,
s - p`, columns `q - p, r - p, u - p` of the Gram matrix. -/
noncomputable def mixedL (L : Finset V → ℝ) (p q r s u : V) : ℝ :=
  det3 (ipL L p q q) (ipL L p q r) (ipL L p q u) (ipL L p r q) (ipL L p r r) (ipL L p r u)
    (ipL L p s q) (ipL L p s r) (ipL L p s u)

/-- The Gram determinant of the edge vectors `q - p, r - p, s - p, u - p` of the 4-simplex
`pqrsu` (expanded along the first row); negative for a Lorentzian 4-simplex. -/
noncomputable def gram4L (L : Finset V → ℝ) (p q r s u : V) : ℝ :=
  ipL L p q q * det3 (ipL L p r r) (ipL L p r s) (ipL L p r u) (ipL L p s r) (ipL L p s s)
      (ipL L p s u) (ipL L p u r) (ipL L p u s) (ipL L p u u)
    - ipL L p q r * det3 (ipL L p r q) (ipL L p r s) (ipL L p r u) (ipL L p s q) (ipL L p s s)
      (ipL L p s u) (ipL L p u q) (ipL L p u s) (ipL L p u u)
    + ipL L p q s * det3 (ipL L p r q) (ipL L p r r) (ipL L p r u) (ipL L p s q) (ipL L p s r)
      (ipL L p s u) (ipL L p u q) (ipL L p u r) (ipL L p u u)
    - ipL L p q u * det3 (ipL L p r q) (ipL L p r r) (ipL L p r s) (ipL L p s q) (ipL L p s r)
      (ipL L p s s) (ipL L p u q) (ipL L p u r) (ipL L p u s)

/-- The **Lorentzian dihedral angle** of the 4-simplex `pqrsu` at its triangle `pqr`, between the
tetrahedra `pqrs` and `pqru`: Sorkin's angle at a spacelike triangle, the Euclidean angle
`arccos(−M/√(G_s G_u))` at a timelike one, and the junk value `0` at a null triangle. -/
noncomputable def lorDihedral4 (L : Finset V → ℝ) (p q r s u : V) : ℂ :=
  if 0 < gram2L L p q r then
    sorkinAngle (gram3L L p q r s) (gram3L L p q r u) (mixedL L p q r s u)
  else if gram2L L p q r < 0 then
    ((arccos (-mixedL L p q r s u / √(gram3L L p q r s * gram3L L p q r u)) : ℝ) : ℂ)
  else 0

/-! ## Symmetry -/

omit [DecidableEq V] in
/-- Signed squared lengths are symmetric. -/
theorem sqL_comm [DecidableEq V] (L : Finset V → ℝ) (a b : V) : sqL L a b = sqL L b a := by
  by_cases h : a = b
  · rw [h]
  · simp [sqL, h, Ne.symm h, pair_comm]

/-- The squared length of a degenerate edge is zero. -/
@[simp] theorem sqL_self (L : Finset V → ℝ) (a : V) : sqL L a a = 0 := by simp [sqL]

/-- The signed squared length of an edge `ab`, `a ≠ b`. -/
theorem sqL_of_ne (L : Finset V → ℝ) {a b : V} (h : a ≠ b) : sqL L a b = L {a, b} := by
  simp [sqL, h]

/-- Normalise signed squared lengths: remove `sqL L a a`, order the arguments, expand. -/
macro "sqL_ring" : tactic =>
  `(tactic| (simp only [mixedL, gram2L, gram3L, gram4L, det3, ipL, sqL_self]
             simp only [sqL_comm]
             ring))

/-- The mixed determinant is symmetric in the first two vertices of the triangle. -/
theorem mixedL_swap_pq (L : Finset V → ℝ) (p q r s u : V) :
    mixedL L q p r s u = mixedL L p q r s u := by sqL_ring

/-- The mixed determinant is symmetric in the last two vertices of the triangle. -/
theorem mixedL_swap_qr (L : Finset V → ℝ) (p q r s u : V) :
    mixedL L p r q s u = mixedL L p q r s u := by sqL_ring

/-- The mixed determinant is symmetric in the two opposite vertices. -/
theorem mixedL_swap_su (L : Finset V → ℝ) (p q r s u : V) :
    mixedL L p q r u s = mixedL L p q r s u := by sqL_ring

/-- `gram3L` is symmetric in its first two points. -/
theorem gram3L_swap_pq (L : Finset V → ℝ) (p q r s : V) :
    gram3L L q p r s = gram3L L p q r s := by sqL_ring

/-- `gram3L` is symmetric in its second and third points. -/
theorem gram3L_swap_qr (L : Finset V → ℝ) (p q r s : V) :
    gram3L L p r q s = gram3L L p q r s := by sqL_ring

/-- `gram3L` is symmetric in its last two points. -/
theorem gram3L_swap_rs (L : Finset V → ℝ) (p q r s : V) :
    gram3L L p q s r = gram3L L p q r s := by sqL_ring

/-- `gram2L` is symmetric in its first two points. -/
theorem gram2L_swap_pq (L : Finset V → ℝ) (p q r : V) : gram2L L q p r = gram2L L p q r := by
  sqL_ring

/-- `gram2L` is symmetric in its last two points. -/
theorem gram2L_swap_qr (L : Finset V → ℝ) (p q r : V) : gram2L L p r q = gram2L L p q r := by
  sqL_ring

/-- The Lorentzian dihedral angle is symmetric in the first two vertices of the triangle. -/
theorem lorDihedral4_swap_pq (L : Finset V → ℝ) (p q r s u : V) :
    lorDihedral4 L q p r s u = lorDihedral4 L p q r s u := by
  simp only [lorDihedral4, mixedL_swap_pq, gram3L_swap_pq, gram2L_swap_pq]

/-- The Lorentzian dihedral angle is symmetric in the last two vertices of the triangle. -/
theorem lorDihedral4_swap_qr (L : Finset V → ℝ) (p q r s u : V) :
    lorDihedral4 L p r q s u = lorDihedral4 L p q r s u := by
  simp only [lorDihedral4, mixedL_swap_qr, gram3L_swap_qr, gram2L_swap_qr]

/-- The Lorentzian dihedral angle is symmetric in the two opposite vertices: Sorkin's angle does
not depend on the order of the two vectors that bound the wedge (`sorkinAngle_comm`). -/
theorem lorDihedral4_swap_su (L : Finset V → ℝ) (p q r s u : V) :
    lorDihedral4 L p q r u s = lorDihedral4 L p q r s u := by
  simp only [lorDihedral4, mixedL_swap_su, sorkinAngle_comm, mul_comm (gram3L L p q r u)]

/-- **Desnanot–Jacobi** for signed squared lengths: `G_s · G_u − M² = G · gram4L`. -/
theorem desnanot_jacobiL (L : Finset V → ℝ) (p q r s u : V) :
    gram3L L p q r s * gram3L L p q r u - mixedL L p q r s u ^ 2 =
      gram2L L p q r * gram4L L p q r s u := by sqL_ring

/-! ## The Euclidean polynomials of M12 -/

/-- For the squares of lengths `ℓ`, the signed squared lengths are the squared lengths of M12. -/
theorem sqL_sq (ℓ : Finset V → ℝ) : sqL (fun e => ℓ e ^ 2) = Lightlike.Regge4.sq ℓ := rfl

/-- For `L = ℓ²`, `ipL` is the inner product `ip` of M12. -/
theorem ipL_sq (ℓ : Finset V → ℝ) : ipL (fun e => ℓ e ^ 2) = Lightlike.Regge4.ip ℓ := rfl

/-- For `L = ℓ²`, `gram2L` is `gram2` of M12. -/
theorem gram2L_sq (ℓ : Finset V → ℝ) : gram2L (fun e => ℓ e ^ 2) = Lightlike.Regge4.gram2 ℓ := rfl

/-- For `L = ℓ²`, `gram3L` is `gram3` of M12. -/
theorem gram3L_sq (ℓ : Finset V → ℝ) : gram3L (fun e => ℓ e ^ 2) = Lightlike.Regge4.gram3 ℓ := rfl

/-- For `L = ℓ²`, `mixedL` is `mixed` of M12. -/
theorem mixedL_sq (ℓ : Finset V → ℝ) : mixedL (fun e => ℓ e ^ 2) = Lightlike.Regge4.mixed ℓ := rfl

/-- For `L = ℓ²`, `gram4L` is `gram4` of M12. -/
theorem gram4L_sq (ℓ : Finset V → ℝ) : gram4L (fun e => ℓ e ^ 2) = Lightlike.Regge4.gram4 ℓ := rfl

/-! ## Realization by a symmetric bilinear form -/

section Bilin

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (g : LinearMap.BilinForm ℝ E)

/-- Sorkin's angle is unchanged when its three arguments are multiplied by `c > 0`. -/
theorem sorkinAngle_mul {c : ℝ} (hc : 0 < c) (aa bb ab : ℝ) :
    sorkinAngle (c * aa) (c * bb) (c * ab) = sorkinAngle aa bb ab := by
  have h := sorkinAngle_div (aa := c * aa) (bb := c * bb) (ab := c * ab) hc
  rw [mul_div_cancel_left₀ _ hc.ne', mul_div_cancel_left₀ _ hc.ne',
    mul_div_cancel_left₀ _ hc.ne'] at h
  exact h.symm

/-- The component of `c` that is `g`-orthogonal to `a` and `b`, by Cramer's rule (meaningful when
the Gram determinant `g(a,a) g(b,b) − g(a,b)²` is non-zero). -/
noncomputable def perpL (a b c : E) : E :=
  c - ((g c a * g b b - g c b * g a b) / (g a a * g b b - g a b ^ 2)) • a -
    ((g c b * g a a - g c a * g a b) / (g a a * g b b - g a b ^ 2)) • b

variable {g} (hg : ∀ y z, g y z = g z y) {a b : E}
include hg

/-- `perpL g a b c` is `g`-orthogonal to `a`. -/
theorem g_perpL_left (h : g a a * g b b - g a b ^ 2 ≠ 0) (c : E) : g (perpL g a b c) a = 0 := by
  simp only [perpL, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul, hg b a]
  linear_combination (-g c a) * mul_inv_cancel₀ h

omit hg in
/-- `perpL g a b c` is `g`-orthogonal to `b`. -/
theorem g_perpL_right (h : g a a * g b b - g a b ^ 2 ≠ 0) (c : E) : g (perpL g a b c) b = 0 := by
  simp only [perpL, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul]
  linear_combination (-g c b) * mul_inv_cancel₀ h

omit hg in
/-- A vector `g`-orthogonal to `a` and `b` has the same `g`-inner product with `perpL g a b d` as
with `d`. -/
theorem g_perpL_of_orth {y : E} (ha : g y a = 0) (hb : g y b = 0) (d : E) :
    g y (perpL g a b d) = g y d := by
  simp only [perpL, map_sub, map_smul, smul_eq_mul, ha, hb, mul_zero, sub_zero]

/-- The `g`-inner product of two orthogonal components is the mixed determinant divided by the
Gram determinant of `a, b` (a Schur complement). -/
theorem g_perpL_perpL (h : g a a * g b b - g a b ^ 2 ≠ 0) (c d : E) :
    g (perpL g a b c) (perpL g a b d) =
      det3 (g a a) (g a b) (g a d) (g b a) (g b b) (g b d) (g c a) (g c b) (g c d) /
        (g a a * g b b - g a b ^ 2) := by
  rw [g_perpL_of_orth (g_perpL_left hg h c) (g_perpL_right h c)]
  simp only [perpL, det3, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul, hg b a]
  linear_combination (-g c d) * mul_inv_cancel₀ h

omit hg in
/-- `c - perpL g a b c` lies in the span of `a` and `b`. -/
theorem sub_perpL_mem_span (c : E) : c - perpL g a b c ∈ Submodule.span ℝ {a, b} := by
  rw [Submodule.mem_span_pair]
  exact ⟨_, _, by simp only [perpL]; abel⟩

variable (x : V → E) {L : Finset V → ℝ}

omit hg in
/-- For the squared lengths of a placement, `sqL` is the `g`-square of the edge vector. -/
theorem sqL_eq_g (hL : ∀ a b, a ≠ b → L {a, b} = g (x b - x a) (x b - x a)) (a b : V) :
    sqL L a b = g (x b - x a) (x b - x a) := by
  by_cases h : a = b
  · simp [h]
  · rw [sqL_of_ne L h, hL a b h]

/-- For the squared lengths of a placement, `ipL` is the `g`-inner product of the edge
vectors. -/
theorem ipL_eq_g (hL : ∀ a b, a ≠ b → L {a, b} = g (x b - x a) (x b - x a)) (o a b : V) :
    ipL L o a b = g (x a - x o) (x b - x o) := by
  rw [ipL, sqL_eq_g x hL, sqL_eq_g x hL, sqL_eq_g x hL,
    show x b - x a = (x b - x o) - (x a - x o) by abel]
  simp only [map_sub, LinearMap.sub_apply]
  rw [hg (x a) (x o), hg (x b) (x o), hg (x b) (x a)]
  ring

/-- For the squared lengths of a placement, `gram2L` is the Gram determinant of the edge
vectors. -/
theorem gram2L_eq_g (hL : ∀ a b, a ≠ b → L {a, b} = g (x b - x a) (x b - x a)) (p q r : V) :
    gram2L L p q r = g (x q - x p) (x q - x p) * g (x r - x p) (x r - x p) -
      g (x q - x p) (x r - x p) ^ 2 := by
  rw [gram2L, ipL_eq_g hg x hL, ipL_eq_g hg x hL, ipL_eq_g hg x hL, ipL_eq_g hg x hL,
    hg (x r - x p) (x q - x p)]
  ring

/-- For the squared lengths of a placement with a non-null triangle `pqr`, `gram3L(pqrs)` is `G`
times the `g`-square of the component of `s - p` orthogonal to the triangle. -/
theorem gram3L_eq_g (hL : ∀ a b, a ≠ b → L {a, b} = g (x b - x a) (x b - x a)) {p q r : V}
    (h : gram2L L p q r ≠ 0) (s : V) :
    gram3L L p q r s = gram2L L p q r *
      g (perpL g (x q - x p) (x r - x p) (x s - x p))
        (perpL g (x q - x p) (x r - x p) (x s - x p)) := by
  have hG := h
  rw [gram2L_eq_g hg x hL] at hG
  rw [g_perpL_perpL hg hG, gram2L_eq_g hg x hL, mul_div_cancel₀ _ hG]
  simp only [gram3L, ipL_eq_g hg x hL]

/-- For the squared lengths of a placement with a non-null triangle `pqr`, the mixed determinant
is `G` times the `g`-inner product of the components of `s - p` and `u - p` orthogonal to the
triangle. -/
theorem mixedL_eq_g (hL : ∀ a b, a ≠ b → L {a, b} = g (x b - x a) (x b - x a)) {p q r : V}
    (h : gram2L L p q r ≠ 0) (s u : V) :
    mixedL L p q r s u = gram2L L p q r *
      g (perpL g (x q - x p) (x r - x p) (x s - x p))
        (perpL g (x q - x p) (x r - x p) (x u - x p)) := by
  have hG := h
  rw [gram2L_eq_g hg x hL] at hG
  rw [g_perpL_perpL hg hG, gram2L_eq_g hg x hL, mul_div_cancel₀ _ hG]
  simp only [mixedL, ipL_eq_g hg x hL]

/-- **At a spacelike triangle the length formula is Sorkin's angle** of the wedge spanned by the
components `P_s`, `P_u` of `s - p` and `u - p` orthogonal to the triangle. -/
theorem lorDihedral4_eq_of_pos (hL : ∀ a b, a ≠ b → L {a, b} = g (x b - x a) (x b - x a))
    {p q r : V} (h : 0 < gram2L L p q r) (s u : V) :
    lorDihedral4 L p q r s u =
      sorkinAngle
        (g (perpL g (x q - x p) (x r - x p) (x s - x p))
          (perpL g (x q - x p) (x r - x p) (x s - x p)))
        (g (perpL g (x q - x p) (x r - x p) (x u - x p))
          (perpL g (x q - x p) (x r - x p) (x u - x p)))
        (g (perpL g (x q - x p) (x r - x p) (x s - x p))
          (perpL g (x q - x p) (x r - x p) (x u - x p))) := by
  rw [lorDihedral4, ite_eq_left h, gram3L_eq_g hg x hL h.ne', gram3L_eq_g hg x hL h.ne',
    mixedL_eq_g hg x hL h.ne', sorkinAngle_mul h]

/-- **At a timelike triangle the length formula is the Euclidean angle** between the components
`P_s`, `P_u` of `s - p` and `u - p` orthogonal to the triangle: `arccos(g(P_s, P_u) /
√(g(P_s, P_s) g(P_u, P_u)))`. -/
theorem lorDihedral4_eq_of_neg (hL : ∀ a b, a ≠ b → L {a, b} = g (x b - x a) (x b - x a))
    {p q r : V} (h : gram2L L p q r < 0) (s u : V) :
    lorDihedral4 L p q r s u =
      ((arccos (g (perpL g (x q - x p) (x r - x p) (x s - x p))
          (perpL g (x q - x p) (x r - x p) (x u - x p)) /
        √(g (perpL g (x q - x p) (x r - x p) (x s - x p))
            (perpL g (x q - x p) (x r - x p) (x s - x p)) *
          g (perpL g (x q - x p) (x r - x p) (x u - x p))
            (perpL g (x q - x p) (x r - x p) (x u - x p)))) : ℝ) : ℂ) := by
  rw [lorDihedral4, ite_eq_right (not_lt.2 h.le), ite_eq_left h, gram3L_eq_g hg x hL h.ne,
    gram3L_eq_g hg x hL h.ne, mixedL_eq_g hg x hL h.ne]
  congr 2
  set G := gram2L L p q r
  generalize g (perpL g (x q - x p) (x r - x p) (x s - x p))
    (perpL g (x q - x p) (x r - x p) (x u - x p)) = Z
  generalize g (perpL g (x q - x p) (x r - x p) (x s - x p))
    (perpL g (x q - x p) (x r - x p) (x s - x p)) = X
  generalize g (perpL g (x q - x p) (x r - x p) (x u - x p))
    (perpL g (x q - x p) (x r - x p) (x u - x p)) = Y
  rw [show G * X * (G * Y) = G ^ 2 * (X * Y) by ring, Real.sqrt_mul (sq_nonneg G),
    Real.sqrt_sq_eq_abs, abs_of_neg h]
  by_cases hXY : √(X * Y) = 0
  · rw [hXY]; simp
  · field_simp
    exact mul_div_cancel_left₀ _ h.ne

end Bilin

end Lightlike.ReggeLor
