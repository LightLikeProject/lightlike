import Lightlike.Regge.D4.Manifold
import Lightlike.Regge.FlatSolution

/-!
# Triangulations of a region of 4-space have zero deficit angles

The 4D counterpart of `Lightlike/Regge/Embedded.lean`: in a 4-dimensional Euclidean space, if the
4-simplices around an interior triangle are non-degenerate and their interiors are pairwise
disjoint, the deficit angle of the triangle is zero.

## Definitions

* `open4 p q r s u`: the points with five positive barycentric coordinates; for a non-degenerate
  4-simplex in a 4-dimensional space this is the interior of its convex hull
  (`open4_eq_interior`).
* `IsGeometric4 K x`: the placement `x` of the vertices is a geometric triangulation: every
  4-simplex is non-degenerate and distinct 4-simplices have disjoint interiors.

## Main results

* `deficit4_eq_zero_of_embedded`: let `E` be a real inner product space of dimension 4 and `x` a
  placement with the induced edge lengths. Let the link of the triangle `abc` be a cycle
  (`IsCycleLink4`), each 4-simplex `{a, b, c, w i, w (i+1)}` around it non-degenerate, and their
  interiors pairwise disjoint. Then the deficit angle at `abc` is zero.
* `IsGeometric4.deficit4_eq_zero`: every interior triangle of a geometric triangulation of a
  region of 4-space has deficit angle zero; `IsGeometric4.reggeAction4_eq`: the Regge action is
  then a pure boundary term.

## Proof

The dihedral angle at `abc` is measured in the plane orthogonal to the triangle
(`dihedral4_dist`). Choose an orthonormal basis `e₂, e₃` of that plane (`exists_planeFrame`) and
write the component of each link vertex in polar coordinates `ρ (cos α e₂ + sin α e₃)`. The
dihedral angle of the 4-simplex `i` is the angle between the directions `α i` and `α (i+1)`.
Points just off the centroid of the triangle in a direction strictly inside that angle lie inside
the 4-simplex (`mem_open4_near`). So disjoint interiors make the wedges between consecutive
directions disjoint, and the planar theorem `Lightlike.Regge.sum_arccos_cos_eq_two_pi` gives `2π`.
-/

open Real Finset InnerProductGeometry InnerProductSpace Module Matrix

namespace Lightlike.Regge4

open Lightlike.FourD (Complex4)
open Lightlike.Regge (InWedge sum_arccos_cos_eq_two_pi angle_planeDir_eq_arccos ofDist ofDist_pair)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Local geometry -/

/-- The open 4-simplex with vertices `p q r s u`: the points `Σ cᵢ Pᵢ` with all five barycentric
coordinates `cᵢ` positive. -/
def open4 (p q r s u : E) : Set E :=
  {y | ∃ c₀ c₁ c₂ c₃ c₄ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧
    c₀ + c₁ + c₂ + c₃ + c₄ = 1 ∧ y = c₀ • p + c₁ • q + c₂ • r + c₃ • s + c₄ • u}

/-- **Points just off the centroid of a triangle lie inside the 4-simplex.** Write
`r = a + ζ (b - a) + η (c - a) + u` and `s = a + ζ' (b - a) + η' (c - a) + u'`. For `l, m > 0` and
all small `ε > 0`, the point `a + ⅓ (b - a) + ⅓ (c - a) + ε (l u + m u')` lies in the open
4-simplex `abcrs`. -/
theorem mem_open4_near {a b c r s u u' : E} {ζ η ζ' η' l m : ℝ}
    (hr : r = a + ζ • (b - a) + η • (c - a) + u) (hs : s = a + ζ' • (b - a) + η' • (c - a) + u')
    (hl : 0 < l) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      a + (1 / 3 : ℝ) • (b - a) + (1 / 3 : ℝ) • (c - a) + ε • (l • u + m • u') ∈
        open4 a b c r s := by
  set X := l * ζ + m * ζ'
  set Y := l * η + m * η'
  have hM : 0 < 3 * (|X| + |Y| + l + m + 1) := by
    linarith [abs_nonneg X, abs_nonneg Y]
  refine ⟨1 / (3 * (|X| + |Y| + l + m + 1)), div_pos one_pos hM, fun ε hε hεδ => ?_⟩
  rw [lt_div_iff₀ hM] at hεδ
  have hX1 : ε * X ≤ ε * |X| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
  have hX2 : ε * (-|X|) ≤ ε * X := mul_le_mul_of_nonneg_left (neg_abs_le _) hε.le
  have hY1 : ε * Y ≤ ε * |Y| := mul_le_mul_of_nonneg_left (le_abs_self _) hε.le
  have hY2 : ε * (-|Y|) ≤ ε * Y := mul_le_mul_of_nonneg_left (neg_abs_le _) hε.le
  have hl' : 0 < ε * l := mul_pos hε hl
  have hm' : 0 < ε * m := mul_pos hε hm
  refine ⟨1 / 3 + ε * (X + Y - l - m), 1 / 3 - ε * X, 1 / 3 - ε * Y, ε * l, ε * m,
    by nlinarith, by nlinarith, by nlinarith, hl', hm', by ring, ?_⟩
  rw [hr, hs]
  simp only [X, Y]
  module

/-- The Gram determinant of two linearly independent vectors is positive. -/
theorem gram_two_pos {A B : E} (h : LinearIndependent ℝ ![A, B]) :
    0 < ⟪A, A⟫_ℝ * ⟪B, B⟫_ℝ - ⟪A, B⟫_ℝ ^ 2 := by
  have := (posDef_gram_of_linearIndependent h).det_pos
  rw [det_fin_two] at this
  simp only [gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, real_inner_comm A B] at this
  nlinarith

/-- **An orthonormal frame of the normal plane.** In a 4-dimensional real inner product space, for
linearly independent `A, B` there are orthonormal `e₂, e₃` spanning the orthogonal complement of
`A, B`. -/
theorem exists_planeFrame [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4) {A B : E}
    (h : LinearIndependent ℝ ![A, B]) :
    ∃ e₂ e₃ : E, ‖e₂‖ = 1 ∧ ‖e₃‖ = 1 ∧ ⟪e₂, e₃⟫_ℝ = 0 ∧
      ∀ y ∈ (Submodule.span ℝ {A, B})ᗮ, y = ⟪y, e₂⟫_ℝ • e₂ + ⟪y, e₃⟫_ℝ • e₃ := by
  have hS : finrank ℝ (Submodule.span ℝ ({A, B} : Set E)) = 2 := by
    have := finrank_span_eq_card h
    have hr : Set.range ![A, B] = ({A, B} : Set E) := by
      ext y
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [hr] at this
    simpa using this
  have hW : finrank ℝ (Submodule.span ℝ ({A, B} : Set E))ᗮ = 2 := by
    have := (Submodule.span ℝ ({A, B} : Set E)).finrank_add_finrank_orthogonal
    omega
  let OB := (stdOrthonormalBasis ℝ (Submodule.span ℝ ({A, B} : Set E))ᗮ).reindex (finCongr hW)
  refine ⟨(OB 0 : E), (OB 1 : E), ?_, ?_, ?_, ?_⟩
  · rw [Submodule.norm_coe]
    exact OB.orthonormal.1 0
  · rw [Submodule.norm_coe]
    exact OB.orthonormal.1 1
  · rw [← Submodule.coe_inner]
    exact OB.orthonormal.2 (by decide : (0 : Fin 2) ≠ 1)
  · intro y hy
    have h1 := congrArg Subtype.val (OB.sum_repr' ⟨y, hy⟩)
    rw [Fin.sum_univ_two] at h1
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_inner] at h1
    rw [real_inner_comm y (OB 0 : E), real_inner_comm y (OB 1 : E)] at h1
    exact h1.symm

/-- **Polar coordinates in the normal plane.** If `y = ⟪y, e₂⟫ e₂ + ⟪y, e₃⟫ e₃`, then
`y = ρ (cos α e₂ + sin α e₃)` with `ρ, α` the modulus and argument of `⟪y, e₂⟫ + i ⟪y, e₃⟫`. -/
theorem polar_repr {e₂ e₃ y : E} (hy : y = ⟪y, e₂⟫_ℝ • e₂ + ⟪y, e₃⟫_ℝ • e₃) :
    y = ‖(⟨⟪y, e₂⟫_ℝ, ⟪y, e₃⟫_ℝ⟩ : ℂ)‖ •
      (cos (Complex.arg ⟨⟪y, e₂⟫_ℝ, ⟪y, e₃⟫_ℝ⟩) • e₂ +
        sin (Complex.arg ⟨⟪y, e₂⟫_ℝ, ⟪y, e₃⟫_ℝ⟩) • e₃) := by
  have h1 : ‖(⟨⟪y, e₂⟫_ℝ, ⟪y, e₃⟫_ℝ⟩ : ℂ)‖ * cos (Complex.arg ⟨⟪y, e₂⟫_ℝ, ⟪y, e₃⟫_ℝ⟩) =
      ⟪y, e₂⟫_ℝ := Complex.norm_mul_cos_arg _
  have h2 : ‖(⟨⟪y, e₂⟫_ℝ, ⟪y, e₃⟫_ℝ⟩ : ℂ)‖ * sin (Complex.arg ⟨⟪y, e₂⟫_ℝ, ⟪y, e₃⟫_ℝ⟩) =
      ⟪y, e₃⟫_ℝ := Complex.norm_mul_sin_arg _
  rw [smul_add, smul_smul, smul_smul, h1, h2]
  exact hy

/-- **Non-degenerate 4-simplices in polar coordinates.** If the edge vectors `A`, `B`,
`v = ζ A + η B + ρ (cos α e₂ + sin α e₃)`, `v' = ζ' A + η' B + ρ' (cos α' e₂ + sin α' e₃)` are
linearly independent, then `ρ ≠ 0`, `ρ' ≠ 0` and `sin (α' - α) ≠ 0` (the two tetrahedra at the
triangle do not lie in one hyperplane). -/
theorem polar_nondeg {A B v v' e₂ e₃ : E} {ζ η ρ α ζ' η' ρ' α' : ℝ}
    (hv : v = ζ • A + η • B + ρ • (cos α • e₂ + sin α • e₃))
    (hv' : v' = ζ' • A + η' • B + ρ' • (cos α' • e₂ + sin α' • e₃))
    (hli : LinearIndependent ℝ ![A, B, v, v']) : ρ ≠ 0 ∧ ρ' ≠ 0 ∧ sin (α' - α) ≠ 0 := by
  have key := Fintype.linearIndependent_iff.mp hli
  have hρ : ρ ≠ 0 := by
    intro h0
    have := key ![ζ, η, -1, 0] (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [hv, h0]
      module) 2
    simp at this
  have hρ' : ρ' ≠ 0 := by
    intro h0
    have := key ![ζ', η', 0, -1] (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [hv', h0]
      module) 3
    simp at this
  refine ⟨hρ, hρ', fun hsin => ?_⟩
  have hc' : cos α' = cos α * cos (α' - α) := by
    rw [show α' = α + (α' - α) by ring, cos_add, show α + (α' - α) - α = α' - α by ring, hsin]
    ring
  have hs' : sin α' = sin α * cos (α' - α) := by
    rw [show α' = α + (α' - α) by ring, sin_add, show α + (α' - α) - α = α' - α by ring, hsin]
    ring
  have := key ![ρ' * cos (α' - α) * ζ - ρ * ζ', ρ' * cos (α' - α) * η - ρ * η',
    -(ρ' * cos (α' - α)), ρ] (by
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hv, hv', hc', hs']
    module) 3
  simp only [Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at this
  exact hρ this

variable {V : Type*} [DecidableEq V]

/-- **Triangulations of a region of 4-space have zero deficit.** Let `E` be a real inner product
space of dimension 4 and `x` a placement of the vertices of `K` in `E`, with the induced edge
lengths. Suppose the link of the triangle `abc` is a cycle `w 0, …, w (n-1)` (`IsCycleLink4`),
each 4-simplex `{a, b, c, w i, w (i+1)}` around it is non-degenerate (its edge vectors from `a` are
linearly independent), and the interiors of these 4-simplices are pairwise disjoint. Then the
deficit angle at `abc` is zero. -/
theorem deficit4_eq_zero_of_embedded [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4)
    (K : Complex4 V) (x : V → E) {a b c : V} {n : ℕ} {w : ℕ → V}
    (hc : IsCycleLink4 K a b c n w)
    (hnd : ∀ i < n, LinearIndependent ℝ
      ![x b - x a, x c - x a, x (w i) - x a, x (w (i + 1)) - x a])
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (open4 (x a) (x b) (x c) (x (w i)) (x (w (i + 1))))
        (open4 (x a) (x b) (x c) (x (w j)) (x (w (j + 1))))) :
    deficit4 K (ofDist fun u v => dist (x u) (x v)) {a, b, c} = 0 := by
  have h3 := hc.three_le
  have hn : 0 < n := by omega
  have hℓ : ∀ u v, u ≠ v → ofDist (fun u v => dist (x u) (x v)) {u, v} = dist (x u) (x v) :=
    fun u v h => ofDist_pair (d := fun u v => dist (x u) (x v)) (fun u => dist_self (x u))
      (fun u v => dist_comm (x u) (x v)) h
  have hAB : LinearIndependent ℝ ![x b - x a, x c - x a] := by
    have := (hnd 0 hn).comp ![0, 1] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  have hGpos := gram_two_pos hAB
  have hG : gram2 (ofDist fun u v => dist (x u) (x v)) a b c ≠ 0 := by
    rw [gram2_eq_inner x hℓ]
    exact hGpos.ne'
  obtain ⟨e₂, e₃, he₂, he₃, he₂₃, hexp⟩ := exists_planeFrame hE hAB
  -- polar coordinates of the normal components of the link vertices
  set P : ℕ → E := fun k => perp2 (x b - x a) (x c - x a) (x (w k) - x a) with hP
  have hPmem : ∀ k, P k ∈ (Submodule.span ℝ {x b - x a, x c - x a})ᗮ := fun k =>
    perp2_mem_orthogonal hGpos.ne' _
  set ρ : ℕ → ℝ := fun k => ‖(⟨⟪P k, e₂⟫_ℝ, ⟪P k, e₃⟫_ℝ⟩ : ℂ)‖ with hρ_def
  set α : ℕ → ℝ := fun k => Complex.arg ⟨⟪P k, e₂⟫_ℝ, ⟪P k, e₃⟫_ℝ⟩ with hα_def
  have hPpol : ∀ k, P k = ρ k • (cos (α k) • e₂ + sin (α k) • e₃) := fun k =>
    polar_repr (hexp _ (hPmem k))
  choose ζ η hζη using fun k =>
    Submodule.mem_span_pair.mp (sub_perp2_mem_span (a := x b - x a) (b := x c - x a)
      (x (w k) - x a))
  have hdec : ∀ k, x (w k) - x a =
      ζ k • (x b - x a) + η k • (x c - x a) + ρ k • (cos (α k) • e₂ + sin (α k) • e₃) := by
    intro k
    rw [hζη k, ← hPpol k]
    simp only [hP]
    abel
  have hρn : ρ n = ρ 0 := by simp only [hρ_def, hP, hc.closed]
  have hαn : α n = α 0 := by simp only [hα_def, hP, hc.closed]
  have hnd' := fun i hi => polar_nondeg (hdec i) (hdec (i + 1)) (hnd i hi)
  have hρpos : ∀ i ≤ n, 0 < ρ i := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact lt_of_le_of_ne (norm_nonneg _) (hnd' i h).1.symm
    · rw [h, hρn]
      exact lt_of_le_of_ne (norm_nonneg _) (hnd' 0 hn).1.symm
  -- disjoint interiors make the wedges between consecutive directions disjoint
  have hW : ∀ i < n, ∀ j < n, i ≠ j → ∀ τ, InWedge (α i) (α (i + 1)) τ →
      ¬ InWedge (α j) (α (j + 1)) τ := by
    intro i hi j hj hij τ h1 h2
    obtain ⟨l, m, hl, hm, hcl, hsl⟩ := h1
    obtain ⟨l', m', hl', hm', hcl', hsl'⟩ := h2
    have hr : ∀ k, x (w k) = x a + ζ k • (x b - x a) + η k • (x c - x a) +
        ρ k • (cos (α k) • e₂ + sin (α k) • e₃) := by
      intro k
      rw [add_assoc, add_assoc, ← add_assoc (ζ k • _), ← hdec k]
      abel
    obtain ⟨δ₁, hδ₁, H₁⟩ := mem_open4_near (hr i) (hr (i + 1))
      (div_pos hl (hρpos i hi.le)) (div_pos hm (hρpos (i + 1) hi))
    obtain ⟨δ₂, hδ₂, H₂⟩ := mem_open4_near (hr j) (hr (j + 1))
      (div_pos hl' (hρpos j hj.le)) (div_pos hm' (hρpos (j + 1) hj))
    have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
    have hε : 0 < min δ₁ δ₂ / 2 := half_pos hmin
    have P₁ := H₁ (min δ₁ δ₂ / 2) hε (by linarith [min_le_left δ₁ δ₂])
    have P₂ := H₂ (min δ₁ δ₂ / 2) hε (by linarith [min_le_right δ₁ δ₂])
    have dir : ∀ (k : ℕ) (l m : ℝ), 0 < ρ k → 0 < ρ (k + 1) →
        (l / ρ k) • (ρ k • (cos (α k) • e₂ + sin (α k) • e₃)) +
          (m / ρ (k + 1)) • (ρ (k + 1) • (cos (α (k + 1)) • e₂ + sin (α (k + 1)) • e₃)) =
        (l * cos (α k) + m * cos (α (k + 1))) • e₂ + (l * sin (α k) + m * sin (α (k + 1))) • e₃ :=
      by
      intro k l m h h'
      rw [smul_smul, smul_smul, div_mul_cancel₀ _ h.ne', div_mul_cancel₀ _ h'.ne']
      module
    rw [dir i l m (hρpos i hi.le) (hρpos (i + 1) hi), ← hcl, ← hsl] at P₁
    rw [dir j l' m' (hρpos j hj.le) (hρpos (j + 1) hj), ← hcl', ← hsl'] at P₂
    exact Set.disjoint_left.mp (hdisj i hi j hj hij) P₁ P₂
  -- the dihedral angles around `abc` add up to `2π`
  have hsum := sum_arccos_cos_eq_two_pi hn α (fun i hi => (hnd' i hi).2.2)
    ⟨by rw [hαn], by rw [hαn]⟩ hW
  have hterm : ∀ i ∈ range n,
      dihedralAt4 (ofDist fun u v => dist (x u) (x v)) {a, b, c, w i, w (i + 1)} {a, b, c} =
        arccos (cos (α (i + 1) - α i)) := by
    intro i hi
    have hi' := mem_range.mp hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi'
    rw [dihedralAt4_eq _ hc.ne_ab hc.ne_ac h₁ h₂ hc.ne_bc h₃ h₄ h₅ h₆ h₇,
      dihedral4_dist x hℓ hG (w i) (w (i + 1))]
    change angle (P i) (P (i + 1)) = _
    rw [hPpol i, hPpol (i + 1), angle_smul_left_of_pos _ _ (hρpos i hi'.le),
      angle_smul_right_of_pos _ _ (hρpos (i + 1) hi'), angle_planeDir_eq_arccos he₂ he₃ he₂₃]
  rw [deficit4, hc.angleSum4_eq, sum_congr rfl hterm, hsum, sub_self]

/-! ## Geometric triangulations -/

/-- **The open 4-simplex is the interior.** For five affinely independent points of a
4-dimensional real inner product space, `open4` (the points with positive barycentric coordinates)
is the topological interior of their convex hull. -/
theorem open4_eq_interior [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4) {p q r s u : E}
    (h : AffineIndependent ℝ ![p, q, r, s, u]) :
    open4 p q r s u = interior (convexHull ℝ {p, q, r, s, u}) := by
  have hspan : affineSpan ℝ (Set.range ![p, q, r, s, u]) = ⊤ :=
    h.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [hE])
  let b : AffineBasis (Fin 5) ℝ E := AffineBasis.mk _ h hspan
  have hb : ⇑b = ![p, q, r, s, u] := rfl
  have hrange : Set.range ![p, q, r, s, u] = ({p, q, r, s, u} : Set E) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
  rw [← hrange, ← hb, b.interior_convexHull]
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c₀, c₁, c₂, c₃, c₄, h₀, h₁, h₂, h₃, h₄, hsum, rfl⟩ i
    have hw : (Finset.univ : Finset (Fin 5)).sum ![c₀, c₁, c₂, c₃, c₄] = 1 := by
      simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
        Matrix.tail_cons]
      linarith
    have key := b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, hb] at key
    simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at key
    rw [key]
    fin_cases i <;> simpa
  · intro hy
    refine ⟨b.coord 0 y, b.coord 1 y, b.coord 2 y, b.coord 3 y, b.coord 4 y, hy 0, hy 1, hy 2,
      hy 3, hy 4, ?_, ?_⟩
    · have := b.sum_coord_apply_eq_one y
      rw [Fin.sum_univ_five] at this
      exact this
    · have := b.affineCombination_coord_eq_self y
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (b.sum_coord_apply_eq_one y), hb,
        Fin.sum_univ_five] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at this
      exact this.symm

/-- The five labelled points of a 4-simplex are affinely independent iff the four edge vectors
from the first are linearly independent. -/
theorem affIndep_five_iff (P₀ P₁ P₂ P₃ P₄ : E) :
    AffineIndependent ℝ ![P₀, P₁, P₂, P₃, P₄] ↔
      LinearIndependent ℝ ![P₁ - P₀, P₂ - P₀, P₃ - P₀, P₄ - P₀] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 5),
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 5))]
  have : ((fun i : {x : Fin 5 // x ≠ 0} => ![P₀, P₁, P₂, P₃, P₄] ↑i -ᵥ ![P₀, P₁, P₂, P₃, P₄] 0) ∘
      finSuccAboveEquiv (0 : Fin 5)) = ![P₁ - P₀, P₂ - P₀, P₃ - P₀, P₄ - P₀] := by
    ext i
    fin_cases i <;> simp [finSuccAboveEquiv, vsub_eq_sub]
  rw [this]

/-- Affine independence of the vertex set of a 4-simplex gives affine independence of the five
points in any labelling. -/
theorem affIndep_five_of_subtype (x : V → E) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u)
    (h : AffineIndependent ℝ fun v : ({p, q, r, s, u} : Finset V) => x v) :
    AffineIndependent ℝ ![x p, x q, x r, x s, x u] := by
  let f : Fin 5 → ({p, q, r, s, u} : Finset V) :=
    ![⟨p, by simp⟩, ⟨q, by simp⟩, ⟨r, by simp⟩, ⟨s, by simp⟩, ⟨u, by simp⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, Subtype.ext_iff, hpq.symm, hpr.symm, hps.symm, hpu.symm, hqr.symm, hqs.symm,
        hqu.symm, hrs.symm, hru.symm, hsu.symm]
  have := h.comp_embedding ⟨f, hf⟩
  convert this using 1
  ext i
  fin_cases i <;> rfl

/-- Affine independence of the vertex set of a 4-simplex gives linear independence of the edge
vectors in any labelling. -/
theorem linIndep_of_affIndep5 (x : V → E) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u)
    (h : AffineIndependent ℝ fun v : ({p, q, r, s, u} : Finset V) => x v) :
    LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p, x u - x p] :=
  (affIndep_five_iff _ _ _ _ _).mp
    (affIndep_five_of_subtype x hpq hpr hps hpu hqr hqs hqu hrs hru hsu h)

/-- Conversely, linear independence of the edge vectors of one labelling gives affine independence
of the vertex set of a 4-simplex. -/
theorem affIndep_of_linIndep5 (x : V → E) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r)
    (hps : p ≠ s) (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s)
    (hru : r ≠ u) (hsu : s ≠ u)
    (h : LinearIndependent ℝ ![x q - x p, x r - x p, x s - x p, x u - x p]) :
    AffineIndependent ℝ fun v : ({p, q, r, s, u} : Finset V) => x v := by
  have h5 := (affIndep_five_iff _ _ _ _ _).mpr h
  have hinj := h5.injective
  have hrange : Set.range (fun v : ({p, q, r, s, u} : Finset V) => x v) =
      Set.range ![x p, x q, x r, x s, x u] := by
    ext y
    simp only [Set.mem_range, Subtype.exists, mem_insert, mem_singleton]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rcases hv with rfl | rfl | rfl | rfl | rfl
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i
      exacts [⟨p, by simp, rfl⟩, ⟨q, by simp, rfl⟩, ⟨r, by simp, rfl⟩, ⟨s, by simp, rfl⟩,
        ⟨u, by simp, rfl⟩]
  refine AffineIndependent.of_set_of_injective ?_ ?_
  · rw [hrange]
    exact h5.range
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only at hab
    simp only [mem_insert, mem_singleton] at ha hb
    have ne : ∀ i j : Fin 5, i ≠ j →
        ![x p, x q, x r, x s, x u] i ≠ ![x p, x q, x r, x s, x u] j :=
      fun i j h => hinj.ne h
    have key : ∀ i j : Fin 5, ![x p, x q, x r, x s, x u] i = ![x p, x q, x r, x s, x u] j →
        i = j := fun i j h => by_contra fun hij => ne i j hij h
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first
      | rfl
      | exact absurd (key 0 1 hab) (by decide)
      | exact absurd (key 0 2 hab) (by decide)
      | exact absurd (key 0 3 hab) (by decide)
      | exact absurd (key 0 4 hab) (by decide)
      | exact absurd (key 1 0 hab) (by decide)
      | exact absurd (key 1 2 hab) (by decide)
      | exact absurd (key 1 3 hab) (by decide)
      | exact absurd (key 1 4 hab) (by decide)
      | exact absurd (key 2 0 hab) (by decide)
      | exact absurd (key 2 1 hab) (by decide)
      | exact absurd (key 2 3 hab) (by decide)
      | exact absurd (key 2 4 hab) (by decide)
      | exact absurd (key 3 0 hab) (by decide)
      | exact absurd (key 3 1 hab) (by decide)
      | exact absurd (key 3 2 hab) (by decide)
      | exact absurd (key 3 4 hab) (by decide)
      | exact absurd (key 4 0 hab) (by decide)
      | exact absurd (key 4 1 hab) (by decide)
      | exact absurd (key 4 2 hab) (by decide)
      | exact absurd (key 4 3 hab) (by decide)

/-- The open simplex of the vertex set `{p, q, r, s, u}` is the open 4-simplex of the
labelling. -/
theorem openHull_eq_open4 (x : V → E) {p q r s u : V} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hpu : p ≠ u) (hqr : q ≠ r) (hqs : q ≠ s) (hqu : q ≠ u) (hrs : r ≠ s) (hru : r ≠ u)
    (hsu : s ≠ u) :
    Lightlike.Regge.openHull x {p, q, r, s, u} = open4 (x p) (x q) (x r) (x s) (x u) := by
  have e₁ : p ∉ ({q, r, s, u} : Finset V) := by simp [hpq, hpr, hps, hpu]
  have e₂ : q ∉ ({r, s, u} : Finset V) := by simp [hqr, hqs, hqu]
  have e₃ : r ∉ ({s, u} : Finset V) := by simp [hrs, hru]
  have e₄ : s ∉ ({u} : Finset V) := by simp [hsu]
  ext y
  constructor
  · rintro ⟨c, hc, hsum, rfl⟩
    rw [sum_insert e₁, sum_insert e₂, sum_insert e₃, sum_insert e₄, sum_singleton] at hsum ⊢
    exact ⟨c p, c q, c r, c s, c u, hc p (by simp), hc q (by simp), hc r (by simp),
      hc s (by simp), hc u (by simp), by linarith, by abel⟩
  · rintro ⟨c₀, c₁, c₂, c₃, c₄, h₀, h₁, h₂, h₃, h₄, hsum, rfl⟩
    refine ⟨fun v => if v = p then c₀ else if v = q then c₁ else if v = r then c₂ else
      if v = s then c₃ else c₄, ?_, ?_, ?_⟩
    · intro v hv
      simp only [mem_insert, mem_singleton] at hv
      have := hpq.symm; have := hpr.symm; have := hps.symm; have := hpu.symm
      have := hqr.symm; have := hqs.symm; have := hqu.symm; have := hrs.symm
      have := hru.symm; have := hsu.symm
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp_all
    · rw [sum_insert e₁, sum_insert e₂, sum_insert e₃, sum_insert e₄, sum_singleton]
      simp [hpq.symm, hpr.symm, hps.symm, hpu.symm, hqr.symm, hqs.symm, hqu.symm, hrs.symm,
        hru.symm, hsu.symm]
      linarith
    · rw [sum_insert e₁, sum_insert e₂, sum_insert e₃, sum_insert e₄, sum_singleton]
      simp [hpq.symm, hpr.symm, hps.symm, hpu.symm, hqr.symm, hqs.symm, hqu.symm, hrs.symm,
        hru.symm, hsu.symm, add_assoc]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The image of a vertex set `{p, q, r, s, u}` under a placement. -/
theorem image_five (x : V → E) (p q r s u : V) :
    x '' ↑({p, q, r, s, u} : Finset V) = ({x p, x q, x r, x s, x u} : Set E) := by
  simp [Set.image_insert_eq]

/-- **The open simplex of a 4-simplex is the interior of its convex hull**, for a non-degenerate
4-simplex placed in a 4-dimensional real inner product space. -/
theorem openHull_eq_interior4 [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4) (x : V → E)
    {σ : Finset V} (hσ : #σ = 5) (h : AffineIndependent ℝ fun v : σ => x v) :
    Lightlike.Regge.openHull x σ = interior (convexHull ℝ (x '' ↑σ)) := by
  obtain ⟨p, t', hp, rfl, h4⟩ := card_eq_succ.mp hσ
  obtain ⟨q, r, s, u, hqr, hqs, hqu, hrs, hru, hsu, rfl⟩ := card_eq_four.mp h4
  simp only [mem_insert, mem_singleton, not_or] at hp
  obtain ⟨hpq, hpr, hps, hpu⟩ := hp
  rw [openHull_eq_open4 x hpq hpr hps hpu hqr hqs hqu hrs hru hsu, image_five,
    open4_eq_interior hE (affIndep_five_of_subtype x hpq hpr hps hpu hqr hqs hqu hrs hru hsu h)]

/-- A placement `x` of the vertices of `K` in `E` is a **geometric triangulation** (of the region
covered by its 4-simplices): every 4-simplex is non-degenerate (its five vertices are affinely
independent), and distinct 4-simplices have disjoint interiors, the topological interiors of their
convex hulls. -/
structure IsGeometric4 (K : Complex4 V) (x : V → E) : Prop where
  /-- Every 4-simplex is non-degenerate. -/
  nondeg : ∀ σ ∈ K.simps, AffineIndependent ℝ fun v : σ => x v
  /-- Distinct 4-simplices have disjoint interiors. -/
  disjoint : ∀ σ ∈ K.simps, ∀ σ' ∈ K.simps, σ ≠ σ' →
    Disjoint (interior (convexHull ℝ (x '' ↑σ))) (interior (convexHull ℝ (x '' ↑σ')))

/-- **In a geometric triangulation of a region of 4-space, a triangle whose link is a cycle has
zero deficit.** -/
theorem IsGeometric4.deficit4_eq_zero_of_cycleLink [FiniteDimensional ℝ E]
    (hE : finrank ℝ E = 4) {K : Complex4 V} {x : V → E} (hK : IsGeometric4 K x) {a b c : V}
    {n : ℕ} {w : ℕ → V} (hc : IsCycleLink4 K a b c n w) :
    deficit4 K (ofDist fun u v => dist (x u) (x v)) {a, b, c} = 0 := by
  apply deficit4_eq_zero_of_embedded hE K x hc
  · intro i hi
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi
    exact linIndep_of_affIndep5 x hc.ne_ab hc.ne_ac h₁ h₂ hc.ne_bc h₃ h₄ h₅ h₆ h₇
      (hK.nondeg _ (hc.simp_mem hi))
  · intro i hi j hj hij
    have hne : ({a, b, c, w i, w (i + 1)} : Finset V) ≠ {a, b, c, w j, w (j + 1)} := fun h =>
      hij (hc.injOn_simp (by simpa using hi) (by simpa using hj) h)
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hc.simp_distinct hi
    obtain ⟨k₁, k₂, k₃, k₄, k₅, k₆, k₇⟩ := hc.simp_distinct hj
    have hd := hK.disjoint _ (hc.simp_mem hi) _ (hc.simp_mem hj) hne
    rw [← openHull_eq_interior4 hE x (K.card_eq _ (hc.simp_mem hi))
        (hK.nondeg _ (hc.simp_mem hi)),
      ← openHull_eq_interior4 hE x (K.card_eq _ (hc.simp_mem hj))
        (hK.nondeg _ (hc.simp_mem hj)),
      openHull_eq_open4 x hc.ne_ab hc.ne_ac h₁ h₂ hc.ne_bc h₃ h₄ h₅ h₆ h₇,
      openHull_eq_open4 x hc.ne_ab hc.ne_ac k₁ k₂ hc.ne_bc k₃ k₄ k₅ k₆ k₇] at hd
    exact hd

/-- **Flat space has zero curvature: every interior triangle of a geometric triangulation of a
region of 4-space has deficit angle zero.** Here `K` satisfies the manifold condition at triangles
and is placed in a 4-dimensional real inner product space by a geometric triangulation `x`, with
the induced edge lengths. -/
theorem IsGeometric4.deficit4_eq_zero [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4)
    {K : Complex4 V} {x : V → E} (hK : IsGeometric4 K x) (hM : IsTriManifold K)
    {t : Finset V} (ht : t ∈ intTris4 K) :
    deficit4 K (ofDist fun u v => dist (x u) (x v)) t = 0 := by
  obtain ⟨a, b, c, n, w, rfl, hc⟩ := hM.mem_intTris4_iff.mp ht
  exact hK.deficit4_eq_zero_of_cycleLink hE hc

/-- **The Regge action of a flat region of 4-space is a pure boundary term**:
`S = Σ_{boundary triangles} A_t (π - Σ θ)`. -/
theorem IsGeometric4.reggeAction4_eq [FiniteDimensional ℝ E] (hE : finrank ℝ E = 4)
    {K : Complex4 V} {x : V → E} (hK : IsGeometric4 K x) (hM : IsTriManifold K) :
    reggeAction4 K (ofDist fun u v => dist (x u) (x v)) =
      ∑ t ∈ bdryTris4 K, area4 (ofDist fun u v => dist (x u) (x v)) t *
        bdryAngle4 K (ofDist fun u v => dist (x u) (x v)) t := by
  rw [reggeAction4, sum_eq_zero fun t ht => by rw [hK.deficit4_eq_zero hE hM ht, mul_zero],
    zero_add]

end Lightlike.Regge4
