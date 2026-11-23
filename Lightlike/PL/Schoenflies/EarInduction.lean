import Mathlib
import Lightlike.PL.Schoenflies.TriMap
import Lightlike.PL.Schoenflies.Glue
import Lightlike.PL.Schoenflies.EarSplit
import Lightlike.PL.Schoenflies.ConvexSplit
import Lightlike.PL.Schoenflies.ScpRot
import Lightlike.PL.Schoenflies.DetColl

/-!
# The statement of the ear induction for the polygonal Schoenflies theorem

Piece 12 of the polygonal Schoenflies theorem (row G3-188, milestone PL5).  We fix the statement
`Spec p c f` that the induction on the number of vertices proves, and its base case, the triangle:

* `f` maps the closed region of the simple polygon `p` bijectively onto the convex hull of the
  vertices of `c`;
* `f` is affine on each edge, sending the edge `p i → p (i+1)` onto the edge `c i → c (i+1)`
  (`EdgeAff`); in particular `f (p i) = c i`;
* `f` is piecewise affine: finitely many triangles `Tri` cover the region and `f` agrees on each
  with the affine map `triMap` (`PiecewiseTri`).
-/

namespace Lightlike.PL.Schoenflies

open Set

/-- A triangle `a b c` of the source together with the target triangle `a' b' c'`. -/
structure Tri where
  /-- Source vertex `a`. -/
  a : ℝ × ℝ
  /-- Source vertex `b`. -/
  b : ℝ × ℝ
  /-- Source vertex `c`. -/
  c : ℝ × ℝ
  /-- Target vertex `a'`, the image of `a`. -/
  a' : ℝ × ℝ
  /-- Target vertex `b'`, the image of `b`. -/
  b' : ℝ × ℝ
  /-- Target vertex `c'`, the image of `c`. -/
  c' : ℝ × ℝ

/-- The source triangle of a `Tri`, as a convex hull. -/
def Tri.src (t : Tri) : Set (ℝ × ℝ) := convexHull ℝ {t.a, t.b, t.c}

/-- `f` is a nondegenerate affine map on the source triangle of `t`, given there by `triMap`. -/
def Tri.Good (f : ℝ × ℝ → ℝ × ℝ) (t : Tri) : Prop :=
  det3 t.a t.b t.c ≠ 0 ∧ det3 t.a' t.b' t.c' ≠ 0 ∧
    EqOn f (triMap t.a t.b t.c t.a' t.b' t.c') t.src

/-- `f` is piecewise affine on `R`: a finite list of nondegenerate triangles covers `R`, and `f` is
affine (equal to `triMap`) on each. -/
def PiecewiseTri (f : ℝ × ℝ → ℝ × ℝ) (R : Set (ℝ × ℝ)) : Prop :=
  ∃ L : List Tri, (∀ t ∈ L, t.Good f) ∧ R = ⋃ t ∈ L, t.src

/-- `f` is affine on every edge of `p` (read cyclically) and sends it onto the corresponding edge of
`c`; the parameter `t` runs over `[0,1]`. -/
def EdgeAff {n : ℕ} [NeZero n] (p c : Polygon n) (f : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∀ (i : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    f (p.cyc i + t • (p.cyc (i + 1) - p.cyc i)) = c.cyc i + t • (c.cyc (i + 1) - c.cyc i)

/-- **The induction statement.**  `f` maps the closed region of `p` bijectively onto the hull of the
vertices of `c`, edge by edge affinely, and is piecewise affine. -/
def Spec {n : ℕ} [NeZero n] (p c : Polygon n) (f : ℝ × ℝ → ℝ × ℝ) : Prop :=
  BijOn f (region p) (convexHull ℝ (range c)) ∧ EdgeAff p c f ∧ PiecewiseTri f (region p)

/-- The range of a triple. -/
lemma range_three (p : Polygon 3) : range p = {p 0, p 1, p 2} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- Cyclic vertices of a triple, by residue mod 3. -/
lemma cyc_three (p : Polygon 3) (i : ℕ) :
    p.cyc i = if i % 3 = 0 then p 0 else if i % 3 = 1 then p 1 else p 2 := by
  have h : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have : p.cyc i = p ⟨i % 3, h⟩ := rfl
  rw [this]
  have h3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases h3 with h3 | h3 | h3
  · simp [h3]
  · simp [h3]
  · simp [h3]

/-- **Base case of the ear induction: a triangle.** -/
theorem spec_triangle {p c : Polygon 3} (hs : p.IsSimple) (hc : StrictConvexPos c) :
    ∃ f, Spec p c f := by
  have hp := det3_ne_zero_of_isSimple hs
  have hc' : det3 (c 0) (c 1) (c 2) ≠ 0 := (hc 0 1 2 (by decide) (by decide)).ne'
  refine ⟨triMap (p 0) (p 1) (p 2) (c 0) (c 1) (c 2), ?_, ?_, ?_⟩
  · rw [region_triangle hs, range_three, range_three]
    exact triMap_bijOn hp hc'
  · intro i t _
    rw [triMap_affine, cyc_three p i, cyc_three p (i + 1), cyc_three c i, cyc_three c (i + 1)]
    have h3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h3 with h3 | h3 | h3
    · have : (i + 1) % 3 = 1 := by omega
      simp [h3, this, triMap_a, triMap_b hp]
    · have : (i + 1) % 3 = 2 := by omega
      simp [h3, this, triMap_b hp, triMap_c hp]
    · have : (i + 1) % 3 = 0 := by omega
      simp [h3, this, triMap_c hp, triMap_a]
  · refine ⟨[⟨p 0, p 1, p 2, c 0, c 1, c 2⟩], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨hp, hc', fun x _ => rfl⟩
    · rw [region_triangle hs, range_three]
      simp [Tri.src]

/-- Non-vacuity and a wrong-input check: for the standard triangle and the translated one the
statement is met by `triMap`, and the image of the vertex `p 1` is `c 1` rather than another vertex. -/
example : triMap (0, 0) (1, 0) (0, 1) (1, 1) (2, 1) (1, 2) (1, 0) = (2, 1) ∧
    triMap (0, 0) (1, 0) (0, 1) (1, 1) (2, 1) (1, 2) (1, 0) ≠ (1, 2) := by
  have h : det3 ((0 : ℝ), (0 : ℝ)) (1, 0) (0, 1) ≠ 0 := by simp [det3, cross]
  refine ⟨triMap_b h, ?_⟩
  rw [triMap_b h]
  intro h2
  have := congrArg Prod.fst h2
  norm_num at this

end Lightlike.PL.Schoenflies
