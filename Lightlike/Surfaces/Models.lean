import Lightlike.Surfaces.Pieces

/-!
# The standard surfaces

`model P j` is the boundary of the tetrahedron `0123` with `j` copies of the piece `P` attached
one after the other: the piece number `j` is glued along its triangle `{0, 1, 2}` to the triangle
`site j` of the previous complex, its other labels `n` becoming `10 (j + 1) + n`, and `site (j + 1)`
is the image of the piece's triangle `{1, 3, 4}`.

The **standard models** are `stdModel true g = model T9 g` (the orientable surface of genus `g`)
and `stdModel false k = model P6 (k + 1)` (the non-orientable surface with `k + 1` cross-caps).

* `euler2_model`: `χ(model P j) = 2 + j (χ(P) − 2)`.
* `isOrientable_model_T9`, `not_isOrientable_model_P6`: the orientable and non-orientable ones.
* `stdModel_inj`: **the standard models are pairwise inequivalent** under 2D bistellar moves.
-/

open Finset

namespace Lightlike.Surfaces

open Lightlike.PR

/-! ## Gluing sites -/

/-- The triangle of the standard model to which the next piece is glued. -/
def site : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 1, 2)
  | j + 1 => ((site j).2.1, 10 * (j + 1) + 3, 10 * (j + 1) + 4)

lemma site_spec (j : ℕ) : (site j).1 < 10 * (j + 1) ∧ (site j).2.1 < 10 * (j + 1) ∧
    (site j).2.2 < 10 * (j + 1) ∧ (site j).1 ≠ (site j).2.1 ∧ (site j).1 ≠ (site j).2.2 ∧
    (site j).2.1 ≠ (site j).2.2 := by
  induction j with
  | zero => simp [site]
  | succ j ih =>
    simp only [site]
    omega

/-- The labels of the piece number `j`: `0, 1, 2` go to `site j`, the others `n` to
`10 (j + 1) + n`. -/
def glFun (j n : ℕ) : ℕ :=
  if n = 0 then (site j).1 else if n = 1 then (site j).2.1 else if n = 2 then (site j).2.2
    else 10 * (j + 1) + n

lemma glFun_injective (j : ℕ) : Function.Injective (glFun j) := by
  have := site_spec j
  intro a b h
  simp only [glFun] at h
  split_ifs at h <;> omega

/-- The embedding placing the piece number `j`. -/
def gl (j : ℕ) : ℕ ↪ ℕ := ⟨glFun j, glFun_injective j⟩

/-- The vertex set of a triple. -/
def triOf (s : ℕ × ℕ × ℕ) : Finset ℕ := {s.1, s.2.1, s.2.2}

/-! ## The models -/

/-- The boundary of the tetrahedron with `j` copies of the piece `P` attached in a chain. -/
def model (P : Finset (Finset ℕ)) : ℕ → Finset (Finset ℕ)
  | 0 => bdry 0 1 2 3
  | j + 1 => csum (model P j) (triOf (site j)) P {0, 1, 2} (gl j)

/-- The conditions on a piece used to build the models. -/
structure IsPiece (P : Finset (Finset ℕ)) : Prop where
  closed : IsClosed2 P
  tri : IsTri2 P
  mem₀ : ({0, 1, 2} : Finset ℕ) ∈ P
  mem₁ : ({1, 3, 4} : Finset ℕ) ∈ P
  lt : ∀ t ∈ P, ∀ x ∈ t, x < 10

theorem isPiece_P6 : IsPiece P6 :=
  ⟨isClosed2_P6, isTri2_P6, by decide, by decide, fun t ht x hx => by
    have := P6_lt t ht x hx; omega⟩

theorem isPiece_T9 : IsPiece T9 :=
  ⟨isClosed2_T9, isTri2_T9, by decide, by decide, fun t ht x hx => by have := T9_lt t ht x hx; omega⟩

lemma triOf_site_map (j : ℕ) : ({0, 1, 2} : Finset ℕ).map (gl j) = triOf (site j) := by
  simp [gl, glFun, triOf]

lemma triOf_site_succ (j : ℕ) : ({1, 3, 4} : Finset ℕ).map (gl j) = triOf (site (j + 1)) := by
  simp [gl, glFun, triOf, site]

/-- **The basic facts about the models**, proven together by induction: closed, made of
triangles, labels below `10 (j + 1)`, and the gluing site is a triangle. -/
theorem model_spec {P : Finset (Finset ℕ)} (hP : IsPiece P) (j : ℕ) :
    IsClosed2 (model P j) ∧ IsTri2 (model P j) ∧ (∀ x ∈ verts2 (model P j), x < 10 * (j + 1)) ∧
      triOf (site j) ∈ model P j := by
  induction j with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact closed_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [model]; unfold IsTri2; decide
    · simp only [model]; decide
    · simp only [model, triOf, site]; decide
  | succ j ih =>
    obtain ⟨hc, ht, hlt, hs⟩ := ih
    have hg : IsGlue (model P j) (triOf (site j)) P {0, 1, 2} (gl j) := by
      refine ⟨hs, hP.mem₀, triOf_site_map j, fun n hn hn0 hv => ?_⟩
      have := hlt _ hv
      simp only [gl, Function.Embedding.coeFn_mk, glFun] at this
      simp only [mem_insert, mem_singleton, not_or] at hn0
      simp only [hn0.1, hn0.2.1, hn0.2.2, ite_false] at this
      omega
    refine ⟨isClosed2_csum hc hP.closed hP.tri hg, isTri2_csum ht hP.tri, fun x hx => ?_, ?_⟩
    · rw [model, verts2_csum hc ht hP.closed hP.tri hg, mem_union] at hx
      rcases hx with hx | hx
      · have := hlt x hx; omega
      · obtain ⟨n, hn, rfl⟩ := mem_map.mp hx
        obtain ⟨t, htP, hnt⟩ := mem_verts2.mp hn
        have hn10 := hP.lt t htP n hnt
        have := site_spec j
        simp only [gl, Function.Embedding.coeFn_mk, glFun]
        split_ifs <;> omega
    · rw [model, ← triOf_site_succ]
      refine mem_union_right _ (mem_liftK.mpr ⟨_, mem_erase.mpr ⟨by decide, hP.mem₁⟩, rfl⟩)

lemma isGlue_model {P : Finset (Finset ℕ)} (hP : IsPiece P) (j : ℕ) :
    IsGlue (model P j) (triOf (site j)) P {0, 1, 2} (gl j) := by
  obtain ⟨-, -, hlt, hs⟩ := model_spec hP j
  refine ⟨hs, hP.mem₀, triOf_site_map j, fun n hn hn0 hv => ?_⟩
  have := hlt _ hv
  simp only [gl, Function.Embedding.coeFn_mk, glFun] at this
  simp only [mem_insert, mem_singleton, not_or] at hn0
  simp only [hn0.1, hn0.2.1, hn0.2.2, ite_false] at this
  omega

/-- **The Euler characteristic of the models**: `χ(model P j) = 2 + j (χ(P) − 2)`. -/
theorem euler2_model {P : Finset (Finset ℕ)} (hP : IsPiece P) (j : ℕ) :
    euler2 (model P j) = 2 + j * (euler2 P - 2) := by
  induction j with
  | zero =>
    simp only [model, CharP.cast_eq_zero, zero_mul, add_zero]
    exact euler2_bdry (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  | succ j ih =>
    obtain ⟨hc, ht, -, -⟩ := model_spec hP j
    rw [model, euler2_csum hc ht hP.closed hP.tri (isGlue_model hP j), ih]
    push_cast
    ring

/-! ## Orientability of the models -/

/-- The boundary of the tetrahedron `0123`, oriented outwards. -/
def bdryOr : List (ℕ × ℕ × ℕ) := [(0, 2, 1), (0, 1, 3), (0, 3, 2), (1, 2, 3)]

/-- **The boundary of the tetrahedron is orientable**: the outward orientation. -/
theorem isOrientation_bdry : IsOrientation (bdry 0 1 2 3) (olist bdryOr) :=
  isOrientation_olist (N := 4) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- **The models built from the torus `T9` are orientable.** -/
theorem isOrientable_model_T9 (j : ℕ) : IsOrientable (model T9 j) := by
  induction j with
  | zero => exact ⟨_, isOrientation_bdry⟩
  | succ j ih =>
    obtain ⟨hc, ht, -, -⟩ := model_spec isPiece_T9 j
    exact isOrientable_csum hc ht isClosed2_T9 isTri2_T9 (isGlue_model isPiece_T9 j) ih
      isOrientable_T9

/-- **The models with at least one projective plane `P6` are not orientable.** -/
theorem not_isOrientable_model_P6 (j : ℕ) : ¬ IsOrientable (model P6 (j + 1)) :=
  not_isOrientable_csum_P6 (isGlue_model isPiece_P6 j)

/-! ## The standard models -/

/-- The **standard models**: `stdModel true g` is the orientable surface of genus `g` (the
tetrahedron boundary with `g` tori attached), and `stdModel false k` the non-orientable surface
with `k + 1` cross-caps (the tetrahedron boundary with `k + 1` projective planes attached). -/
def stdModel : Bool → ℕ → Finset (Finset ℕ)
  | true, g => model T9 g
  | false, k => model P6 (k + 1)

/-- The Euler characteristic of the orientable models: `χ = 2 − 2g`. -/
theorem euler2_stdModel_true (g : ℕ) : euler2 (stdModel true g) = 2 - 2 * g := by
  rw [stdModel, euler2_model isPiece_T9, euler2_T9]
  ring

/-- The Euler characteristic of the non-orientable models: `χ = 1 − k`. -/
theorem euler2_stdModel_false (k : ℕ) : euler2 (stdModel false k) = 1 - k := by
  rw [stdModel, euler2_model isPiece_P6, euler2_P6]
  push_cast
  ring

/-- **The standard model `stdModel b n` is orientable exactly when `b` is `true`.** -/
theorem isOrientable_stdModel (b : Bool) (n : ℕ) : IsOrientable (stdModel b n) ↔ b = true := by
  cases b
  · simpa [stdModel] using not_isOrientable_model_P6 n
  · simpa [stdModel] using isOrientable_model_T9 n

/-- **The standard models are pairwise inequivalent**: if two of them are related by 2D
bistellar moves, they are the same model. The orientability and the Euler characteristic are
invariants of the moves. -/
theorem stdModel_inj {b b' : Bool} {n n' : ℕ}
    (h : Relation.EqvGen Move2 (stdModel b n) (stdModel b' n')) : b = b' ∧ n = n' := by
  have ho := isOrientable_iff_of_eqvGen h
  have he := euler2_eq_of_eqvGen h
  rw [isOrientable_stdModel, isOrientable_stdModel] at ho
  cases b <;> cases b'
  · rw [euler2_stdModel_false, euler2_stdModel_false] at he
    exact ⟨rfl, by omega⟩
  · simp at ho
  · simp at ho
  · rw [euler2_stdModel_true, euler2_stdModel_true] at he
    exact ⟨rfl, by omega⟩

end Lightlike.Surfaces
