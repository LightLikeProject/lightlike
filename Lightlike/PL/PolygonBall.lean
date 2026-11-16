import Lightlike.PL.PolygonEars
import Lightlike.PL.Attach
import Lightlike.PL.PolygonTriangulation

/-!
# The triangulated region of a simple polygon is a PL ball

By induction on the number of vertices, clipping an ear. Besides the triangulation, the induction
carries the fact that every edge of the polygon lies in exactly one triangle; this is what lets
the ear be attached as a stellar equivalence (`SComplex.stellarEquivIn_closure_insert`).

## Main results

* `Lightlike.PL.Polygon.exists_ball_triangulation`
-/

open Set Finset

namespace Lightlike.PL
namespace Polygon

variable {n : ℕ}

/-- Every edge of `q` lies in exactly one triangle of `T`. -/
def EdgeUnique (q : Polygon n) (T : Finset (Finset (ℝ × ℝ))) : Prop :=
  ∀ i, ∃ x, ({q i, q (finRotate n i), x} : Finset (ℝ × ℝ)) ∈ T ∧
    ∀ t ∈ T, q i ∈ t → q (finRotate n i) ∈ t → t = {q i, q (finRotate n i), x}

/-- The vertex set of a triangle polygon. -/
lemma image_triangle (q : Polygon 3) :
    (Finset.univ.image q : Finset (ℝ × ℝ)) = {q 0, q 1, q 2} := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- The triangulation of a triangle by itself. -/
theorem isTriangulation_triangle' {q : Polygon 3} (hs : q.IsSimple) :
    IsTriangulation q {({q 0, q 1, q 2} : Finset (ℝ × ℝ))} ∧
      EdgeUnique q {({q 0, q 1, q 2} : Finset (ℝ × ℝ))} := by
  have hT := isTriangulation_triangle hs
  rw [image_triangle] at hT
  refine ⟨hT, fun i => ?_⟩
  have e : ({q i, q (finRotate 3 i), q (finRotate 3 (finRotate 3 i))} : Finset (ℝ × ℝ)) =
      {q 0, q 1, q 2} := by
    have e0 : finRotate 3 0 = 1 := by decide
    have e1 : finRotate 3 1 = 2 := by decide
    have e2 : finRotate 3 2 = 0 := by decide
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, e0, e1, e2] <;>
      ext y <;> simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto
  refine ⟨q (finRotate 3 (finRotate 3 i)), ?_, ?_⟩
  · rw [e]; exact Finset.mem_singleton_self _
  · intro t ht _ _
    rw [e]; exact Finset.mem_singleton.1 ht

variable {q : Polygon n} [NeZero n]

lemma edgeUnique_of_rot (a : Fin n) {T : Finset (Finset (ℝ × ℝ))} (h : EdgeUnique (q.rot a) T) :
    EdgeUnique q T := by
  intro i
  obtain ⟨x, hx, hu⟩ := h (i - a)
  have e1 : (q.rot a) (i - a) = q i := by simp [rot]
  have e2 : (q.rot a) (finRotate n (i - a)) = q (finRotate n i) := by
    simp only [rot]
    congr 1
    rw [← finRotate_add]; simp
  rw [e1, e2] at hx hu
  exact ⟨x, hx, hu⟩

/-- Cyclic reading of vertices is injective below `n`. -/
lemma cyc_inj (hs : q.IsSimple) {j k : ℕ} (hj : j < n) (hk : k < n) (h : q.cyc j = q.cyc k) :
    j = k := by
  rw [q.cyc_of_lt hj, q.cyc_of_lt hk] at h
  exact Fin.mk.inj (vertex_injective hs h)

/-- **Clipping an ear preserves the ball.** If the polygon has an ear at `0` and the polygon with
the ear removed has a ball triangulation, so does the polygon. -/
theorem ball_step (hs : q.IsSimple) (h4 : 4 ≤ n) (hear : q.Ear 0)
    (hIH : ∀ P : Polygon (n - 2 + 1), P.IsSimple → ∃ T, IsTriangulation P T ∧ EdgeUnique P T ∧
      SComplex.IsBallIn (SComplex.closure T)) :
    ∃ T, IsTriangulation q T ∧ EdgeUnique q T ∧ SComplex.IsBallIn (SComplex.closure T) := by
  have hn2 : 2 ≤ n := by omega
  have hD : openSegment ℝ (q.cyc 0) (q.cyc 2) ⊆ q.inside := by
    simpa [Ear] using hear
  have hopen : ∀ x ∈ openSegment ℝ (q.cyc 0) (q.cyc 2), x ∉ q.carrier := fun x hx hxc =>
    (hD hx).1 hxc
  obtain ⟨hdis, hspl⟩ := inside_split hs (b := 2) le_rfl (by omega) hD
  have hsR := isSimple_right hs (b := 2) le_rfl (by omega) hopen
  have hsL := isSimple_left hs (b := 2) le_rfl (by omega) hopen
  obtain ⟨T_R, hTR, hUR, hBR⟩ := hIH (q.right 2) hsR
  obtain ⟨hTL, hUL⟩ := isTriangulation_triangle' (q := q.left 2) hsL
  have hT : IsTriangulation q ({({(q.left 2) 0, (q.left 2) 1, (q.left 2) 2} : Finset (ℝ × ℝ))} ∪ T_R) :=
    isTriangulation_union hs le_rfl (by omega) hdis hspl hTL hTR
  have hSeq : ({(q.left 2) 0, (q.left 2) 1, (q.left 2) 2} : Finset (ℝ × ℝ)) =
      {q.cyc 0, q.cyc 1, q.cyc 2} := rfl
  rw [hSeq] at hT
  set S : Finset (ℝ × ℝ) := {q.cyc 0, q.cyc 1, q.cyc 2} with hS
  -- the vertex `1` is not a vertex of the clipped polygon
  have hnotin : ∀ t ∈ T_R, q.cyc 1 ∉ t := by
    intro t ht hc
    obtain ⟨j, hj⟩ := (hTR.1 t ht).2 hc
    have hj' : q.cyc (2 + (j : ℕ)) = q.cyc 1 := hj
    have hjlt : (j : ℕ) < n - 2 + 1 := j.2
    rcases Nat.lt_or_ge (2 + (j : ℕ)) n with h | h
    · have := cyc_inj hs h (by omega) hj'
      omega
    · have e : 2 + (j : ℕ) = n + 0 := by omega
      rw [e, q.cyc_self_add 0] at hj'
      have := cyc_inj hs (by omega : 0 < n) (by omega : 1 < n) hj'
      omega
  have hUq : EdgeUnique q ({S} ∪ T_R) := by
    intro i
    have hi := i.2
    by_cases hi0 : (i : ℕ) = 0
    · have hqi : q i = q.cyc 0 := by rw [fin_eq_cyc (q := q) i, hi0]
      have hqf : q (finRotate n i) = q.cyc 1 := by rw [finRotate_eq_cyc (q := q) hn2 i, hi0]
      refine ⟨q.cyc 2, ?_, ?_⟩
      · rw [hqi, hqf]; exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
      · intro t ht h1 h2
        rw [hqi, hqf]
        rw [hqf] at h2
        rcases Finset.mem_union.1 ht with ht | ht
        · rw [Finset.mem_singleton] at ht; rw [ht]
        · exact absurd h2 (hnotin t ht)
    by_cases hi1 : (i : ℕ) = 1
    · have hqi : q i = q.cyc 1 := by rw [fin_eq_cyc (q := q) i, hi1]
      have hqf : q (finRotate n i) = q.cyc 2 := by rw [finRotate_eq_cyc (q := q) hn2 i, hi1]
      refine ⟨q.cyc 0, ?_, ?_⟩
      · rw [hqi, hqf]
        refine Finset.mem_union_left _ ?_
        rw [Finset.mem_singleton, hS]
        ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      · intro t ht h1 h2
        rw [hqi] at h1
        rcases Finset.mem_union.1 ht with ht | ht
        · rw [Finset.mem_singleton] at ht
          rw [ht, hqi, hqf, hS]
          ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        · exact absurd h1 (hnotin t ht)
    have hi2 : 2 ≤ (i : ℕ) := by omega
    obtain ⟨x, hx, hu⟩ := hUR ⟨(i : ℕ) - 2, by omega⟩
    have e1 : (q.right 2) ⟨(i : ℕ) - 2, by omega⟩ = q i := by
      show q.cyc (2 + ((i : ℕ) - 2)) = _
      rw [fin_eq_cyc (q := q) i, Nat.add_sub_cancel' hi2]
    have e2 : (q.right 2) (finRotate (n - 2 + 1) ⟨(i : ℕ) - 2, by omega⟩) =
        q (finRotate n i) := by
      show q.cyc (2 + ((finRotate (n - 2 + 1) ⟨(i : ℕ) - 2, by omega⟩ : Fin (n - 2 + 1)) : ℕ)) = _
      rw [finRotate_val (by omega), finRotate_eq_cyc (q := q) hn2 i]
      simp only
      rw [Nat.mod_eq_of_lt (by omega)]
      congr 1; omega
    rw [e1, e2] at hx hu
    refine ⟨x, Finset.mem_union_right _ hx, ?_⟩
    intro t ht h1 h2
    rcases Finset.mem_union.1 ht with ht | ht
    · exfalso
      rw [Finset.mem_singleton] at ht
      rw [ht, hS, fin_eq_cyc (q := q) i] at h1
      rw [ht, hS, finRotate_eq_cyc (q := q) hn2 i] at h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
      rcases h1 with h | h | h
      · have := cyc_inj hs hi (by omega) h; omega
      · have := cyc_inj hs hi (by omega) h; omega
      · have h2' := cyc_inj hs hi (by omega) h
        rcases h2 with h' | h' | h'
        · have := cyc_inj hs (by omega) (by omega) h'; omega
        · have := cyc_inj hs (by omega) (by omega) h'; omega
        · have := cyc_inj hs (by omega) (by omega) h'; omega
    · exact hu t ht h1 h2
  have hBq : SComplex.IsBallIn (SComplex.closure ({S} ∪ T_R)) := by
    obtain ⟨x, hx, hu⟩ := hUR ⟨n - 2, by omega⟩
    have e1 : (q.right 2) ⟨n - 2, by omega⟩ = q.cyc 0 := by
      show q.cyc (2 + (n - 2)) = _
      have : 2 + (n - 2) = n + 0 := by omega
      rw [this, q.cyc_self_add 0]
    have e2 : (q.right 2) (finRotate (n - 2 + 1) ⟨n - 2, by omega⟩) = q.cyc 2 := by
      show q.cyc (2 + ((finRotate (n - 2 + 1) ⟨n - 2, by omega⟩ : Fin (n - 2 + 1)) : ℕ)) = _
      rw [finRotate_val (by omega)]
      simp only
      rw [Nat.mod_self]
    rw [e1, e2] at hx hu
    have hc3 := (hTR.1 _ hx).1
    have hxu : x ≠ q.cyc 0 := by
      intro h
      rw [h] at hc3
      have : ({q.cyc 0, q.cyc 2, q.cyc 0} : Finset (ℝ × ℝ)).card ≤ 2 := by
        have : ({q.cyc 0, q.cyc 2, q.cyc 0} : Finset (ℝ × ℝ)) = {q.cyc 0, q.cyc 2} := by
          ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [this]; exact Finset.card_le_two
      omega
    have hxw : x ≠ q.cyc 2 := by
      intro h
      rw [h] at hc3
      have : ({q.cyc 0, q.cyc 2, q.cyc 2} : Finset (ℝ × ℝ)).card ≤ 2 := by
        have : ({q.cyc 0, q.cyc 2, q.cyc 2} : Finset (ℝ × ℝ)) = {q.cyc 0, q.cyc 2} := by
          ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [this]; exact Finset.card_le_two
      omega
    have huw : q.cyc 0 ≠ q.cyc 2 := fun h => by
      have := cyc_inj hs (by omega : 0 < n) (by omega : 2 < n) h; omega
    have hatt := SComplex.stellarEquivIn_closure_insert (T := T_R) (u := q.cyc 0) (w := q.cyc 2)
      (x := x) (v := q.cyc 1) huw hxu hxw hx hnotin hu
    have hins : ({S} ∪ T_R : Finset (Finset (ℝ × ℝ))) = insert S T_R := by
      rw [Finset.insert_eq]
    rw [hins, hS]
    exact SComplex.IsBallIn.of_stellarEquivIn hBR hatt
  exact ⟨_, hT, hUq, hBq⟩

/-- **A simple polygon has a triangulation by its own vertices whose complex is a PL ball.** -/
theorem exists_ball_triangulation : ∀ (n : ℕ) [NeZero n] (p : Polygon n), 3 ≤ n → p.IsSimple →
    ∃ T, IsTriangulation p T ∧ EdgeUnique p T ∧ SComplex.IsBallIn (SComplex.closure T) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro _ p hn hs
    rcases (by omega : n = 3 ∨ 4 ≤ n) with rfl | h4
    · obtain ⟨h1, h2⟩ := isTriangulation_triangle' hs
      refine ⟨_, h1, h2, ?_⟩
      rw [SComplex.closure_singleton]
      exact SComplex.isBallIn_simplex ⟨p 0, by simp⟩
    · obtain ⟨k₁, k₂, hk1, hk2, e1, e2, -, -⟩ := two_ears n p h4 hs
      set a : Fin n := ⟨k₁, hk1⟩ with ha
      have hsq := isSimple_rot hs a
      have hear : (p.rot a).Ear 0 := (ear_rot p a 0).2 (by simpa [ha] using e1)
      obtain ⟨T, hT, hU, hB⟩ := ball_step hsq h4 hear
        (fun P hP => ih (n - 2 + 1) (by omega) P (by omega) hP)
      exact ⟨T, isTriangulation_of_rot a hT, edgeUnique_of_rot a hU, hB⟩

end Polygon

end Lightlike.PL
