import Lightlike.Regge.Linear3.TorusComplex
import Lightlike.Regge.Conv3.ReggeConvergence

/-!
# The Regge action of the periodic Kuhn complex as a sum over edge classes and cells

For arbitrary edge lengths `ℓ` on the periodic Kuhn complex `torusComplex n` (`n ≥ 3`), the Regge action
`Σ_e ℓ_e δ_e` is the sum over the seven edge classes `k` and the cells `z` of
`ℓ(edge z k) · (2π - Σ_{(σ,h) in class k} θ)`, where the sum runs over the 36 incidences (tetrahedron `σ`,
hinge `h`) of the Kuhn star whose hinge has direction `k`, the dihedral angle taken in the tetrahedron
`(z - off σ (hP h), σ)` (`reggeAction_torus`). The pieces are:

* `edgeOf z k`, the edge from `z` in the direction `k`: the map `(z, k) ↦ edgeOf z k` is injective
  (`edgeOf_injective`) and onto the edges of the complex (`edges_torus`);
* `angleSum_gen`, `angleSum_edgeOf`: the angle sum at an edge as a sum over the incidences of its class;
* `dirsN`: the seven directions as vectors of natural numbers, equal to `Lightlike.Regge.Conv3.dirs`
  (`dirsN_cast`).

This file is purely combinatorial: it holds for every length assignment, and does not use any geometry.

## Main results

* `reggeAction_torus`: the Regge action of the periodic complex as a sum over classes and cells.
* `edgeOf_injective`, `edges_torus`: the edges of the complex are the pairs (cell, class).

**Limits.** The periodic Kuhn complex of `(ℤ/n)³` only, `n ≥ 3`; the comparison with the lattice sum of
`reggeAction3` for the geodesic lengths of a periodic metric is `TorusBridgeLengths.lean`.
-/

open Real Finset
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3
open Lightlike.PR (Complex3)

variable (n : ℕ) [NeZero n]

/-- The seven edge directions as vectors of natural numbers. -/
def dirsN : Fin 7 → Fin 3 → ℕ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1]]

theorem dirsN_le (k : Fin 7) (i : Fin 3) : dirsN k i ≤ 1 := by
  fin_cases k <;> fin_cases i <;> simp [dirsN]

theorem dirsN_ne (k : Fin 7) : ∃ i, dirsN k i ≠ 0 := by
  fin_cases k <;> simp [dirsN] <;> decide

theorem dirsN_cast (k : Fin 7) (i : Fin 3) : ((dirsN k i : ℕ) : ℝ) = dirs k i := by
  fin_cases k <;> fin_cases i <;> simp [dirsN, dirs]

theorem dirsN_inj : Function.Injective dirsN := by
  intro a b h
  have h' := fun i => congrFun h i
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; have := h' 0; have := h' 1; have := h' 2; simp_all [dirsN]; done)

theorem dirsN_surj (w : Fin 3 → ℕ) (hw1 : ∀ i, w i ≤ 1) (hw0 : ∃ i, w i ≠ 0) : ∃ k, dirsN k = w := by
  have h0 := hw1 0; have h1 := hw1 1; have h2 := hw1 2
  obtain ⟨i, hi⟩ := hw0
  have e0 : w 0 = 0 ∨ w 0 = 1 := by omega
  have e1 : w 1 = 0 ∨ w 1 = 1 := by omega
  have e2 : w 2 = 0 ∨ w 2 = 1 := by omega
  rcases e0 with e0 | e0 <;> rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
  · exfalso; fin_cases i <;> simp_all
  · exact ⟨2, by funext j; fin_cases j <;> simp [dirsN, e0, e1, e2]⟩
  · exact ⟨1, by funext j; fin_cases j <;> simp [dirsN, e0, e1, e2]⟩
  · exact ⟨5, by funext j; fin_cases j <;> simp [dirsN, e0, e1, e2]⟩
  · exact ⟨0, by funext j; fin_cases j <;> simp [dirsN, e0, e1, e2]⟩
  · exact ⟨4, by funext j; fin_cases j <;> simp [dirsN, e0, e1, e2]⟩
  · exact ⟨3, by funext j; fin_cases j <;> simp [dirsN, e0, e1, e2]⟩
  · exact ⟨6, by funext j; fin_cases j <;> simp [dirsN, e0, e1, e2]⟩


/-- The edge of the periodic complex from the cube vertex `z` in the direction class `k`. -/
def edgeOf (z : TV n) (k : Fin 7) : Finset (TV n) := {z, z + wv n (dirsN k)}

/-- The sum of the dihedral angles at an edge of the periodic complex, for arbitrary lengths, is the sum
over the pairs (cube, tetrahedron) and hinges that realise the edge. -/
theorem angleSum_gen (hn : 3 ≤ n) (ℓ : Finset (TV n) → ℝ) (e : Finset (TV n)) (he : e.card = 2) :
    angleSum (torusComplex n (by omega)) ℓ e =
      ∑ p : TV n × Fin 6, ∑ h : Fin 6,
        if e = hing n p.1 p.2 h then dihedralAt ℓ (tetV n p.1 p.2) (hing n p.1 p.2 h) else 0 := by
  unfold angleSum
  rw [star_sum n hn]
  refine sum_congr rfl fun p _ => ?_
  by_cases hs : e ⊆ tetV n p.1 p.2
  · obtain ⟨h0, rfl⟩ := (subset_tetV_iff n (by omega) p.1 p.2 he).1 hs
    rw [ite_eq_left hs, sum_eq_single h0]
    · simp
    · intro h _ hh
      rw [ite_eq_right]
      exact fun e' => hh (hing_inj n (by omega) p.1 p.2 e').symm
    · simp
  · rw [ite_eq_right hs]
    symm
    refine sum_eq_zero fun h _ => ?_
    rw [ite_eq_right]
    intro e'
    exact hs ((subset_tetV_iff n (by omega) p.1 p.2 he).2 ⟨h, e'⟩)

/-- **The angle sum at the edge of class `k` at `z`:** the 36 incidences of the Kuhn star, sorted by the
class of the hinge, with the cube `z - off σ (hP h)`. -/
theorem angleSum_edgeOf (hn : 3 ≤ n) (ℓ : Finset (TV n) → ℝ) (z : TV n) (k : Fin 7) :
    angleSum (torusComplex n (by omega)) ℓ (edgeOf n z k) =
      ∑ σ : Fin 6, ∑ h : Fin 6, if Cond (dirsN k) σ h then
        dihedralAt ℓ (tetV n (z - off n σ (hP h)) σ) (hing n (z - off n σ (hP h)) σ h) else 0 := by
  have hw1 := dirsN_le k
  have hw0 := dirsN_ne k
  have hcard : (edgeOf n z k).card = 2 := by
    unfold edgeOf
    rw [card_pair]; intro h; apply wv_ne_zero n (by omega) hw1 hw0; simpa using h
  rw [angleSum_gen n hn ℓ _ hcard, Fintype.sum_prod_type]
  have hiff := fun c σ h => hing_eq_iff n hn hw1 hw0 z c σ h
  simp only [edgeOf, hiff]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  by_cases hc : Cond (dirsN k) σ h
  · simp only [hc, true_and, ite_true]
    rw [sum_eq_single (z - off n σ (hP h))]
    · simp
    · intro c _ hne; simp [hne]
    · simp
  · simp [hc]


theorem wv_injective (hn : 2 ≤ n) {w w' : Fin 3 → ℕ} (hw : ∀ i, w i ≤ 1) (hw' : ∀ i, w' i ≤ 1)
    (h : wv n w = wv n w') : w = w' := by
  funext i
  exact natCast_inj01 n (hw i) (hw' i) hn (congrFun h i)

theorem wv_add_ne_zero (hn : 3 ≤ n) {w w' : Fin 3 → ℕ} (hw : ∀ i, w i ≤ 1) (hw' : ∀ i, w' i ≤ 1)
    (hw0 : ∃ i, w i ≠ 0) : wv n w + wv n w' ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := hw0
  have h1 := congrFun h i
  simp only [wv, Pi.add_apply, Pi.zero_apply] at h1
  have h2 : (((w i + w' i : ℕ)) : ZMod n) = ((0 : ℕ) : ZMod n) := by push_cast; simpa using h1
  have := natCast_inj2 n (by have := hw i; have := hw' i; omega) (by omega) hn h2
  omega

theorem edgeOf_injective (hn : 3 ≤ n) : Function.Injective fun p : TV n × Fin 7 => edgeOf n p.1 p.2 := by
  rintro ⟨z, k⟩ ⟨z', k'⟩ h
  have h : edgeOf n z k = edgeOf n z' k' := h
  have hk := dirsN_le k
  have hk0 := dirsN_ne k
  have hk' := dirsN_le k'
  have hk0' := dirsN_ne k'
  have ha := wv_ne_zero n (by omega) hk hk0
  have hb := wv_ne_zero n (by omega) hk' hk0'
  have m1 : z ∈ edgeOf n z' k' := by rw [← h]; simp [edgeOf]
  have m2 : z + wv n (dirsN k) ∈ edgeOf n z' k' := by rw [← h]; simp [edgeOf]
  have m3 : z' ∈ edgeOf n z k := by rw [h]; simp [edgeOf]
  have m4 : z' + wv n (dirsN k') ∈ edgeOf n z k := by rw [h]; simp [edgeOf]
  simp only [edgeOf, mem_insert, mem_singleton] at m1 m2 m3 m4
  rcases m1 with m1 | m1
  · subst m1
    rcases m2 with m2 | m2
    · exact absurd (by simpa using m2) ha
    · have := add_left_cancel m2
      have := wv_injective n (by omega) hk hk' this
      have := dirsN_inj this
      subst this; rfl
  · exfalso
    subst m1
    rcases m2 with m2 | m2
    · apply wv_add_ne_zero n hn hk' hk hk0'
      have : z' + (wv n (dirsN k') + wv n (dirsN k)) = z' + 0 := by rw [← add_assoc, add_zero]; exact m2
      exact add_left_cancel this
    · apply ha
      have : z' + wv n (dirsN k') + wv n (dirsN k) = z' + wv n (dirsN k') + 0 := by rw [add_zero]; exact m2
      exact add_left_cancel this


theorem class_nonempty : ∀ k : Fin 7, ∃ σ h : Fin 6, Cond (dirsN k) σ h := by
  unfold Cond; decide

theorem edges_torus (hn : 3 ≤ n) :
    (torusComplex n (by omega)).edges = univ.image fun p : TV n × Fin 7 => edgeOf n p.1 p.2 := by
  ext e
  rw [Complex3.mem_edges]
  simp only [mem_image, mem_univ, true_and, Prod.exists]
  constructor
  · intro hmem
    obtain ⟨t, ht, hse, h2⟩ := hmem
    have := edge_form n hn (Complex3.mem_edges.2 ⟨t, ht, hse, h2⟩)
    obtain ⟨z, w, hw1, hw0, rfl⟩ := this
    obtain ⟨k, rfl⟩ := dirsN_surj w hw1 hw0
    exact ⟨z, k, rfl⟩
  · rintro ⟨z, k, rfl⟩
    obtain ⟨σ, h, hc⟩ := class_nonempty k
    have hw1 := dirsN_le k
    have hw0 := dirsN_ne k
    have hcard : (edgeOf n z k).card = 2 := by
      unfold edgeOf
      rw [card_pair]; intro h; apply wv_ne_zero n (by omega) hw1 hw0; simpa using h
    have hing : edgeOf n z k = hing n (z - off n σ (hP h)) σ h :=
      (hing_eq_iff n hn hw1 hw0 z _ σ h).2 ⟨hc, rfl⟩
    refine ⟨tetV n (z - off n σ (hP h)) σ, ?_, ?_, hcard⟩
    · exact mem_image.2 ⟨(z - off n σ (hP h), σ), mem_univ _, rfl⟩
    · exact (subset_tetV_iff n (by omega) _ σ hcard).2 ⟨h, hing⟩

/-- **The Regge action of the periodic complex as a sum over classes and cells.** For arbitrary edge lengths
`ℓ`, `S = Σ_k Σ_z ℓ(edge z k) (2π - Σ over the class-`k` incidences of the dihedral angle)`. -/
theorem reggeAction_torus (hn : 3 ≤ n) (ℓ : Finset (TV n) → ℝ) :
    reggeAction (torusComplex n (by omega)) ℓ =
      ∑ k : Fin 7, ∑ z : TV n, ℓ (edgeOf n z k) * (2 * π - ∑ σ : Fin 6, ∑ h : Fin 6,
        if Cond (dirsN k) σ h then
          dihedralAt ℓ (tetV n (z - off n σ (hP h)) σ) (hing n (z - off n σ (hP h)) σ h) else 0) := by
  rw [reggeAction_of_bdryTris_eq_empty (bdryTris_torus n hn), edges_torus n hn,
    sum_image (fun a _ b _ h => edgeOf_injective n hn h), Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun k _ => sum_congr rfl fun z _ => ?_
  rw [deficit, angleSum_edgeOf n hn]

end Lightlike.Regge.Linear3
