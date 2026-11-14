module

public import Lightlike.PonzanoRegge.Unconditional

/-!
# Odd perimeters: the rounding in the triangle weight is never seen

The triangle weight `triSign` and `triW` use the natural-number division
`(j_uv + j_vw + j_wu) / 2` of doubled spins. For an odd perimeter this rounds down, which is not
a physical value. This file proves that the rounding never matters.

* `sixJSym_eq_zero_of_odd`: a 6j symbol vanishes if one of its four triads has an odd
  perimeter (doubled units). Proof: every summand contains a 3j symbol, and a 3j symbol is zero
  unless the perimeter of its triad is even (the last field of Physlib's `Adm3`). Physlib has no
  such lemma (`sixJSym_eq_zero_of_lt` covers the triangle inequality only).
* `tetAmp_eq_zero_of_odd`: `tetAmp col p = 0` if one of the four faces of `p` has an odd
  doubled perimeter.
* `tetW_eq_zero_of_odd`: the same for `tetW`, for a tetrahedron with a face `f` of odd perimeter.
* `weightWith_eq_weight`, `amplitudeWith_eq_amplitude`: replace the triangle weight `triW` by any
  function `g` that agrees with it on triangles of even perimeter; the weight and the cut-off
  amplitude do not change. So `triSign` (and `triW`) may take any value on odd-perimeter
  triangles. Every triangle of a `Complex3` lies in a tetrahedron, whose 6j symbol then vanishes.

Trust checks are in `Lightlike/Tests/PonzanoRegge.lean` (`weightWith_example`,
`weightWith_wrong_model`).
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- **A 6j symbol with an odd triad perimeter vanishes** (doubled spins). The four triads are
`(j₁ j₂ j₃)`, `(j₁ j₅ j₆)`, `(j₄ j₂ j₆)`, `(j₄ j₅ j₃)`. -/
lemma sixJSym_eq_zero_of_odd {j₁ j₂ j₃ j₄ j₅ j₆ : ℕ}
    (h : (j₁ + j₂ + j₃) % 2 = 1 ∨ (j₁ + j₅ + j₆) % 2 = 1 ∨ (j₄ + j₂ + j₆) % 2 = 1 ∨
      (j₄ + j₅ + j₃) % 2 = 1) :
    sixJSym j₁ j₂ j₃ j₄ j₅ j₆ = 0 := by
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases h with h | h | h | h
  · have h0 : threeJ j₁ j₂ j₃ (-m 0) (-m 1) (-m 2) = 0 :=
      threeJ_of_not fun h' => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, t⟩ := h'
        omega
    simp [sixJTerm, h0]
  · have h0 : threeJ j₁ j₅ j₆ (m 0) (-m 4) (m 5) = 0 :=
      threeJ_of_not fun h' => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, t⟩ := h'
        omega
    simp [sixJTerm, h0]
  · have h0 : threeJ j₄ j₂ j₆ (m 3) (m 1) (-m 5) = 0 :=
      threeJ_of_not fun h' => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, t⟩ := h'
        omega
    simp [sixJTerm, h0]
  · have h0 : threeJ j₄ j₅ j₃ (-m 3) (m 4) (m 2) = 0 :=
      threeJ_of_not fun h' => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, t⟩ := h'
        omega
    simp [sixJTerm, h0]

/-- **A tetrahedron amplitude with an odd face perimeter vanishes.** The faces of `p` are
`{p 1, p 2, p 3}`, `{p 0, p 2, p 3}`, `{p 0, p 1, p 3}`, `{p 0, p 1, p 2}`; the perimeter of a face
is the sum of the doubled spins on its three edges. -/
theorem tetAmp_eq_zero_of_odd (col : Colouring V) (p : Fin 4 → V)
    (h : (col {p 2, p 3} + col {p 1, p 3} + col {p 1, p 2}) % 2 = 1 ∨
      (col {p 2, p 3} + col {p 0, p 2} + col {p 0, p 3}) % 2 = 1 ∨
      (col {p 0, p 1} + col {p 1, p 3} + col {p 0, p 3}) % 2 = 1 ∨
      (col {p 0, p 1} + col {p 0, p 2} + col {p 1, p 2}) % 2 = 1) :
    tetAmp col p = 0 := by
  rw [tetAmp_eq]
  exact sixJSym_eq_zero_of_odd h

/-- The sum of `col` over the three edges of a triangle `{u, v, w}`. -/
lemma sum_edges_three (col : Colouring V) {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∑ e ∈ ({u, v, w} : Finset V).powersetCard 2, col e =
      col {u, v} + col {v, w} + col {w, u} := by
  have hu : u ∉ ({v, w} : Finset V) := by simp [huv, huw]
  have hP : ({u, v, w} : Finset V).powersetCard 2 = {{v, w}, {u, v}, {u, w}} := by
    have hself : ({v, w} : Finset V).powersetCard 2 = {{v, w}} := by
      rw [← card_pair hvw, powersetCard_self]
    rw [show (2 : ℕ) = 1 + 1 from rfl, powersetCard_succ_insert hu, powersetCard_one]
    rw [show Nat.succ 1 = 2 from rfl, hself]
    ext s; simp only [mem_union, mem_image, mem_map, mem_insert, mem_singleton]; aesop
  have h1 : ({v, w} : Finset V) ∉ ({{u, v}, {u, w}} : Finset (Finset V)) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨fun h => hu (h ▸ mem_insert_self u {v}), fun h => hu (h ▸ mem_insert_self u {w})⟩
  have h2 : ({u, v} : Finset V) ≠ {u, w} := by
    intro h
    have : v ∈ ({u, w} : Finset V) := h ▸ mem_insert_of_mem (mem_singleton_self v)
    simp only [mem_insert, mem_singleton] at this
    tauto
  rw [hP, sum_insert h1, sum_pair h2, pair_comm w u]
  ring

/-- **A tetrahedron with an odd-perimeter face has weight `0`.** `f` is a triangle of the
tetrahedron `t`, and the sum of `col` over its three edges is odd. -/
theorem tetW_eq_zero_of_odd (col : Colouring V) {t f : Finset V} (ht : #t = 4) (hft : f ⊆ t)
    (hf : #f = 3) (hodd : (∑ e ∈ f.powersetCard 2, col e) % 2 = 1) : tetW col t = 0 := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := Finset.card_eq_three.mp hf
  rw [sum_edges_three col huv huw hvw] at hodd
  have hx : (t \ {u, v, w}).card = 1 := by
    rw [card_sdiff_of_subset hft, ht, hf]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hx
  have hxt : x ∈ t \ {u, v, w} := by rw [hx]; exact mem_singleton_self x
  have hxf : x ∉ ({u, v, w} : Finset V) := (mem_sdiff.mp hxt).2
  have hxu : x ≠ u := fun h => hxf (by simp [h])
  have hxv : x ≠ v := fun h => hxf (by simp [h])
  have hxw : x ≠ w := fun h => hxf (by simp [h])
  have htx : t = {x, u, v, w} := by
    ext y
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hy
      by_cases hyf : y ∈ ({u, v, w} : Finset V)
      · simp only [mem_insert, mem_singleton] at hyf
        tauto
      · left
        have : y ∈ t \ {u, v, w} := mem_sdiff.mpr ⟨hy, hyf⟩
        rw [hx, mem_singleton] at this
        exact this
    · rintro (rfl | rfl | rfl | rfl)
      · exact (mem_sdiff.mp hxt).1
      · exact hft (by simp)
      · exact hft (by simp)
      · exact hft (by simp)
  have hp : Function.Injective (![x, u, v, w] : Fin 4 → V) := by
    intro i k hik
    fin_cases i <;> fin_cases k <;> simp [hxu, hxv, hxw, huv, huw, hvw, Ne.symm hxu, Ne.symm hxv,
      Ne.symm hxw, Ne.symm huv, Ne.symm huw, Ne.symm hvw] at hik ⊢
  have hpt : ∀ i, (![x, u, v, w] : Fin 4 → V) i ∈ t := by
    intro i
    rw [htx]
    fin_cases i <;> simp
  rw [tetW_eq_tetAmp col ht hp hpt]
  refine tetAmp_eq_zero_of_odd col _ (Or.inl ?_)
  show (col {v, w} + col {u, w} + col {u, v}) % 2 = 1
  rw [pair_comm w u] at hodd
  omega

/-- The Ponzano–Regge weight with the triangle weight `triW` replaced by an arbitrary function
`g` of the triangle. -/
noncomputable def weightWith (g : Finset V → ℝ) (K : Complex3 V) (col : Colouring V) : ℝ :=
  (∏ e ∈ K.edges, edgeW (col e)) * (∏ f ∈ K.tris, g f) * ∏ t ∈ K.tets, tetW col t

/-- The cut-off amplitude built from `weightWith g`. -/
noncomputable def amplitudeWith (g : Finset V → ℝ) (K : Complex3 V) (L : ℕ) : ℝ :=
  ∑ c ∈ K.edges.pi (fun _ => range (L + 1)),
    weightWith g K (fun e => if h : e ∈ K.edges then c e h else 0)

/-- **The weight does not depend on the triangle weight on odd-perimeter triangles.** If `g`
agrees with `triW col` on every triangle of `K` of even perimeter, then `weightWith g K col =
weight K col`, whatever `g` is on the odd ones. Hence the `ℕ` division in `triSign` and `triW` is
never seen: an odd-perimeter triangle lies in a tetrahedron, whose 6j symbol vanishes
(`tetW_eq_zero_of_odd`), and then both sides are `0`. -/
theorem weightWith_eq_weight (g : Finset V → ℝ) (K : Complex3 V) (col : Colouring V)
    (hg : ∀ f ∈ K.tris, (∑ e ∈ f.powersetCard 2, col e) % 2 = 0 → g f = triW col f) :
    weightWith g K col = weight K col := by
  by_cases hall : ∀ f ∈ K.tris, (∑ e ∈ f.powersetCard 2, col e) % 2 = 0
  · unfold weightWith weight
    rw [prod_congr rfl fun f hf => hg f hf (hall f hf)]
  · simp only [not_forall] at hall
    obtain ⟨f, hf, hodd⟩ := hall
    obtain ⟨t, ht, hft, hcard⟩ := Complex3.mem_tris.mp hf
    have h0 : ∏ t ∈ K.tets, tetW col t = 0 :=
      prod_eq_zero ht (tetW_eq_zero_of_odd col (K.card_eq t ht) hft hcard (by omega))
    unfold weightWith weight
    rw [h0, mul_zero, mul_zero]

/-- The cut-off amplitude does not depend on the triangle weight on odd-perimeter triangles
(`weightWith_eq_weight`). The hypothesis is required for every colouring of the edges. -/
theorem amplitudeWith_eq_amplitude (g : Finset V → ℝ) (K : Complex3 V) (L : ℕ)
    (hg : ∀ col : Colouring V, ∀ f ∈ K.tris, (∑ e ∈ f.powersetCard 2, col e) % 2 = 0 →
      g f = triW col f) :
    amplitudeWith g K L = amplitude K L := by
  unfold amplitudeWith amplitude
  exact sum_congr rfl fun c _ => weightWith_eq_weight g K _ (hg _)

end Lightlike.PR
