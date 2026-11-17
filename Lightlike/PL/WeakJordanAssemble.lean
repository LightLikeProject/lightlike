import Lightlike.PL.WeakJordanLink

/-!
# The `K₃,₃` configuration of the weak Jordan theorem

Nine arcs, cut from two arcs of a circuit, an outer arc, a horizontal segment and a connecting arc,
form a drawing of `K₃,₃`; `no_K33_set` shows that this cannot exist.

## Main results

* `false_of_pieces`: the contradiction from the nine arcs and the facts on how they meet
  (Klazar, arXiv:2604.04296, Section 2, Claim 4: "We set `U = {a, b, e}`, `V = {c, d, g}` ... It is
  easy to check that the nine arcs defined have mutually disjoint interiors").
-/

open Set

namespace Lightlike.PL

/-- The ends of an arc belong to it. -/
lemma IsArc.left_mem {A : Set (ℝ × ℝ)} {p q : ℝ × ℝ} (h : IsArc A p q) : p ∈ A := by
  obtain ⟨γ, -, -, h0, -, rfl⟩ := h
  exact ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩

/-- The ends of an arc belong to it. -/
lemma IsArc.right_mem {A : Set (ℝ × ℝ)} {p q : ℝ × ℝ} (h : IsArc A p q) : q ∈ A := by
  obtain ⟨γ, -, -, -, h1, rfl⟩ := h
  exact ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩

-- needs 200000–240000 heartbeats (measured); about twice the smallest passing limit
set_option maxHeartbeats 500000 in
/-- **The nine arcs of the weak Jordan theorem cannot exist.** -/
theorem false_of_pieces {Pac Pad Pag Pcb Pdb Pgb Tec Ted B : Set (ℝ × ℝ)} {a b c d e g : ℝ × ℝ}
    (hac : IsArc Pac a c) (had : IsArc Pad a d) (hag : IsArc Pag a g)
    (hcb : IsArc Pcb b c) (hdb : IsArc Pdb b d) (hgb : IsArc Pgb b g)
    (hec : IsArc Tec e c) (hed : IsArc Ted e d) (heg : IsArc B e g)
    (h1 : ∀ z, z ∈ Pac → z ∈ Pcb → z = c) (h2 : ∀ z, z ∈ Pad → z ∈ Pdb → z = d)
    (h3 : ∀ z, z ∈ Pag → z ∈ Pgb → z = g) (h4 : ∀ z, z ∈ Tec → z ∈ Ted → z = e)
    (h5 : ∀ z, (z ∈ Pac ∨ z ∈ Pcb) → (z ∈ Pad ∨ z ∈ Pdb) → z = a ∨ z = b)
    (h6 : ∀ z, (z ∈ Pag ∨ z ∈ Pgb) → (z ∈ Pac ∨ z ∈ Pcb ∨ z ∈ Pad ∨ z ∈ Pdb) → z = a ∨ z = b)
    (h7 : ∀ z, (z ∈ Tec ∨ z ∈ Ted) → (z ∈ Pac ∨ z ∈ Pcb ∨ z ∈ Pad ∨ z ∈ Pdb) → z = c ∨ z = d)
    (h8 : ∀ z, z ∈ B → ¬ (z ∈ Pac ∨ z ∈ Pcb ∨ z ∈ Pad ∨ z ∈ Pdb))
    (h9 : ∀ z, (z ∈ Pag ∨ z ∈ Pgb) → ¬ (z ∈ Tec ∨ z ∈ Ted))
    (h10 : ∀ z, z ∈ B → (z ∈ Tec ∨ z ∈ Ted) → z = e)
    (h11 : ∀ z, z ∈ B → (z ∈ Pag ∨ z ∈ Pgb) → z = g)
    (hab : a ≠ b) (hcd : c ≠ d) (hca : c ≠ a) (hcb' : c ≠ b) (hda : d ≠ a) (hdb' : d ≠ b) : False := by
  have m1 := hac.left_mem; have m2 := hac.right_mem; have m3 := had.left_mem; have m4 := had.right_mem
  have m5 := hag.left_mem; have m6 := hag.right_mem; have m7 := hcb.left_mem; have m8 := hcb.right_mem
  have m9 := hdb.left_mem; have m10 := hdb.right_mem; have m11 := hgb.left_mem; have m12 := hgb.right_mem
  have m13 := hec.left_mem; have m14 := hec.right_mem; have m15 := hed.left_mem; have m16 := hed.right_mem
  have m17 := heg.left_mem; have m18 := heg.right_mem
  let AA : Fin 3 → Fin 3 → Set (ℝ × ℝ)
    | 0, 0 => Pac | 0, 1 => Pad | 0, 2 => Pag
    | 1, 0 => Pcb | 1, 1 => Pdb | 1, 2 => Pgb
    | 2, 0 => Tec | 2, 1 => Ted | 2, 2 => B
  refine no_K33_set
    { u := ![a, b, e]
      v := ![c, d, g]
      A := AA
      arc := fun i j => ?_
      disj := fun i j i' j' hne => ?_
      inj_u := fun i j hij => ?_
      inj_v := fun i j hij => ?_
      uv_ne := fun i j => ?_ }
  · fin_cases i <;> fin_cases j <;> assumption
  · intro z hz
    fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
      first
      | exact absurd rfl hne
      | (simp only [AA, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
         simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hz ⊢
         grind)
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind
  · fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind
  · fin_cases i <;> fin_cases j <;> simp <;> grind

end Lightlike.PL
