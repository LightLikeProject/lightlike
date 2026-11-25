import Mathlib
import Lightlike.TemperleyLieb.Recoupling

/-!
# Balanced cap and cup words reduce to the Temperley–Lieb subalgebra

`nestCap l i · Z · nestCup l' i ∈ C (N - 2 i)` for `Z ∈ C N`, with two different junctions `l`, `l'`, and a version
with leftover caps or cups that meet other elements of `C`.  This is the reduction needed for the Gram pairing of the
two tree bases.
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- Splitting a stack of caps. -/
lemma nestCap_add (q : kˣ) (l i j : ℕ) :
    (nestCap q l (i + j) : Module.End k (ModelSpace k)) = nestCap q l i * nestCap q (l + i) j := by
  induction j with
  | zero => simp [nestCap]
  | succ j ih =>
    have e1 : (nestCap q l (i + (j + 1)) : Module.End k (ModelSpace k)) = nestCap q l (i + j) * capOp q (l + (i + j)) := rfl
    have e2 : (nestCap q (l + i) (j + 1) : Module.End k (ModelSpace k)) = nestCap q (l + i) j * capOp q (l + i + j) := rfl
    rw [e1, e2, ih, mul_assoc, show l + (i + j) = l + i + j by ring]

/-- Splitting a stack of cups. -/
lemma nestCup_add (q : kˣ) (l i j : ℕ) :
    (nestCup q l (i + j) : Module.End k (ModelSpace k)) = nestCup q (l + i) j * nestCup q l i := by
  induction j with
  | zero => simp [nestCup]
  | succ j ih =>
    have e1 : (nestCup q l (i + (j + 1)) : Module.End k (ModelSpace k)) = cupOp q (l + (i + j)) * nestCup q l (i + j) := rfl
    have e2 : (nestCup q (l + i) (j + 1) : Module.End k (ModelSpace k)) = cupOp q (l + i + j) * nestCup q (l + i) j := rfl
    rw [e1, e2, ih, ← mul_assoc, show l + (i + j) = l + i + j by ring]

/-- **Balanced nested caps and cups at two junctions reduce.** -/
theorem nestCap_mul_nestCup_mem_gen (q : kˣ) (l l' : ℕ) :
    ∀ (i N : ℕ) {Z : Module.End k (ModelSpace k)}, Z ∈ CSub q N → l + 2 * i ≤ N + 1 → l' + 2 * i ≤ N + 1 →
      nestCap q l i * Z * nestCup q l' i ∈ CSub q (N - 2 * i) := by
  intro i
  induction i with
  | zero => intro N Z hZ _ _; simpa [nestCap, nestCup] using hZ
  | succ i ih =>
    intro N Z hZ hl hl'
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have h1 : nestCap q l (i + 1) * Z * nestCup q l' (i + 1) =
        nestCap q l i * (capOp q (l + i) * Z * cupOp q (l' + i)) * nestCup q l' i := by
      simp only [nestCap, nestCup, mul_assoc]
    rw [h1]
    have h2 := cap_mul_cup_mem q hZ (l + i) (l' + i) (by omega) (by omega)
    have h3 := ih (n - 1) h2 (by omega) (by omega)
    have e : n + 1 - 2 * (i + 1) = n - 1 - 2 * i := by omega
    rw [e]; exact h3

end Lightlike.TemperleyLieb
