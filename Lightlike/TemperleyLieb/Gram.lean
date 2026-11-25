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

/-- **Three layers, case `e ≤ f`.** `caps_{d'+t} · Y_L · caps_e · Z · cups_{t+e} · Y_R · cups_{d'}` lies in
`C (N - 2e - 2t - 2d')` for `Z ∈ C N`, `Y_L ∈ C (N - 2e)`, `Y_R ∈ C (N - 2e - 2t)`. -/
theorem balanced_le (q : kˣ) {N : ℕ} {Z YL YR : Module.End k (ModelSpace k)} (hZ : Z ∈ CSub q N)
    (e t d' lam l l' l'' : ℕ) (hYL : YL ∈ CSub q (N - 2 * e)) (hYR : YR ∈ CSub q (N - 2 * e - 2 * t))
    (h1 : l + 2 * e ≤ N + 1) (h1' : l' + t + 2 * e ≤ N + 1)
    (h2 : lam + d' + 2 * t ≤ N - 2 * e + 1) (h2' : l' + 2 * t ≤ N - 2 * e + 1)
    (h3 : lam + 2 * d' ≤ N - 2 * e - 2 * t + 1) (h3' : l'' + 2 * d' ≤ N - 2 * e - 2 * t + 1) :
    nestCap q lam (d' + t) * YL * nestCap q l e * Z * nestCup q l' (t + e) * YR * nestCup q l'' d' ∈
      CSub q (N - 2 * e - 2 * t - 2 * d') := by
  have hZ1 := nestCap_mul_nestCup_mem_gen q l (l' + t) e N hZ h1 h1'
  have hY1 : YL * (nestCap q l e * Z * nestCup q (l' + t) e) ∈ CSub q (N - 2 * e) := Subalgebra.mul_mem _ hYL hZ1
  have hZ2 := nestCap_mul_nestCup_mem_gen q (lam + d') l' t (N - 2 * e) hY1 h2 h2'
  have hZ3 : nestCap q (lam + d') t * (YL * (nestCap q l e * Z * nestCup q (l' + t) e)) * nestCup q l' t * YR ∈
      CSub q (N - 2 * e - 2 * t) := Subalgebra.mul_mem _ hZ2 hYR
  have hZ4 := nestCap_mul_nestCup_mem_gen q lam l'' d' (N - 2 * e - 2 * t) hZ3 h3 h3'
  have e1 : nestCap q lam (d' + t) * YL * nestCap q l e * Z * nestCup q l' (t + e) * YR * nestCup q l'' d' =
      nestCap q lam d' * ((nestCap q (lam + d') t * (YL * (nestCap q l e * Z * nestCup q (l' + t) e)) *
        nestCup q l' t * YR)) * nestCup q l'' d' := by
    rw [nestCap_add, nestCup_add]
    simp only [mul_assoc]
  rw [e1]
  have e2 : N - 2 * e - 2 * t - 2 * d' = N - 2 * e - 2 * t - 2 * d' := rfl
  exact hZ4

/-- **Three layers, case `f ≤ e`.** `caps_d · Y_L · caps_{t+f} · Z · cups_f · Y_R · cups_{d+t}` lies in
`C (N - 2f - 2t - 2d)` for `Z ∈ C N`, `Y_R ∈ C (N - 2f)`, `Y_L ∈ C (N - 2f - 2t)`. -/
theorem balanced_ge (q : kˣ) {N : ℕ} {Z YL YR : Module.End k (ModelSpace k)} (hZ : Z ∈ CSub q N)
    (f t d lam l l' l'' : ℕ) (hYR : YR ∈ CSub q (N - 2 * f)) (hYL : YL ∈ CSub q (N - 2 * f - 2 * t))
    (h1 : l + t + 2 * f ≤ N + 1) (h1' : l' + 2 * f ≤ N + 1)
    (h2 : l + 2 * t ≤ N - 2 * f + 1) (h2' : l'' + d + 2 * t ≤ N - 2 * f + 1)
    (h3 : lam + 2 * d ≤ N - 2 * f - 2 * t + 1) (h3' : l'' + 2 * d ≤ N - 2 * f - 2 * t + 1) :
    nestCap q lam d * YL * nestCap q l (t + f) * Z * nestCup q l' f * YR * nestCup q l'' (d + t) ∈
      CSub q (N - 2 * f - 2 * t - 2 * d) := by
  have hZ1 := nestCap_mul_nestCup_mem_gen q (l + t) l' f N hZ h1 h1'
  have hZ1' : (nestCap q (l + t) f * Z * nestCup q l' f) * YR ∈ CSub q (N - 2 * f) := Subalgebra.mul_mem _ hZ1 hYR
  have hZ2 := nestCap_mul_nestCup_mem_gen q l (l'' + d) t (N - 2 * f) hZ1' h2 h2'
  have hZ3 : YL * (nestCap q l t * ((nestCap q (l + t) f * Z * nestCup q l' f) * YR) * nestCup q (l'' + d) t) ∈
      CSub q (N - 2 * f - 2 * t) := Subalgebra.mul_mem _ hYL hZ2
  have hZ4 := nestCap_mul_nestCup_mem_gen q lam l'' d (N - 2 * f - 2 * t) hZ3 h3 h3'
  have e1 : nestCap q lam d * YL * nestCap q l (t + f) * Z * nestCup q l' f * YR * nestCup q l'' (d + t) =
      nestCap q lam d * (YL * (nestCap q l t * ((nestCap q (l + t) f * Z * nestCup q l' f) * YR) *
        nestCup q (l'' + d) t)) * nestCup q l'' d := by
    rw [nestCap_add, nestCup_add]
    simp only [mul_assoc]
  rw [e1]
  exact hZ4

end Lightlike.TemperleyLieb
