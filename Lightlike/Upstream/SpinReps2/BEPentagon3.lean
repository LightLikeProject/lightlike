module

public import Lightlike.Upstream.SpinReps2.BEPentagon2
public import Lightlike.Upstream.SpinReps2.SixJOrth

/-!
# The recoupling pentagon, part 3: from recoupling coefficients to the 6j symbol

The proof-free recoupling coefficient `rc` of `Lightlike.Upstream.SpinReps2.BEPentagon2` is
expressed through Physlib's `sixJSym`, and four more tetrahedral symmetries of `sixJSym` are
recorded, in the shapes in which the Biedenharn–Elliott proof uses them.

## Main results

* `PhyslibAlpha.Sl2.Pentagon.rc_eq_sixJSym`: `rc` is `(-1)^(x+y+z-K) √((2j₁₂+1)(2j₂₃+1))`
  times a 6j symbol (doubled spins), or `0`.
-/

@[expose] public section

open PhyslibAlpha.Sl2 Finset

namespace PhyslibAlpha.Sl2.Pentagon

/-- The permutation of `Fin 4` given by a vector (bijectivity by `decide`). -/
noncomputable def permOf (v : Fin 4 → Fin 4) (h : Function.Bijective v) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective v h

lemma sixJSym_P2 (c d x e f q : ℕ) : sixJSym c d x e f q = sixJSym e x f c q d := by
  have := sixJSym_perm (permOf ![2, 3, 1, 0] (by decide)) e x f c q d
  simpa [permOf, edgeM] using this

lemma sixJSym_P3 (e f x b a r : ℕ) : sixJSym e f x b a r = sixJSym e a r b f x := by
  have := sixJSym_perm (permOf ![1, 0, 3, 2] (by decide)) e a r b f x
  simpa [permOf, edgeM] using this

lemma sixJSym_R1 (p q r e a d : ℕ) : sixJSym p q r e a d = sixJSym e a r p q d := by
  have := sixJSym_perm (permOf ![3, 2, 1, 0] (by decide)) e a r p q d
  simpa [permOf, edgeM] using this

lemma sixJSym_R2 (p q r f b c : ℕ) : sixJSym p q r f b c = sixJSym r b f c q p := by
  have := sixJSym_perm (permOf ![1, 2, 3, 0] (by decide)) r b f c q p
  simpa [permOf, edgeM] using this

/-- **`rc` in terms of the 6j symbol**: `R = (-1)^(j₁+j₂+j₃+J) √((2j₁₂+1)(2j₂₃+1)) {j₁ j₂ j₁₂; j₃ J j₂₃}`
(doubled units), for positive outer spins. -/
lemma rc_eq_sixJSym {x y z K l k₁ k₃ : ℕ} (hx : 0 < x) (hz : 0 < z) (hl : l ≤ x + y + z - 2 * K) :
    rc x y z K l k₁ k₃ =
      if k₁ < min x y + 1 ∧ k₃ < min y z + 1 ∧ ValidA x y z K k₁ ∧ ValidB x y z K k₃ then
        (-1) ^ (x + y + z - K) *
          Real.sqrt (((x + y - 2 * k₁ + 1 : ℕ) : ℝ) * ((y + z - 2 * k₃ + 1 : ℕ) : ℝ)) *
            sixJSym x y (x + y - 2 * k₁) z (x + y + z - 2 * K) (y + z - 2 * k₃)
      else 0 := by
  unfold rc
  by_cases h : k₁ < min x y + 1 ∧ k₃ < min y z + 1 ∧ ValidA x y z K k₁ ∧ ValidB x y z K k₃
  · obtain ⟨h1, h3, hA, hB⟩ := h
    rw [dite_eq_left ⟨by omega, by omega, h1, h3, hA, hB⟩, ite_eq_left ⟨h1, h3, hA, hB⟩,
      recoupling_eq_sixJ (by omega) (by omega) hx (k₁ := ⟨k₁, h1⟩) (k₃ := ⟨k₃, h3⟩) hA hB hl,
      sixJ_eq_sixJSym (by omega) (by omega) hx hz hA hB]
  · rw [ite_eq_right h, dite_eq_right (fun h' => h ⟨h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2⟩)]

end PhyslibAlpha.Sl2.Pentagon
