import Lightlike.OperatorAlgebras.BisognanoWichmannStandardSubspace.Uniqueness

/-!
# The standard subspace determines the modular pair

Row G1-054 (Bisognano–Wichmann in the standard-subspace form of Brunetti–Guido–Longo).

If two Tomita data `S, S'` have the same fixed-point subspace `H`, then `Dom S = Dom S'` and
`S = S'` on it: `Dom S = H + iH` and `S (a + i c) = a - i c` for `a, c ∈ H`
(this is `docs/notes/op3-finite.md`'s version of Longo, Lemma 2.1.1, in the form used here).
Combined with `ModularPair.ext_of_op` this shows that a positive modular pair `(D, J)` is
determined by its standard subspace `H(D, J)`.

## Main results

* `TomitaData.dom_op_eq_of_fixedClosed` — same fixed points ⇒ same domain and same operator.
* `ModularPair.ext_of_subspace` — positive modular pairs with the same standard subspace coincide.
-/

open Complex
open scoped LinearPMap

namespace Lightlike.Rows.G1_054

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗]

namespace TomitaData

variable (T : TomitaData 𝓗)

/-- For `a, c` fixed by `S`, `a + i c ∈ Dom S` and `S (a + i c) = a - i c`. -/
lemma op_decomp {a c : 𝓗} (ha : a ∈ T.fixedClosed) (hc : c ∈ T.fixedClosed) :
    a + I • c ∈ T.dom ∧ T.op (a + I • c) = a + (-I) • c := by
  obtain ⟨ha1, ha2⟩ := (T.mem_fixedClosed_iff a).mp ha
  obtain ⟨hc1, hc2⟩ := (T.mem_fixedClosed_iff c).mp hc
  have hI : I • c ∈ T.dom := T.dom.smul_mem _ hc1
  refine ⟨T.dom.add_mem ha1 hI, ?_⟩
  rw [T.op_add _ ha1 _ hI, T.op_smul _ _ hc1, ha2, hc2, Complex.conj_I]

/-- Tomita data with the same fixed points have the same domain and the same operator. -/
lemma dom_op_eq_of_fixedClosed (T' : TomitaData 𝓗) (h : T.fixedClosed = T'.fixedClosed) :
    T.dom ≤ T'.dom ∧ ∀ x ∈ T.dom, T.op x = T'.op x := by
  have key : ∀ x ∈ T.dom, x ∈ T'.dom ∧ T.op x = T'.op x := by
    intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (T.dom_subset_sup hx)
    have ha' : a ∈ T.fixedClosed := ha
    have hc := (T.mem_mulI_iff b).mp hb
    have hc' : (-I) • b ∈ T.fixedClosed := hc
    have hb' : b = I • ((-I) • b) := by
      rw [smul_smul]; simp
    have hxe : x = a + I • ((-I) • b) := by rw [← hb']; exact hab.symm
    have ha'' : a ∈ T'.fixedClosed := h ▸ ha'
    have hc'' : (-I) • b ∈ T'.fixedClosed := h ▸ hc'
    obtain ⟨d1, o1⟩ := T.op_decomp ha' hc'
    obtain ⟨d2, o2⟩ := T'.op_decomp ha'' hc''
    rw [← hxe] at d2 o2 o1
    exact ⟨d2, o1.trans o2.symm⟩
  exact ⟨fun x hx => (key x hx).1, fun x hx => (key x hx).2⟩

end TomitaData

namespace ModularPair

variable [CompleteSpace 𝓗]

/-- **The standard subspace determines the modular pair.** Two positive modular pairs with the same
standard subspace `H(D, J)` have the same `D` and `J`. -/
theorem ext_of_subspace {P Q : ModularPair 𝓗} (hP : P.IsPositive) (hQ : Q.IsPositive)
    (h : P.subspace = Q.subspace) : P.D = Q.D ∧ P.J = Q.J := by
  have hf : P.tomita.fixedClosed = Q.tomita.fixedClosed :=
    congrArg StandardSubspace.toClosedSubmodule h
  obtain ⟨h1, h2⟩ := P.tomita.dom_op_eq_of_fixedClosed Q.tomita hf
  obtain ⟨h3, h4⟩ := Q.tomita.dom_op_eq_of_fixedClosed P.tomita hf.symm
  exact ModularPair.ext_of_op hP hQ (le_antisymm h1 h3) h2

end ModularPair

end Lightlike.Rows.G1_054
