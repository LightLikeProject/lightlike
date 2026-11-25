import Mathlib

/-!
# The Temperley–Lieb algebra

For a field `k` and a loop value `δ : k`, `TL k δ` is the `k`-algebra with generators `e i` (`i : ℕ`) and
relations
`e i ^ 2 = δ e i`, `e i e (i+1) e i = e i`, `e (i+1) e i e (i+1) = e (i+1)`, `e i e j = e j e i` for
`i + 2 ≤ j`.  The generator `e i` joins the strands `i` and `i + 1`.  `IsTL δ e` states the relations for a
family `e` in any `k`-algebra, so that the Jones–Wenzl theory of `JonesWenzl.lean` applies to every
representation.  The sequence `chebD δ` is the sequence of values of the Chebyshev polynomials,
`d₀ = 1`, `d₁ = δ`, `d_{n+2} = δ d_{n+1} − d_n`; for `δ = −[2]` it is `(−1)ⁿ [n+1]`.

## References

* L. H. Kauffman, S. L. Lins, *Temperley–Lieb recoupling theory and invariants of 3-manifolds*,
  Annals of Mathematics Studies 134 (1994), Chapters 1 and 3 (the algebra and the Jones–Wenzl projectors).
-/

namespace Lightlike.TemperleyLieb

variable {k : Type*} [Field k]

/-- The relations of a family `e` of the Temperley–Lieb algebra with loop value `δ`. -/
structure IsTL {A : Type*} [Ring A] [Algebra k A] (δ : k) (e : ℕ → A) : Prop where
  /-- `eᵢ² = δ eᵢ`. -/
  sq : ∀ i, e i * e i = algebraMap k A δ * e i
  /-- `eᵢ eᵢ₊₁ eᵢ = eᵢ`. -/
  braid_l : ∀ i, e i * e (i + 1) * e i = e i
  /-- `eᵢ₊₁ eᵢ eᵢ₊₁ = eᵢ₊₁`. -/
  braid_r : ∀ i, e (i + 1) * e i * e (i + 1) = e (i + 1)
  /-- Distant generators commute. -/
  comm : ∀ i j, i + 2 ≤ j → e i * e j = e j * e i

/-- The relations of the Temperley–Lieb algebra as relations on the free algebra. -/
inductive Rel (δ : k) : FreeAlgebra k ℕ → FreeAlgebra k ℕ → Prop
  | sq (i : ℕ) : Rel δ (FreeAlgebra.ι k i * FreeAlgebra.ι k i)
      (algebraMap k _ δ * FreeAlgebra.ι k i)
  | braid_l (i : ℕ) : Rel δ (FreeAlgebra.ι k i * FreeAlgebra.ι k (i + 1) * FreeAlgebra.ι k i)
      (FreeAlgebra.ι k i)
  | braid_r (i : ℕ) : Rel δ (FreeAlgebra.ι k (i + 1) * FreeAlgebra.ι k i * FreeAlgebra.ι k (i + 1))
      (FreeAlgebra.ι k (i + 1))
  | comm (i j : ℕ) (h : i + 2 ≤ j) : Rel δ (FreeAlgebra.ι k i * FreeAlgebra.ι k j)
      (FreeAlgebra.ι k j * FreeAlgebra.ι k i)

variable (k) in
/-- The Temperley–Lieb algebra with loop value `δ`. -/
abbrev TL (δ : k) := RingQuot (Rel δ)

namespace TL

variable {δ : k}

/-- The generator `eᵢ` of the Temperley–Lieb algebra. -/
def e (i : ℕ) : TL k δ := RingQuot.mkAlgHom k _ (FreeAlgebra.ι k i)

/-- The generators of `TL k δ` satisfy the Temperley–Lieb relations. -/
theorem isTL : IsTL δ (e : ℕ → TL k δ) where
  sq i := by simpa [e] using RingQuot.mkAlgHom_rel k (Rel.sq (k := k) (δ := δ) i)
  braid_l i := by simpa [e] using RingQuot.mkAlgHom_rel k (Rel.braid_l (k := k) (δ := δ) i)
  braid_r i := by simpa [e] using RingQuot.mkAlgHom_rel k (Rel.braid_r (k := k) (δ := δ) i)
  comm i j h := by simpa [e] using RingQuot.mkAlgHom_rel k (Rel.comm (k := k) (δ := δ) i j h)

/-- **Universal property**: a family satisfying the relations extends to an algebra map out of `TL`. -/
noncomputable def lift {A : Type*} [Ring A] [Algebra k A] (f : ℕ → A) (hf : IsTL δ f) :
    TL k δ →ₐ[k] A :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k f, by
    intro x y h
    cases h with
    | sq i => simpa using hf.sq i
    | braid_l i => simpa using hf.braid_l i
    | braid_r i => simpa using hf.braid_r i
    | comm i j h => simpa using hf.comm i j h⟩

@[simp] theorem lift_e {A : Type*} [Ring A] [Algebra k A] (f : ℕ → A) (hf : IsTL δ f) (i : ℕ) :
    lift f hf (e i) = f i := by
  simp [lift, e]

end TL

/-- The Chebyshev sequence `d₀ = 1`, `d₁ = δ`, `d_{n+2} = δ d_{n+1} − d_n`. -/
def chebD (δ : k) : ℕ → k
  | 0 => 1
  | 1 => δ
  | n + 2 => δ * chebD δ (n + 1) - chebD δ n

/-- The recurrence of `chebD`. -/
theorem chebD_succ_succ (δ : k) (n : ℕ) : chebD δ (n + 2) = δ * chebD δ (n + 1) - chebD δ n := rfl

end Lightlike.TemperleyLieb
