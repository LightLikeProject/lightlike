import Mathlib

/-!
# Green operators of a linear operator with a causal support rule

The abstract setting of the Green operators of Bär–Ginoux–Pfäffle (bgp-2007, §3.4): a linear
operator `P` on a space `E` of (smooth) functions `X → ℝ`, a space `D ≤ E` of test functions, and a
*support rule* `J : Set X → Set X` (the causal future `J⁺` for a retarded operator, the causal past
`J⁻` for an advanced one). A *Green operator* for `(P, J)` is a linear map `G : D → E` that is a
right and a left inverse of `P` and satisfies `supp (G f) ⊆ J (supp f)`.

The theorem here is the uniqueness half of the statement: if the homogeneous equation `P h = 0`
has no non-zero solution with support in `J (supp f)` (this is the uniqueness of the Cauchy problem
for a wave operator on a globally hyperbolic spacetime, bgp-2007, §3.4), then there is at most one
Green operator. Existence is proved for the wave operator of `1+1` Minkowski space in the other
files of this folder.

## Main definitions

* `Lightlike.Spacetime.WaveEquationGreenOperators.IsGreenOperator`: the defining properties of a Green operator.

## Main results

* `Lightlike.Spacetime.WaveEquationGreenOperators.IsGreenOperator.unique`: at most one Green operator for `(P, J)` when the
  homogeneous problem with support in `J (supp f)` has only the zero solution.
-/

open Function

namespace Lightlike.Spacetime.WaveEquationGreenOperators

variable {X : Type*}

/-- **A Green operator** of `P : E → E` with support rule `J` on the test functions `D ≤ E`: `G` is
a right inverse (`P (G f) = f`) and a left inverse (`G g' = g` whenever `P g = g'`, for `g, g'` test
functions) of `P`, and `supp (G f) ⊆ J (supp f)`.
For the wave operator on a globally hyperbolic spacetime, `J = J⁺` gives the retarded and `J = J⁻`
the advanced Green operator (bgp-2007, §3.4). -/
structure IsGreenOperator (E D : Submodule ℝ (X → ℝ)) (hDE : D ≤ E) (P : E →ₗ[ℝ] E)
    (J : Set X → Set X) (G : D →ₗ[ℝ] E) : Prop where
  /-- `P ∘ G = id` on test functions. -/
  right_inv : ∀ f : D, P (G f) = ⟨f, hDE f.2⟩
  /-- `G ∘ P = id` on test functions: if `P g = f` for test functions `g, f` then `G f = g`. -/
  left_inv : ∀ g f : D, P ⟨g, hDE g.2⟩ = ⟨f, hDE f.2⟩ → (G f : X → ℝ) = g
  /-- The support rule `supp (G f) ⊆ J (supp f)`. -/
  support_subset : ∀ f : D, support ((G f : E) : X → ℝ) ⊆ J (support (f : X → ℝ))

/-- **Uniqueness of the Green operator.** If the only solution `h ∈ E` of `P h = 0` supported in
`J (supp f)` is `h = 0`, for each test function `f`, then two Green operators of `(P, J)` agree.
The proof: `G f - G' f` solves the homogeneous equation and is supported in `J (supp f)`. -/
theorem IsGreenOperator.unique {E D : Submodule ℝ (X → ℝ)} {hDE : D ≤ E} {P : E →ₗ[ℝ] E}
    {J : Set X → Set X} {G G' : D →ₗ[ℝ] E}
    (hG : IsGreenOperator E D hDE P J G) (hG' : IsGreenOperator E D hDE P J G')
    (hU : ∀ f : D, ∀ h : E, P h = 0 → support (h : X → ℝ) ⊆ J (support (f : X → ℝ)) → h = 0) :
    G = G' := by
  refine LinearMap.ext fun f => ?_
  have h0 : P (G f - G' f) = 0 := by
    rw [map_sub, hG.right_inv, hG'.right_inv, sub_self]
  have hsupp : support ((G f - G' f : E) : X → ℝ) ⊆ J (support (f : X → ℝ)) := fun x hx => by
    by_contra hxJ
    apply hx
    have h1 : (G f : X → ℝ) x = 0 := by
      by_contra h; exact hxJ (hG.support_subset f h)
    have h2 : (G' f : X → ℝ) x = 0 := by
      by_contra h; exact hxJ (hG'.support_subset f h)
    simp [h1, h2]
  exact sub_eq_zero.mp (hU f _ h0 hsupp)

end Lightlike.Spacetime.WaveEquationGreenOperators

/-! Deprecated names (kept for one release) -/

@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.IsGreenOperator := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.IsGreenOperator
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.IsGreenOperator.left_inv := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.IsGreenOperator.left_inv
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.IsGreenOperator.right_inv := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.IsGreenOperator.right_inv
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.IsGreenOperator.support_subset := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.IsGreenOperator.support_subset
@[deprecated (since := "0.4.0")] alias _root_.Lightlike.Rows.G1_059.IsGreenOperator.unique := _root_.Lightlike.Spacetime.WaveEquationGreenOperators.IsGreenOperator.unique
