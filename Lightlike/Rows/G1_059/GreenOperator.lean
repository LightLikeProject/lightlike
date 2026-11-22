import Mathlib

/-!
# Green operators of a linear operator with a causal support rule

The abstract setting of the Green operators of Bär–Ginoux–Pfäffle (bgp-2007, §3.4): a linear
operator `P` on functions `X → ℝ` that preserves a space `D` of test functions, and a *support
rule* `J : Set X → Set X` (the causal future `J⁺` for a retarded operator, the causal past `J⁻`
for an advanced one). A *Green operator* for `(P, J)` is a linear map `G : D → (X → ℝ)` that is a
right and a left inverse of `P` and satisfies `supp (G f) ⊆ J (supp f)`.

The theorem here is the uniqueness half of the statement: if the homogeneous equation `P h = 0`
has no non-zero solution with support in `J (supp f)` (this is the uniqueness of the Cauchy problem
for a wave operator on a globally hyperbolic spacetime, bgp-2007, §3.4), then there is at most one
Green operator. Existence is proved for the wave operator of `1+1` Minkowski space in the other
files of this folder.

## Main definitions

* `Lightlike.Rows.G1_059.IsGreenOperator`: the defining properties of a Green operator.

## Main results

* `Lightlike.Rows.G1_059.IsGreenOperator.unique`: at most one Green operator for `(P, J)` when the
  homogeneous problem with support in `J (supp f)` has only the zero solution.
-/

open Function

namespace Lightlike.Rows.G1_059

variable {X : Type*}

/-- **A Green operator** of `P` with support rule `J` on the test functions `D`: `G` is a right
inverse (`P (G f) = f`) and a left inverse (`G (P f) = f`) of `P`, and `supp (G f) ⊆ J (supp f)`.
For the wave operator on a globally hyperbolic spacetime, `J = J⁺` gives the retarded and `J = J⁻`
the advanced Green operator (bgp-2007, §3.4). -/
structure IsGreenOperator (P : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (D : Submodule ℝ (X → ℝ))
    (hP : ∀ f ∈ D, P f ∈ D) (J : Set X → Set X) (G : D →ₗ[ℝ] (X → ℝ)) : Prop where
  /-- `P ∘ G = id` on test functions. -/
  right_inv : ∀ f : D, P (G f) = f
  /-- `G ∘ P = id` on test functions. -/
  left_inv : ∀ f : D, G ⟨P f, hP f f.2⟩ = f
  /-- The support rule `supp (G f) ⊆ J (supp f)`. -/
  support_subset : ∀ f : D, support (G f) ⊆ J (support (f : X → ℝ))

/-- **Uniqueness of the Green operator.** If the only solution of `P h = 0` supported in
`J (supp f)` is `h = 0`, for each test function `f`, then two Green operators of `(P, J)` agree.
The proof: `G f - G' f` solves the homogeneous equation and is supported in `J (supp f)`. -/
theorem IsGreenOperator.unique {P : (X → ℝ) →ₗ[ℝ] (X → ℝ)} {D : Submodule ℝ (X → ℝ)}
    {hP : ∀ f ∈ D, P f ∈ D} {J : Set X → Set X} {G G' : D →ₗ[ℝ] (X → ℝ)}
    (hG : IsGreenOperator P D hP J G) (hG' : IsGreenOperator P D hP J G')
    (hU : ∀ f : D, ∀ h : X → ℝ, P h = 0 → support h ⊆ J (support (f : X → ℝ)) → h = 0) :
    G = G' := by
  refine LinearMap.ext fun f => ?_
  have h0 : P (G f - G' f) = 0 := by
    rw [map_sub, hG.right_inv, hG'.right_inv, sub_self]
  have hsupp : support (G f - G' f) ⊆ J (support (f : X → ℝ)) := fun x hx => by
    by_contra hxJ
    apply hx
    have h1 : G f x = 0 := by
      by_contra h; exact hxJ (hG.support_subset f h)
    have h2 : G' f x = 0 := by
      by_contra h; exact hxJ (hG'.support_subset f h)
    simp [h1, h2]
  exact sub_eq_zero.mp (hU f _ h0 hsupp)

end Lightlike.Rows.G1_059
