module

public import Mathlib

/-!
# Green operators and their uniqueness, abstractly (row G1-059, milestone SC6)

C. Bär, N. Ginoux and F. Pfäffle, *Wave equations on Lorentzian manifolds and quantization*,
arXiv:0806.1036 (key `bgp-2007`), Section 3.4: an *advanced* (resp. *retarded*) *Green operator* of a
differential operator `P` is a map `G` on the test functions with `P ∘ G = id`, `G ∘ P = id` and
`supp (G f) ⊆ J⁻(supp f)` (resp. `J⁺(supp f)`). The uniqueness half of the theorem there reduces to the
uniqueness of solutions of `P h = 0` whose support lies in `J^∓` of a compact set: two Green operators
differ on `f` by such an `h`.

This file isolates that reduction, with no manifold structure: `M` is any type, `P` any operator on
real functions, `Test` any predicate (smooth, compactly supported), `J` any "causal hull" of subsets.
The concrete data (the 1+1 Minkowski wave operator, with the explicit Green operators and the
Cauchy-uniqueness hypothesis proved) are in the other files of this folder.

* `IsGreen P Test J G`: `G` is a Green operator for `P` with support rule `J`;
* `IsGreen.eq_of_cauchyUnique`: uniqueness of Green operators from the uniqueness of the
  `J`-supported solutions of `P h = 0` (`CauchyUnique`);
* `pauliJordan G₊ G₋`: the propagator `G₊ - G₋`; `pauliJordan_ker`, `pauliJordan_comp`: it solves
  `P E f = 0` and vanishes on the image of `P`.
-/

@[expose] public section

namespace Lightlike.GreenOps

variable {M : Type*}

/-- `G` is a *Green operator* of `P` for the test predicate `Test` and the support rule `J`
(`J⁺` for a retarded, `J⁻` for an advanced operator): `P (G f) = f`, `G (P f) = f` for test functions `f`,
and `supp (G f) ⊆ J (supp f)` (BGP, Section 3.4). -/
structure IsGreen (P : (M → ℝ) → (M → ℝ)) (Test : (M → ℝ) → Prop) (J : Set M → Set M)
    (G : (M → ℝ) → (M → ℝ)) : Prop where
  /-- `P ∘ G = id` on test functions. -/
  left_inv : ∀ f, Test f → P (G f) = f
  /-- `G ∘ P = id` on test functions. -/
  right_inv : ∀ f, Test f → G (P f) = f
  /-- The support of `G f` lies in `J (supp f)`. -/
  supp_subset : ∀ f, Test f → Function.support (G f) ⊆ J (Function.support f)

/-- **Cauchy uniqueness** for `P`, `Test`, `J`: a solution of `P h = 0` whose support lies in
`J (supp f)` for a test function `f` vanishes. -/
def CauchyUnique (P : (M → ℝ) → (M → ℝ)) (Test : (M → ℝ) → Prop) (J : Set M → Set M) : Prop :=
  ∀ h f : M → ℝ, Test f → P h = 0 → Function.support h ⊆ J (Function.support f) → h = 0

/-- Two Green operators with the same support rule agree on test functions as soon as `P` is
`J`-Cauchy-unique, when `P` is additive (the uniqueness half of BGP, Section 3.4). -/
theorem IsGreen.eq_of_cauchyUnique {P : (M → ℝ) → (M → ℝ)} {Test : (M → ℝ) → Prop}
    {J : Set M → Set M} (hP : ∀ g h, P (g - h) = P g - P h) (hU : CauchyUnique P Test J)
    {G G' : (M → ℝ) → (M → ℝ)} (hG : IsGreen P Test J G) (hG' : IsGreen P Test J G') {f : M → ℝ}
    (hf : Test f) : G f = G' f := by
  have h0 : P (G f - G' f) = 0 := by
    rw [hP, hG.left_inv f hf, hG'.left_inv f hf, sub_self]
  have hs : Function.support (G f - G' f) ⊆ J (Function.support f) := by
    intro x hx
    by_cases h1 : G f x = 0
    · have : G' f x ≠ 0 := by
        intro h2
        exact hx (by simp [h1, h2])
      exact hG'.supp_subset f hf this
    · exact hG.supp_subset f hf h1
  exact sub_eq_zero.mp (hU _ f hf h0 hs)

/-- The **Pauli–Jordan propagator** (causal propagator) `E = G₊ - G₋` of a retarded and an advanced
Green operator. -/
def pauliJordan (Gret Gadv : (M → ℝ) → (M → ℝ)) (f : M → ℝ) : M → ℝ := Gret f - Gadv f

/-- `P (E f) = 0` for a test function `f`: the Pauli–Jordan propagator maps into solutions. -/
theorem pauliJordan_ker {P : (M → ℝ) → (M → ℝ)} {Test : (M → ℝ) → Prop} {Jp Jm : Set M → Set M}
    (hP : ∀ g h, P (g - h) = P g - P h) {Gret Gadv : (M → ℝ) → (M → ℝ)}
    (hr : IsGreen P Test Jp Gret) (ha : IsGreen P Test Jm Gadv) {f : M → ℝ} (hf : Test f) :
    P (pauliJordan Gret Gadv f) = 0 := by
  unfold pauliJordan
  rw [hP, hr.left_inv f hf, ha.left_inv f hf, sub_self]

/-- `E (P f) = 0` for a test function `f`: the Pauli–Jordan propagator kills the image of `P`. -/
theorem pauliJordan_comp {P : (M → ℝ) → (M → ℝ)} {Test : (M → ℝ) → Prop} {Jp Jm : Set M → Set M}
    {Gret Gadv : (M → ℝ) → (M → ℝ)} (hr : IsGreen P Test Jp Gret) (ha : IsGreen P Test Jm Gadv)
    {f : M → ℝ} (hf : Test f) : pauliJordan Gret Gadv (P f) = 0 := by
  unfold pauliJordan
  rw [hr.right_inv f hf, ha.right_inv f hf, sub_self]

end Lightlike.GreenOps
