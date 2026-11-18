import Lightlike.GFT.Bubble
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pseudo-complexes with indexed simplices

A graded poset of simplices (`GradedPoset`): a poset `ι` whose elements are the simplices, `a ≤ b` meaning
that `a` is a face of `b`, with a rank `rk σ`, the number of vertices of `σ`. On it this file defines the
conditions of Gurau, *Lost in translation: topological singularities in group field theory*, Class.
Quantum Grav. 27 (2010) 235023, arXiv:1006.0714, Section 2: a complex of top rank `n` (dimension `n - 1`)
is a pseudo-manifold if it is pure, non-branching (each simplex of rank `n - 1` is a face of precisely two
simplices of rank `n`) and strongly connected (any two simplices of rank `n` are joined by a chain in which
neighbours share a face of rank `n - 1`), and normal if all its links are pseudo-manifolds. The link of a
simplex `σ` is the set of simplices containing `σ`, with the rank counted from `σ`. The numbers `f_p` of
`p`-simplices and the Euler characteristic `Σ (-1)^p f_p` are defined too.

## How it differs from `SComplex`

`Lightlike.PL.SComplex` (Lightlike/PL/Complex.lean) is a set of faces, each face a set of vertices, so two
simplices with the same vertex set are one. The gluing `Δ_G` of a colored graph (Gurau, Section 2: "`Δ` is
not a set but a collection (or a multiset)") can have several simplices with the same vertices: in the graph
with two vertices and three lines both top simplices have the vertex set `{(0, {a, b}), (1, {a, b}),
(2, {a, b})}`. Here the simplices are indexed by a type, and the face relation and the rank are data, so
repeated vertex sets stay distinct. No vertex set is part of the structure; that each lower interval is
a Boolean lattice, the property of a simplicial poset, is a separate statement where it is needed.

## Main definitions

* `GradedPoset`, `IsPure`, `IsNonBranching`, `Adjacent`, `IsStronglyConnected`, `IsPseudoManifold`.
* `GradedPoset.link`, `IsNormal`, `IsNormalPseudoManifold`.
* `GradedPoset.f`, `GradedPoset.eulerChar`.

## References

* R. Gurau, *Lost in translation: topological singularities in group field theory*, Class. Quantum
  Grav. 27 (2010) 235023, arXiv:1006.0714, Section 2.
-/

open Finset

namespace Lightlike.GFT

/-- A finite poset of simplices with a rank function: `rk σ` is the number of vertices of `σ`, and
`a < b` means that `a` is a proper face of `b`. -/
structure GradedPoset (ι : Type*) [PartialOrder ι] where
  /-- The number of vertices of a simplex. -/
  rk : ι → ℕ
  /-- A proper face has fewer vertices. -/
  rk_lt : ∀ {a b : ι}, a < b → rk a < rk b

variable {ι : Type*} [PartialOrder ι]

namespace GradedPoset

variable (P : GradedPoset ι)

lemma rk_le {a b : ι} (h : a ≤ b) : P.rk a ≤ P.rk b := by
  rcases h.lt_or_eq with h | rfl
  · exact (P.rk_lt h).le
  · exact le_rfl

/-- **Purity**: every simplex is a face of a simplex of the top rank `n`. -/
def IsPure (n : ℕ) : Prop := ∀ σ : ι, ∃ τ, σ ≤ τ ∧ P.rk τ = n

/-- **Non-branching**: every simplex of rank `n - 1` is a face of exactly two simplices of rank `n`. -/
def IsNonBranching (n : ℕ) : Prop :=
  ∀ σ : ι, P.rk σ + 1 = n → Nat.card {τ : ι // σ ≤ τ ∧ P.rk τ = n} = 2

/-- Two distinct simplices of rank `n` share a face of rank `n - 1`. -/
def Adjacent (n : ℕ) (a b : ι) : Prop :=
  P.rk a = n ∧ P.rk b = n ∧ a ≠ b ∧ ∃ σ, P.rk σ + 1 = n ∧ σ ≤ a ∧ σ ≤ b

/-- **Strong connectivity**: any two simplices of rank `n` are joined by a strong chain, a sequence in
which neighbours share a face of rank `n - 1`. -/
def IsStronglyConnected (n : ℕ) : Prop :=
  ∀ a b : ι, P.rk a = n → P.rk b = n → Relation.ReflTransGen (P.Adjacent n) a b

/-- **A pseudo-manifold of top rank `n`** (dimension `n - 1`): pure, non-branching and strongly connected
(Gurau 2010, Section 2). -/
structure IsPseudoManifold (n : ℕ) : Prop where
  pure : P.IsPure n
  nonBranching : P.IsNonBranching n
  stronglyConnected : P.IsStronglyConnected n

/-- **The link of a simplex `σ`**: the simplices that contain `σ` as a face, with the rank counted from
`σ`. -/
def link (σ : ι) : GradedPoset (Set.Ici σ) where
  rk τ := P.rk τ.1 - P.rk σ
  rk_lt {a b} h := by
    have h1 : P.rk σ ≤ P.rk a.1 := P.rk_le a.2
    have h2 : P.rk a.1 < P.rk b.1 := P.rk_lt h
    omega

/-- **Normality**: every link of a simplex of rank at most `n - 2` is a pseudo-manifold, of top rank
`n - rk σ`. -/
def IsNormal (n : ℕ) : Prop :=
  ∀ σ : ι, P.rk σ + 2 ≤ n → (P.link σ).IsPseudoManifold (n - P.rk σ)

/-- **A normal pseudo-manifold** of top rank `n`. -/
structure IsNormalPseudoManifold (n : ℕ) : Prop where
  isPseudoManifold : P.IsPseudoManifold n
  isNormal : P.IsNormal n

/-- The number `f_p` of `p`-simplices, those of rank `p + 1`. -/
noncomputable def f (p : ℕ) : ℕ := Nat.card {σ : ι // P.rk σ = p + 1}

/-- The Euler characteristic `Σ_{p < n} (-1)^p f_p` of a complex of top rank `n`. -/
noncomputable def eulerChar (n : ℕ) : ℤ := ∑ p ∈ range n, (-1) ^ p * (P.f p : ℤ)

end GradedPoset

end Lightlike.GFT
