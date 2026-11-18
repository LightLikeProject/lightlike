import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic

/-!
# The Dirac algorithm with constraint functions: termination by counting under independence

Second attempt at the nonlinear Dirac algorithm (Henneaux and Teitelboim 1992, Chapter One, "Constrained
Hamiltonian Systems"), by a route that avoids the manifold API. Stage `k` is a tuple of `n k` smooth constraint
functions `Φ k : Fin (n k) → E → ℝ` on a finite-dimensional real normed space `E`, each stage extending the previous
one by the new (secondary, tertiary, ...) constraints. **Regularity is an added hypothesis**: at every point of the
stage's zero set the derivatives of the `n k` functions are linearly independent (constant rank, in the form the
counting needs). Then at most `dim E` functions can be independent, so the number of constraints stops growing:

* `card_le_finrank_of_regular`: a regular stage has at most `finrank E` constraint functions.
* `exists_stable_of_regular`: for a regular sequence of stages (with nonempty zero sets) there is a stage from which no
  function is added, hence the zero sets stop changing (`zeroSet_eq_of_card_eq`).

**What this does not give.** That the new functions of each stage exist and cut out exactly the consistency
conditions (the secondary constraints as smooth functions): under constant rank of the bracket matrix this needs a
smooth choice of left null vectors, which is the implicit-function / constant-rank theorem for the matrix family, not
established here. The statement is therefore conditional on the sequence of stages being given.
-/

namespace Lightlike.Gauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The zero set of a tuple of constraint functions. -/
def zeroSet {n : ℕ} (Φ : Fin n → E → ℝ) : Set E := {x | ∀ i, Φ i x = 0}

/-- **Regular**: at every point of the zero set the derivatives are linearly independent. -/
def IsRegularStage {n : ℕ} (Φ : Fin n → E → ℝ) : Prop :=
  ∀ x ∈ zeroSet Φ, LinearIndependent ℝ fun i => fderiv ℝ (Φ i) x

/-- A regular stage with nonempty zero set has at most `dim E` constraint functions. -/
theorem card_le_finrank_of_regular {n : ℕ} (Φ : Fin n → E → ℝ) (hreg : IsRegularStage Φ)
    (hne : (zeroSet Φ).Nonempty) : n ≤ Module.finrank ℝ E := by
  obtain ⟨x, hx⟩ := hne
  have h1 := LinearIndependent.fintype_card_le_finrank (hreg x hx)
  have h2 : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
    rw [← LinearEquiv.finrank_eq (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ))]
    exact Subspace.dual_finrank_eq
  simpa [h2] using h1

/-- A stage and the next one, when no function is added, have the same zero set. -/
theorem zeroSet_eq_of_card_eq {m k : ℕ} (Φ : Fin m → E → ℝ) (Ψ : Fin k → E → ℝ) (hmk : m ≤ k)
    (hext : ∀ i, Ψ (Fin.castLE hmk i) = Φ i) (heq : m = k) : zeroSet Ψ = zeroSet Φ := by
  ext x
  constructor
  · intro hx i
    rw [← hext i]; exact hx _
  · intro hx j
    have hj : j = Fin.castLE hmk ⟨j.val, by omega⟩ := Fin.ext rfl
    rw [hj, hext]; exact hx _

/-- **Termination by counting**: for stages `Φ k` extending one another, all regular with nonempty zero sets, the
number of constraint functions is bounded by `dim E`, so from some stage on no function is added and the zero sets
stop changing. -/
theorem exists_stable_of_regular (n : ℕ → ℕ) (Φ : ∀ k, Fin (n k) → E → ℝ)
    (hmono : ∀ k, n k ≤ n (k + 1))
    (hext : ∀ k i, Φ (k + 1) (Fin.castLE (hmono k) i) = Φ k i)
    (hreg : ∀ k, IsRegularStage (Φ k)) (hne : ∀ k, (zeroSet (Φ k)).Nonempty) :
    ∃ N, ∀ k, N ≤ k → zeroSet (Φ k) = zeroSet (Φ N) := by
  have hb : ∀ k, n k ≤ Module.finrank ℝ E := fun k => card_le_finrank_of_regular _ (hreg k) (hne k)
  have hmon : Monotone n := monotone_nat_of_le_succ hmono
  have hbdd : BddAbove (Set.range n) := ⟨Module.finrank ℝ E, by rintro _ ⟨k, rfl⟩; exact hb k⟩
  obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty n) hbdd
  have hconst : ∀ k, N ≤ k → n k = n N := fun k hk =>
    le_antisymm (hN ▸ le_csSup hbdd ⟨k, rfl⟩) (hmon hk)
  refine ⟨N, fun k hk => ?_⟩
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih]
    exact zeroSet_eq_of_card_eq (Φ k) (Φ (k + 1)) (hmono k) (hext k) (by rw [hconst k hk, hconst (k+1) (by omega)])

/-- **Adding the next constraints to a stage**: the tuple `Φ` followed by the new constraint functions `χ`. -/
def appendStage {a b : ℕ} (Φ : Fin a → E → ℝ) (χ : Fin b → E → ℝ) : Fin (a + b) → E → ℝ :=
  Fin.append Φ χ

/-- The zero set of the extended stage is the zero set of the old stage cut by the new constraints. -/
theorem zeroSet_appendStage {a b : ℕ} (Φ : Fin a → E → ℝ) (χ : Fin b → E → ℝ) :
    zeroSet (appendStage Φ χ) = zeroSet Φ ∩ zeroSet χ := by
  ext x
  simp only [zeroSet, appendStage, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd b i), fun i => by simpa using h (Fin.natAdd a i)⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using h1 i
    · simpa using h2 i

/-- The extended stage restricts to the old one on the first `a` functions, as `exists_stable_of_regular` asks. -/
theorem appendStage_castLE {a b : ℕ} (Φ : Fin a → E → ℝ) (χ : Fin b → E → ℝ) (i : Fin a) :
    appendStage Φ χ (Fin.castLE (Nat.le_add_right a b) i) = Φ i := by
  have : Fin.castLE (Nat.le_add_right a b) i = Fin.castAdd b i := rfl
  rw [this]
  simp [appendStage]

end Lightlike.Gauge
