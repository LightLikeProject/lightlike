import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign

/-!
# The sign of an injective tuple

For the embedding of the `n`-particle fermionic Fock space `Γₙ` (the closed span of the wedges `B S`, `|S| = n`, in
`ℓ²(Finset ι)`) into the coordinate tensor power `ℓ²(Fin n → ι)` (J. Dereziński, arXiv:math-ph/0511030, Section 5.2:
`Γₙ^a(Z)` is the antisymmetric subspace of `⊗ⁿZ`): a wedge `B S` goes to `(n!)^{-1/2} ∑ sign(f) e_f` over the injective tuples
`f` enumerating `S`, where the sign of `f` is that of the permutation sorting it (Mathlib's `Tuple.sort`).

* `tupleSign`, `sort_comp_perm`, `tupleSign_comp`: `sign(f ∘ τ) = sign τ · sign f` for injective `f`;
* `Enum`, `enumEquiv`, `card_enum`: an `n`-element set has `n!` enumerations by injective tuples.
-/

namespace Lightlike.OperatorAlgebras.SecondQuantWedge

variable {ι : Type*} [LinearOrder ι]

/-- **The sign of a tuple**: the sign of the permutation `Tuple.sort f` that sorts it. -/
def tupleSign {n : ℕ} (f : Fin n → ι) : ℤˣ := Equiv.Perm.sign (Tuple.sort f)

/-- **Sorting a permuted injective tuple**: `sort (f ∘ τ) = τ⁻¹ * sort f`, as the monotone rearrangement of an injective
tuple is unique. -/
lemma sort_comp_perm {n : ℕ} {f : Fin n → ι} (hf : Function.Injective f) (τ : Equiv.Perm (Fin n)) :
    Tuple.sort (f ∘ τ) = τ⁻¹ * Tuple.sort f := by
  have hmono : Monotone ((f ∘ τ) ∘ (τ⁻¹ * Tuple.sort f)) := by
    have : (f ∘ τ) ∘ (τ⁻¹ * Tuple.sort f) = f ∘ Tuple.sort f := by
      funext x; simp [Equiv.Perm.mul_apply]
    rw [this]
    exact Tuple.monotone_sort f
  have heq := (Tuple.comp_sort_eq_comp_iff_monotone (f := f ∘ τ) (σ := τ⁻¹ * Tuple.sort f)).mpr hmono
  ext x
  have := congrFun heq x
  exact congrArg Fin.val ((hf.comp τ.injective) this).symm

/-- **`sign(f ∘ τ) = sign τ · sign f`** for an injective tuple `f`. -/
lemma tupleSign_comp {n : ℕ} {f : Fin n → ι} (hf : Function.Injective f) (τ : Equiv.Perm (Fin n)) :
    tupleSign (f ∘ τ) = Equiv.Perm.sign τ * tupleSign f := by
  rw [tupleSign, sort_comp_perm hf, map_mul, Equiv.Perm.sign_inv, tupleSign]

/-- The injective tuples enumerating a finite set `S`. -/
def Enum (n : ℕ) (S : Finset ι) := {f : Fin n → ι // Function.Injective f ∧ Finset.univ.image f = S}

/-- **The enumerations of `S` are the bijections `Fin n ≃ S`.** -/
noncomputable def enumEquiv (n : ℕ) (S : Finset ι) (hS : S.card = n) : Enum n S ≃ (Fin n ≃ S) where
  toFun f := Equiv.ofBijective (fun i => ⟨f.1 i, (Finset.ext_iff.mp f.2.2 (f.1 i)).mp (Finset.mem_image_of_mem f.1 (Finset.mem_univ i))⟩)
    ⟨fun i j h => f.2.1 (congrArg Subtype.val h), fun s => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ((Finset.ext_iff.mp f.2.2 s).mpr s.2)
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨fun i => (e i : ι), fun i j h => e.injective (Subtype.ext h), by
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hs
      exact ⟨e.symm ⟨s, hs⟩, by simp⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    ext i
    rfl

/-- The enumerations of `S` form a finite type. -/
noncomputable instance (n : ℕ) (S : Finset ι) : Fintype (Enum n S) := by
  classical
  by_cases hS : S.card = n
  · exact Fintype.ofEquiv _ (enumEquiv n S hS).symm
  · refine ⟨∅, fun f => absurd ?_ hS⟩
    rw [← f.2.2, Finset.card_image_of_injective _ f.2.1, Finset.card_univ, Fintype.card_fin]

/-- **An `n`-element set has `n!` enumerations.** -/
theorem card_enum (n : ℕ) (S : Finset ι) (hS : S.card = n) : Fintype.card (Enum n S) = n.factorial := by
  classical
  rw [Fintype.card_congr (enumEquiv n S hS), Fintype.card_equiv (Fintype.equivOfCardEq (by simp [hS])),
    Fintype.card_fin]

end Lightlike.OperatorAlgebras.SecondQuantWedge
