import Lightlike.SpinFoam.EPRLStateSum.NodePairGluing

/-!
# Sums over `Fin 5 → ℕ` boxes as five nested sums

`sum_piFinset_five`: a sum over `Fintype.piFinset A` for `A : Fin 5 → Finset ℕ` is the nested sum
over the five coordinates. Used to rewrite the five-fold sums of the vertex amplitude as sums over
the virtual-spin vector `l : Fin 5 → ℕ` needed for `global_gluing_nodeI`.
-/

open Finset

namespace Lightlike.SpinFoam.EPRLStateSum

/-- A sum over a box `Fin 5 → ℕ` as five nested sums. -/
theorem sum_piFinset_five {M : Type*} [AddCommMonoid M] (A : Fin 5 → Finset ℕ)
    (f : (Fin 5 → ℕ) → M) :
    ∑ l ∈ Fintype.piFinset A, f l =
      ∑ l₀ ∈ A 0, ∑ l₁ ∈ A 1, ∑ l₂ ∈ A 2, ∑ l₃ ∈ A 3, ∑ l₄ ∈ A 4,
        f ![l₀, l₁, l₂, l₃, l₄] := by
  have h : ∑ l ∈ Fintype.piFinset A, f l =
      ∑ p ∈ A 0 ×ˢ (A 1 ×ˢ (A 2 ×ˢ (A 3 ×ˢ A 4))),
        f ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2] := by
    refine Finset.sum_nbij' (fun l => (l 0, l 1, l 2, l 3, l 4))
      (fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      simp only [Fintype.mem_piFinset] at hl
      simp [hl 0, hl 1, hl 2, hl 3, hl 4]
    · intro p hp
      simp only [Finset.mem_product] at hp
      simp only [Fintype.mem_piFinset]
      intro a
      fin_cases a <;> simp [hp]
    · intro l _
      ext a
      fin_cases a <;> simp
    · intro p _
      simp
    · intro l _
      congr 1
      ext a
      fin_cases a <;> simp
  rw [h]
  simp only [Finset.sum_product]

end Lightlike.SpinFoam.EPRLStateSum
