import Lightlike.Rows.G2_009.System

/-!
# A group-valued projective system and a non-consistent Haar family (row G2-009, CA2)

`X n = G^{n+1}` (the configuration space of a graph with `n+1` edges, holonomies in `G`) with the
bonding maps forgetting the last edges.  The product of Haar measures is a consistent family
(proved in later files of this folder); the same family with a wrong normalisation is not, and has
no projective limit: the check "a family of measures that is not cylindrically consistent has no
limit" of CA2.
-/

open MeasureTheory

namespace Lightlike.Rows.G2_009

variable (G : Type) [TopologicalSpace G]

/-- The edge-forgetting bonding maps `G^{m+1} → G^{n+1}` for `n ≤ m`. -/
def forget ⦃n m : ℕ⦄ (h : n ≤ m) (x : Fin (m + 1) → G) : Fin (n + 1) → G :=
  fun k => x (Fin.castLE (Nat.succ_le_succ h) k)

lemma isProjSystem_forget : IsProjSystem (X := fun n : ℕ => Fin (n + 1) → G) (forget G) where
  cont _ _ _ := continuous_pi fun _ => continuous_apply _
  id _ _ _ := rfl
  comp _ _ _ _ _ _ := rfl

variable {G}

/-- A scaled family `μ n = (n+1) • P n` of probability measures has no projective limit,
as its total masses `n+1` differ. -/
theorem not_exists_isLimit_scaled [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G]
    (P : ∀ n : ℕ, Measure (Fin (n + 1) → G)) [∀ n, IsProbabilityMeasure (P n)] :
    ¬ ∃ ν : Measure (Lim (X := fun n : ℕ => Fin (n + 1) → G) (forget G)),
      IsLimit (forget G) ν (fun n => ((n : ENNReal) + 1) • P n) := by
  refine not_exists_isLimit_of_measure_univ_ne (i := 0) (j := 1) ?_
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    Nat.cast_zero, zero_add, Nat.cast_one]
  norm_num

end Lightlike.Rows.G2_009
