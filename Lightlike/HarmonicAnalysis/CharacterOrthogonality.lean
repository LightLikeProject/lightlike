import Lightlike.HarmonicAnalysis.SchurOrthogonality

/-!
# Orthogonality of characters, and non-compact groups

* `UnitaryMatrixRep.character`: the character `g ↦ tr ρ(g)` of a unitary matrix representation.
* `character_orthogonality_ne`, `character_orthogonality_eq`: for irreducible `ρ`, `σ` of a compact group with a
  Haar probability measure, `∫ χ_ρ · conj χ_σ dμ` is `0` if `ρ`, `σ` are inequivalent, and `∫ |χ_ρ|² dμ = 1`.
* `not_forall_memLp_two_of_measure_univ_eq_top`: on a group whose (Haar) measure is infinite, no row of a
  unitary matrix representation consists of square-integrable matrix coefficients; in particular a
  one-dimensional representation (a unitary character, as for `ℝ`) has no square-integrable coefficient
  (`not_memLp_two_of_unique`). This is the check that compactness is needed in the Peter–Weyl theorem.

Supporting lemmas and checks; no catalogue entry.

## References

* T. Tao, *The Peter–Weyl theorem, and non-abelian Fourier analysis on compact groups* (blog post,
  23 January 2011), §1 (Corollary 5, Proposition 8) for the orthogonality of the coefficients, from which
  the character relations follow by taking traces.
-/

open MeasureTheory Matrix

namespace Lightlike.HarmonicAnalysis

noncomputable section

namespace UnitaryMatrixRep

variable {G : Type*} [Group G] [TopologicalSpace G]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The character `g ↦ tr ρ(g)` of a unitary matrix representation. -/
def character (ρ : UnitaryMatrixRep G ι) (g : G) : ℂ := (ρ.mat g).trace

lemma character_apply (ρ : UnitaryMatrixRep G ι) (g : G) : ρ.character g = ∑ i, ρ.mat g i i := rfl

/-- The rows of a unitary matrix have norm one. -/
lemma sum_norm_sq_row (ρ : UnitaryMatrixRep G ι) (g : G) (i : ι) : ∑ j, ‖ρ.mat g i j‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (ρ.mat_mul_star_mat g) i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ j, ‖ρ.mat g i j‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.mul_conj']
    rfl
  exact_mod_cast h2

section NonCompact

variable [MeasurableSpace G]

/-- **Compactness is needed.** If the measure of the group is infinite (a Haar measure of a non-compact
group), then no row of a unitary matrix representation consists of square-integrable coefficients. -/
theorem not_forall_memLp_two_of_measure_univ_eq_top (μ : Measure G) (hμ : μ Set.univ = ⊤)
    (ρ : UnitaryMatrixRep G ι) (i : ι) : ¬ ∀ j, MemLp (fun g => ρ.mat g i j) 2 μ := by
  intro h
  have hint : Integrable (fun g => ∑ j, ‖ρ.mat g i j‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => by
      have h2 : MemLp (fun g => ρ.mat g i j) ((2 : ℕ) : ENNReal) μ := by simpa using h j
      exact h2.integrable_norm_pow (by norm_num)
  have h1 : Integrable (fun _ : G => (1 : ℝ)) μ := by
    refine hint.congr (Filter.Eventually.of_forall fun g => ?_)
    exact ρ.sum_norm_sq_row g i
  have hfin : IsFiniteMeasure μ := by
    rcases integrable_const_iff.1 h1 with h0 | h0
    · exact absurd h0 one_ne_zero
    · exact h0
  exact absurd hμ (measure_ne_top μ Set.univ)

/-- A one-dimensional unitary representation of a group of infinite measure (for example a unitary character
of `ℝ`) has no square-integrable matrix coefficient. -/
theorem not_memLp_two_of_unique [Unique ι] (μ : Measure G) (hμ : μ Set.univ = ⊤)
    (ρ : UnitaryMatrixRep G ι) (i j : ι) : ¬ MemLp (fun g => ρ.mat g i j) 2 μ := by
  intro h
  refine not_forall_memLp_two_of_measure_univ_eq_top μ hμ ρ i fun j' => ?_
  rwa [Subsingleton.elim j' j]

end NonCompact

section Compact

variable [MeasurableSpace G] [IsTopologicalGroup G] [CompactSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure] [IsProbabilityMeasure μ]

lemma integrable_entry_mul_conj (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) (i j : ι) (k l : κ) :
    Integrable (fun g => ρ.mat g i j * starRingEnd ℂ (σ.mat g l k)) μ :=
  ((ρ.continuous_mat_apply i j).mul
    (Complex.continuous_conj.comp (σ.continuous_mat_apply l k))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integral_character_mul_conj (ρ : UnitaryMatrixRep G ι) (σ : UnitaryMatrixRep G κ) :
    ∫ g, ρ.character g * starRingEnd ℂ (σ.character g) ∂μ =
      ∑ i, ∑ l, ∫ g, ρ.mat g i i * starRingEnd ℂ (σ.mat g l l) ∂μ := by
  simp only [character_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun i _ => integrable_entry_mul_conj μ ρ σ i i l l]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun i _ => integrable_entry_mul_conj μ ρ σ i i l l]

/-- **Orthogonality of characters, inequivalent case.** -/
theorem character_orthogonality_ne {ρ : UnitaryMatrixRep G ι} {σ : UnitaryMatrixRep G κ}
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible) (hne : ¬ Equivalent ρ σ) :
    ∫ g, ρ.character g * starRingEnd ℂ (σ.character g) ∂μ = 0 := by
  rw [integral_character_mul_conj]
  simp [schur_orthogonality_ne μ hρ hσ hne]

/-- **Orthogonality of characters, equal case:** `∫ |χ_ρ|² dμ = 1` for irreducible `ρ`. -/
theorem character_orthogonality_eq {ρ : UnitaryMatrixRep G ι} (hρ : ρ.IsIrreducible) :
    ∫ g, ρ.character g * starRingEnd ℂ (ρ.character g) ∂μ = 1 := by
  haveI := hρ.1
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [integral_character_mul_conj]
  simp only [schur_orthogonality_eq μ hρ, and_self]
  simp [Finset.sum_ite_eq, hn]

end Compact

end UnitaryMatrixRep

end

end Lightlike.HarmonicAnalysis
