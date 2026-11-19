import Lightlike.NCG.KrajewskiModel

/-!
# Tests for the multiplicity matrix and the real triple of a symmetric multiplicity matrix

The two-point space is `A = M₁(ℂ) ⊕ M₁(ℂ) = ℂ ⊕ ℂ` with the diagonal multiplicity matrix `r = 1` (one vertex at `(0, 0)`
and one at `(1, 1)`).

* `twoPointR`, `krajewski_twoPoint_diag`, `krajewski_twoPoint_off`: the model's multiplicities are `r₀₀ = 1`,
  `r₀₁ = 0`;
* `not_multiplicity_eq_of_not_symm`: a non-symmetric matrix is the multiplicity matrix of no real structure (wrong
  input);
* `twoPoint_link_eq_zero`: on `ℂ ⊕ ℂ`, every first-order `D` has `E₀₀ D E₁₁ = 0`: a Dirac operator joining the two
  points is rejected.
-/

namespace Lightlike.NCG.TestsClassification

/-- The multiplicity matrix of the two-point space, `rᵢⱼ = δᵢⱼ`. -/
def twoPointR (i j : Fin 2) : ℕ := if i = j then 1 else 0

lemma twoPointR_symm (i j : Fin 2) : twoPointR i j = twoPointR j i := by
  simp only [twoPointR, eq_comm]

lemma twoPointR_pos (i : Fin 2) : ∃ j, 0 < twoPointR i j := ⟨i, by simp [twoPointR]⟩

/-- `r₀₀ = 1` for the model of the two-point space. -/
theorem krajewski_twoPoint_diag :
    multiplicity (krajewskiReal (n := fun _ : Fin 2 => 1) (r := twoPointR) twoPointR_symm twoPointR_pos) 0 0 = 1 := by
  rw [multiplicity_krajewskiReal]
  simp [twoPointR]

/-- `r₀₁ = 0` for the model of the two-point space. -/
theorem krajewski_twoPoint_off :
    multiplicity (krajewskiReal (n := fun _ : Fin 2 => 1) (r := twoPointR) twoPointR_symm twoPointR_pos) 0 1 = 0 := by
  rw [multiplicity_krajewskiReal]
  simp [twoPointR]

/-- **Wrong input**: a matrix with `r₀₁ ≠ r₁₀` is the multiplicity matrix of no real structure. -/
theorem not_multiplicity_eq_of_not_symm {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} [∀ i, NeZero (n i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
    {T : FiniteSpectralTriple (MatSum n) H} (R : RealStructure T) (r : ι → ι → ℕ) {i j : ι} (hij : r i j ≠ r j i) :
    ¬ ∀ k l, multiplicity R k l = r k l := fun h =>
  hij (by rw [← h, ← h, multiplicity_symm])

/-- **The rejected Dirac operator**: on `ℂ ⊕ ℂ`, the first-order condition forces `E₀₀ D E₁₁ = 0` (Paschke-Sitarz,
Lemma 6), so a `D` joining the two points of the diagonal diagram is not first order. -/
theorem twoPoint_link_eq_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [CompleteSpace H] {T : FiniteSpectralTriple (MatSum (fun _ : Fin 2 => 1)) H} (R : RealStructure T) (x : H) :
    proj R (stdPartition _) (0, 0) (T.D (proj R (stdPartition _) (1, 1) x)) = 0 :=
  proj_D_proj_eq_zero R _ (by decide) (by decide) x

end Lightlike.NCG.TestsClassification
