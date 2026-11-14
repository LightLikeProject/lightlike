import Lightlike.Spin4.SO4
import Lightlike.Spin4.SpinSchur
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
# The Haar measure of SU(2) and Schur averaging

`haarSU2` is the normalised Haar measure of the compact group SU(2) (Mathlib's `haarMeasure`,
normalised on the whole group), a left-invariant probability measure. Matrix-valued functions are
integrated entry by entry (`matInt`).

## Main results

* `haarSU2` is a left-invariant probability measure (instances), and every continuous function
  of `g ∈ SU(2)` is integrable (`integrable_of_continuous`).
* `matInt_spinMat_conj`: **Schur averaging**: for every matrix `A` on `V_{n/2}`,
  `∫ D(g) A D(g)ᴴ dg = (tr A / (n+1)) · 1`.

## References

* J. Diestel, A. Spalsbury, *The Joys of Haar Measure*, Graduate Studies in Mathematics 150,
  AMS (2014) (Haar measure of compact groups).
* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer (1985), Ch. II (Schur orthogonality).
-/

open Matrix MeasureTheory

namespace Lightlike.Spin4

open SU2

/-- **The normalised Haar measure of SU(2)**: Mathlib's left Haar measure, normalised so that the
whole group has measure `1`. -/
noncomputable def haarSU2 : Measure SU2 := Measure.haarMeasure ⊤

instance : IsProbabilityMeasure haarSU2 :=
  ⟨by simpa [haarSU2] using
    Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts SU2))⟩

instance : haarSU2.IsMulLeftInvariant := Measure.isMulLeftInvariant_haarMeasure ⊤

instance : IsFiniteMeasureOnCompacts haarSU2 := by
  unfold haarSU2; infer_instance

/-- Every continuous function on SU(2) is integrable for the Haar measure. -/
theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {f : SU2 → E}
    (hf : Continuous f) : Integrable f haarSU2 :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The integral of a matrix-valued function, entry by entry. -/
noncomputable def matInt {ι κ : Type*} (F : SU2 → Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  Matrix.of fun i j => ∫ g, F g i j ∂haarSU2

lemma matInt_apply {ι κ : Type*} (F : SU2 → Matrix ι κ ℂ) (i : ι) (j : κ) :
    matInt F i j = ∫ g, F g i j ∂haarSU2 := rfl

/-- Left invariance of the matrix integral: `∫ F(h g) dg = ∫ F(g) dg`. -/
lemma matInt_mul_left {ι κ : Type*} (F : SU2 → Matrix ι κ ℂ) (h : SU2) :
    matInt (fun g => F (h * g)) = matInt F := by
  ext i j
  exact integral_mul_left_eq_self (fun g => F g i j) h

/-- The integral of a constant is the constant (`haarSU2` is a probability measure). -/
lemma matInt_const {ι κ : Type*} (A : Matrix ι κ ℂ) : matInt (fun _ => A) = A := by
  ext i j
  simp [matInt_apply]

lemma continuous_spinMat_apply (n : ℕ) (i j : Fin (n + 1)) :
    Continuous fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  (continuous_apply j).comp
    ((continuous_apply i).comp (continuous_spinMat.comp continuous_subtype_val))

/-- Multiplying by constant matrices commutes with the integral, for continuous integrands. -/
lemma matInt_mul_mul {ι κ μ ν : Type*} [Fintype κ] [Fintype μ] (A : Matrix ι κ ℂ)
    (F : SU2 → Matrix κ μ ℂ) (B : Matrix μ ν ℂ) (hF : ∀ k l, Continuous fun g => F g k l) :
    matInt (fun g => A * F g * B) = A * matInt F * B := by
  ext i j
  have hI : ∀ k l, Integrable (fun g => F g k l) haarSU2 := fun k l =>
    integrable_of_continuous (hF k l)
  have hin : ∀ l, Integrable (fun g => ∑ k, A i k * F g k l) haarSU2 := fun l =>
    integrable_finsetSum _ fun k _ => (hI k l).const_mul _
  calc matInt (fun g => A * F g * B) i j
      = ∫ g, ∑ l, (∑ k, A i k * F g k l) * B l j ∂haarSU2 := by
        simp only [matInt_apply, mul_apply]
    _ = ∑ l, ∫ g, (∑ k, A i k * F g k l) * B l j ∂haarSU2 :=
        integral_finsetSum _ fun l _ => (hin l).mul_const _
    _ = ∑ l, (∑ k, A i k * ∫ g, F g k l ∂haarSU2) * B l j := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_mul_const, integral_finsetSum _ fun k _ => (hI k l).const_mul _]
        simp only [integral_const_mul]
    _ = (A * matInt F * B) i j := by simp only [mul_apply, matInt_apply]

/-- The trace commutes with the integral. -/
lemma trace_matInt {ι : Type*} [Fintype ι] (F : SU2 → Matrix ι ι ℂ)
    (hF : ∀ k l, Continuous fun g => F g k l) : trace (matInt F) = ∫ g, trace (F g) ∂haarSU2 := by
  simp only [trace, diag, matInt_apply]
  exact (integral_finsetSum _ fun i _ => integrable_of_continuous (hF i i)).symm

/-- **Schur averaging**: `∫ D(g) A D(g)ᴴ dg = (tr A / (n+1)) · 1` on `V_{n/2}`. -/
theorem matInt_spinMat_conj (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    matInt (fun g : SU2 => spinMat n g * A * (spinMat n g)ᴴ) = (trace A / (n + 1 : ℂ)) • 1 := by
  set M := matInt (fun g : SU2 => spinMat n g * A * (spinMat n g)ᴴ) with hM
  have hcont : ∀ k l, Continuous fun g : SU2 => (spinMat n g * A * (spinMat n g)ᴴ) k l := by
    intro k l
    simp only [mul_apply, conjTranspose_apply]
    refine continuous_finsetSum _ fun b _ => ?_
    refine Continuous.mul ?_ (continuous_star.comp (continuous_spinMat_apply n l b))
    exact continuous_finsetSum _ fun a _ =>
      (continuous_spinMat_apply n k a).mul continuous_const
  have hunit : ∀ h : SU2, (spinMat n h)ᴴ * spinMat n h = 1 := fun h =>
    Matrix.mem_unitaryGroup_iff'.mp (spinMat_mem_unitaryGroup
      (Matrix.specialUnitaryGroup_le_unitaryGroup h.2))
  -- `M` commutes with every `D(h)`
  have hinv : ∀ h : SU2, spinMat n h * M = M * spinMat n h := by
    intro h
    have hconj : spinMat n h * M * (spinMat n h)ᴴ = M := by
      have e1 := (matInt_mul_mul (spinMat n h)
        (fun g : SU2 => spinMat n g * A * (spinMat n g)ᴴ) (spinMat n h)ᴴ hcont).symm
      have e2 : (fun g : SU2 => spinMat n h * (spinMat n g * A * (spinMat n g)ᴴ) *
          (spinMat n h)ᴴ) =
          fun g : SU2 => spinMat n ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) * A *
            (spinMat n ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
        funext g
        have hc : ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (h : Matrix (Fin 2) (Fin 2) ℂ) * g :=
          rfl
        rw [hc, spinMat_mul, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      rw [hM, e1, e2]
      exact matInt_mul_left (fun g : SU2 => spinMat n g * A * (spinMat n g)ᴴ) h
    calc spinMat n h * M = spinMat n h * M * ((spinMat n h)ᴴ * spinMat n h) := by
          rw [hunit, Matrix.mul_one]
      _ = M * spinMat n h := by rw [← Matrix.mul_assoc, hconj]
  obtain ⟨c, hc⟩ := spin_intertwiner_eq_smul (N := n) (T := M) hinv
  have htr : trace M = trace A := by
    rw [hM, trace_matInt _ hcont]
    have : ∀ g : SU2, trace (spinMat n g * A * (spinMat n g)ᴴ) = trace A := fun g => by
      rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hunit, Matrix.mul_one]
    simp [this]
  rw [hc] at htr ⊢
  rw [trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at htr
  rw [← htr]
  congr 1
  push_cast
  field_simp

end Lightlike.Spin4
