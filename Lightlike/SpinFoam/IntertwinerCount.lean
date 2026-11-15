import Lightlike.SpinFoam.HaarProducts
import Lightlike.Spin4.Intertwiner4

/-!
# Haar integrals of products of characters count intertwiners

`∫ Π_a χ_{J_a}(g) dg = tr P` is the dimension of the space of invariant vectors in
`⊗_a V_{J_a/2}` (`integral_prod_spinChar`). For three and four spins this dimension is the number of
admissible intertwiners: `1` or `0` by the triangle rule for three spins, and the number of
admissible virtual (coupled) spins for four.

## Main results
* `spinChar_real`: the characters of `SU(2)` are real, `conj χ_n = χ_n`.
* `spinChar_mul_eq_sum`: `χ_n χ_m = Σ_{z ∈ triSet n m} χ_z` (Clebsch–Gordan series).
* `integral_spinChar_mul`: `∫ χ_n χ_m = δ_{nm}`.
* `integral_spinChar_three`: `∫ χ_a χ_b χ_c = 1` if `(a, b, c)` is a triad, `0` otherwise.
* `integral_spinChar_four`: `∫ χ_a χ_b χ_c χ_d` is the number of virtual spins `z` with `(a, b, z)`
  and `(c, d, z)` triads (`channel`).
* `trace_avgP_three`, `trace_avgP_four`: the same as traces of `avgP`.
-/

open Matrix MeasureTheory Finset Lightlike.SU2 Lightlike.Spin4 Lightlike.Pentagon
open scoped Kronecker

namespace Lightlike.SpinFoam

/-- The embedding `emb` has real entries. -/
lemma emb_real (n : ℕ) (s : Str n) (k : Fin (n + 1)) : star (emb n s k) = emb n s k := by
  simp only [emb_apply]
  split_ifs
  · exact star_nrm n k
  · simp

lemma emb_conjTranspose_eq (n : ℕ) : (emb n)ᴴ = (emb n)ᵀ := by
  ext k s; simp [conjTranspose_apply, emb_real]

lemma emb_conj_eq (n : ℕ) : ((emb n)ᴴ)ᵀ = emb n := by
  ext s k; simp [conjTranspose_apply, emb_real]

lemma kron_transpose (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : (kron n g)ᵀ = kron n gᵀ := by
  ext s t; simp [kron_apply, transpose_apply]

/-- `spinMat n` commutes with the transpose. -/
lemma spinMat_transpose (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinMat n g)ᵀ = spinMat n gᵀ := by
  unfold spinMat
  rw [transpose_mul, transpose_mul, emb_conj_eq, kron_transpose, ← emb_conjTranspose_eq,
    Matrix.mul_assoc]

/-- For `g ∈ SU(2)`, `conj g = w g w⁻¹` with `w = [[0,1],[-1,0]]`. -/
lemma conj_eq_conj_by (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ).map star =
      !![0, 1; -1, 0] * (g : Matrix (Fin 2) (Fin 2) ℂ) * !![0, -1; 1, 0] := by
  have hu : star (g : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2))
  have hd : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  have hadj : star (g : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
    calc star (g : Matrix (Fin 2) (Fin 2) ℂ)
        = star (g : Matrix (Fin 2) (Fin 2) ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℂ) *
            (g : Matrix (Fin 2) (Fin 2) ℂ).adjugate) := by
          rw [mul_adjugate, hd]; simp
      _ = _ := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have h00 := congrFun (congrFun hadj 0) 0
  have h01 := congrFun (congrFun hadj 0) 1
  have h10 := congrFun (congrFun hadj 1) 0
  have h11 := congrFun (congrFun hadj 1) 1
  simp [Matrix.adjugate_fin_two] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h00, h01, h10, h11]

/-- **The characters of `SU(2)` are real.** -/
theorem spinChar_real (n : ℕ) (g : SU2) : star (spinChar n g) = spinChar n g := by
  have h1 : star (spinChar n g) = trace (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) := by
    unfold spinChar
    rw [← trace_conjTranspose, spinMat_conjTranspose]
  have h2 : (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = ((g : Matrix (Fin 2) (Fin 2) ℂ).map star)ᵀ := by
    ext i j; simp [conjTranspose_apply]
  rw [h1, h2, ← spinMat_transpose, trace_transpose, conj_eq_conj_by g]
  unfold spinChar
  rw [spinMat_mul, spinMat_mul, trace_mul_comm, ← Matrix.mul_assoc, ← spinMat_mul]
  have : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; -1, 0] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [this, spinMat_one, Matrix.one_mul]

/-- **Clebsch–Gordan series for characters:** `χ_n χ_m = Σ_{z ∈ triSet n m} χ_z`. -/
theorem spinChar_mul_eq_sum (n m : ℕ) (g : SU2) :
    spinChar n g * spinChar m g = ∑ z ∈ triSet n m, spinChar z g := by
  set K := spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ)
  have hK : trace K = spinChar n g * spinChar m g := by
    unfold spinChar; rw [trace_kronecker]
  rw [← hK]
  calc trace K = trace (K * ∑ z ∈ triSet n m, cgz n m z * (cgz n m z)ᴴ) := by
        rw [cgz_complete, Matrix.mul_one]
    _ = ∑ z ∈ triSet n m, trace (K * (cgz n m z * (cgz n m z)ᴴ)) := by
        rw [Finset.mul_sum, trace_sum]
    _ = ∑ z ∈ triSet n m, spinChar z g := by
        refine sum_congr rfl fun z hz => ?_
        have hzt : Tri n m z := mem_triSet.mp hz
        rw [← Matrix.mul_assoc, cgz_equivariant hzt g, Matrix.mul_assoc, trace_mul_comm,
          Matrix.mul_assoc, cgz_isometry hzt, Matrix.mul_one]
        rfl

/-- **Orthonormality of the characters** (real form): `∫ χ_n χ_m = δ_{nm}`. -/
theorem integral_spinChar_mul (n m : ℕ) :
    ∫ g, spinChar n g * spinChar m g ∂haarSU2 = if n = m then 1 else 0 := by
  have := integral_spinChar_mul_star n m
  simpa only [spinChar_real] using this

/-- **Three spins:** `∫ χ_a χ_b χ_c = 1` if `(a, b, c)` is a triad and `0` otherwise. -/
theorem integral_spinChar_three (a b c : ℕ) :
    ∫ g, spinChar a g * spinChar b g * spinChar c g ∂haarSU2 = if Tri a b c then 1 else 0 := by
  have hexp : ∀ g : SU2, spinChar a g * spinChar b g * spinChar c g =
      ∑ z ∈ triSet a b, spinChar z g * spinChar c g := by
    intro g; rw [spinChar_mul_eq_sum, Finset.sum_mul]
  have hint : ∀ z : ℕ, Integrable (fun g : SU2 => spinChar z g * spinChar c g) haarSU2 :=
    fun z => integrable_of_continuous ((continuous_spinChar z).mul (continuous_spinChar c))
  simp_rw [hexp]
  rw [integral_finsetSum _ fun z _ => hint z]
  simp_rw [integral_spinChar_mul]
  rw [Finset.sum_ite_eq' (triSet a b) c]
  simp only [mem_triSet]

/-- **Four spins:** `∫ χ_a χ_b χ_c χ_d` is the number of virtual spins `z` with `(a, b, z)` and
`(c, d, z)` triads. -/
theorem integral_spinChar_four (a b c d : ℕ) :
    ∫ g, spinChar a g * spinChar b g * (spinChar c g * spinChar d g) ∂haarSU2 =
      ((channel a b c d).card : ℂ) := by
  have hexp : ∀ g : SU2, spinChar a g * spinChar b g * (spinChar c g * spinChar d g) =
      ∑ z ∈ triSet a b, ∑ w ∈ triSet c d, spinChar z g * spinChar w g := by
    intro g; rw [spinChar_mul_eq_sum, spinChar_mul_eq_sum, Finset.sum_mul_sum]
  have hint : ∀ z w : ℕ, Integrable (fun g : SU2 => spinChar z g * spinChar w g) haarSU2 :=
    fun z w => integrable_of_continuous ((continuous_spinChar z).mul (continuous_spinChar w))
  simp_rw [hexp]
  rw [integral_finsetSum _ fun z _ => integrable_finsetSum _ fun w _ => hint z w]
  have : ∀ z ∈ triSet a b, ∫ g, ∑ w ∈ triSet c d, spinChar z g * spinChar w g ∂haarSU2 =
      if z ∈ triSet c d then 1 else 0 := by
    intro z _
    rw [integral_finsetSum _ fun w _ => hint z w]
    simp_rw [integral_spinChar_mul]
    rw [Finset.sum_ite_eq (triSet c d) z]
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext z
  simp only [channel, triSet, Finset.mem_filter, Finset.mem_range]
  unfold Tri
  omega

/-- `tr avgP` for three spins is the triangle indicator. -/
theorem trace_avgP_three (a b c : ℕ) :
    trace (avgP ![a, b, c]) = if Tri a b c then 1 else 0 := by
  rw [← integral_prod_spinChar (J := ![a, b, c])]
  simpa [Fin.prod_univ_three] using integral_spinChar_three a b c

/-- `tr avgP` for four spins is the number of virtual spins. -/
theorem trace_avgP_four (a b c d : ℕ) :
    trace (avgP ![a, b, c, d]) = ((channel a b c d).card : ℂ) := by
  rw [← integral_prod_spinChar (J := ![a, b, c, d])]
  simpa [Fin.prod_univ_four, mul_assoc] using integral_spinChar_four a b c d

/-! ## Trust checks -/

/-- Two spin-`1/2` and one spin-`1` (doubled spins `1, 1, 2`) have one invariant vector. -/
theorem trace_avgP_three_112 : trace (avgP ![1, 1, 2]) = 1 := by
  rw [trace_avgP_three]
  have : Tri 1 1 2 := by unfold Tri; omega
  simp [this]

/-- A wrong model is detected: doubled spins `1, 1, 1` (odd total) have no invariant vector. -/
theorem trace_avgP_three_111 : trace (avgP ![1, 1, 1]) = 0 := by
  rw [trace_avgP_three]
  have : ¬ Tri 1 1 1 := by unfold Tri; omega
  simp [this]

/-- Four spins `1/2`: `1/2 ⊗ 1/2 = 0 ⊕ 1` gives two intertwiners. -/
theorem trace_avgP_four_1111 : trace (avgP ![1, 1, 1, 1]) = 2 := by
  rw [trace_avgP_four]
  have : channel 1 1 1 1 = {0, 2} := by decide +kernel
  simp [this]

/-- Four spins `1`: `1 ⊗ 1 = 0 ⊕ 1 ⊕ 2` gives three intertwiners. -/
theorem trace_avgP_four_2222 : trace (avgP ![2, 2, 2, 2]) = 3 := by
  rw [trace_avgP_four]
  have : channel 2 2 2 2 = {0, 2, 4} := by decide +kernel
  simp [this]

end Lightlike.SpinFoam
