import Lightlike.Spin4.Haar
import Lightlike.Spin4.EPRL
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Perelomov coherent states of SU(2) and Spin(4)

The SU(2) coherent state of spin `j = n/2` attached to `g ∈ SU(2)` is
`|j, g⟩ = D^j(g) |j, j⟩` (Perelomov), the image of the highest weight state `e₀ = |j, j⟩`
(`cohState`). It depends on `g` through the unit vector `ν(g) = g e_z g⁻¹ ∈ S²` (`bloch`), up to a
phase.

## Main results

* `cohState_apply`: `|j, g⟩ = Σ_a √C(n,a) α^{n-a} β^a e_a` with `(α, β) = g e₀`, the binomial form.
* `inner_cohState`: **the overlap** `⟨j, g | j, h⟩ = ((gᴴ h)₀₀)^{2j}`, and `normSq_inner_cohState`:
  `|⟨j, g | j, h⟩|² = ((1 + ν(g)·ν(h))/2)^{2j}`.
* `resolution_cohState`: **resolution of the identity** `(2j+1) ∫ |j,g⟩⟨j,g| dg = 1`.
* Spin(4): `cohState4 n m (g₊, g₋) = |j₊, g₊⟩ ⊗ |j₋, g₋⟩`, with `inner_cohState4` and
  `resolution_cohState4` (`(2j₊+1)(2j₋+1) ∫∫ |g₊,g₋⟩⟨g₊,g₋| = 1`).
* `eprlMap_cohState`: **the EPRL map sends coherent states to coherent states**:
  `Y |j, g⟩ = |j₊, g⟩ ⊗ |j₋, g⟩`.

## References

* A. Perelomov, *Generalized Coherent States and Their Applications*, Springer (1986), Ch. 4.
* E. R. Livine, S. Speziale, *A new spinfoam vertex for quantum gravity*, Phys. Rev. D 76 (2007)
  084028, arXiv:0705.0674.
-/

open Matrix MeasureTheory Finset
open scoped Kronecker

namespace Lightlike.Spin4

open SU2

variable {n m : ℕ}

/-! ## A. The coherent states -/

/-- **The Perelomov coherent state** `|j, g⟩ = D^j(g) e₀` of spin `j = n/2`. -/
noncomputable def cohState (n : ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) : Fin (n + 1) → ℂ :=
  spinMat n g *ᵥ Pi.single 0 1

lemma downs_ne_zero {t : Str n} (ht : t ≠ fun _ => 0) : downs t ≠ 0 := by
  intro h
  apply ht
  funext i
  have hi : i ∉ univ.filter fun i => t i = 1 := by
    rw [Finset.card_eq_zero.mp h]; exact Finset.notMem_empty i
  simp only [mem_filter, mem_univ, true_and] at hi
  rcases Fin.exists_fin_two.mp ⟨t i, rfl⟩ with h0 | h1
  · exact h0
  · exact absurd h1 hi

/-- **The first column of a spin matrix**: `D^j(g)_{a0} = √C(n,a) g₀₀^{n-a} g₁₀^a`. -/
theorem spinMat_apply_zero (g : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin (n + 1)) :
    spinMat n g a 0 = (Real.sqrt (n.choose a) : ℂ) * g 0 0 ^ (n - a) * g 1 0 ^ (a : ℕ) := by
  have ha : (a : ℕ) ≤ n := Nat.lt_succ_iff.mp a.2
  rw [spinMat, mul_apply, sum_eq_single (fun _ => (0 : Fin 2))]
  · rw [mul_apply]
    have hkey : ∀ s : Str n, (emb n)ᴴ a s * kron n g s (fun _ => 0) =
        if s ∈ cls n a then nrm n a * (g 0 0 ^ (n - a) * g 1 0 ^ (a : ℕ)) else 0 := by
      intro s
      rw [conjTranspose_apply, emb_apply, kron_apply, prod_fin_two (fun x => g x 0) s]
      by_cases h : downs s = a
      · simp [cls, h, star_nrm]
      · simp [cls, h]
    have hemb : emb n (fun _ => (0 : Fin 2)) 0 = nrm n 0 := by
      rw [emb_apply]; simp [downs]
    simp only [hkey, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, hemb]
    have hC : (0 : ℝ) ≤ n.choose a := Nat.cast_nonneg _
    have hCpos : (0 : ℝ) < Real.sqrt (n.choose a) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos ha)
    have hc : (clsCard n a : ℂ) * nrm n a = (Real.sqrt (n.choose a) : ℂ) := by
      rw [nrm, clsCard_eq_choose]
      have hsq : ((n.choose a : ℕ) : ℂ) =
          (Real.sqrt (n.choose a) : ℂ) * (Real.sqrt (n.choose a) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hC]; push_cast; rfl
      rw [hsq]
      have hne : (Real.sqrt (n.choose a) : ℂ) ≠ 0 := by exact_mod_cast hCpos.ne'
      push_cast
      field_simp
    have h0 : nrm n 0 = 1 := by simp [nrm, clsCard_eq_choose]
    rw [h0, mul_one, show (cls n a).card = clsCard n a from rfl, ← mul_assoc, hc]
    ring
  · intro t _ ht
    rw [emb_apply]
    simp [downs_ne_zero ht]
  · simp

/-- **The binomial form** `|j, g⟩ = Σ_a √C(n,a) α^{n-a} β^a e_a`, `(α, β) = g e₀`. -/
theorem cohState_apply (g : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin (n + 1)) :
    cohState n g a = (Real.sqrt (n.choose a) : ℂ) * g 0 0 ^ (n - a) * g 1 0 ^ (a : ℕ) := by
  rw [cohState, mulVec_single_one, ← spinMat_apply_zero]
  rfl

/-- The coherent state of `g = 1` is the highest weight state. -/
lemma cohState_one : cohState n 1 = Pi.single 0 1 := by
  rw [cohState, spinMat_one, one_mulVec]

/-- The highest entry of a spin matrix: `D^j(g)₀₀ = (g₀₀)^{2j}`. -/
lemma spinMat_zero_zero (g : Matrix (Fin 2) (Fin 2) ℂ) : spinMat n g 0 0 = g 0 0 ^ n := by
  rw [spinMat_apply_zero]
  simp

/-- **The overlap of coherent states**: `⟨j, g | j, h⟩ = ((gᴴ h)₀₀)^{2j}`. -/
theorem inner_cohState (g h : Matrix (Fin 2) (Fin 2) ℂ) :
    star (cohState n g) ⬝ᵥ cohState n h = ((gᴴ * h) 0 0) ^ n := by
  rw [cohState, cohState, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    spinMat_conjTranspose, ← spinMat_mul, mulVec_single_one, ← spinMat_zero_zero]
  simp [dotProduct, Pi.single_apply]

/-- The coherent states are unit vectors. -/
theorem inner_cohState_self (g : SU2) : star (cohState n g) ⬝ᵥ cohState n g = 1 := by
  rw [inner_cohState]
  have hu : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  rw [hu]
  simp

/-- **The Bloch vector** `ν(g) = g e_z g⁻¹` of `g ∈ SU(2)`, from its first column `(α, β)`:
`ν = (2 Re(ᾱβ), 2 Im(ᾱβ), |α|² - |β|²)`. -/
noncomputable def bloch (g : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![2 * (star (g 0 0) * g 1 0).re, 2 * (star (g 0 0) * g 1 0).im,
    Complex.normSq (g 0 0) - Complex.normSq (g 1 0)]

/-- The first column of an element of SU(2) is a unit vector. -/
lemma normSq_col (g : SU2) :
    Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
      Complex.normSq ((g : Matrix (Fin 2) (Fin 2) ℂ) 1 0) = 1 := by
  have hu : ((g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * g = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  have h := congrFun (congrFun hu 0) 0
  simp only [mul_apply, Fin.sum_univ_two, conjTranspose_apply, one_apply_eq] at h
  have h' := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.star_def,
    mul_comm ((starRingEnd ℂ) _), Complex.mul_conj, Complex.ofReal_re] at h'
  exact h'

/-- **The overlap in terms of the normals**: `|(gᴴ h)₀₀|² = (1 + ν(g)·ν(h))/2`. -/
theorem normSq_overlap (g h : SU2) :
    Complex.normSq (((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * h) 0 0) =
      (1 + bloch g ⬝ᵥ bloch h) / 2 := by
  have hg := normSq_col g
  have hh := normSq_col h
  set α := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set β := (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  set α' := (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  set β' := (h : Matrix (Fin 2) (Fin 2) ℂ) 1 0
  have e : ((g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * h) 0 0 = star α * α' + star β * β' := by
    simp [mul_apply, Fin.sum_univ_two, α, β, α', β']
  rw [e, bloch, bloch]
  simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im] at hg hh ⊢
  linear_combination
    (1 / 2 * (α'.re * α'.re + α'.im * α'.im + (β'.re * β'.re + β'.im * β'.im))) * hg
    + (1 / 2) * hh

/-- **Overlap of coherent states in terms of the normals**:
`|⟨j, g | j, h⟩|² = ((1 + ν(g)·ν(h))/2)^{2j}`. -/
theorem normSq_inner_cohState (g h : SU2) :
    Complex.normSq (star (cohState n g) ⬝ᵥ cohState n h) = ((1 + bloch g ⬝ᵥ bloch h) / 2) ^ n := by
  rw [inner_cohState, map_pow, normSq_overlap]

/-- The projector onto the highest weight state. -/
lemma vecMulVec_cohState (g : Matrix (Fin 2) (Fin 2) ℂ) :
    vecMulVec (cohState n g) (star (cohState n g)) =
      spinMat n g * vecMulVec (Pi.single 0 1 : Fin (n + 1) → ℂ) (star (Pi.single 0 1)) *
        (spinMat n g)ᴴ := by
  ext i j
  simp [vecMulVec_apply, cohState, mul_apply, Pi.single_apply, conjTranspose_apply]

/-- **Resolution of the identity**: `(2j+1) ∫ |j, g⟩⟨j, g| dg = 1`. -/
theorem resolution_cohState (n : ℕ) :
    ((n : ℂ) + 1) • matInt (fun g : SU2 => vecMulVec (cohState n g) (star (cohState n g))) = 1 := by
  simp only [vecMulVec_cohState]
  rw [matInt_spinMat_conj, smul_smul]
  have htr : trace (vecMulVec (Pi.single 0 1 : Fin (n + 1) → ℂ) (star (Pi.single 0 1))) = 1 := by
    simp [trace, vecMulVec_apply, Pi.single_apply]
  rw [htr]
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_one_div_cancel hn, one_smul]

/-! ## B. Spin(4) coherent states and the EPRL map -/

/-- **The Spin(4) coherent state** `|j₊, g₊⟩ ⊗ |j₋, g₋⟩` of `(g₊, g₋) ∈ Spin(4)`. -/
noncomputable def cohState4 (n m : ℕ) (g : Spin4) : Idx n m → ℂ :=
  fun p => cohState n g.1 p.1 * cohState m g.2 p.2

/-- The normalised Haar measure of `Spin(4) = SU(2) × SU(2)`. -/
noncomputable def haarSpin4 : Measure Spin4 := haarSU2.prod haarSU2

/-- The Spin(4) coherent states are the image of the highest weight state. -/
theorem cohState4_eq (g : Spin4) :
    cohState4 n m g = spin4Mat n m g *ᵥ fun p => (Pi.single 0 1 : Fin (n + 1) → ℂ) p.1 *
      (Pi.single 0 1 : Fin (m + 1) → ℂ) p.2 := by
  rw [spin4Mat, kronecker_mulVec_prod]
  rfl

/-- **Overlap of Spin(4) coherent states**: the product of the two SU(2) overlaps. -/
theorem inner_cohState4 (g h : Spin4) :
    star (cohState4 n m g) ⬝ᵥ cohState4 n m h =
      ((((g.1 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * h.1) 0 0) ^ n *
        ((((g.2 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * h.2) 0 0) ^ m := by
  rw [← inner_cohState, ← inner_cohState]
  simp only [cohState4, dotProduct, Pi.star_apply, star_mul', Fintype.sum_prod_type,
    Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Resolution of the identity for Spin(4)**:
`(2j₊+1)(2j₋+1) ∫ |g₊, g₋⟩⟨g₊, g₋| dg₊ dg₋ = 1`. -/
theorem resolution_cohState4 (n m : ℕ) :
    (((n : ℂ) + 1) * ((m : ℂ) + 1)) •
      (Matrix.of fun p q => ∫ g, vecMulVec (cohState4 n m g) (star (cohState4 n m g)) p q
        ∂haarSpin4) = (1 : Matrix (Idx n m) (Idx n m) ℂ) := by
  have h : (Matrix.of fun p q => ∫ g, vecMulVec (cohState4 n m g) (star (cohState4 n m g)) p q
      ∂haarSpin4) = matInt (fun g : SU2 => vecMulVec (cohState n g) (star (cohState n g))) ⊗ₖ
        matInt (fun g : SU2 => vecMulVec (cohState m g) (star (cohState m g))) := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [of_apply, kroneckerMap_apply, matInt_apply, vecMulVec_apply, cohState4,
      Pi.star_apply, star_mul', haarSpin4]
    rw [← integral_prod_mul (fun g : SU2 => cohState n g a * star (cohState n g c))
      (fun g : SU2 => cohState m g b * star (cohState m g d))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp only; ring)
  have hs : (((n : ℂ) + 1) * ((m : ℂ) + 1)) •
      (matInt (fun g : SU2 => vecMulVec (cohState n g) (star (cohState n g))) ⊗ₖ
        matInt (fun g : SU2 => vecMulVec (cohState m g) (star (cohState m g)))) =
      (((n : ℂ) + 1) • matInt (fun g : SU2 => vecMulVec (cohState n g) (star (cohState n g)))) ⊗ₖ
        (((m : ℂ) + 1) •
          matInt (fun g : SU2 => vecMulVec (cohState m g) (star (cohState m g)))) := by
    rw [smul_kronecker, kronecker_smul, smul_smul]
  rw [h, hs, resolution_cohState, resolution_cohState, one_kronecker_one]

/-- The EPRL map sends the highest weight state to the product of highest weight states. -/
lemma eprlMap_mulVec_single :
    eprlMap n m *ᵥ (Pi.single 0 1 : Fin (n + m + 1) → ℂ) =
      fun p => (Pi.single 0 1 : Fin (n + 1) → ℂ) p.1 * (Pi.single 0 1 : Fin (m + 1) → ℂ) p.2 := by
  funext ⟨a, b⟩
  rw [mulVec_single_one, Matrix.col_apply, eprlMap_apply]
  by_cases h : (a : ℕ) + b = ((0 : Fin (n + m + 1)) : ℕ)
  · have ha : a = 0 := Fin.ext (by simp at h; omega)
    have hb : b = 0 := Fin.ext (by simp at h; omega)
    subst ha hb
    simp
  · rw [ite_eq_right h]
    have : ¬ (a = 0 ∧ b = 0) := fun ⟨ha, hb⟩ => h (by simp [ha, hb])
    by_cases ha : a = 0
    · have hb : b ≠ 0 := fun hb => this ⟨ha, hb⟩
      simp [ha, hb]
    · simp [ha]

/-- **The EPRL map sends coherent states to coherent states**: `Y |j, g⟩ = |j₊, g⟩ ⊗ |j₋, g⟩`. -/
theorem eprlMap_cohState (g : SU2) :
    eprlMap n m *ᵥ cohState (n + m) g = cohState4 n m (g, g) := by
  rw [cohState, mulVec_mulVec, ← eprlMap_equivariant, ← mulVec_mulVec, eprlMap_mulVec_single,
    kronecker_mulVec_prod]
  rfl

end Lightlike.Spin4
