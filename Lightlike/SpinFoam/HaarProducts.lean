import Lightlike.SpinFoam.GroupIntegral
import Lightlike.Spin4.SpinSchur
import Lightlike.Spin4.CoherentIntertwiner

/-!
# Haar integrals of products of characters of `SU(2)`

Schur orthogonality of the spin-`n/2` characters and the integrals of products of characters that
the cut-off Ponzano–Regge sum needs (`Lightlike.SpinFoam.partitionN`); see Serre, *Linear
Representations of Finite Groups* (1977), §2.3, and Fulton–Harris, *Representation Theory* (1991),
Lecture 1, for the orthogonality of characters.

## Main results

* `matInt_spinMat_cross`: for `n ≠ m`, `∫ D^{n/2}(g) A D^{m/2}(g)ᴴ dg = 0` for every matrix `A`
  (Schur's lemma for different spins and left invariance of the Haar measure).
* `integral_spinChar_mul_star`: `∫ χ_n(g) conj χ_m(g) dg = δ_{nm}`.
* `integral_prod_spinChar`: `∫ Π_a χ_{J_a}(g) dg = tr P`, where `P = ∫ ⊗_a D^{J_a/2}(g) dg` is the
  projection onto the invariant vectors of `⊗_a V_{J_a/2}` (`avgP`).
* `sphereCx`, `partitionN_sphere`: two faces glued along one edge loop with opposite orientations
  (the 2-sphere) give `Σ_{n ≤ N} (n+1)²` at cut-off `N`, so the cut-off cannot be removed, while a
  single face on the loop gives `1` (`partitionN_loop`).
-/

open Matrix MeasureTheory Finset Lightlike.SU2 Lightlike.Spin4

namespace Lightlike.SpinFoam

/-- **Schur orthogonality for different spins**, matrix form. -/
theorem matInt_spinMat_cross {n m : ℕ} (hnm : n ≠ m) (A : Matrix (Fin (n + 1)) (Fin (m + 1)) ℂ) :
    matInt (fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) * A *
      (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) = 0 := by
  set M := matInt (fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) * A *
    (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) with hM
  have hcont : ∀ k l, Continuous fun g : SU2 =>
      (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) * A *
        (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) k l := by
    intro k l
    simp only [mul_apply, conjTranspose_apply]
    refine continuous_finsetSum _ fun b _ => ?_
    refine Continuous.mul ?_ (continuous_star.comp (continuous_spinMat_apply m l b))
    exact continuous_finsetSum _ fun a _ =>
      (continuous_spinMat_apply n k a).mul continuous_const
  have hunit : ∀ h : SU2, (spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
      spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ) = 1 := fun h =>
    Matrix.mem_unitaryGroup_iff'.mp (spinMat_mem_unitaryGroup
      (Matrix.specialUnitaryGroup_le_unitaryGroup h.2))
  have hinv : ∀ h : SU2, spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ) * M =
      M * spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro h
    have hconj : spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ) * M *
        (spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ))ᴴ = M := by
      have e1 := (matInt_mul_mul (spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ))
        (fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) * A *
          (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ)
        (spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ))ᴴ hcont).symm
      have e2 : (fun g : SU2 => spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ) *
          (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) * A *
            (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) *
          (spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) =
          fun g : SU2 => spinMat n ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) * A *
            (spinMat m ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ := by
        funext g
        have hc : ((h * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
            (h : Matrix (Fin 2) (Fin 2) ℂ) * g := rfl
        rw [hc, spinMat_mul, spinMat_mul, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      rw [hM, e1, e2]
      exact matInt_mul_left (fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) * A *
        (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) h
    calc spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ) * M
        = spinMat n (h : Matrix (Fin 2) (Fin 2) ℂ) * M *
            ((spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
              spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ)) := by rw [hunit, Matrix.mul_one]
      _ = M * spinMat m (h : Matrix (Fin 2) (Fin 2) ℂ) := by rw [← Matrix.mul_assoc, hconj]
  exact spin_intertwiner_eq_zero (N := m) (M := n) (Ne.symm hnm) hinv

/-- **Orthogonality of the characters**: `∫ χ_n conj χ_m dg = δ_{nm}`. -/
theorem integral_spinChar_mul_star (n m : ℕ) :
    ∫ g, spinChar n g * star (spinChar m g) ∂haarSU2 = if n = m then 1 else 0 := by
  have hexp : ∀ g : SU2, spinChar n g * star (spinChar m g) =
      ∑ i : Fin (n + 1), ∑ j : Fin (m + 1),
        spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) i i *
          star (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ) j j) := by
    intro g
    simp only [spinChar, trace, Matrix.diag, star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hint : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), Integrable (fun g : SU2 =>
      spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) i i *
        star (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ) j j)) haarSU2 := fun i j =>
    integrable_of_continuous ((continuous_spinMat_apply n i i).mul
      (continuous_star.comp (continuous_spinMat_apply m j j)))
  have hentry : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), ∫ g : SU2,
      spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) i i *
        star (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ) j j) ∂haarSU2 =
      matInt (fun g : SU2 => spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) *
        (Matrix.single i j (1 : ℂ)) * (spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) i j := by
    intro i j
    rw [matInt_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [mul_apply, conjTranspose_apply, Matrix.single_apply, ite_and, ite_mul, Finset.sum_ite_eq]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, hentry]
  by_cases hnm : n = m
  · subst hnm
    simp_rw [matInt_spinMat_conj]
    simp [Matrix.single_apply, Matrix.one_apply, Finset.sum_ite_eq, trace]
    have h1 : ∀ x : Fin (n + 1), ((Finset.univ.filter fun x_1 => x = x_1).card : ℂ) = 1 := by
      intro x
      have : Finset.univ.filter (fun x_1 : Fin (n + 1) => x = x_1) = {x} := by
        ext y; simp [eq_comm]
      rw [this]; simp
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · simp_rw [matInt_spinMat_cross hnm]
    simp [hnm]

lemma spinChar_inv (n : ℕ) (g : SU2) : spinChar n g⁻¹ = star (spinChar n g) := by
  unfold spinChar
  have : ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := rfl
  rw [this, ← spinMat_conjTranspose, trace_conjTranspose]

/-- The complex of the 2-sphere: one edge loop with two faces glued to it with opposite
orientations. -/
def sphereCx : Cell2 Unit Unit Bool where
  src _ := ()
  tgt _ := ()
  bdry b := [((), b)]

/-- **The sphere does not converge.** The cut-off partition function of the 2-sphere is
`Σ_{n ≤ N} (n+1)²`, unbounded in `N`; the single face on the loop gives `1` (`partitionN_loop`).
This matches `H² ≠ 0` for the sphere (`sphere_su2_H2_nontrivial`). -/
theorem partitionN_sphere (N : ℕ) :
    partitionN sphereCx N = ∑ n ∈ range (N + 1), ((n : ℂ) + 1) ^ 2 := by
  unfold partitionN
  have h : ∀ g : Unit → SU2, ∏ f : Bool, truncDelta N (hol g (sphereCx.bdry f)) =
      truncDelta N (g ()) * truncDelta N (g ())⁻¹ := by
    intro g; simp [sphereCx, hol, lh]
  simp_rw [h]
  rw [integral_haarE_unit (fun x => truncDelta N x * truncDelta N x⁻¹)]
  have hexp : ∀ x : SU2, truncDelta N x * truncDelta N x⁻¹ =
      ∑ n ∈ range (N + 1), ∑ m ∈ range (N + 1),
        ((n : ℂ) + 1) * ((m : ℂ) + 1) * (spinChar n x * star (spinChar m x)) := by
    intro x
    unfold truncDelta
    simp_rw [spinChar_inv]
    rw [Finset.sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun m _ => ?_
    ring
  have hint : ∀ n m : ℕ, Integrable (fun x : SU2 =>
      ((n : ℂ) + 1) * ((m : ℂ) + 1) * (spinChar n x * star (spinChar m x))) haarSU2 := fun n m =>
    integrable_of_continuous (continuous_const.mul ((continuous_spinChar n).mul
      (continuous_star.comp (continuous_spinChar m))))
  simp_rw [hexp]
  rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m]
  refine sum_congr rfl fun n hn => ?_
  rw [integral_finsetSum _ fun m _ => hint n m]
  simp_rw [integral_const_mul, integral_spinChar_mul_star]
  rw [Finset.sum_eq_single n]
  · simp [sq]
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd hn h

/-- The sphere and the single loop already differ at cut-off `1` (`5` against `1`). -/
theorem partitionN_loop_ne_sphere : partitionN loopCx 1 ≠ partitionN sphereCx 1 := by
  rw [partitionN_loop, partitionN_sphere]
  norm_num [Finset.sum_range_succ]

/-- The trace of the diagonal action is the product of the characters. -/
lemma trace_rhoN {N : ℕ} (J : Fin N → ℕ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (rhoN J g) = ∏ a, trace (spinMat (J a) g) := by
  simp only [trace, Matrix.diag, rhoN, Matrix.of_apply]
  rw [Finset.prod_univ_sum]
  rfl

/-- **The Haar integral of a product of characters is the trace of the invariant projection**:
`∫ Π_a χ_{J_a}(g) dg = tr P`, with `P = ∫ ⊗_a D^{J_a/2}(g) dg` (`avgP`) the orthogonal projection
onto the invariant vectors of `⊗_a V_{J_a/2}`. -/
theorem integral_prod_spinChar {N : ℕ} (J : Fin N → ℕ) :
    ∫ g, ∏ a, spinChar (J a) g ∂haarSU2 = trace (avgP J) := by
  unfold avgP
  rw [trace_matInt _ continuous_rhoN_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [spinChar, trace_rhoN]

/-- The one-factor case: `tr P` is the integral of one character, `δ_{n0}`. -/
theorem trace_avgP_single (n : ℕ) : trace (avgP (fun _ : Fin 1 => n)) = if n = 0 then 1 else 0 := by
  rw [← integral_prod_spinChar]
  simp [integral_spinChar]

end Lightlike.SpinFoam
