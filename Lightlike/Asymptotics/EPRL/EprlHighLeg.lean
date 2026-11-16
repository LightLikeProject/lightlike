import Lightlike.Asymptotics.EPRL.EprlHighMap
import Lightlike.Asymptotics.EPRL.Amplitude

/-!
# The leg amplitude of the lowest Clebsch–Gordan component

For `γ > 1` the amplitude `(⟨n, M| ⊗ ⟨m, M'|) Y_low |k, g⟩` of the lowest component `k = n - m` on
coherent states is, up to a Clebsch–Gordan constant `c₀ = Y_low[(0, m), 0]`, the product
`(-1)^m c₀ ⟨M|g⟩^k ⟨M|J M'⟩^m` (`eprlMapLow_cohState`). The minus sector enters through the structure
map `J`, which makes the amplitude invariant under the phase of `M` and of `M'`: BDFGH eq. (19) is
written in a convention that absorbs this phase. The proof is by weight conservation of an
equivariant map (`weight_of_equivariant`) and the `SU(2)` covariance of `Y_low` (`legAmp_mul`), which
reduces the general amplitude to `M = 1`, where a single entry of `Y_low` survives.
The constant `c₀` is kept abstract; its positivity and its value `√((k+1)/(n+1))` are not proved here.
Numerically `c₀ = √((k+1)/(n+1))` (`scripts/spinfoam/eprl_high_check.py`, check (0)).

## Main results

* `weight_of_equivariant`: an `SU(2)`-equivariant map `V_k → V_n ⊗ V_m` conserves the weights.
* `c0Low`: the Clebsch–Gordan entry `Y_low[(0, m), 0]`.
* `legAmp`, `legAmp_mul`: the leg amplitude and its invariance under simultaneous left multiplication.
* `eprlMapLow_cohState_one`: the amplitude at `M = 1`.
* `eprlMapLow_cohState`: the closed form for general `M, M', g`.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, Section 3.4, eqs. (17)–(19).
-/

open Matrix Finset
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam

/-- **Weight conservation for an equivariant map**: an `SU(2)`-equivariant map
`V_k → V_n ⊗ V_m` has `Y((a, b), c) = 0` unless the weights agree, `(n - 2a) + (m - 2b) = k - 2c`. -/
theorem weight_of_equivariant {n m k : ℕ} (Y : Matrix (Idx n m) (Fin (k + 1)) ℂ)
    (hY : ∀ g : SU2, (spinMat n (g : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ spinMat m (g : Matrix (Fin 2) (Fin 2) ℂ)) * Y =
      Y * spinMat k (g : Matrix (Fin 2) (Fin 2) ℂ)) (a : Fin (n + 1)) (b : Fin (m + 1))
    (c : Fin (k + 1))
    (h : ((n : ℤ) - 2 * (a : ℕ)) + ((m : ℤ) - 2 * (b : ℕ)) ≠ (k : ℤ) - 2 * (c : ℕ)) : Y (a, b) c = 0 := by
  set W : ℝ := ((((n : ℤ) - 2 * (a : ℕ)) + ((m : ℤ) - 2 * (b : ℕ)) - ((k : ℤ) - 2 * (c : ℕ)) : ℤ) : ℝ) with hW
  have hWne : W ≠ 0 := by
    intro h0; apply h
    have := (Int.cast_eq_zero (α := ℝ)).mp h0
    omega
  set θ : ℝ := Real.pi / W with hθ
  have hz : Complex.exp (θ * Complex.I) * star (Complex.exp (θ * Complex.I)) = 1 := by
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]; simp [Complex.conj_ofReal]
  have h1 := congrFun (congrFun (hY (torus (Complex.exp (θ * Complex.I)) hz)) (a, b)) c
  have hn := spinMat_torus_exp (n := n) θ
  have hm := spinMat_torus_exp (n := m) θ
  have hk := spinMat_torus_exp (n := k) θ
  simp only [hn, hm, hk, Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    Matrix.diagonal_apply] at h1
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h1
  set E1 := Complex.exp ((((n : ℝ) - 2 * (a : ℕ)) * θ : ℝ) * Complex.I)
  set E2 := Complex.exp ((((m : ℝ) - 2 * (b : ℕ)) * θ : ℝ) * Complex.I)
  set E3 := Complex.exp ((((k : ℝ) - 2 * (c : ℕ)) * θ : ℝ) * Complex.I)
  have hexp : E1 * E2 = -E3 := by
    have : E1 * E2 = Complex.exp (((((n : ℝ) - 2 * (a : ℕ)) * θ : ℝ) * Complex.I) +
        ((((m : ℝ) - 2 * (b : ℕ)) * θ : ℝ) * Complex.I)) := (Complex.exp_add _ _).symm
    rw [this]
    have h3 : ((((n : ℝ) - 2 * (a : ℕ)) * θ : ℝ) * Complex.I) +
        ((((m : ℝ) - 2 * (b : ℕ)) * θ : ℝ) * Complex.I) =
        ((((k : ℝ) - 2 * (c : ℕ)) * θ : ℝ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      have hWθ : W * θ = Real.pi := by rw [hθ]; field_simp
      have hW' : W = ((n : ℝ) - 2 * (a : ℕ)) + ((m : ℝ) - 2 * (b : ℕ)) - ((k : ℝ) - 2 * (c : ℕ)) := by
        rw [hW]; push_cast; ring
      rw [hW'] at hWθ
      have hc : ((((n : ℝ) - 2 * (a : ℕ)) + ((m : ℝ) - 2 * (b : ℕ)) - ((k : ℝ) - 2 * (c : ℕ))) * θ : ℝ) =
          Real.pi := hWθ
      have hcC : ((((((n : ℝ) - 2 * (a : ℕ)) + ((m : ℝ) - 2 * (b : ℕ)) - ((k : ℝ) - 2 * (c : ℕ))) * θ :
          ℝ)) : ℂ) = (Real.pi : ℂ) := by rw [hc]
      push_cast at hcC ⊢
      linear_combination (Complex.I) * hcC
    rw [h3, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have h2 : (E1 * E2) * Y (a, b) c = Y (a, b) c * E3 := by
    rw [← h1]
  rw [hexp] at h2
  have h4 : (2 : ℂ) * E3 * Y (a, b) c = 0 := by linear_combination (-1 : ℂ) * h2
  have hE3 : E3 ≠ 0 := Complex.exp_ne_zero _
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exact absurd h5 (mul_ne_zero two_ne_zero hE3)
  · exact h5


/-- The Clebsch–Gordan constant of the lowest component: the entry `Y_low[(0, m), 0]`. -/
noncomputable def c0Low (n m : ℕ) : ℂ := eprlMapLow n m (0, Fin.last m) 0

/-- **The leg amplitude at `M = 1`**: `(⟨n, 1| ⊗ ⟨m, M'|) Y_low |k, g⟩ = (-1)^m c₀ g₀₀^k ((M' ε)₀₀)^m`. -/
theorem eprlMapLow_cohState_one {n m : ℕ} (h : m ≤ n) (M' g : SU2) :
    ∑ p : Idx n m, star (cohState n (1 : Matrix (Fin 2) (Fin 2) ℂ) p.1) *
        star (cohState m (M' : Matrix (Fin 2) (Fin 2) ℂ) p.2) *
        (eprlMapLow n m *ᵥ cohState (n - m) (g : Matrix (Fin 2) (Fin 2) ℂ)) p =
      (-1 : ℂ) ^ m * c0Low n m * ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ (n - m) *
        (((M' : Matrix (Fin 2) (Fin 2) ℂ) * epsMat) 0 0) ^ m := by
  have hw := fun a b c => weight_of_equivariant (eprlMapLow n m)
    (fun g => eprlMapLow_equivariant h g) a b c
  have hM'01 : ((M' : Matrix (Fin 2) (Fin 2) ℂ) * epsMat) 0 0 =
      -star ((M' : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
    obtain ⟨-, h01, -⟩ := su2_entries M'
    simp [Matrix.mul_apply, Fin.sum_univ_two, epsMat, h01]
  rw [hM'01, Fintype.sum_prod_type, Finset.sum_eq_single (0 : Fin (n + 1))]
  · rw [Finset.sum_eq_single (Fin.last m)]
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (0 : Fin (n - m + 1))]
      · simp only [cohState_apply, c0Low]
        simp
        have hsq : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; simp
        rw [neg_pow]
        linear_combination (-((starRingEnd ℂ) ((M' : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ^ m *
          eprlMapLow n m (0, Fin.last m) 0 * ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ (n - m))) * hsq
      · intro c _ hc
        have hc0 : (c : ℕ) ≠ 0 := fun h0 => hc (Fin.ext h0)
        have h0 : eprlMapLow n m (0, Fin.last m) c = 0 := by
          refine hw 0 (Fin.last m) c ?_
          simp only [Fin.val_zero, Fin.val_last]
          have : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := by omega
          omega
        rw [h0]; simp
      · intro hc; exact absurd (Finset.mem_univ _) hc
    · intro b _ hb
      have hb0 : (b : ℕ) ≠ m := fun h0 => hb (Fin.ext (by simpa using h0))
      have hbm := b.isLt
      have h0 : ∀ c : Fin (n - m + 1), eprlMapLow n m (0, b) c = 0 := fun c => by
        refine hw 0 b c ?_
        simp only [Fin.val_zero]
        have : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := by omega
        have hc := c.isLt
        omega
      simp [Matrix.mulVec, dotProduct, h0]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  · intro a _ ha
    simp [cohState_one, Pi.single_apply, ha]
  · intro ha; exact absurd (Finset.mem_univ _) ha


/-- The leg amplitude `(⟨n, M| ⊗ ⟨m, M'|) Y_low |k, g⟩` of coherent states of matrices `M, M', g`. -/
noncomputable def legAmp (n m : ℕ) (M M' g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ p : Idx n m, star (cohState n M p.1) * star (cohState m M' p.2) *
    (eprlMapLow n m *ᵥ cohState (n - m) g) p

/-- **The leg amplitude is invariant under simultaneous left multiplication** by an `SU(2)` element
(covariance of `Y_low`). -/
theorem legAmp_mul {n m : ℕ} (h : m ≤ n) (u M M' g : SU2) :
    legAmp n m ((u * M : SU2) : Matrix (Fin 2) (Fin 2) ℂ) ((u * M' : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
        ((u * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      legAmp n m (M : Matrix (Fin 2) (Fin 2) ℂ) (M' : Matrix (Fin 2) (Fin 2) ℂ) (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hc : ∀ (j : ℕ) (A B : SU2), cohState j (((A * B : SU2)) : Matrix (Fin 2) (Fin 2) ℂ) =
      spinMat j (A : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ cohState j (B : Matrix (Fin 2) (Fin 2) ℂ) := fun j A B => by
    simp only [cohState, mulVec_mulVec, ← spinMat_mul]
    rfl
  have hU : (spinMat n (u : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ))ᴴ *
      (spinMat n (u : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, spinMat_conjTranspose_mul_self,
      spinMat_conjTranspose_mul_self, Matrix.one_kronecker_one]
  have hE := eprlMapLow_equivariant h u
  unfold legAmp
  rw [hc n, hc m, hc (n - m)]
  have hvec : (fun p : Idx n m => star ((spinMat n (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ cohState n (M : Matrix (Fin 2) (Fin 2) ℂ)) p.1) *
      star ((spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ cohState m (M' : Matrix (Fin 2) (Fin 2) ℂ)) p.2)) =
      star ((spinMat n (u : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ)) *ᵥ
        (fun p : Idx n m => cohState n (M : Matrix (Fin 2) (Fin 2) ℂ) p.1 *
          cohState m (M' : Matrix (Fin 2) (Fin 2) ℂ) p.2)) := by
    rw [kronecker_mulVec_prod]
    funext p
    simp [Pi.star_apply, star_mul']
  set U := spinMat n (u : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ) with hUdef
  set x : Idx n m → ℂ := fun p => cohState n (M : Matrix (Fin 2) (Fin 2) ℂ) p.1 *
    cohState m (M' : Matrix (Fin 2) (Fin 2) ℂ) p.2 with hx
  set y := eprlMapLow n m *ᵥ cohState (n - m) (g : Matrix (Fin 2) (Fin 2) ℂ) with hy
  have hY : eprlMapLow n m *ᵥ (spinMat (n - m) (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
      cohState (n - m) (g : Matrix (Fin 2) (Fin 2) ℂ)) = U *ᵥ y := by
    rw [hy, mulVec_mulVec, mulVec_mulVec, ← hE]
  have hl : ∀ (a b : Idx n m → ℂ), (∑ p, a p * b p) = a ⬝ᵥ b := fun a b => rfl
  have hr : (∑ p : Idx n m, star (cohState n (M : Matrix (Fin 2) (Fin 2) ℂ) p.1) *
      star (cohState m (M' : Matrix (Fin 2) (Fin 2) ℂ) p.2) * y p) = star x ⬝ᵥ y := by
    simp only [dotProduct, hx, Pi.star_apply, star_mul']
  have hl' : (∑ p : Idx n m, star ((spinMat n (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ cohState n (M : Matrix (Fin 2) (Fin 2) ℂ)) p.1) *
      star ((spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ cohState m (M' : Matrix (Fin 2) (Fin 2) ℂ)) p.2) *
      (eprlMapLow n m *ᵥ (spinMat (n - m) (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
        cohState (n - m) (g : Matrix (Fin 2) (Fin 2) ℂ))) p) = star (U *ᵥ x) ⬝ᵥ (U *ᵥ y) := by
    rw [hY]
    have := congrFun hvec
    simp only [dotProduct, Pi.star_apply] at this ⊢
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← this p]
  rw [hl', hr]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]


/-- **The leg amplitude for `γ > 1`** (BDFGH eq. (17), up to the Clebsch–Gordan constant `c₀`):
`(⟨n, M| ⊗ ⟨m, M'|) Y_low |k, g⟩ = (-1)^m c₀ ⟨M|g⟩^k ⟨M|J M'⟩^m` with `k = n - m`, where
`⟨M|g⟩ = (M† g)₀₀` and `⟨M|J M'⟩ = (M† (M' ε))₀₀` (`J M'` is the first column of `M' ε`). The minus
sector enters through the structure map `J`, which makes the amplitude invariant under the phase of `M`
and of `M'`. -/
theorem eprlMapLow_cohState {n m : ℕ} (h : m ≤ n) (M M' g : SU2) :
    legAmp n m (M : Matrix (Fin 2) (Fin 2) ℂ) (M' : Matrix (Fin 2) (Fin 2) ℂ)
        (g : Matrix (Fin 2) (Fin 2) ℂ) =
      (-1 : ℂ) ^ m * c0Low n m *
        ((((M : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (g : Matrix (Fin 2) (Fin 2) ℂ)) 0 0) ^ (n - m) *
        ((((M : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * ((M' : Matrix (Fin 2) (Fin 2) ℂ) * epsMat)) 0 0) ^ m := by
  have h1 := legAmp_mul h (star M) M M' g
  have hM : ((star M * M : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have hu : ((M : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (M : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp (Matrix.specialUnitaryGroup_le_unitaryGroup M.2)
    simpa [Matrix.star_eq_conjTranspose] using hu
  rw [hM] at h1
  rw [← h1]
  have h2 := eprlMapLow_cohState_one h (star M * M') (star M * g)
  have hcoe : ∀ A : SU2, ((star M * A : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (M : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * (A : Matrix (Fin 2) (Fin 2) ℂ) := fun A => by
    simp [Matrix.star_eq_conjTranspose]
  rw [hcoe, hcoe] at h2
  rw [Matrix.mul_assoc] at h2
  exact h2

end Lightlike.Asymptotics.EPRL
