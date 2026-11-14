import Lightlike.SU2.LieBridge
import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorHighestWeight

/-!
# The ladder operators of the spin representations in coordinates

`SU2.dSpin n X` is the differential of the spin-`n/2` representation `SU2.spinMat n`. This file
computes its matrix for the standard basis `E = [[0,1],[0,0]]`, `F = [[0,0],[1,0]]`,
`H = diag(1,-1)` of `sl₂(ℂ)` in the basis `e_a` of `ℂ^{n+1}` (`a = 0, …, n`, the state
`|j, m⟩` with `j = n/2`, `m = j - a`):

* `E e_{a+1} = √((a+1)(n-a)) e_a` and `E e_0 = 0` (`dSpin_E_apply`),
* `F e_a = √((a+1)(n-a)) e_{a+1}` and `F e_n = 0` (`dSpin_F_apply`),
* `H e_a = (n - 2a) e_a` (`dSpin_H_apply`).

These are the textbook (Condon–Shortley) matrix elements `J₊ |j m⟩ = √((j-m)(j+m+1)) |j m+1⟩`,
`J₋ |j m⟩ = √((j+m)(j-m+1)) |j m-1⟩`, `2J_z |j m⟩ = 2m |j m⟩`, the same as those of Physlib's
normalised basis `normVec` (`PhyslibAlpha.Sl2.ρE_normVec_succ`, `ρF_normVec`, `ρH_normVec`). So
the basis `e_a` of the group representation `spinMat n` is Physlib's `|j, m⟩`, with the same
phases; `Lightlike/Spin4/CGBridge.lean` uses this to show that Physlib's Clebsch–Gordan coefficients
intertwine the group representations.

The proof goes through `SU2.Ψ`, which identifies Physlib's unnormalised basis `v_a` with
`a! √C(n,a) e_a`; for this we show that the number of strings of `n` up/down labels with `a` down
labels is `C(n, a)` (`clsCard_eq_choose`).

The quadratic Casimir `J_x² + J_y² + J_z² = ½(EF + FE) + ¼H²` is the scalar `(n/2)(n/2 + 1)`
(`casimir_eq`).

## References

* E. U. Condon, G. H. Shortley, *The Theory of Atomic Spectra*, Cambridge University Press
  (1935), Ch. III (the matrix elements of the angular momentum operators).
* J. J. Sakurai, J. Napolitano, *Modern Quantum Mechanics*, 2nd ed., Addison-Wesley (2011), §3.5
  (eigenvalues and eigenstates of angular momentum).
-/

open Matrix Finset PhyslibAlpha.Sl2
open scoped Kronecker

namespace Lightlike.Spin4

open SU2 PhyslibAlpha.Sl2.StandardSl2Module

variable {n : ℕ}

/-! ## A. Counting strings -/

/-- The strings of `n` labels with exactly `k` down labels are counted by `C(n, k)`. -/
theorem clsCard_eq_choose (n k : ℕ) : clsCard n k = n.choose k := by
  have hc : #(powersetCard k (univ : Finset (Fin n))) = n.choose k := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
  rw [clsCard, cls, ← hc]
  refine Finset.card_nbij' (fun s => univ.filter fun i => s i = 1)
    (fun S i => if i ∈ S then 1 else 0) ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_coe, mem_filter] at hs
    rw [mem_coe, mem_powersetCard]
    exact ⟨subset_univ _, hs.2⟩
  · intro S hS
    rw [mem_coe, mem_powersetCard] at hS
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [downs, ← hS.2]
    congr 1
    ext i
    by_cases h : i ∈ S <;> simp [h]
  · intro s _
    funext i
    rcases Fin.exists_fin_two.mp ⟨s i, rfl⟩ with h | h <;> simp [h]
  · intro S _
    ext i
    by_cases h : i ∈ S <;> simp [h]

/-! ## B. The ladder coefficient and the scale factors of `Ψ` -/

/-- The ladder coefficient `√((a+1)(n-a))`: the matrix element `⟨a | E | a+1⟩ = ⟨a+1 | F | a⟩`
of the spin-`n/2` representation (Physlib's normalisation). -/
noncomputable def lad (n a : ℕ) : ℝ := Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a))

lemma lad_nonneg (n a : ℕ) : 0 ≤ lad n a := Real.sqrt_nonneg _

lemma lad_sq {a : ℕ} (ha : a ≤ n) : lad n a * lad n a = ((a : ℝ) + 1) * ((n : ℝ) - a) := by
  have : (a : ℝ) ≤ n := by exact_mod_cast ha
  exact Real.mul_self_sqrt (by nlinarith)

lemma lad_pos {a : ℕ} (ha : a < n) : 0 < lad n a := by
  have : (a : ℝ) < n := by exact_mod_cast ha
  exact Real.sqrt_pos.mpr (by nlinarith)

/-- `lad n n = 0`: the top state is annihilated. -/
lemma lad_self (n : ℕ) : lad n n = 0 := by simp [lad]

/-- The scale factor of `Ψ` as a real number: `scale n k = k! · √C(n,k)`. -/
noncomputable def scaleR (n k : ℕ) : ℝ := (k.factorial : ℝ) * Real.sqrt (n.choose k)

lemma scale_eq (k : Fin (n + 1)) : scale n k = (scaleR n k : ℂ) := by
  rw [scale, nrm, scaleR, clsCard_eq_choose]
  push_cast
  rw [div_eq_mul_inv, inv_inv]

lemma scaleR_pos {k : ℕ} (hk : k ≤ n) : 0 < scaleR n k :=
  mul_pos (by exact_mod_cast Nat.factorial_pos k)
    (Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hk))

/-- `scale n (a+1) = √((a+1)(n-a)) · scale n a`. -/
lemma scaleR_succ {a : ℕ} (ha : a < n) : scaleR n (a + 1) = lad n a * scaleR n a := by
  have hc : (n.choose (a + 1) : ℝ) * (a + 1) = n.choose a * ((n : ℝ) - a) := by
    have h := Nat.choose_succ_right_eq n a
    have h2 : ((n - a : ℕ) : ℝ) = (n : ℝ) - a := by rw [Nat.cast_sub ha.le]
    rw [← h2]
    exact_mod_cast h
  have hle : (a : ℝ) < n := by exact_mod_cast ha
  rw [scaleR, scaleR, lad, Nat.factorial_succ]
  push_cast
  have e : Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a)) * Real.sqrt (n.choose a) =
      ((a : ℝ) + 1) * Real.sqrt (n.choose (a + 1)) := by
    rw [← Real.sqrt_mul (by nlinarith)]
    rw [show ((a : ℝ) + 1) * ((n : ℝ) - a) * (n.choose a) =
        ((a : ℝ) + 1) ^ 2 * (n.choose (a + 1)) by
          rw [mul_assoc, mul_comm ((n : ℝ) - a), ← hc]; ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  calc ((a : ℝ) + 1) * (a.factorial : ℝ) * Real.sqrt (n.choose (a + 1))
      = (a.factorial : ℝ) * (((a : ℝ) + 1) * Real.sqrt (n.choose (a + 1))) := by ring
    _ = (a.factorial : ℝ) * (Real.sqrt (((a : ℝ) + 1) * ((n : ℝ) - a)) *
          Real.sqrt (n.choose a)) := by rw [e]
    _ = _ := by ring

/-! ## C. The matrices of `E`, `F`, `H` -/

/-- `Ψ` sends Physlib's basis vector `v_a` to `scale n a · e_a`. -/
lemma Ψ_vNat {a : ℕ} (ha : a ≤ n) :
    Ψ n (vNat n a) = (scaleR n a : ℂ) • Pi.single (⟨a, Nat.lt_succ_of_le ha⟩ : Fin (n + 1)) 1 := by
  funext k
  rw [Ψ_apply, vNat_apply, Pi.smul_apply, Pi.single_apply, scale_eq]
  by_cases h : (k : ℕ) = a
  · have : k = ⟨a, Nat.lt_succ_of_le ha⟩ := Fin.ext h
    subst this
    simp
  · have : k ≠ ⟨a, Nat.lt_succ_of_le ha⟩ := fun e => h (by rw [e])
    simp [h, this]

lemma single_eq_Ψ (j : Fin (n + 1)) :
    (Pi.single j 1 : Fin (n + 1) → ℂ) = ((scaleR n j : ℂ)⁻¹) • Ψ n (vNat n j) := by
  rw [Ψ_vNat (Nat.lt_succ_iff.mp j.2), smul_smul, inv_mul_cancel₀ (by
    exact_mod_cast (scaleR_pos (Nat.lt_succ_iff.mp j.2)).ne'), one_smul]

lemma entry_eq (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i j : Fin (n + 1)) :
    M i j = (M *ᵥ Pi.single j 1) i := by
  simp

/-- **The lowering operator** in coordinates: `F e_j = √((j+1)(n-j)) e_{j+1}`. -/
theorem dSpin_F_apply (i j : Fin (n + 1)) :
    dSpin n matF i j = if (i : ℕ) = j + 1 then (lad n j : ℂ) else 0 := by
  rw [entry_eq (dSpin n matF) i j, single_eq_Ψ, mulVec_smul, dSpin_F, ρF_vNat, Pi.smul_apply]
  rcases lt_or_ge (j : ℕ) n with hj | hj
  · rw [Ψ_vNat (by omega : (j : ℕ) + 1 ≤ n), Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      smul_eq_mul, scaleR_succ hj]
    have hs : (scaleR n j : ℂ) ≠ 0 := by
      exact_mod_cast (scaleR_pos (Nat.lt_succ_iff.mp j.2)).ne'
    by_cases h : (i : ℕ) = j + 1
    · have : i = ⟨j + 1, by omega⟩ := Fin.ext h
      simp only [this, ↓reduceIte]
      push_cast
      field_simp
    · have : i ≠ ⟨j + 1, by omega⟩ := fun e => h (by rw [e])
      simp [this, h]
  · rw [vNat_of_lt (by omega), map_zero, Pi.zero_apply, smul_zero]
    have : ¬ (i : ℕ) = j + 1 := by have := i.2; omega
    simp [this]

/-- **The raising operator** in coordinates: `E e_{i+1} = √((i+1)(n-i)) e_i`, `E e_0 = 0`. -/
theorem dSpin_E_apply (i j : Fin (n + 1)) :
    dSpin n matE i j = if (j : ℕ) = i + 1 then (lad n i : ℂ) else 0 := by
  rw [entry_eq (dSpin n matE) i j, single_eq_Ψ, mulVec_smul, dSpin_E, Pi.smul_apply]
  rcases Nat.eq_zero_or_pos (j : ℕ) with hj | hj
  · rw [hj, ρE_vNat_zero, map_zero, Pi.zero_apply, smul_zero]
    simp
  · obtain ⟨j', hj'⟩ : ∃ j', (j : ℕ) = j' + 1 := ⟨(j : ℕ) - 1, by omega⟩
    have hj'n : j' < n := by have := j.2; omega
    rw [hj', ρE_vNat_succ, map_smul, Ψ_vNat hj'n.le, smul_smul, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, smul_eq_mul]
    have hsj : scaleR n (j' + 1) = lad n j' * scaleR n j' := scaleR_succ hj'n
    have hs : (scaleR n j' : ℂ) ≠ 0 := by exact_mod_cast (scaleR_pos hj'n.le).ne'
    have hl : (lad n j' : ℂ) ≠ 0 := by exact_mod_cast (lad_pos hj'n).ne'
    have hsq : (lad n j' : ℂ) * lad n j' = ((j' : ℂ) + 1) * ((n : ℂ) - j') := by
      exact_mod_cast lad_sq hj'n.le
    by_cases h : (i : ℕ) = j'
    · have : i = ⟨j', by omega⟩ := Fin.ext h
      simp only [this, ↓reduceIte, mul_one]
      rw [hsj]
      push_cast
      rw [← hsq]
      field_simp
    · have : i ≠ ⟨j', by omega⟩ := fun e => h (by rw [e])
      have h3 : ¬ j' = (i : ℕ) := fun e => h e.symm
      simp [this, h3]

/-- **The weight operator** in coordinates: `H e_a = (n - 2a) e_a`. -/
theorem dSpin_H_apply (i j : Fin (n + 1)) :
    dSpin n matH i j = if i = j then ((n : ℂ) - 2 * (j : ℕ)) else 0 := by
  rw [entry_eq (dSpin n matH) i j, single_eq_Ψ, mulVec_smul, dSpin_H, ρH_vNat, map_smul,
    Ψ_vNat (Nat.lt_succ_iff.mp j.2), smul_smul, smul_smul, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul]
  have hs : (scaleR n j : ℂ) ≠ 0 := by
    exact_mod_cast (scaleR_pos (Nat.lt_succ_iff.mp j.2)).ne'
  have hj : (⟨(j : ℕ), Nat.lt_succ_of_le (Nat.lt_succ_iff.mp j.2)⟩ : Fin (n + 1)) = j := rfl
  rw [hj]
  by_cases h : i = j
  · subst h; simp only [↓reduceIte, mul_one]; field_simp
  · simp [h]

/-! ## D. Sums against the ladder matrices

The matrix products that occur below, written with functions `f : ℕ → ℂ` of the basis label so
that no `Fin` bookkeeping is left. -/

lemma sum_dSpin_F_mul (f : ℕ → ℂ) (a : Fin (n + 1)) :
    ∑ a' : Fin (n + 1), dSpin n matF a a' * f a' =
      if 0 < (a : ℕ) then (lad n ((a : ℕ) - 1) : ℂ) * f ((a : ℕ) - 1) else 0 := by
  simp only [dSpin_F_apply, ite_mul, zero_mul]
  by_cases ha : 0 < (a : ℕ)
  · rw [Finset.sum_eq_single ⟨(a : ℕ) - 1, by omega⟩ (fun b _ hb => by
      have : ¬ (a : ℕ) = b + 1 := fun h => hb (Fin.ext (by simp; omega))
      simp [this]) (by simp)]
    have e : (a : ℕ) = ((⟨(a : ℕ) - 1, by omega⟩ : Fin (n + 1)) : ℕ) + 1 := by simp only; omega
    rw [ite_eq_left e, ite_eq_left ha]
  · rw [Finset.sum_eq_zero (fun b _ => by
      have : ¬ (a : ℕ) = b + 1 := by omega
      simp [this]), ite_eq_right ha]

lemma sum_dSpin_E_mul (f : ℕ → ℂ) (a : Fin (n + 1)) :
    ∑ a' : Fin (n + 1), dSpin n matE a a' * f a' =
      if (a : ℕ) < n then (lad n a : ℂ) * f ((a : ℕ) + 1) else 0 := by
  simp only [dSpin_E_apply, ite_mul, zero_mul]
  by_cases ha : (a : ℕ) < n
  · rw [Finset.sum_eq_single ⟨(a : ℕ) + 1, by omega⟩ (fun b _ hb => by
      have : ¬ (b : ℕ) = a + 1 := fun h => hb (Fin.ext h)
      simp [this]) (by simp)]
    simp [ha]
  · rw [Finset.sum_eq_zero (fun b _ => by
      have : ¬ (b : ℕ) = a + 1 := by have := b.2; omega
      simp [this]), ite_eq_right ha]

lemma sum_dSpin_H_mul (f : ℕ → ℂ) (a : Fin (n + 1)) :
    ∑ a' : Fin (n + 1), dSpin n matH a a' * f a' = ((n : ℂ) - 2 * (a : ℕ)) * f a := by
  simp only [dSpin_H_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

lemma sum_mul_dSpin_F (f : ℕ → ℂ) (l : Fin (n + 1)) :
    ∑ l' : Fin (n + 1), f l' * dSpin n matF l' l =
      if (l : ℕ) < n then f ((l : ℕ) + 1) * (lad n l : ℂ) else 0 := by
  simp only [dSpin_F_apply, mul_ite, mul_zero]
  by_cases hl : (l : ℕ) < n
  · rw [Finset.sum_eq_single ⟨(l : ℕ) + 1, by omega⟩ (fun b _ hb => by
      have : ¬ (b : ℕ) = l + 1 := fun h => hb (Fin.ext h)
      simp [this]) (by simp)]
    simp [hl]
  · rw [Finset.sum_eq_zero (fun b _ => by
      have : ¬ (b : ℕ) = l + 1 := by have := b.2; omega
      simp [this]), ite_eq_right hl]

lemma sum_mul_dSpin_E (f : ℕ → ℂ) (l : Fin (n + 1)) :
    ∑ l' : Fin (n + 1), f l' * dSpin n matE l' l =
      if 0 < (l : ℕ) then f ((l : ℕ) - 1) * (lad n ((l : ℕ) - 1) : ℂ) else 0 := by
  simp only [dSpin_E_apply, mul_ite, mul_zero]
  by_cases hl : 0 < (l : ℕ)
  · rw [Finset.sum_eq_single ⟨(l : ℕ) - 1, by omega⟩ (fun b _ hb => by
      have : ¬ (l : ℕ) = b + 1 := fun h => hb (Fin.ext (by simp; omega))
      simp [this]) (by simp)]
    have e : (l : ℕ) = ((⟨(l : ℕ) - 1, by omega⟩ : Fin (n + 1)) : ℕ) + 1 := by simp only; omega
    rw [ite_eq_left e, ite_eq_left hl]
  · rw [Finset.sum_eq_zero (fun b _ => by
      have : ¬ (l : ℕ) = b + 1 := by omega
      simp [this]), ite_eq_right hl]

lemma sum_mul_dSpin_H (f : ℕ → ℂ) (l : Fin (n + 1)) :
    ∑ l' : Fin (n + 1), f l' * dSpin n matH l' l = f l * ((n : ℂ) - 2 * (l : ℕ)) := by
  simp only [dSpin_H_apply, mul_ite, mul_zero]
  rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- The entries of `(A ⊗ 1 + 1 ⊗ B) C` for a matrix `C` with rows indexed by pairs. -/
lemma kron_sum_mul_apply {ι κ μ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) (C : Matrix (ι × κ) μ ℂ) (p : ι × κ) (l : μ) :
    ((A ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ B) * C) p l =
      ∑ a', A p.1 a' * C (a', p.2) l + ∑ b', B p.2 b' * C (p.1, b') l := by
  rw [Matrix.add_mul, Matrix.add_apply, mul_apply, mul_apply]
  simp only [Fintype.sum_prod_type]
  congr 1
  · refine Finset.sum_congr rfl fun a' _ => ?_
    simp only [kroneckerMap_apply, one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    simp only [kroneckerMap_apply, one_apply, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]

/-! ## E. The Casimir operator -/

/-- **The Casimir operator** of the spin-`n/2` representation is a scalar:
`½(EF + FE) + ¼H² = J_x² + J_y² + J_z² = (n/2)(n/2 + 1)`. -/
theorem casimir_eq (n : ℕ) :
    (1 / 2 : ℂ) • (dSpin n matE * dSpin n matF + dSpin n matF * dSpin n matE) +
      (1 / 4 : ℂ) • (dSpin n matH * dSpin n matH) =
      ((n : ℂ) / 2 * ((n : ℂ) / 2 + 1)) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, mul_apply, dSpin_E_apply, dSpin_F_apply,
    dSpin_H_apply, smul_eq_mul, one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, mul_one]
    -- the three sums each have at most one nonzero term
    have hEF : ∑ x : Fin (n + 1), (if (x : ℕ) = i + 1 then (lad n i : ℂ) else 0) *
        (if (x : ℕ) = i + 1 then (lad n i : ℂ) else 0) =
        ((i : ℂ) + 1) * ((n : ℂ) - i) := by
      rcases lt_or_ge (i : ℕ) n with hi | hi
      · rw [Finset.sum_eq_single ⟨i + 1, by omega⟩ (fun b _ hb => by
          have : ¬ (b : ℕ) = i + 1 := fun h => hb (Fin.ext h)
          simp [this]) (by simp)]
        simp only [↓reduceIte]
        exact_mod_cast lad_sq hi.le
      · have hin : (i : ℕ) = n := by have := i.2; omega
        rw [Finset.sum_eq_zero (fun b _ => by
          have : ¬ (b : ℕ) = i + 1 := by have := b.2; omega
          simp [this])]
        rw [hin]; ring
    have hFE : ∑ x : Fin (n + 1), (if (i : ℕ) = x + 1 then (lad n x : ℂ) else 0) *
        (if (i : ℕ) = x + 1 then (lad n x : ℂ) else 0) = (i : ℂ) * ((n : ℂ) - i + 1) := by
      rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
      · rw [Finset.sum_eq_zero (fun b _ => by
          have : ¬ (i : ℕ) = b + 1 := by omega
          simp [this])]
        rw [hi]; ring
      · rw [Finset.sum_eq_single ⟨(i : ℕ) - 1, by omega⟩ (fun b _ hb => by
          have : ¬ (i : ℕ) = b + 1 := fun h => hb (Fin.ext (by simp; omega))
          simp [this]) (by simp)]
        have e : (i : ℕ) = ((⟨(i : ℕ) - 1, by omega⟩ : Fin (n + 1)) : ℕ) + 1 := by
          simp only; omega
        rw [ite_eq_left e]
        simp only
        have := lad_sq (n := n) (a := (i : ℕ) - 1) (by have := i.2; omega)
        have hc : (((i : ℕ) - 1 : ℕ) : ℂ) = (i : ℂ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        have h' : (lad n ((i : ℕ) - 1) : ℂ) * lad n ((i : ℕ) - 1) =
            ((((i : ℕ) - 1 : ℕ) : ℂ) + 1) * ((n : ℂ) - (((i : ℕ) - 1 : ℕ) : ℂ)) := by
          exact_mod_cast this
        rw [h', hc]; ring
    have hHH : ∑ x : Fin (n + 1), (if i = x then ((n : ℂ) - 2 * (x : ℕ)) else 0) *
        (if x = i then ((n : ℂ) - 2 * (i : ℕ)) else 0) = ((n : ℂ) - 2 * (i : ℕ)) ^ 2 := by
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp [sq]
    rw [hEF, hFE, hHH]
    ring
  · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    simp only [hij, ↓reduceIte, mul_zero]
    have z1 : ∑ x : Fin (n + 1), (if (x : ℕ) = i + 1 then (lad n i : ℂ) else 0) *
        (if (x : ℕ) = j + 1 then (lad n j : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        by_cases h1 : (x : ℕ) = i + 1
        · have : ¬ (x : ℕ) = j + 1 := by omega
          simp [this]
        · simp [h1]
    have z2 : ∑ x : Fin (n + 1), (if (i : ℕ) = x + 1 then (lad n x : ℂ) else 0) *
        (if (j : ℕ) = x + 1 then (lad n x : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        by_cases h1 : (i : ℕ) = x + 1
        · have : ¬ (j : ℕ) = x + 1 := by omega
          simp [this]
        · simp [h1]
    have z3 : ∑ x : Fin (n + 1), (if i = x then (n : ℂ) - 2 * ((x : ℕ) : ℂ) else 0) *
        (if x = j then (n : ℂ) - 2 * ((j : ℕ) : ℂ) else 0) = 0 :=
      Finset.sum_eq_zero fun x _ => by
        by_cases h1 : i = x
        · subst h1; simp [hij]
        · simp [h1]
    rw [z1, z2, z3]
    ring

end Lightlike.Spin4
