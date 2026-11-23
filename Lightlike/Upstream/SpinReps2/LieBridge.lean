module

public import Lightlike.Upstream.SU2Spin.SpinRep
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Classification
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# The spin-`n/2` representation of SU(2) differentiates to Physlib's `V(n)`

Physlib builds its 6j symbols on the standard `sl₂`-modules `StandardSl2Module K n = V(n)`, with
explicit raising, lowering and weight operators `ρE`, `ρF`, `ρH`. The spin representations of
`Lightlike.Upstream.SU2Spin.SpinRep` are representations of the *group* SU(2). This file connects
the two on the algebraic side.

## Main definitions

* `SU2Spin.dkron n X = Σᵢ 1 ⊗ … ⊗ X ⊗ … ⊗ 1` (`X` in slot `i`), the derivative at the identity of
  `g ↦ g^{⊗n}`.
* `SU2Spin.dSpin n X = embᴴ · dkron n X · emb`, the derivative of `spinMat n` on the symmetric
  subspace `ℂ^{n+1}`.
* `SU2Spin.psi n : V(n) →ₗ[ℂ] ℂ^{Str n}`, `psi w s = (downs s)! · w (downs s)`.
* `SU2Spin.Ψ n : V(n) ≃ₗ[ℂ] ℂ^{n+1}`, diagonal, `v_k ↦ (k! / nrm n k) e_k`.
* `SU2Spin.matE`, `matF`, `matH`: the standard basis of `sl₂(ℂ)`.

## Main results

* `SU2Spin.isSl2Triple_mat`: `(H, E, F)` is an `sl₂`-triple in `gl₂(ℂ)`.
* `SU2Spin.dkron_E_psi`, `dkron_F_psi`, `dkron_H_psi`: `psi` intertwines `ρE, ρF, ρH` with
  `dkron n E, dkron n F, dkron n H`.
* `SU2Spin.dSpin_E`, `dSpin_F`, `dSpin_H`: under `Ψ n`, the differential of the spin-`n/2`
  representation is Physlib's `sl₂`-module: `E, F, H` act by `ρE, ρF, ρH`.

## References

B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (Springer, 2015), ch. 4;
J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory* (Springer, 1972), §7
(representations of sl(2)).
-/

@[expose] public section

open Matrix Finset PhyslibAlpha.Sl2

namespace SU2Spin

variable {n : ℕ}

/-- The differential of `g ↦ g^{⊗n}` at the identity: `X` acting on one slot at a time. -/
def dkron (n : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Str n) (Str n) ℂ :=
  Matrix.of fun s t => ∑ i, if ∀ j, j ≠ i → s j = t j then X (s i) (t i) else 0

/-- Strings agreeing with `s` off slot `i` are exactly `update s i c`. -/
lemma sum_agree_off (s : Str n) (i : Fin n) (G : Str n → ℂ) :
    ∑ t : Str n, (if ∀ j, j ≠ i → s j = t j then G t else 0) =
      ∑ c : Fin 2, G (Function.update s i c) := by
  rw [← sum_filter]
  have himg : (univ.filter fun t : Str n => ∀ j, j ≠ i → s j = t j) =
      univ.image (fun c : Fin 2 => Function.update s i c) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      refine ⟨t i, funext fun j => ?_⟩
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, h j hj]
    · rintro ⟨c, rfl⟩ j hj
      rw [Function.update_of_ne hj]
  rw [himg, sum_image]
  intro c _ c' _ h
  have := congrFun h i
  simpa using this

/-- `dkron` acting on a vector: `(dkron X v) s = Σᵢ Σ_c X (s i) c · v (s with slot i set to c)`. -/
lemma dkron_mulVec (X : Matrix (Fin 2) (Fin 2) ℂ) (v : Str n → ℂ) (s : Str n) :
    (dkron n X *ᵥ v) s = ∑ i, ∑ c : Fin 2, X (s i) c * v (Function.update s i c) := by
  simp only [mulVec, dotProduct, dkron, of_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have h := sum_agree_off s i (fun t => X (s i) (t i) * v t)
  simp only [Function.update_self] at h
  rw [← h]
  refine sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

/-- Number of down labels after setting slot `i` to `c`. -/
lemma downs_update (s : Str n) (i : Fin n) (c : Fin 2) :
    downs (Function.update s i c) + (if s i = 1 then 1 else 0) =
      downs s + (if c = 1 then 1 else 0) := by
  unfold downs
  rw [card_filter, card_filter, ← add_sum_erase _ _ (mem_univ i),
    ← add_sum_erase _ _ (mem_univ i)]
  have : ∑ j ∈ univ.erase i, (if Function.update s i c j = 1 then 1 else 0) =
      ∑ j ∈ univ.erase i, (if s j = 1 then 1 else 0) :=
    sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
  rw [this, Function.update_self]
  ring

/-- The number of up labels is `n - downs s`. -/
lemma card_ups (s : Str n) : #(univ.filter fun i => s i = 0) = n - downs s := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (p := fun i => s i = 1)
  have h01 : ∀ x : Fin 2, ¬ x = 1 ↔ x = 0 := by decide
  simp only [h01, card_univ, Fintype.card_fin] at h
  unfold downs
  omega

/-- A vector of `V(n)` read as a function of `ℕ` (zero beyond `n`). -/
def wfun (w : StandardSl2Module ℂ n) (k : ℕ) : ℂ := if h : k < n + 1 then w ⟨k, h⟩ else 0

lemma wfun_fin (w : StandardSl2Module ℂ n) (k : Fin (n + 1)) : wfun w k = w k := by
  simp [wfun, k.isLt]

/-- **The intertwiner** `V(n) → ℂ^{Str n}`: `psi w s = (downs s)! · w (downs s)`. On Physlib's basis
`v_k` it is `k!` times the indicator of the strings with `k` down labels. -/
def psi (n : ℕ) : StandardSl2Module ℂ n →ₗ[ℂ] (Str n → ℂ) where
  toFun w s := ((downs s).factorial : ℂ) * wfun w (downs s)
  map_add' w w' := by funext s; simp only [wfun, Pi.add_apply]; split_ifs <;> ring
  map_smul' c w := by
    funext s; simp only [wfun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

lemma psi_apply (w : StandardSl2Module ℂ n) (s : Str n) :
    psi n w s = ((downs s).factorial : ℂ) * wfun w (downs s) := rfl

/-- The raising element `E = !![0, 1; 0, 0]` of the standard `sl₂(ℂ)` basis. -/
def matE : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
/-- The lowering element `F = !![0, 0; 1, 0]` of the standard `sl₂(ℂ)` basis. -/
def matF : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
/-- The Cartan element `H = diag(1, -1)` of the standard `sl₂(ℂ)` basis. -/
def matH : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

section Commutator

attribute [local instance 100] LieRing.ofAssociativeRing

/-- `(H, E, F)` is an `sl₂`-triple in `gl₂(ℂ)` (commutator bracket, `LieRing.ofAssociativeRing`), so
Physlib's results apply to `sl₂(ℂ)` itself. -/
theorem isSl2Triple_mat : IsSl2Triple matH matE matF where
  h_ne_zero h := by have := congrFun (congrFun h 0) 0; simp [matH] at this
  lie_e_f := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LieRing.of_associative_ring_bracket, matE, matF, matH]
  lie_h_e_nsmul := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LieRing.of_associative_ring_bracket, matE, matH]; norm_num
  lie_h_f_nsmul := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [LieRing.of_associative_ring_bracket, matF, matH]; norm_num

end Commutator

lemma fin_two_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  have h : ∀ y : Fin 2, y = 0 ∨ y = 1 := by decide
  exact h x

/-- **`H` acts by the weight `n - 2k`.** -/
theorem dkron_H_psi (w : StandardSl2Module ℂ n) :
    dkron n matH *ᵥ psi n w = psi n (ρH w) := by
  funext s
  rw [dkron_mulVec, psi_apply]
  have hterm : ∀ i, ∑ c : Fin 2, matH (s i) c * psi n w (Function.update s i c) =
      (if s i = 1 then -1 else 1) * psi n w s := by
    intro i
    rcases fin_two_cases (s i) with h | h
    · have hs : Function.update s i 0 = s := by rw [← h, Function.update_eq_self]
      simp [Fin.sum_univ_two, matH, h, hs]
    · have hs : Function.update s i 1 = s := by rw [← h, Function.update_eq_self]
      simp [Fin.sum_univ_two, matH, h, hs]
  rw [sum_congr rfl fun i _ => hterm i, ← sum_mul]
  have hcount : ∑ i : Fin n, (if s i = 1 then (-1 : ℂ) else 1) = (n : ℂ) - 2 * (downs s : ℂ) := by
    have : ∀ i : Fin n, (if s i = 1 then (-1 : ℂ) else 1) = 1 - 2 * (if s i = 1 then 1 else 0) := by
      intro i; split_ifs <;> ring
    rw [sum_congr rfl fun i _ => this i, sum_sub_distrib, ← mul_sum]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold downs
    rw [card_filter]
    push_cast
    rfl
  have hd := Nat.lt_succ_of_le (downs_le s)
  simp only [hcount, psi_apply, wfun, hd, dite_true]
  show _ = _ * (((n : ℂ) - 2 * ((downs s : ℕ) : ℂ)) * w ⟨downs s, hd⟩)
  ring

/-- **`E` raises the number of down labels**: it intertwines with Physlib's `ρE`. -/
theorem dkron_E_psi (w : StandardSl2Module ℂ n) :
    dkron n matE *ᵥ psi n w = psi n (ρE w) := by
  funext s
  rw [dkron_mulVec]
  have hterm : ∀ i, ∑ c : Fin 2, matE (s i) c * psi n w (Function.update s i c) =
      (if s i = 0 then 1 else 0) *
        (((downs s + 1).factorial : ℂ) * wfun w (downs s + 1)) := by
    intro i
    rcases fin_two_cases (s i) with h | h
    · have hd : downs (Function.update s i 1) = downs s + 1 := by
        have := downs_update s i 1; simp [h] at this; omega
      simp [Fin.sum_univ_two, matE, h, psi_apply, hd]
    · simp [Fin.sum_univ_two, matE, h]
  rw [sum_congr rfl fun i _ => hterm i, ← sum_mul]
  have hcount : ∑ i : Fin n, (if s i = 0 then (1 : ℂ) else 0) = ((n - downs s : ℕ) : ℂ) := by
    rw [← card_ups s, card_filter]; push_cast; rfl
  rw [hcount, psi_apply]
  have hd := Nat.lt_succ_of_le (downs_le s)
  simp only [wfun, hd, dite_true]
  show _ = _ * (if hk : downs s = n then 0
    else (((downs s : ℕ) + 1) * ((n : ℂ) - (downs s : ℕ))) * w ⟨downs s + 1, by omega⟩)
  by_cases hdn : downs s = n
  · simp [hdn]
  · have hlt : downs s + 1 < n + 1 := by have := downs_le s; omega
    simp only [hdn, hlt, ↓reduceDIte]
    rw [Nat.cast_sub (downs_le s), Nat.factorial_succ]
    push_cast
    ring

/-- **`F` lowers the number of down labels**: it intertwines with Physlib's `ρF`. -/
theorem dkron_F_psi (w : StandardSl2Module ℂ n) :
    dkron n matF *ᵥ psi n w = psi n (ρF w) := by
  funext s
  rw [dkron_mulVec]
  have hterm : ∀ i, ∑ c : Fin 2, matF (s i) c * psi n w (Function.update s i c) =
      (if s i = 1 then 1 else 0) *
        (((downs s - 1).factorial : ℂ) * wfun w (downs s - 1)) := by
    intro i
    rcases fin_two_cases (s i) with h | h
    · simp [Fin.sum_univ_two, matF, h]
    · have hd : downs (Function.update s i 0) = downs s - 1 := by
        have := downs_update s i 0; simp [h] at this; omega
      simp [Fin.sum_univ_two, matF, h, psi_apply, hd]
  rw [sum_congr rfl fun i _ => hterm i, ← sum_mul]
  have hcount : ∑ i : Fin n, (if s i = 1 then (1 : ℂ) else 0) = (downs s : ℂ) := by
    unfold downs; rw [card_filter]; push_cast; rfl
  rw [hcount, psi_apply]
  have hd := Nat.lt_succ_of_le (downs_le s)
  simp only [wfun, hd, dite_true]
  show _ = _ * (if hk : downs s = 0 then 0 else w ⟨downs s - 1, by omega⟩)
  by_cases h0 : downs s = 0
  · simp [h0]
  · have hlt : downs s - 1 < n + 1 := by omega
    simp only [h0, hlt, ↓reduceDIte]
    rw [← Nat.mul_factorial_pred h0]
    push_cast
    ring

/-! ## The compression to `ℂ^{n+1}` -/

/-- The scale factor between Physlib's basis `v_k` and the orthonormal basis: `k! / nrm n k`. -/
noncomputable def scale (n : ℕ) (k : Fin (n + 1)) : ℂ := ((k : ℕ).factorial : ℂ) / nrm n k

lemma scale_ne_zero (k : Fin (n + 1)) : scale n k ≠ 0 :=
  div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (nrm_ne_zero (Nat.lt_succ_iff.mp k.2))

/-- **The linear isomorphism `V(n) ≃ ℂ^{n+1}`**: diagonal, `v_k ↦ (k! / nrm n k) e_k`. -/
noncomputable def Ψ (n : ℕ) : StandardSl2Module ℂ n ≃ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearEquiv.piCongrRight fun k => LinearEquiv.smulOfNeZero ℂ ℂ (scale n k) (scale_ne_zero k)

lemma Ψ_apply (w : StandardSl2Module ℂ n) (k : Fin (n + 1)) : Ψ n w k = scale n k * w k := rfl

/-- `psi` factors through the symmetric embedding: `psi w = emb (Ψ w)`. -/
lemma psi_eq_emb_mulVec (w : StandardSl2Module ℂ n) : psi n w = emb n *ᵥ Ψ n w := by
  funext s
  have hd := Nat.lt_succ_of_le (downs_le s)
  have hne := nrm_ne_zero (downs_le s)
  rw [mulVec, dotProduct, sum_eq_single (⟨downs s, hd⟩ : Fin (n + 1))]
  · simp only [emb_apply, Ψ_apply, scale, psi_apply, wfun, hd, dite_true, ↓reduceIte]
    field_simp
  · intro k _ hk
    have : ¬ downs s = (k : ℕ) := fun h => hk (Fin.ext h.symm)
    simp only [emb_apply, this, ↓reduceIte, zero_mul]
  · simp

/-- The differential of the spin-`n/2` representation: `embᴴ · dkron n X · emb`. -/
noncomputable def dSpin (n : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (emb n)ᴴ * dkron n X * emb n

lemma dSpin_Ψ_of {X : Matrix (Fin 2) (Fin 2) ℂ} {ρX : Module.End ℂ (StandardSl2Module ℂ n)}
    (h : ∀ w, dkron n X *ᵥ psi n w = psi n (ρX w)) (w : StandardSl2Module ℂ n) :
    dSpin n X *ᵥ Ψ n w = Ψ n (ρX w) := by
  rw [dSpin, ← mulVec_mulVec, ← mulVec_mulVec, ← psi_eq_emb_mulVec, h, psi_eq_emb_mulVec,
    mulVec_mulVec, emb_conjTranspose_mul_emb, one_mulVec]

/-- **Algebraic half.** Under `Ψ`, the differential of the spin-`n/2` representation is Physlib's
standard `sl₂`-module `V(n)`: `E, F, H` act by `ρE, ρF, ρH`. -/
theorem dSpin_E (w : StandardSl2Module ℂ n) : dSpin n matE *ᵥ Ψ n w = Ψ n (ρE w) :=
  dSpin_Ψ_of dkron_E_psi w

/-- Under `Ψ`, the differential of `F` acts as Physlib's `ρF` on `V(n)`. -/
theorem dSpin_F (w : StandardSl2Module ℂ n) : dSpin n matF *ᵥ Ψ n w = Ψ n (ρF w) :=
  dSpin_Ψ_of dkron_F_psi w

/-- Under `Ψ`, the differential of `H` acts as Physlib's `ρH` on `V(n)`. -/
theorem dSpin_H (w : StandardSl2Module ℂ n) : dSpin n matH *ᵥ Ψ n w = Ψ n (ρH w) :=
  dSpin_Ψ_of dkron_H_psi w

end SU2Spin
