import Lightlike.Asymptotics.EPRL.EprlCoherentPullback

/-!
# The EPRL map sends the `SU(2)` coherent intertwiner to the Spin(4) coherent intertwiner

For `γ < 1` the EPRL map takes the `SU(2)` coherent intertwiner `ι_{n+m}(g)` to the product
`ι_n(g) ⊗ ι_m(g)` of the self-dual and anti-self-dual coherent intertwiners with the same group
elements, in Hom form (`eprlIntertwiner_homForm_cohInt`). The projection-form bridge uses the
constant sign `nodeSign` of `vec_eq_sum`, which is additive (`nodeSign_add`), so it cancels.

## Main results

* `eprlIntertwiner_homForm_cohInt`: `Φ(ι_{n+m}(g)) = ι_n(g) ⊗ ι_m(g)`.
* `nodeSign`, `nodeSign_add`: the sign, and its additivity for `J = n + m` with even spin sums.
* `projNode_projOf`: `projNode` at the projections of `k` is the component `k`.
* `eprlNode_eq_eprlIntertwiner'`: the node tensor at the projections of two components is the
  signed EPRL map of a basis intertwiner.
* `eprlIntertwiner_sum_smul`: the EPRL map on intertwiners is linear.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, §3.
-/

open Matrix Finset
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

variable (n m : Fin 4 → ℕ)

/-- **The EPRL map sends the `SU(2)` coherent intertwiner to the Spin(4) coherent intertwiner**:
`Φ(ι_{n+m}(g)) = ι_n(g) ⊗ ι_m(g)` in Hom form, for `γ < 1` (the same `g` on both chiral halves). -/
theorem eprlIntertwiner_homForm_cohInt (g : Fin 4 → SU2) :
    eprlIntertwiner (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
        (homForm (n + m) (cohInt (n + m) g)) =
      homForm n (cohInt n g) ⊗ₖ homForm m (cohInt m g) := by
  have hn := homForm_isIntertwiner n (cohInt_isInvariantN (J := n) g)
  have hm := homForm_isIntertwiner m (cohInt_isInvariantN (J := m) g)
  have en := eq_sum_ivec hn
  have em := eq_sum_ivec hm
  unfold eprlIntertwiner projSpin4
  calc _ = ∑ p ∈ channel (n 0) (n 1) (n 2) (n 3) ×ˢ channel (m 0) (m 1) (m 2) (m 3),
        (hsInner (ivec (n 0) (n 1) (n 2) (n 3) p.1) (homForm n (cohInt n g)) *
          hsInner (ivec (m 0) (m 1) (m 2) (m 3) p.2) (homForm m (cohInt m g))) •
          ivec4 (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) p.1 p.2 := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mem_product] at hp
        rw [hsInner_ivec4_eprlLift_cohInt n m g hp.1 hp.2]
    _ = _ := by
        rw [Finset.sum_product]
        conv_rhs => rw [en, em]
        ext P Q
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, kroneckerMap_apply, ivec4,
          Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring

section Sign

/-- The constant sign relating the Hom-form and projection-form expansions of an invariant
four-leg tensor (`vec_eq_sum`). -/
def nodeSign (J : Fin 4 → ℕ) : ℂ := (-1 : ℂ) ^ (J 1 + J 2 + (∑ a, J a) / 2)

/-- **The sign is additive**: for `J = n + m` with even spin sums, the signs of `n + m`, `n` and `m`
multiply to `1`. -/
theorem nodeSign_add (n m : Fin 4 → ℕ) (hn : Even (∑ a, n a)) (hm : Even (∑ a, m a)) :
    nodeSign (n + m) * nodeSign n * nodeSign m = 1 := by
  unfold nodeSign
  rw [← pow_add, ← pow_add]
  obtain ⟨a, ha⟩ := hn
  obtain ⟨b, hb⟩ := hm
  have hs : ∑ i, (n + m) i = ∑ i, n i + ∑ i, m i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [hs, Pi.add_apply, Pi.add_apply]
  apply Even.neg_one_pow
  exact ⟨n 1 + m 1 + n 2 + m 2 + a + b, by omega⟩

end Sign

open Lightlike.Asymptotics.EPRL in
/-- `projNode` at the projections of `k` is the component `k`. -/
lemma projNode_projOf (J : Fin 4 → ℕ) (v : LIdx J → ℂ) (k : LIdx J) :
    projNode J v (projOf J k) = v k := by
  unfold projNode
  rw [Finset.sum_eq_single k]
  · have : (∏ l, if projOf J k l = (J l : ℤ) - 2 * ((k l : Fin (J l + 1)) : ℕ) then (1 : ℂ) else 0) = 1 :=
      Finset.prod_eq_one fun l _ => if_pos rfl
    rw [this, one_mul]
  · intro k' _ hk'
    obtain ⟨a, ha⟩ : ∃ a, k a ≠ k' a := not_forall.mp fun hc => hk' (funext fun x => (hc x).symm)
    have : (∏ l, if projOf J k l = (J l : ℤ) - 2 * ((k' l : Fin (J l + 1)) : ℕ) then (1 : ℂ) else 0) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ?_)
      intro h
      apply ha
      simp only [projOf] at h
      have := (k a).isLt
      have := (k' a).isLt
      exact Fin.ext (by omega)
    rw [this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

section NodeBridge

variable (n m : Fin 4 → ℕ)

/-- The signed bridge from the node tensor to the EPRL map on a basis intertwiner, in terms of the
legs of `Fin 4 → ℕ` spins. -/
theorem eprlNode_eq_eprlIntertwiner' (z : ℕ) (k : LIdx n) (l : LIdx m) :
    eprlNode n m z (projOf n k) (projOf m l) =
      (-1 : ℂ) ^ (n 1 + n 3 + (k 0 : ℕ) + k 1) * (-1 : ℂ) ^ (m 1 + m 3 + (l 0 : ℕ) + l 1) *
        eprlIntertwiner (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
          (ivec (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3) z)
          ((k 0, k 1), (l 0, l 1))
          ((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) := by
  have key := eprlNode_eq_eprlIntertwiner (n₁ := n 0) (n₂ := n 1) (n₃ := n 2) (n₄ := n 3)
    (m₁ := m 0) (m₂ := m 1) (m₃ := m 2) (m₄ := m 3) z ((k 0, k 1), (l 0, l 1))
    ((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3)))
  have hn : n = ![n 0, n 1, n 2, n 3] := by funext i; fin_cases i <;> rfl
  have hm : m = ![m 0, m 1, m 2, m 3] := by funext i; fin_cases i <;> rfl
  have hμ : projOf n k = ![(n 0 : ℤ) - 2 * ((k 0 : ℕ) : ℤ), (n 1 : ℤ) - 2 * ((k 1 : ℕ) : ℤ),
      2 * (((Fin.rev (k 2) : Fin (n 2 + 1)) : ℕ) : ℤ) - (n 2 : ℤ),
      2 * (((Fin.rev (k 3) : Fin (n 3 + 1)) : ℕ) : ℤ) - (n 3 : ℤ)] := by
    funext i
    have h2 := (k 2).isLt
    have h3 := (k 3).isLt
    fin_cases i <;> simp [projOf, Fin.val_rev] <;> omega
  have hν : projOf m l = ![(m 0 : ℤ) - 2 * ((l 0 : ℕ) : ℤ), (m 1 : ℤ) - 2 * ((l 1 : ℕ) : ℤ),
      2 * (((Fin.rev (l 2) : Fin (m 2 + 1)) : ℕ) : ℤ) - (m 2 : ℤ),
      2 * (((Fin.rev (l 3) : Fin (m 3 + 1)) : ℕ) : ℤ) - (m 3 : ℤ)] := by
    funext i
    have h2 := (l 2).isLt
    have h3 := (l 3).isLt
    fin_cases i <;> simp [projOf, Fin.val_rev] <;> omega
  rw [hμ, hν]
  rw [← hn, ← hm] at key
  exact key

/-- The EPRL map on intertwiners is linear. -/
theorem eprlIntertwiner_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (T : ι → Matrix (Idx (n 0 + m 0) (n 1 + m 1)) (Idx (n 2 + m 2) (n 3 + m 3)) ℂ) :
    eprlIntertwiner (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) (∑ i ∈ s, c i • T i) =
      ∑ i ∈ s, c i • eprlIntertwiner (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3) (T i) := by
  unfold eprlIntertwiner projSpin4 eprlLift
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, hsInner_sum_right,
    hsInner_smul_right, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_smul]


end NodeBridge

end Lightlike.Asymptotics.EPRL
