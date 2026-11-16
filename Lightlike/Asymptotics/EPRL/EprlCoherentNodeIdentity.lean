import Lightlike.Asymptotics.EPRL.EprlCoherentIntertwiner

/-!
# The coherent EPRL node tensor

The coherent EPRL node tensor `eprlCohNode n m g`, the image of the `SU(2)` coherent intertwiner of
spins `n + m` under the EPRL map written in the `eprlNode` basis with the coefficients of
`vec_eq_sum`, is the product of the self-dual and anti-self-dual coherent node tensors
(`eprlCohNode_eq`), for every pair of projection tuples and with no sign.

## Main results

* `eprlCohNode`: the coherent EPRL node tensor `Σ_z c_z eprlNode n m z`.
* `eprlCohNode_projOf`: the identity at the projections of two components.
* `eprlCohNode_eq`: the **node identity**, `eprlCohNode n m g μ ν = projNode n ι_n(g) μ ·
  projNode m ι_m(g) ν` for all `μ, ν`.

## References

* J. W. Barrett, R. J. Dowdall, W. J. Fairbairn, H. Gomes, F. Hellmann, *J. Math. Phys.* 50 (2009)
  112504, arXiv:0902.1170, §3.
-/

open Matrix Finset
open scoped Matrix Kronecker

namespace Lightlike.Asymptotics.EPRL

open Lightlike.Spin4 Lightlike.SU2 Lightlike.SpinFoam Lightlike.Recoupling

section NodeBridge

variable (n m : Fin 4 → ℕ)

/-- **The coherent EPRL node tensor**: the image `Φ(ι_{n+m}(g))` of the `SU(2)` coherent intertwiner
under the EPRL map, as `Σ_z c_z eprlNode n m z`, where `c_z` are the coefficients of `ι_{n+m}(g)` in
the `fourJ` basis (`nodeSign * ⟨ι_z, homForm ι⟩`, see `vec_eq_sum`). -/
noncomputable def eprlCohNode (g : Fin 4 → SU2) (μ ν : Fin 4 → ℤ) : ℂ :=
  ∑ z ∈ channel (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3),
    (nodeSign (n + m) *
      hsInner (ivec (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3) z)
        (homForm (n + m) (cohInt (n + m) g))) * eprlNode n m z μ ν

/-- **The coherent EPRL node tensor at the projections of two components**, before the signs are
combined: `ns * (-1)^… * (-1)^… * T⁺(P.1, Q.1) * T⁻(P.2, Q.2)`. -/
theorem eprlCohNode_projOf_aux (g : Fin 4 → SU2) (k : LIdx n) (l : LIdx m) :
    eprlCohNode n m g (projOf n k) (projOf m l) =
      nodeSign (n + m) *
        ((-1 : ℂ) ^ (n 1 + n 3 + (k 0 : ℕ) + k 1) * (-1 : ℂ) ^ (m 1 + m 3 + (l 0 : ℕ) + l 1)) *
        (homForm n (cohInt n g) (k 0, k 1) (Fin.rev (k 2), Fin.rev (k 3)) *
          homForm m (cohInt m g) (l 0, l 1) (Fin.rev (l 2), Fin.rev (l 3))) := by
  have hn := homForm_isIntertwiner (n + m) (cohInt_isInvariantN (J := n + m) g)
  have e := eq_sum_ivec hn
  simp only [Pi.add_apply] at e
  have hk := eprlIntertwiner_homForm_cohInt n m g
  have hlin := eprlIntertwiner_sum_smul n m
    (channel (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3))
    (fun z => hsInner (ivec (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3) z)
        (homForm (n + m) (cohInt (n + m) g)))
    (fun z => ivec (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3) z)
  unfold eprlCohNode
  simp only [eprlNode_eq_eprlIntertwiner' n m _ k l]
  have h3 : eprlIntertwiner (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
      (homForm (n + m) (cohInt (n + m) g)) ((k 0, k 1), (l 0, l 1))
        ((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) =
      ∑ z ∈ channel (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3),
        hsInner (ivec (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3) z)
          (homForm (n + m) (cohInt (n + m) g)) *
        eprlIntertwiner (n 0) (n 1) (n 2) (n 3) (m 0) (m 1) (m 2) (m 3)
          (ivec (n 0 + m 0) (n 1 + m 1) (n 2 + m 2) (n 3 + m 3) z) ((k 0, k 1), (l 0, l 1))
          ((Fin.rev (k 2), Fin.rev (k 3)), (Fin.rev (l 2), Fin.rev (l 3))) := by
    conv_lhs => rw [e]
    rw [hlin]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hk] at h3
  simp only [kroneckerMap_apply] at h3
  rw [h3]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  ring

/-- On total weight zero the signs of `homForm_apply` and of the bridge combine to `nodeSign`. -/
lemma sign_of_weight_zero (J : Fin 4 → ℕ) (k : LIdx J)
    (hw : ∑ l, ((J l : ℤ) - 2 * (k l : ℕ)) = 0) :
    (-1 : ℂ) ^ (((Fin.rev (k 2) : Fin (J 2 + 1)) : ℕ) + (Fin.rev (k 3) : Fin (J 3 + 1))) *
        (-1 : ℂ) ^ (J 1 + J 3 + (k 0 : ℕ) + k 1) = nodeSign J := by
  unfold nodeSign
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := J 1 + J 2 + (∑ a, J a) / 2)]
  congr 1
  have h2 := (k 2).isLt
  have h3 := (k 3).isLt
  rw [Fin.sum_univ_four] at hw
  rw [Fin.sum_univ_four]
  simp only [Fin.val_rev]
  omega

/-- **The node identity at the projections of two components**: the coherent EPRL node tensor is the
product of the self-dual and anti-self-dual coherent node tensors. No sign survives. -/
theorem eprlCohNode_projOf (g : Fin 4 → SU2) (k : LIdx n) (l : LIdx m) :
    eprlCohNode n m g (projOf n k) (projOf m l) = cohInt n g k * cohInt m g l := by
  rw [eprlCohNode_projOf_aux, homForm_apply, homForm_apply]
  have hk : (legEquiv n).symm ((k 0, k 1), (Fin.rev (Fin.rev (k 2)), Fin.rev (Fin.rev (k 3)))) = k := by
    rw [Equiv.symm_apply_eq]
    simp only [Fin.rev_rev]
    rfl
  have hl : (legEquiv m).symm ((l 0, l 1), (Fin.rev (Fin.rev (l 2)), Fin.rev (Fin.rev (l 3)))) = l := by
    rw [Equiv.symm_apply_eq]
    simp only [Fin.rev_rev]
    rfl
  simp only [hk, hl]
  by_cases hwk : ∑ i, ((n i : ℤ) - 2 * (k i : ℕ)) = 0
  · by_cases hwl : ∑ i, ((m i : ℤ) - 2 * (l i : ℕ)) = 0
    · have sk := sign_of_weight_zero n k hwk
      have sl := sign_of_weight_zero m l hwl
      have hen : Even (∑ a, n a) := by
        rw [Fin.sum_univ_four] at hwk ⊢
        exact ⟨(k 0 : ℕ) + k 1 + k 2 + k 3, by omega⟩
      have hem : Even (∑ a, m a) := by
        rw [Fin.sum_univ_four] at hwl ⊢
        exact ⟨(l 0 : ℕ) + l 1 + l 2 + l 3, by omega⟩
      have hs := nodeSign_add n m hen hem
      calc _ = (nodeSign (n + m) * nodeSign n * nodeSign m) * (cohInt n g k * cohInt m g l) := by
            rw [← sk, ← sl]; ring
        _ = _ := by rw [hs, one_mul]
    · have : cohInt n g k * cohInt m g l = 0 := by
        rw [invariant_weight_zero m (cohInt_isInvariantN g) l hwl, mul_zero]
      rw [this]
      rw [invariant_weight_zero m (cohInt_isInvariantN g) l hwl]; ring
  · have : cohInt n g k = 0 := invariant_weight_zero n (cohInt_isInvariantN g) k hwk
    rw [this]; ring

/-- A nonzero node tensor has projections of the form `projOf J k`. -/
lemma exists_projOf_of_fourJNode_ne_zero (J : Fin 4 → ℕ) (x : ℕ) (κ : Fin 4 → ℤ)
    (h : fourJNode J x κ ≠ 0) : ∃ k : LIdx J, κ = projOf J k := by
  have hs := fourJ_support (by simpa [fourJNode] using h)
  obtain ⟨-, a0, a1, a2, a3⟩ := hs
  have key : ∀ l : Fin 4, Recoupling.AdmProj (J l) (κ l) → ∃ i : Fin (J l + 1), κ l = (J l : ℤ) - 2 * (i : ℕ) := by
    intro l ⟨h1, h2, h3⟩
    refine ⟨⟨(((J l : ℤ) - κ l) / 2).toNat, by omega⟩, ?_⟩
    show κ l = (J l : ℤ) - 2 * ((((J l : ℤ) - κ l) / 2).toNat : ℕ)
    omega
  obtain ⟨i0, e0⟩ := key 0 a0
  obtain ⟨i1, e1⟩ := key 1 a1
  obtain ⟨i2, e2⟩ := key 2 a2
  obtain ⟨i3, e3⟩ := key 3 a3
  refine ⟨(legEquiv J).symm ((i0, i1), (i2, i3)), ?_⟩
  funext l
  fin_cases l
  · exact e0
  · exact e1
  · exact e2
  · exact e3

/-- `projNode` vanishes off the projections of components. -/
lemma projNode_eq_zero_of_not (J : Fin 4 → ℕ) (v : LIdx J → ℂ) (κ : Fin 4 → ℤ)
    (h : ¬ ∃ k : LIdx J, κ = projOf J k) : projNode J v κ = 0 := by
  unfold projNode
  refine Finset.sum_eq_zero fun k _ => ?_
  have : (∏ l, if κ l = (J l : ℤ) - 2 * ((k l : Fin (J l + 1)) : ℕ) then (1 : ℂ) else 0) = 0 := by
    by_contra hne
    apply h
    refine ⟨k, funext fun l => ?_⟩
    by_contra hl
    apply hne
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)
  rw [this, zero_mul]

/-- The node tensor vanishes unless both projection tuples are those of components. -/
lemma eprlNode_eq_zero_of_not (z : ℕ) (μ ν : Fin 4 → ℤ)
    (h : ¬ ((∃ k : LIdx n, μ = projOf n k) ∧ ∃ l : LIdx m, ν = projOf m l)) :
    eprlNode n m z μ ν = 0 := by
  unfold eprlNode
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases h1 : fourJNode n p.1 μ = 0
  · rw [h1]; ring
  · by_cases h2 : fourJNode m p.2 ν = 0
    · rw [h2]; ring
    · exact absurd ⟨exists_projOf_of_fourJNode_ne_zero n _ _ h1,
        exists_projOf_of_fourJNode_ne_zero m _ _ h2⟩ h

/-- **The node identity**: for every pair of projection tuples, the coherent EPRL node tensor is the
product of the self-dual and anti-self-dual coherent node tensors `projNode` of the `SU(2)` coherent
intertwiners `ι_n(g)` and `ι_m(g)`, with no sign. -/
theorem eprlCohNode_eq (g : Fin 4 → SU2) (μ ν : Fin 4 → ℤ) :
    eprlCohNode n m g μ ν = projNode n (cohInt n g) μ * projNode m (cohInt m g) ν := by
  by_cases h : (∃ k : LIdx n, μ = projOf n k) ∧ ∃ l : LIdx m, ν = projOf m l
  · obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := h
    rw [eprlCohNode_projOf, projNode_projOf, projNode_projOf]
  · have h0 : eprlCohNode n m g μ ν = 0 := by
      unfold eprlCohNode
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [eprlNode_eq_zero_of_not n m z μ ν h, mul_zero]
    rw [h0]
    by_cases h1 : ∃ k : LIdx n, μ = projOf n k
    · have h2 : ¬ ∃ l : LIdx m, ν = projOf m l := fun h2 => h ⟨h1, h2⟩
      rw [projNode_eq_zero_of_not m _ ν h2, mul_zero]
    · rw [projNode_eq_zero_of_not n _ μ h1, zero_mul]

end NodeBridge

end Lightlike.Asymptotics.EPRL
