import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# The Fock representation of the CAR over a Hilbert space (Dereziński, Theorem 28)

J. Dereziński, arXiv:math-ph/0511030 (read): Section 5.3, p. 20 (the antisymmetric Fock space `Γₐ(Z)`); Section 7.1,
pp. 29-30 (the creation and annihilation operators `a*(w)`, `a(w)`, the field operators `φ(w) = a*(w) + a(w)`, and
Theorem 28: they form an irreducible representation of the CAR over `Re(Z ⊕ Z̄)`).

For a Hilbert basis `(eᵢ)_{i ∈ ι}` of `Z` with a linear order on `ι`, `Γₐ(Z)` has the orthonormal basis
`e_{i₁} ∧ ⋯ ∧ e_{iₚ}` (`i₁ < ⋯ < iₚ`), one vector per finite set `S ⊆ ι`. Here the Fock space is any Hilbert space `Γ`
with a Hilbert basis `B` indexed by `Finset ι` (for instance `ℓ²(Finset ι)`), and `B S` stands for the normalized wedge
product of the `eᵢ`, `i ∈ S`, in increasing order:

* `fermiCre B j` maps `B S` to `(-1)^{#{i ∈ S, i < j}} B (S ∪ {j})` for `j ∉ S` and to `0` otherwise
  (`fermiCre_basis`), `fermiAnn B j` is its adjoint, and they satisfy the CAR (`fermiAnn_fermiCre_anticomm`,
  `fermiCre_anticomm`);
* `creW B b w` is `a*(w) = ∑ⱼ ⟪eⱼ, w⟫ a*(eⱼ)`, of norm at most `‖w‖`, `annW B b w = a*(w)*`, and
  `annW_creW_anticomm`, `creW_anticomm`, `annW_anticomm` are the CAR for general `w`;
* `fockField B b w = a*(w) + a(w)` is self-adjoint with `[φ(w), φ(w')]₊ = 2 Re⟪w, w'⟫` (`fockField_anticomm`), and the
  representation is irreducible (`fockField_irreducible`).
-/

open scoped InnerProductSpace
open Filter Topology

namespace Lightlike.OperatorAlgebras

variable {ι : Type*} [LinearOrder ι]

/-- `ℓ²(Finset ι)`, the coefficient space of the Fock space. -/
noncomputable abbrev FermiL2 (ι : Type*) := lp (fun _ : Finset ι => ℂ) 2

/-- The sign `(-1)^{#{i ∈ S, i < j}}` of inserting `j` into `S`. -/
def fermiSign (S : Finset ι) (j : ι) : ℂ := (-1) ^ (S.filter (· < j)).card

lemma norm_fermiSign (S : Finset ι) (j : ι) : ‖fermiSign S j‖ = 1 := by
  simp [fermiSign]

lemma fermiSign_mul_self (S : Finset ι) (j : ι) : fermiSign S j * fermiSign S j = 1 := by
  rw [fermiSign, ← pow_add, ← two_mul, pow_mul]; simp

lemma conj_fermiSign (S : Finset ι) (j : ι) : (starRingEnd ℂ) (fermiSign S j) = fermiSign S j := by
  simp [fermiSign]

/-- The coefficients of `fermiCre j ψ`. -/
def creFun (j : ι) (ψ : Finset ι → ℂ) (T : Finset ι) : ℂ :=
  if j ∈ T then fermiSign (T.erase j) j * ψ (T.erase j) else 0

lemma sum_norm_sq_creFun_le (j : ι) (ψ : FermiL2 ι) (s : Finset (Finset ι)) :
    ∑ T ∈ s, ‖creFun j ψ T‖ ^ (2 : ℝ) ≤ ‖ψ‖ ^ (2 : ℝ) := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  calc ∑ T ∈ s, ‖creFun j ψ T‖ ^ (2 : ℝ) = ∑ T ∈ s.filter (j ∈ ·), ‖ψ (T.erase j)‖ ^ (2 : ℝ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun T _ => ?_
        unfold creFun
        split_ifs <;> simp [norm_mul, norm_fermiSign]
    _ = ∑ S ∈ (s.filter (j ∈ ·)).image (fun T => T.erase j), ‖ψ S‖ ^ (2 : ℝ) := by
        rw [Finset.sum_image]
        intro T hT T' hT' he
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hT hT'
        rw [← Finset.insert_erase hT.2, ← Finset.insert_erase hT'.2]
        exact congrArg (insert j) he
    _ ≤ ‖ψ‖ ^ (2 : ℝ) := by
        have := lp.sum_rpow_le_norm_rpow h2 ψ ((s.filter (j ∈ ·)).image (fun T => T.erase j))
        simpa using this

lemma memℓp_creFun (j : ι) (ψ : FermiL2 ι) : Memℓp (creFun j ψ) 2 :=
  memℓp_gen' (C := ‖ψ‖ ^ (2 : ℝ)) fun s => by simpa using sum_norm_sq_creFun_le j ψ s

lemma creFun_add (j : ι) (ψ φ : Finset ι → ℂ) (T : Finset ι) :
    creFun j (ψ + φ) T = creFun j ψ T + creFun j φ T := by
  unfold creFun; split_ifs <;> simp [mul_add]

lemma creFun_smul (j : ι) (r : ℂ) (ψ : Finset ι → ℂ) (T : Finset ι) :
    creFun j (r • ψ) T = r * creFun j ψ T := by
  unfold creFun; split_ifs <;> simp; ring


/-- The coefficients `creFun j ψ` as a bounded linear map of `ℓ²(Finset ι)`. -/
noncomputable def creCoeff (j : ι) : FermiL2 ι →ₗ[ℂ] FermiL2 ι where
  toFun ψ := ⟨creFun j ψ, memℓp_creFun j ψ⟩
  map_add' ψ φ := by
    ext T; simp only [lp.coeFn_add, Pi.add_apply, creFun]; split_ifs <;> ring
  map_smul' c ψ := by
    ext T; simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, creFun, RingHom.id_apply]
    split_ifs <;> ring

lemma creCoeff_apply (j : ι) (ψ : FermiL2 ι) (T : Finset ι) : creCoeff j ψ T = creFun j ψ T := rfl

lemma norm_creCoeff_le (j : ι) (ψ : FermiL2 ι) : ‖creCoeff j ψ‖ ≤ 1 * ‖ψ‖ := by
  simp only [one_mul]
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) h2).mp ?_
  rw [lp.norm_rpow_eq_tsum h2]
  exact Real.tsum_le_of_sum_le (fun T => by positivity) fun s => by
    simpa [creCoeff_apply] using sum_norm_sq_creFun_le j ψ s

variable {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
variable (B : HilbertBasis (Finset ι) ℂ Γ)

/-- The operator of `Γ` acting on the coefficients in the basis `B` as the bounded linear map `f` of `ℓ²(Finset ι)`. -/
noncomputable def ofCoeff (f : FermiL2 ι →ₗ[ℂ] FermiL2 ι) (C : ℝ) (hf : ∀ ψ, ‖f ψ‖ ≤ C * ‖ψ‖) : Γ →L[ℂ] Γ :=
  LinearMap.mkContinuous
    ((B.repr.symm.toLinearEquiv.toLinearMap ∘ₗ f) ∘ₗ B.repr.toLinearEquiv.toLinearMap) C
    (fun x => by
      show ‖B.repr.symm (f (B.repr x))‖ ≤ C * ‖x‖
      rw [LinearIsometryEquiv.norm_map]
      calc ‖f (B.repr x)‖ ≤ C * ‖B.repr x‖ := hf _
        _ = C * ‖x‖ := by rw [LinearIsometryEquiv.norm_map])

lemma repr_ofCoeff (f : FermiL2 ι →ₗ[ℂ] FermiL2 ι) (C : ℝ) (hf : ∀ ψ, ‖f ψ‖ ≤ C * ‖ψ‖) (x : Γ) :
    B.repr (ofCoeff B f C hf x) = f (B.repr x) := by
  show B.repr (B.repr.symm (f (B.repr x))) = f (B.repr x)
  exact B.repr.apply_symm_apply _

lemma norm_ofCoeff_le (f : FermiL2 ι →ₗ[ℂ] FermiL2 ι) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ ψ, ‖f ψ‖ ≤ C * ‖ψ‖) :
    ‖ofCoeff B f C hf‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- Two operators with the same coefficients are equal. -/
lemma ext_repr {A A' : Γ →L[ℂ] Γ} (h : ∀ x T, B.repr (A x) T = B.repr (A' x) T) : A = A' :=
  ContinuousLinearMap.ext fun x => B.repr.injective (lp.ext (funext (h x)))

/-- **The creation operator** `a*(e_j)`, of norm at most `1`. -/
noncomputable def fermiCre (j : ι) : Γ →L[ℂ] Γ := ofCoeff B (creCoeff j) 1 (norm_creCoeff_le j)

lemma repr_fermiCre_apply (j : ι) (x : Γ) (T : Finset ι) : B.repr (fermiCre B j x) T = creFun j (B.repr x) T := by
  rw [fermiCre, repr_ofCoeff, creCoeff_apply]

/-- Inserting `k ≠ j` into `S` changes the sign at `j` by `-1` iff `k < j`. -/
lemma fermiSign_insert {S : Finset ι} {k : ι} (j : ι) (hk : k ∉ S) :
    fermiSign (insert k S) j = (if k < j then -1 else 1) * fermiSign S j := by
  unfold fermiSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hk]), pow_succ]; ring
  · ring

lemma fermiCre_basis (j : ι) (S : Finset ι) :
    fermiCre B j (B S) = if j ∈ S then 0 else fermiSign S j • B (insert j S) := by
  apply B.repr.injective
  ext T
  rw [repr_fermiCre_apply, HilbertBasis.repr_self, creFun]
  by_cases hjS : j ∈ S
  · rw [if_pos hjS, map_zero]
    split_ifs with hjT
    · have hne : T.erase j ≠ S := fun h => (Finset.notMem_erase j T) (h ▸ hjS)
      simp [lp.single_apply, Pi.single_apply, hne]
    · simp
  · rw [if_neg hjS, map_smul, HilbertBasis.repr_self, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hT : T = insert j S
    · subst hT
      rw [if_pos (Finset.mem_insert_self j S), Finset.erase_insert hjS]
      simp [lp.single_apply_self]
    · split_ifs with hjT
      · have hne : T.erase j ≠ S := fun h => hT (by rw [← h, Finset.insert_erase hjT])
        simp [lp.single_apply, Pi.single_apply, hne, hT]
      · simp [lp.single_apply, Pi.single_apply, hT]

/-- **The annihilation operator** `a(e_j)`, the adjoint of `a*(e_j)`. -/
noncomputable def fermiAnn (j : ι) : Γ →L[ℂ] Γ := ContinuousLinearMap.adjoint (fermiCre B j)

lemma repr_fermiAnn_apply (j : ι) (φ : Γ) (S : Finset ι) :
    B.repr (fermiAnn B j φ) S = if j ∈ S then 0 else fermiSign S j * B.repr φ (insert j S) := by
  rw [HilbertBasis.repr_apply_apply, fermiAnn, ContinuousLinearMap.adjoint_inner_right, fermiCre_basis]
  split_ifs
  · simp
  · rw [inner_smul_left, conj_fermiSign, ← HilbertBasis.repr_apply_apply]

/-- **The CAR** `a(eᵢ) a*(eⱼ) + a*(eⱼ) a(eᵢ) = δᵢⱼ`. -/
theorem fermiAnn_fermiCre_anticomm (i j : ι) :
    fermiAnn B i * fermiCre B j + fermiCre B j * fermiAnn B i = if i = j then (1 : Γ →L[ℂ] Γ) else 0 := by
  refine ext_repr B fun ψ T => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, map_add, lp.coeFn_add, Pi.add_apply]
  rw [repr_fermiAnn_apply, repr_fermiCre_apply, creFun, repr_fermiCre_apply, creFun, repr_fermiAnn_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, ContinuousLinearMap.one_apply]
    by_cases hT : i ∈ T
    · rw [if_pos hT, if_pos hT, if_neg (Finset.notMem_erase i T), Finset.insert_erase hT, zero_add, ← mul_assoc,
        fermiSign_mul_self, one_mul]
    · rw [if_neg hT, if_neg hT, if_pos (Finset.mem_insert_self i T), Finset.erase_insert hT, add_zero, ← mul_assoc,
        fermiSign_mul_self, one_mul]
  · rw [if_neg hij]
    simp only [ContinuousLinearMap.zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
    by_cases hiT : i ∈ T
    · have : i ∈ T.erase j := Finset.mem_erase.mpr ⟨hij, hiT⟩
      rw [if_pos hiT]
      split_ifs <;> simp
    · by_cases hjT : j ∈ T
      · have hiU : i ∉ T.erase j := fun h => hiT (Finset.mem_of_mem_erase h)
        rw [if_neg hiT, if_pos (Finset.mem_insert_of_mem hjT), if_pos hjT, if_neg hiU,
          Finset.erase_insert_of_ne hij]
        have h1 : fermiSign T i = (if j < i then -1 else 1) * fermiSign (T.erase j) i := by
          conv_lhs => rw [← Finset.insert_erase hjT]
          exact fermiSign_insert i (Finset.notMem_erase j T)
        have h2 : fermiSign (insert i (T.erase j)) j = (if i < j then -1 else 1) * fermiSign (T.erase j) j :=
          fermiSign_insert j hiU
        rw [h1, h2]
        rcases lt_or_gt_of_ne hij with h | h
        · simp only [h, if_true, not_lt.mpr h.le, if_false]; ring
        · simp only [h, if_true, not_lt.mpr h.le, if_false]; ring
      · have hj : j ∉ insert i T := by
          rw [Finset.mem_insert]; push_neg; exact ⟨Ne.symm hij, hjT⟩
        rw [if_neg hiT, if_neg hj, if_neg hjT]; ring

/-- `a*(eᵢ) a*(eⱼ) + a*(eⱼ) a*(eᵢ) = 0`. -/
theorem fermiCre_anticomm (i j : ι) : fermiCre B i * fermiCre B j + fermiCre B j * fermiCre B i = (0 : Γ →L[ℂ] Γ) := by
  refine ext_repr B fun ψ T => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, map_add, lp.coeFn_add, Pi.add_apply,
    ContinuousLinearMap.zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply]
  rw [repr_fermiCre_apply, creFun, repr_fermiCre_apply, creFun, repr_fermiCre_apply, creFun, repr_fermiCre_apply, creFun]
  by_cases hij : i = j
  · subst hij
    split_ifs with h1 h2 <;> simp_all [Finset.notMem_erase]
  · by_cases hiT : i ∈ T
    · by_cases hjT : j ∈ T
      · have hj : j ∈ T.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hjT⟩
        have hi : i ∈ T.erase j := Finset.mem_erase.mpr ⟨hij, hiT⟩
        rw [if_pos hiT, if_pos hj, if_pos hjT, if_pos hi, Finset.erase_right_comm]
        set U := (T.erase j).erase i with hU
        have hU1 : T.erase i = insert j U := by
          rw [hU, Finset.erase_right_comm, Finset.insert_erase hj]
        have hU2 : T.erase j = insert i U := by rw [hU, Finset.insert_erase hi]
        have hjU : j ∉ U := by rw [hU]; simp
        have hiU : i ∉ U := by rw [hU]; simp
        rw [hU1, hU2, fermiSign_insert i hjU, fermiSign_insert j hiU]
        try rw [Finset.erase_insert hjU]
        try rw [Finset.erase_insert hiU]
        rcases lt_or_gt_of_ne hij with h | h
        · simp only [h, if_true, not_lt.mpr h.le, if_false]; ring
        · simp only [h, if_true, not_lt.mpr h.le, if_false]; ring
      · have hj : j ∉ T.erase i := fun h => hjT (Finset.mem_of_mem_erase h)
        rw [if_pos hiT, if_neg hj, if_neg hjT]; ring
    · have hi : ∀ U : Finset ι, U ⊆ T → i ∉ U := fun U hU h => hiT (hU h)
      rw [if_neg hiT]
      split_ifs with h1 h2
      · exact absurd h2 (hi _ (Finset.erase_subset _ _))
      · ring
      · ring


lemma adjoint_sum_fermiCre (J : Finset ι) (c : ι → ℂ) :
    ContinuousLinearMap.adjoint (∑ j ∈ J, c j • fermiCre B j) = ∑ j ∈ J, star (c j) • fermiAnn B j := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smulₛₗ]
  rfl

/-- `A*A + AA* = (∑ |cⱼ|²) 1` for `A = ∑ⱼ cⱼ a*(eⱼ)`. -/
lemma adjoint_mul_add_mul_adjoint_sum_cre (J : Finset ι) (c : ι → ℂ) :
    ContinuousLinearMap.adjoint (∑ j ∈ J, c j • fermiCre B j) * (∑ j ∈ J, c j • fermiCre B j) +
        (∑ j ∈ J, c j • fermiCre B j) * ContinuousLinearMap.adjoint (∑ j ∈ J, c j • fermiCre B j) =
      ((∑ j ∈ J, ‖c j‖ ^ 2 : ℝ) : ℂ) • (1 : Γ →L[ℂ] Γ) := by
  rw [adjoint_sum_fermiCre B]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.sum_comm (s := J) (t := J) (f := fun j i => (c j • fermiCre B j) * (star (c i) • fermiAnn B i)),
    ← Finset.sum_add_distrib]
  have hpt : ∀ i ∈ J, ∑ j ∈ J, (star (c i) • fermiAnn B i) * (c j • fermiCre B j) +
      ∑ j ∈ J, (c j • fermiCre B j) * (star (c i) • fermiAnn B i) =
      ((‖c i‖ ^ 2 : ℝ) : ℂ) • (1 : Γ →L[ℂ] Γ) := by
    intro i hi
    rw [← Finset.sum_add_distrib]
    have : ∀ j ∈ J, (star (c i) • fermiAnn B i) * (c j • fermiCre B j) + (c j • fermiCre B j) * (star (c i) • fermiAnn B i) =
        if i = j then (star (c i) * c i) • (1 : Γ →L[ℂ] Γ) else 0 := by
      intro j _
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c j), ← smul_add, fermiAnn_fermiCre_anticomm B]
      split_ifs with hij
      · subst hij; rfl
      · rw [smul_zero]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hi]
    congr 1
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_smul]
  push_cast; rfl

/-- **`‖∑ⱼ cⱼ a*(eⱼ) ψ‖² ≤ (∑ |cⱼ|²) ‖ψ‖²`**, from the CAR. -/
lemma norm_sq_sum_cre_apply_le (J : Finset ι) (c : ι → ℂ) (ψ : Γ) :
    ‖(∑ j ∈ J, c j • fermiCre B j) ψ‖ ^ 2 ≤ (∑ j ∈ J, ‖c j‖ ^ 2) * ‖ψ‖ ^ 2 := by
  set A := ∑ j ∈ J, c j • fermiCre B j
  have h := congrArg (fun T : Γ →L[ℂ] Γ => ⟪ψ, T ψ⟫_ℂ) (adjoint_mul_add_mul_adjoint_sum_cre B J c)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, inner_add_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right] at h
  have e1 : ⟪ψ, ContinuousLinearMap.adjoint A (A ψ)⟫_ℂ = ⟪A ψ, A ψ⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_right A ψ (A ψ)
  have e2 : ⟪ψ, A (ContinuousLinearMap.adjoint A ψ)⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint A ψ, ContinuousLinearMap.adjoint A ψ⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_left A (ContinuousLinearMap.adjoint A ψ) ψ).symm
  rw [e1, e2] at h
  have k1 : (⟪A ψ, A ψ⟫_ℂ).re = ‖A ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (A ψ)
  have k2 : (⟪ContinuousLinearMap.adjoint A ψ, ContinuousLinearMap.adjoint A ψ⟫_ℂ).re =
      ‖ContinuousLinearMap.adjoint A ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (ContinuousLinearMap.adjoint A ψ)
  have k3 : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hre := congrArg Complex.re h
  rw [Complex.add_re, Complex.re_ofReal_mul, k1, k2, k3] at hre
  nlinarith [sq_nonneg ‖ContinuousLinearMap.adjoint A ψ‖]


/-- The coefficients of `a*(w) ψ` for `w = ∑ cⱼ eⱼ`: `(a*(w) ψ)(T) = ∑_{j ∈ T} cⱼ (a*(eⱼ) ψ)(T)`. -/
def creWFun (c : ι → ℂ) (ψ : Finset ι → ℂ) (T : Finset ι) : ℂ := ∑ j ∈ T, c j * creFun j ψ T

lemma sum_cre_apply_coeff (c : ι → ℂ) (x : Γ) (J : Finset ι) (T : Finset ι) :
    B.repr ((∑ j ∈ J, c j • fermiCre B j) x) T = ∑ j ∈ J, c j * creFun j (B.repr x) T := by
  rw [ContinuousLinearMap.sum_apply, map_sum, lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.smul_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, repr_fermiCre_apply]

lemma creWFun_eq_sum (c : ι → ℂ) (x : Γ) {J T : Finset ι} (hT : T ⊆ J) :
    creWFun c (B.repr x) T = B.repr ((∑ j ∈ J, c j • fermiCre B j) x) T := by
  rw [sum_cre_apply_coeff, creWFun]
  refine Finset.sum_subset hT fun j _ hj => ?_
  simp [creFun, hj]

lemma sum_norm_sq_creWFun_le (c : ι → ℂ) {C : ℝ} (hC : ∀ J : Finset ι, ∑ j ∈ J, ‖c j‖ ^ 2 ≤ C) (x : Γ)
    (s : Finset (Finset ι)) : ∑ T ∈ s, ‖creWFun c (B.repr x) T‖ ^ (2 : ℝ) ≤ C * ‖x‖ ^ 2 := by
  set J := s.sup id with hJ
  have hsub : ∀ T ∈ s, T ⊆ J := fun T hT => Finset.le_sup (f := id) hT
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  calc ∑ T ∈ s, ‖creWFun c (B.repr x) T‖ ^ (2 : ℝ)
        = ∑ T ∈ s, ‖B.repr ((∑ j ∈ J, c j • fermiCre B j) x) T‖ ^ (2 : ℝ) :=
        Finset.sum_congr rfl fun T hT => by rw [creWFun_eq_sum B c x (hsub T hT)]
    _ ≤ ‖B.repr ((∑ j ∈ J, c j • fermiCre B j) x)‖ ^ (2 : ℝ) := by
        simpa using lp.sum_rpow_le_norm_rpow h2 (B.repr ((∑ j ∈ J, c j • fermiCre B j) x)) s
    _ = ‖(∑ j ∈ J, c j • fermiCre B j) x‖ ^ 2 := by rw [LinearIsometryEquiv.norm_map]; norm_cast
    _ ≤ (∑ j ∈ J, ‖c j‖ ^ 2) * ‖x‖ ^ 2 := norm_sq_sum_cre_apply_le B J c x
    _ ≤ C * ‖x‖ ^ 2 := by gcongr; exact hC J

/-- `ℓ²(Finset ι)` with its canonical Hilbert basis. -/
noncomputable def fermiL2Basis (ι : Type*) : HilbertBasis (Finset ι) ℂ (FermiL2 ι) := ⟨LinearIsometryEquiv.refl ℂ _⟩

lemma fermiL2Basis_repr (ψ : FermiL2 ι) : (fermiL2Basis ι).repr ψ = ψ := rfl

lemma memℓp_creWFun (c : ι → ℂ) {C : ℝ} (hC : ∀ J : Finset ι, ∑ j ∈ J, ‖c j‖ ^ 2 ≤ C) (ψ : FermiL2 ι) :
    Memℓp (creWFun c ψ) 2 := by
  have := fun s => sum_norm_sq_creWFun_le (fermiL2Basis ι) c hC ψ s
  exact memℓp_gen' (C := C * ‖ψ‖ ^ 2) fun s => by simpa [fermiL2Basis_repr] using this s

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (b : HilbertBasis ι ℂ Z)

lemma sum_norm_sq_repr_le (w : Z) (J : Finset ι) : ∑ j ∈ J, ‖b.repr w j‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  have := b.orthonormal.sum_inner_products_le (x := w) (s := J)
  simpa [HilbertBasis.repr_apply_apply] using this

/-- The coefficients of `a*(w)` as a linear map of `ℓ²(Finset ι)`. -/
noncomputable def creWCoeff (w : Z) : FermiL2 ι →ₗ[ℂ] FermiL2 ι where
  toFun ψ := ⟨creWFun (fun j => b.repr w j) ψ, memℓp_creWFun _ (sum_norm_sq_repr_le b w) ψ⟩
  map_add' ψ φ := by
    ext T
    simp only [lp.coeFn_add, Pi.add_apply, creWFun, creFun_add, mul_add, Finset.sum_add_distrib]
  map_smul' r ψ := by
    ext T
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, creWFun, creFun_smul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

lemma creWCoeff_apply (w : Z) (ψ : FermiL2 ι) (T : Finset ι) :
    creWCoeff b w ψ T = ∑ j ∈ T, b.repr w j * creFun j ψ T := rfl

lemma norm_creWCoeff_le (w : Z) (ψ : FermiL2 ι) : ‖creWCoeff b w ψ‖ ≤ ‖w‖ * ‖ψ‖ := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) h2).mp ?_
  rw [lp.norm_rpow_eq_tsum h2, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  refine Real.tsum_le_of_sum_le (fun T => by positivity) fun s => ?_
  have := sum_norm_sq_creWFun_le (fermiL2Basis ι) (fun j => b.repr w j) (sum_norm_sq_repr_le b w) ψ s
  simp only [fermiL2Basis_repr] at this
  simp only [ENNReal.toReal_ofNat]
  calc ∑ T ∈ s, ‖creWCoeff b w ψ T‖ ^ (2 : ℝ) ≤ ‖w‖ ^ 2 * ‖ψ‖ ^ 2 := this
    _ = ‖w‖ ^ (2 : ℝ) * ‖ψ‖ ^ (2 : ℝ) := by norm_cast

/-- **The creation operator** `a*(w) = ∑ⱼ ⟪eⱼ, w⟫ a*(eⱼ)` of a vector `w` of the one-particle space, of norm at most
`‖w‖`. -/
noncomputable def creW (w : Z) : Γ →L[ℂ] Γ := ofCoeff B (creWCoeff b w) ‖w‖ (norm_creWCoeff_le b w)

lemma repr_creW_apply (w : Z) (x : Γ) (T : Finset ι) :
    B.repr (creW B b w x) T = ∑ j ∈ T, b.repr w j * creFun j (B.repr x) T := by
  rw [creW, repr_ofCoeff, creWCoeff_apply]

lemma creW_add (w w' : Z) : creW B b (w + w') = creW B b w + creW B b w' := by
  refine ext_repr B fun x T => ?_
  simp only [repr_creW_apply, ContinuousLinearMap.add_apply, map_add, lp.coeFn_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

lemma creW_smul (r : ℂ) (w : Z) : creW B b (r • w) = r • creW B b w := by
  refine ext_repr B fun x T => ?_
  simp only [repr_creW_apply, ContinuousLinearMap.smul_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

lemma creW_basis (i : ι) : creW B b (b i) = fermiCre B i := by
  refine ext_repr B fun x T => ?_
  rw [repr_creW_apply, repr_fermiCre_apply]
  simp only [HilbertBasis.repr_self, lp.single_apply, Pi.single_apply]
  by_cases hi : i ∈ T
  · rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (fun h => absurd hi h)]; simp
  · rw [Finset.sum_eq_zero (fun j hj => by simp [show j ≠ i from fun h => hi (h ▸ hj)])]
    simp [creFun, hi]

lemma norm_creW_le (w : Z) : ‖creW B b w‖ ≤ ‖w‖ := norm_ofCoeff_le B _ (norm_nonneg w) _

/-- `a(eⱼ) a*(eⱼ)` keeps the coefficients of the sets without `j`. -/
lemma fermiAnn_fermiCre_apply (j : ι) (x : Γ) (T : Finset ι) :
    B.repr (fermiAnn B j (fermiCre B j x)) T = if j ∈ T then 0 else B.repr x T := by
  rw [repr_fermiAnn_apply]
  split_ifs with h
  · rfl
  · rw [repr_fermiCre_apply, creFun, if_pos (Finset.mem_insert_self j T), Finset.erase_insert h, ← mul_assoc,
      fermiSign_mul_self, one_mul]

/-- The coefficients of the sets disjoint from `J`, as a linear map of `ℓ²(Finset ι)`. -/
noncomputable def disjCoeff (J : Finset ι) : FermiL2 ι →ₗ[ℂ] FermiL2 ι where
  toFun ψ := ⟨fun T => if Disjoint T J then ψ T else 0, Memℓp.mono' (lp.memℓp ψ) fun T => by split_ifs <;> simp⟩
  map_add' ψ φ := by
    ext T
    simp only [lp.coeFn_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' r ψ := by
    ext T
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

lemma disjCoeff_apply (J : Finset ι) (ψ : FermiL2 ι) (T : Finset ι) :
    disjCoeff J ψ T = if Disjoint T J then ψ T else 0 := rfl

lemma norm_disjCoeff_le (J : Finset ι) (ψ : FermiL2 ι) : ‖disjCoeff J ψ‖ ≤ 1 * ‖ψ‖ := by
  rw [one_mul]
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine lp.norm_le_of_forall_sum_le h2 (norm_nonneg _) fun s => ?_
  refine le_trans ?_ (lp.sum_rpow_le_norm_rpow h2 ψ s)
  refine Finset.sum_le_sum fun T _ => ?_
  by_cases hT : Disjoint T J <;> simp [disjCoeff_apply, hT, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]

/-- The restriction to the basis vectors of the sets disjoint from `J`. -/
noncomputable def restrictDisj (J : Finset ι) : Γ →L[ℂ] Γ := ofCoeff B (disjCoeff J) 1 (norm_disjCoeff_le J)

lemma repr_restrictDisj_apply (J : Finset ι) (x : Γ) (T : Finset ι) :
    B.repr (restrictDisj B J x) T = if Disjoint T J then B.repr x T else 0 := by
  rw [restrictDisj, repr_ofCoeff, disjCoeff_apply]

/-- A subspace invariant under the `a(eⱼ) a*(eⱼ)` is invariant under every `restrictDisj J`. -/
lemma restrictDisj_mem {W : Submodule ℂ Γ} (hW : ∀ j, ∀ x ∈ W, fermiAnn B j (fermiCre B j x) ∈ W) (J : Finset ι) :
    ∀ x ∈ W, restrictDisj B J x ∈ W := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro x hx
    have : restrictDisj B ∅ x = x := B.repr.injective (lp.ext (funext fun T => by simp [repr_restrictDisj_apply]))
    rwa [this]
  | insert j J hj ih =>
    intro x hx
    have : restrictDisj B (insert j J) x = fermiAnn B j (fermiCre B j (restrictDisj B J x)) := by
      refine B.repr.injective (lp.ext (funext fun T => ?_))
      rw [fermiAnn_fermiCre_apply, repr_restrictDisj_apply, repr_restrictDisj_apply]
      by_cases hjT : j ∈ T <;> simp [hjT, Finset.disjoint_insert_right]
    rw [this]
    exact hW j _ (ih x hx)

lemma repr_sum_basis (s : Finset (Finset ι)) (x : Γ) (T : Finset ι) :
    B.repr (∑ S ∈ s, B.repr x S • B S) T = if T ∈ s then B.repr x T else 0 := by
  rw [map_sum, lp.coeFn_sum, Finset.sum_apply]
  simp only [map_smul, HilbertBasis.repr_self, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

lemma restrictDisj_partial (x : Γ) {s : Finset (Finset ι)} (hs : ∅ ∈ s) :
    restrictDisj B (s.sup id) (∑ S ∈ s, B.repr x S • B S) = B.repr x ∅ • B ∅ := by
  refine B.repr.injective (lp.ext (funext fun T => ?_))
  rw [repr_restrictDisj_apply, repr_sum_basis, map_smul, HilbertBasis.repr_self, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, Pi.single_apply, smul_eq_mul]
  by_cases hT : T = ∅
  · subst hT; simp [hs]
  · rw [if_neg hT, mul_zero]
    split_ifs with h1 h2
    · exfalso
      have hsub : T ⊆ s.sup id := Finset.le_sup (f := id) h2
      exact hT (Finset.disjoint_self_iff_empty T |>.mp (Finset.disjoint_of_subset_right hsub h1))
    · rfl
    · rfl

/-- **The vacuum is in every closed invariant subspace with a vector of nonzero vacuum coefficient.** -/
lemma vacuum_mem {W : Submodule ℂ Γ} (hWc : IsClosed (W : Set Γ))
    (hW : ∀ j, ∀ x ∈ W, fermiAnn B j (fermiCre B j x) ∈ W) {x : Γ} (hx : x ∈ W) (h0 : B.repr x ∅ ≠ 0) :
    B ∅ ∈ W := by
  have hc : B.repr x ∅ • B ∅ ∈ W := by
    rw [← SetLike.mem_coe, ← hWc.closure_eq]
    refine Metric.mem_closure_iff.mpr fun ε hε => ?_
    have hsum := B.hasSum_repr x
    have h1 : ∀ᶠ s in atTop, dist (∑ S ∈ s, B.repr x S • B S) x < ε := (Metric.tendsto_nhds.mp hsum) ε hε
    have h2 : ∀ᶠ s : Finset (Finset ι) in atTop, ∅ ∈ s := eventually_ge_atTop {∅} |>.mono fun s hs => hs (by simp)
    obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
    refine ⟨restrictDisj B (s.sup id) x, restrictDisj_mem B hW _ x hx, ?_⟩
    rw [← restrictDisj_partial B x hs2, dist_eq_norm, ← map_sub]
    calc ‖restrictDisj B (s.sup id) ((∑ S ∈ s, B.repr x S • B S) - x)‖
        ≤ 1 * ‖(∑ S ∈ s, B.repr x S • B S) - x‖ :=
          (restrictDisj B (s.sup id)).le_of_opNorm_le (norm_ofCoeff_le B _ zero_le_one _) _
      _ < ε := by rw [one_mul, ← dist_eq_norm]; exact hs1
  have := W.smul_mem (B.repr x ∅)⁻¹ hc
  rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this

/-- Every basis vector `B T` lies in a subspace containing the vacuum and invariant under the creation operators. -/
lemma basis_mem {W : Submodule ℂ Γ} (hW : ∀ j, ∀ x ∈ W, fermiCre B j x ∈ W) (h0 : B ∅ ∈ W) :
    ∀ T : Finset ι, B T ∈ W := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => exact h0
  | insert j T hj ih =>
    have := W.smul_mem (fermiSign T j) (hW j _ ih)
    rwa [fermiCre_basis, if_neg hj, smul_smul, fermiSign_mul_self, one_smul] at this

/-- **The Fock representation is irreducible** for the `a*(eⱼ)`, `a(eⱼ)`: a closed subspace invariant under all of them is
`0` or everything. -/
theorem fermiFock_irreducible (W : Submodule ℂ Γ) (hWc : IsClosed (W : Set Γ))
    (hc : ∀ j, ∀ x ∈ W, fermiCre B j x ∈ W) (ha : ∀ j, ∀ x ∈ W, fermiAnn B j x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨ψ, hψW, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨S, hS⟩ : ∃ S, B.repr ψ S ≠ 0 := by
    by_contra hcon; push_neg at hcon
    exact hψ0 (B.repr.injective (by rw [map_zero]; exact lp.ext (funext hcon)))
  have hlow : ∀ n, ∀ S : Finset ι, S.card = n → ∀ ψ ∈ W, B.repr ψ S ≠ 0 → ∃ χ ∈ W, B.repr χ ∅ ≠ 0 := by
    intro n
    induction n with
    | zero =>
      intro S hS ψ hψ h
      rw [Finset.card_eq_zero] at hS; subst hS; exact ⟨ψ, hψ, h⟩
    | succ n ih =>
      intro S hS ψ hψ h
      obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
      refine ih (S.erase j) (by rw [Finset.card_erase_of_mem hj]; omega) (fermiAnn B j ψ) (ha j ψ hψ) ?_
      rw [repr_fermiAnn_apply, if_neg (Finset.notMem_erase j S), Finset.insert_erase hj]
      exact mul_ne_zero (by intro h0; simpa [h0] using norm_fermiSign (S.erase j) j) h
  obtain ⟨χ, hχW, hχ0⟩ := hlow _ S rfl ψ hψW hS
  have h0 := vacuum_mem B hWc (fun j φ hφ => ha j _ (hc j φ hφ)) hχW hχ0
  have hall := basis_mem B hc h0
  rw [eq_top_iff]
  intro φ _
  rw [← SetLike.mem_coe, ← hWc.closure_eq]
  refine mem_closure_of_tendsto (B.hasSum_repr φ) (Eventually.of_forall fun s => ?_)
  exact W.sum_mem fun S _ => W.smul_mem _ (hall S)

/-- `w ↦ a*(w)` as a bounded linear map. -/
noncomputable def creL : Z →L[ℂ] (Γ →L[ℂ] Γ) :=
  LinearMap.mkContinuous ⟨⟨creW B b, creW_add B b⟩, fun r w => creW_smul B b r w⟩ 1
    (fun w => by rw [one_mul]; exact norm_creW_le B b w)

lemma creL_apply (w : Z) : creL B b w = creW B b w := rfl

/-- **The annihilation operator** `a(w) = a*(w)*`. -/
noncomputable def annW (w : Z) : Γ →L[ℂ] Γ := ContinuousLinearMap.adjoint (creW B b w)

lemma annW_basis (i : ι) : annW B b (b i) = fermiAnn B i := by rw [annW, creW_basis B b]; rfl

/-- **The field operator** `φ(w) = a*(w) + a(w)` (Dereziński, §7.1, p. 29). -/
noncomputable def fockField (w : Z) : Γ →L[ℂ] Γ := creW B b w + annW B b w

/-- **The field operator `φ(w) = a*(w) + a(w)` is self-adjoint** (Dereziński, Section 7.1, p. 30). -/
lemma isSelfAdjoint_fockField (w : Z) : IsSelfAdjoint (fockField B b w) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, fockField, map_add, annW,
    ContinuousLinearMap.adjoint_adjoint, add_comm]

lemma creW_sum (J : Finset ι) (c : ι → ℂ) : creW B b (∑ i ∈ J, c i • b i) = ∑ i ∈ J, c i • fermiCre B i := by
  rw [← creL_apply B b, map_sum]
  simp only [map_smul, creL_apply, creW_basis B b]

/-- The CAR `a(w) a*(w') + a*(w') a(w) = ⟪w, w'⟫` on finite combinations of the basis. -/
lemma annW_creW_anticomm_sum (J : Finset ι) (c c' : ι → ℂ) :
    annW B b (∑ i ∈ J, c i • b i) * creW B b (∑ i ∈ J, c' i • b i) +
        creW B b (∑ i ∈ J, c' i • b i) * annW B b (∑ i ∈ J, c i • b i) =
      ⟪∑ i ∈ J, c i • b i, ∑ i ∈ J, c' i • b i⟫_ℂ • (1 : Γ →L[ℂ] Γ) := by
  rw [annW, creW_sum, creW_sum, b.orthonormal.inner_sum, adjoint_sum_fermiCre B]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.sum_comm (s := J) (t := J) (f := fun j i => (c' j • fermiCre B j) * (star (c i) • fermiAnn B i)),
    ← Finset.sum_add_distrib, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_add_distrib]
  have : ∀ j ∈ J, (star (c i) • fermiAnn B i) * (c' j • fermiCre B j) + (c' j • fermiCre B j) * (star (c i) • fermiAnn B i) =
      if i = j then (star (c i) * c' i) • (1 : Γ →L[ℂ] Γ) else 0 := by
    intro j _
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c' j), ← smul_add, fermiAnn_fermiCre_anticomm B]
    split_ifs with hij
    · subst hij; rfl
    · rw [smul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hi, Complex.star_def]

/-- `a*(w) a*(w') + a*(w') a*(w) = 0` on finite combinations of the basis. -/
lemma creW_anticomm_sum (J : Finset ι) (c c' : ι → ℂ) :
    creW B b (∑ i ∈ J, c i • b i) * creW B b (∑ i ∈ J, c' i • b i) +
        creW B b (∑ i ∈ J, c' i • b i) * creW B b (∑ i ∈ J, c i • b i) = 0 := by
  rw [creW_sum, creW_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
    Finset.sum_comm (s := J) (t := J) (f := fun j i => (c' j • fermiCre B j) * (c i • fermiCre B i)), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (c' j), ← smul_add, fermiCre_anticomm B, smul_zero]

lemma continuous_annW : Continuous (annW B b) := by
  have : annW B b = fun w => (ContinuousLinearMap.adjoint (𝕜 := ℂ)) (creL B b w) := rfl
  rw [this]
  exact (ContinuousLinearMap.adjoint (𝕜 := ℂ)).continuous.comp (creL B b).continuous

lemma continuous_creW : Continuous (creW B b) := (creL B b).continuous

/-- Two vectors of the span of the basis are combinations over a common finite set. -/
lemma exists_common_sum {w w' : Z} (hw : w ∈ Submodule.span ℂ (Set.range b)) (hw' : w' ∈ Submodule.span ℂ (Set.range b)) :
    ∃ (J : Finset ι) (c c' : ι → ℂ), w = ∑ i ∈ J, c i • b i ∧ w' = ∑ i ∈ J, c' i • b i := by
  classical
  obtain ⟨l, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hw
  obtain ⟨l', rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hw'
  refine ⟨l.support ∪ l'.support, l, l', ?_, ?_⟩
  · exact Finsupp.sum_of_support_subset _ Finset.subset_union_left _ (fun i _ => zero_smul ℂ _)
  · exact Finsupp.sum_of_support_subset _ Finset.subset_union_right _ (fun i _ => zero_smul ℂ _)

/-- A continuous identity in `(w, w')` that holds on finite combinations of the basis holds everywhere. -/
lemma eq_of_span {P Q : Z → Z → (Γ →L[ℂ] Γ)} (hP : Continuous fun p : Z × Z => P p.1 p.2)
    (hQ : Continuous fun p : Z × Z => Q p.1 p.2)
    (h : ∀ (J : Finset ι) (c c' : ι → ℂ), P (∑ i ∈ J, c i • b i) (∑ i ∈ J, c' i • b i) =
      Q (∑ i ∈ J, c i • b i) (∑ i ∈ J, c' i • b i)) (w w' : Z) : P w w' = Q w w' := by
  set D : Set Z := (Submodule.span ℂ (Set.range b) : Set Z)
  have hD : Dense D := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]; exact b.dense_span
  have hS : IsClosed {p : Z × Z | P p.1 p.2 = Q p.1 p.2} := isClosed_eq hP hQ
  have hsub : D ×ˢ D ⊆ {p : Z × Z | P p.1 p.2 = Q p.1 p.2} := by
    rintro ⟨u, u'⟩ ⟨hu, hu'⟩
    obtain ⟨J, c, c', rfl, rfl⟩ := exists_common_sum b hu hu'
    exact h J c c'
  have := hS.closure_subset_iff.mpr hsub
  rw [closure_prod_eq, hD.closure_eq] at this
  exact this (Set.mk_mem_prod (Set.mem_univ w) (Set.mem_univ w'))

/-- **The CAR** `a(w) a*(w') + a*(w') a(w) = ⟪w, w'⟫`. -/
theorem annW_creW_anticomm (w w' : Z) :
    annW B b w * creW B b w' + creW B b w' * annW B b w = ⟪w, w'⟫_ℂ • (1 : Γ →L[ℂ] Γ) :=
  eq_of_span b (P := fun w w' => annW B b w * creW B b w' + creW B b w' * annW B b w)
    (Q := fun w w' => ⟪w, w'⟫_ℂ • (1 : Γ →L[ℂ] Γ))
    (by
      have h1 := (continuous_annW B b).comp (continuous_fst : Continuous fun p : Z × Z => p.1)
      have h2 := (continuous_creW B b).comp (continuous_snd : Continuous fun p : Z × Z => p.2)
      exact (h1.mul h2).add (h2.mul h1))
    ((continuous_inner (𝕜 := ℂ) (E := Z)).smul (continuous_const (y := (1 : Γ →L[ℂ] Γ))))
    (fun J c c' => annW_creW_anticomm_sum B b J c c') w w'

/-- `a*(w) a*(w') + a*(w') a*(w) = 0`. -/
theorem creW_anticomm (w w' : Z) : creW B b w * creW B b w' + creW B b w' * creW B b w = 0 :=
  eq_of_span b (P := fun w w' => creW B b w * creW B b w' + creW B b w' * creW B b w) (Q := fun _ _ => 0)
    (by
      have h1 := (continuous_creW B b).comp (continuous_fst : Continuous fun p : Z × Z => p.1)
      have h2 := (continuous_creW B b).comp (continuous_snd : Continuous fun p : Z × Z => p.2)
      exact (h1.mul h2).add (h2.mul h1))
    (continuous_const (y := (0 : Γ →L[ℂ] Γ))) (fun J c c' => creW_anticomm_sum B b J c c') w w'

/-- `a(w) a(w') + a(w') a(w) = 0`, the adjoint of `creW_anticomm`. -/
theorem annW_anticomm (w w' : Z) : annW B b w * annW B b w' + annW B b w' * annW B b w = 0 := by
  have := congrArg ContinuousLinearMap.adjoint (creW_anticomm B b w' w)
  simp only [map_add, map_zero, ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp] at this
  simpa [annW, ContinuousLinearMap.mul_def] using this

/-- **Dereziński, Theorem 28 (the representation)**: the field operators `φ(w) = a*(w) + a(w)` are self-adjoint and satisfy
`[φ(w), φ(w')]₊ = 2 Re⟪w, w'⟫`, a representation of the CAR over `Z` with the real scalar product `Re⟪·,·⟫`. -/
theorem fockField_anticomm (w w' : Z) :
    fockField B b w * fockField B b w' + fockField B b w' * fockField B b w =
      ((2 * (⟪w, w'⟫_ℂ).re : ℝ) : ℂ) • (1 : Γ →L[ℂ] Γ) := by
  have h1 := annW_creW_anticomm B b w w'
  have h2 := annW_creW_anticomm B b w' w
  have h3 := creW_anticomm B b w w'
  have h4 := annW_anticomm B b w w'
  have hre : ((2 * (⟪w, w'⟫_ℂ).re : ℝ) : ℂ) = ⟪w, w'⟫_ℂ + ⟪w', w⟫_ℂ := by
    rw [show ⟪w', w⟫_ℂ = (starRingEnd ℂ) ⟪w, w'⟫_ℂ from (inner_conj_symm w' w).symm, Complex.add_conj]
  rw [hre, add_smul]
  simp only [fockField, add_mul, mul_add]
  rw [← h1, ← h2]
  linear_combination (norm := abel_nf) h3 + h4

/-- **Dereziński, Theorem 28 (irreducibility)**: a closed subspace invariant under every field operator `φ(w)` is `0` or
everything. -/
theorem fockField_irreducible (W : Submodule ℂ Γ) (hWc : IsClosed (W : Set Γ))
    (hW : ∀ w, ∀ ψ ∈ W, fockField B b w ψ ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hci : ∀ j, creW B b (Complex.I • b j) = Complex.I • fermiCre B j := fun j => by rw [creW_smul B b, creW_basis B b]
  have hai : ∀ j, annW B b (Complex.I • b j) = -Complex.I • fermiAnn B j := fun j => by
    rw [annW, hci, map_smulₛₗ, Complex.conj_I]; rfl
  have hc : ∀ j, fermiCre B j = (1 / 2 : ℂ) • (fockField B b (b j) - Complex.I • fockField B b (Complex.I • b j)) := by
    intro j
    rw [fockField, fockField, hci, hai, creW_basis B b, annW_basis B b]
    have e1 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have e2 : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
    simp only [smul_add, smul_smul, e1, e2]
    module
  have ha : ∀ j, fermiAnn B j = (1 / 2 : ℂ) • (fockField B b (b j) + Complex.I • fockField B b (Complex.I • b j)) := by
    intro j
    rw [fockField, fockField, hci, hai, creW_basis B b, annW_basis B b]
    have e1 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have e2 : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
    simp only [smul_add, smul_smul, e1, e2]
    module
  refine fermiFock_irreducible B W hWc (fun j ψ hψ => ?_) (fun j ψ hψ => ?_)
  · rw [hc, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
    exact W.smul_mem _ (W.sub_mem (hW _ ψ hψ) (W.smul_mem _ (hW _ ψ hψ)))
  · rw [ha, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    exact W.smul_mem _ (W.add_mem (hW _ ψ hψ) (W.smul_mem _ (hW _ ψ hψ)))

end Lightlike.OperatorAlgebras
