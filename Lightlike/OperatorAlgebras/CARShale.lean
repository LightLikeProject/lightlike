import Lightlike.OperatorAlgebras.FermiFockGeneral
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Fermionic Fock representations of the CAR over a Hilbert space: words of creation operators

Algebra for the infinite-mode fermionic Shale theorem (see `docs/notes/op2-fermionic-shale-plan.md`). For a family
`c : ι → (E →L[ℂ] E)` of anticommuting operators and a vector `Ω`, the word of a list `l` is
`c l₀ (c l₁ (⋯ Ω))`. For a sorted list, a creation operator `c j` acts on the word by inserting `j`
with the sign `(-1)^{#{i ∈ l, i < j}}`.
-/

open scoped InnerProductSpace

namespace Lightlike.OperatorAlgebras.CARShale

variable {ι : Type*} [LinearOrder ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The word `c l₀ (c l₁ (⋯ (c lₙ Ω)))` of a list of creation operators applied to `Ω`. -/
def word (c : ι → (E →L[ℂ] E)) (Ω : E) : List ι → E
  | [] => Ω
  | a :: t => c a (word c Ω t)

variable {c : ι → (E →L[ℂ] E)} {Ω : E}

/-- A creation operator `c j` on the word of a list containing `j` gives `0`. -/
lemma cre_word_of_mem (hc : ∀ i j, c i * c j + c j * c i = 0) {j : ι} :
    ∀ {l : List ι}, j ∈ l → c j (word c Ω l) = 0
  | [], h => by simp at h
  | a :: t, h => by
    rcases List.mem_cons.1 h with rfl | ht
    · have := hc j j
      have h2 : c j * c j = 0 := by
        have : (2 : ℂ) • (c j * c j) = 0 := by rw [two_smul]; exact this
        exact (smul_eq_zero.1 this).resolve_left two_ne_zero
      show (c j * c j) (word c Ω t) = 0
      rw [h2]; rfl
    · have h1 := cre_word_of_mem hc ht
      have : c j (c a (word c Ω t)) = - c a (c j (word c Ω t)) := by
        have := congrArg (fun f => f (word c Ω t)) (hc j a)
        simp only [add_apply, mul_apply_eq_comp, zero_apply] at this
        exact eq_neg_of_add_eq_zero_left this
      show c j (c a (word c Ω t)) = 0
      rw [this, h1, map_zero, neg_zero]

/-- **A creation operator on a sorted word inserts its index with the sign `(-1)^{#{i < j}}`.** -/
lemma cre_word_insert (hc : ∀ i j, c i * c j + c j * c i = 0) {j : ι} :
    ∀ {l : List ι}, l.Pairwise (· ≤ ·) → j ∉ l →
      c j (word c Ω l) = (-1 : ℂ) ^ (l.filter (fun i => decide (i < j))).length •
        word c Ω (l.orderedInsert (· ≤ ·) j)
  | [], _, _ => by simp [word]
  | a :: t, hs, h => by
    have hja : j ≠ a := fun e => h (e ▸ List.mem_cons_self)
    have hjt : j ∉ t := fun e => h (List.mem_cons_of_mem _ e)
    have hanti : c j (c a (word c Ω t)) = - c a (c j (word c Ω t)) := by
      have := congrArg (fun f => f (word c Ω t)) (hc j a)
      simp only [add_apply, mul_apply_eq_comp, zero_apply] at this
      exact eq_neg_of_add_eq_zero_left this
    rcases lt_or_gt_of_ne hja with hlt | hgt
    · have hf : (a :: t).filter (fun i => decide (i < j)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro i hi
        have : a ≤ i := by
          rcases List.mem_cons.1 hi with rfl | hit
          · exact le_rfl
          · exact (List.pairwise_cons.1 hs).1 i hit
        simp only [decide_eq_true_eq, not_lt]
        exact le_trans hlt.le this
      rw [hf, List.orderedInsert_cons, if_pos hlt.le]
      simp [word]
    · rw [List.orderedInsert_cons, if_neg (not_le.2 hgt)]
      have ih := cre_word_insert hc (List.pairwise_cons.1 hs).2 hjt
      show c j (c a (word c Ω t)) = _
      rw [hanti, ih, List.filter_cons_of_pos (by simpa using hgt)]
      simp only [List.length_cons, pow_succ, word, map_smul, neg_smul, mul_neg, mul_one]

/-- **An annihilation operator on a strictly sorted word** removes its index with the sign `(-1)^{#{i < j}}`, or gives
`0` if the index does not occur. -/
lemma ann_word [DecidableEq ι] (a : ι → (E →L[ℂ] E)) (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0)
    (hΩ : ∀ j, a j Ω = 0) {j : ι} :
    ∀ {l : List ι}, l.Pairwise (· < ·) →
      a j (word c Ω l) = if j ∈ l then (-1 : ℂ) ^ (l.filter (fun i => decide (i < j))).length • word c Ω (l.erase j)
        else 0
  | [], _ => by simp [hΩ, word]
  | x :: t, hs => by
    have hrel := congrArg (fun f => f (word c Ω t)) (hca j x)
    simp only [add_apply, mul_apply_eq_comp, Function.comp_apply] at hrel
    have hx : a j (c x (word c Ω t)) = (if j = x then (1 : ℂ) else 0) • word c Ω t - c x (a j (word c Ω t)) := by
      have : (if j = x then (1 : E →L[ℂ] E) else 0) (word c Ω t) = (if j = x then (1 : ℂ) else 0) • word c Ω t := by
        split_ifs <;> simp
      rw [this] at hrel
      rw [eq_sub_iff_add_eq]; exact hrel.trans (by rfl)
    have ih := ann_word a hca hΩ (j := j) (List.pairwise_cons.1 hs).2
    show a j (c x (word c Ω t)) = _
    rw [hx, ih]
    by_cases hjx : j = x
    · subst hjx
      have hjt : j ∉ t := fun h => lt_irrefl _ ((List.pairwise_cons.1 hs).1 j h)
      have hf : (j :: t).filter (fun i => decide (i < j)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hit
        · simp
        · simpa using ((List.pairwise_cons.1 hs).1 i hit).le
      simp [hjt, hf, List.erase_cons_head]
    · have hne : x ≠ j := fun e => hjx e.symm
      by_cases hjt : j ∈ t
      · have hxj : x < j := (List.pairwise_cons.1 hs).1 j hjt
        have he : (x :: t).erase j = x :: t.erase j := List.erase_cons_tail (by simpa using hne)
        have hfl : ((x :: t).filter (fun i => decide (i < j))).length = (t.filter (fun i => decide (i < j))).length + 1 := by
          rw [List.filter_cons_of_pos (by simpa using hxj), List.length_cons]
        simp [hjx, hjt, he, hfl, pow_succ, word]
      · simp [hjx, hjt, List.erase_cons_tail, hne]

/-- The vector of a finite set `S`: the word of its increasing enumeration. -/
def vec (c : ι → (E →L[ℂ] E)) (Ω : E) (S : Finset ι) : E := word c Ω (S.sort (· ≤ ·))

lemma sort_insert' [DecidableEq ι] {S : Finset ι} {j : ι} (hj : j ∉ S) :
    (insert j S).sort (· ≤ ·) = (S.sort (· ≤ ·)).orderedInsert (· ≤ ·) j := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
  · exact Finset.pairwise_sort _ _
  · exact (Finset.pairwise_sort _ _).orderedInsert _ _
  · rw [← Multiset.coe_eq_coe, Finset.sort_eq, Finset.insert_val_of_notMem hj]
    refine Eq.trans ?_ (Multiset.coe_eq_coe.2 (List.perm_orderedInsert (· ≤ ·) j _)).symm
    rw [← Multiset.cons_coe, Finset.sort_eq]

lemma sort_filter_length (S : Finset ι) (j : ι) :
    ((S.sort (· ≤ ·)).filter (fun i => decide (i < j))).length = (S.filter (· < j)).card := by
  have h := congrArg Multiset.card (show (((S.sort (· ≤ ·)).filter (fun i => decide (i < j)) : List ι) : Multiset ι) =
      S.val.filter (· < j) by rw [← Multiset.filter_coe, Finset.sort_eq])
  rw [Multiset.coe_card] at h
  rw [h]; rfl

lemma sort_erase [DecidableEq ι] (S : Finset ι) (j : ι) :
    (S.sort (· ≤ ·)).erase j = (S.erase j).sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => le_antisymm h1 h2)
  · exact (Finset.pairwise_sort _ _).sublist (List.erase_sublist)
  · exact Finset.pairwise_sort _ _
  · rw [← Multiset.coe_eq_coe, Finset.sort_eq, ← Multiset.coe_erase, Finset.sort_eq]
    rfl

lemma sort_pairwise_lt (S : Finset ι) : (S.sort (· ≤ ·)).Pairwise (· < ·) := by
  exact Finset.sortedLT_sort S |>.pairwise

/-- `c j` on the vector of a set not containing `j`. -/
lemma cre_vec [DecidableEq ι] (hc : ∀ i j, c i * c j + c j * c i = 0) {S : Finset ι} {j : ι} (hj : j ∉ S) :
    c j (vec c Ω S) = (-1 : ℂ) ^ (S.filter (· < j)).card • vec c Ω (insert j S) := by
  unfold vec
  rw [cre_word_insert hc (Finset.pairwise_sort _ _) (by simpa using hj), sort_filter_length, sort_insert' hj]

/-- `a j` on the vector of a set. -/
lemma ann_vec [DecidableEq ι] (a : ι → (E →L[ℂ] E))
    (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (hΩ : ∀ j, a j Ω = 0) (S : Finset ι) (j : ι) :
    a j (vec c Ω S) = if j ∈ S then (-1 : ℂ) ^ (S.filter (· < j)).card • vec c Ω (S.erase j) else 0 := by
  unfold vec
  rw [ann_word a hca hΩ (sort_pairwise_lt S), sort_filter_length, sort_erase S j]
  simp

lemma conj_neg_one_pow (n : ℕ) : (starRingEnd ℂ) ((-1 : ℂ) ^ n) = (-1 : ℂ) ^ n := by simp

lemma neg_one_pow_mul_self (n : ℕ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; simp

/-- **The vectors `vec S` are orthonormal** when `Ω` is a unit vector killed by the annihilation operators `a j`,
`a j` is adjoint to `c j`, and the CAR hold. -/
theorem orthonormal_vec [DecidableEq ι] (a : ι → (E →L[ℂ] E)) (hc : ∀ i j, c i * c j + c j * c i = 0)
    (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (hΩ : ∀ j, a j Ω = 0)
    (hn : ⟪Ω, Ω⟫_ℂ = 1) (hadj : ∀ j x y, ⟪a j x, y⟫_ℂ = ⟪x, c j y⟫_ℂ) :
    ∀ (n : ℕ) (S T : Finset ι), S.card = n → ⟪vec c Ω S, vec c Ω T⟫_ℂ = if S = T then 1 else 0 := by
  have hadj' : ∀ j x y, ⟪c j x, y⟫_ℂ = ⟪x, a j y⟫_ℂ := fun j x y => by
    rw [← inner_conj_symm, ← hadj, inner_conj_symm]
  intro n
  induction n with
  | zero =>
    intro S T hS
    rw [Finset.card_eq_zero] at hS
    subst hS
    have hv : vec c Ω ∅ = Ω := by simp [vec, word]
    rw [hv]
    by_cases hT : T = ∅
    · subst hT; rw [if_pos rfl, hv]; exact hn
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hT
      have h1 := cre_vec (Ω := Ω) hc (S := T.erase j) (j := j) (by simp)
      rw [Finset.insert_erase hj] at h1
      have h2 : vec c Ω T = (-1 : ℂ) ^ ((T.erase j).filter (· < j)).card • c j (vec c Ω (T.erase j)) := by
        rw [h1, smul_smul, neg_one_pow_mul_self, one_smul]
      rw [h2, inner_smul_right, ← hadj, hΩ, inner_zero_left, mul_zero, if_neg (Ne.symm hT)]
  | succ n ih =>
    intro S T hS
    obtain ⟨j, hj⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    have hS' : (S.erase j).card = n := by rw [Finset.card_erase_of_mem hj]; omega
    have h1 := cre_vec (Ω := Ω) hc (S := S.erase j) (j := j) (by simp)
    rw [Finset.insert_erase hj] at h1
    have h2 : vec c Ω S = (-1 : ℂ) ^ ((S.erase j).filter (· < j)).card • c j (vec c Ω (S.erase j)) := by
      rw [h1, smul_smul, neg_one_pow_mul_self, one_smul]
    rw [h2, inner_smul_left, hadj', conj_neg_one_pow, ann_vec a hca hΩ]
    by_cases hjT : j ∈ T
    · rw [if_pos hjT, inner_smul_right, ih (S.erase j) (T.erase j) hS']
      have hf : (S.erase j).filter (· < j) = S.filter (· < j) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_erase]; constructor
        · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨⟨ne_of_lt h', h⟩, h'⟩
      by_cases hST : S = T
      · subst hST
        rw [if_pos rfl, if_pos rfl, hf, ← mul_assoc, neg_one_pow_mul_self]; simp
      · have : S.erase j ≠ T.erase j := fun e => hST (by
          rw [← Finset.insert_erase hj, ← Finset.insert_erase hjT, e])
        rw [if_neg hST, if_neg this]; simp
    · rw [if_neg hjT, inner_zero_right, mul_zero, if_neg (fun e => hjT (by rw [← e]; exact hj))]

section Unitary

variable {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ] [CompleteSpace E]

/-- **The unitary from a Fock space to a CAR representation with a vacuum and dense words.** If the words
`vec c Ω S` span a dense subspace of `E` then `B S ↦ vec c Ω S` extends to a unitary `U : Γ ≃ₗᵢ E`, and
`U` intertwines the creation operators `fermiCre B j` with `c j`. -/
theorem exists_unitary_of_dense (B : HilbertBasis (Finset ι) ℂ Γ) (a : ι → (E →L[ℂ] E))
    (hc : ∀ i j, c i * c j + c j * c i = 0)
    (hca : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (hΩ : ∀ j, a j Ω = 0)
    (hn : ⟪Ω, Ω⟫_ℂ = 1) (hadj : ∀ j x y, ⟪a j x, y⟫_ℂ = ⟪x, c j y⟫_ℂ)
    (hdense : ⊤ ≤ (Submodule.span ℂ (Set.range (vec c Ω))).topologicalClosure) :
    ∃ U : Γ ≃ₗᵢ[ℂ] E, (∀ S, U (B S) = vec c Ω S) ∧ ∀ j x, U (fermiCre B j x) = c j (U x) := by
  have horth : Orthonormal ℂ (vec c Ω) := by
    rw [orthonormal_iff_ite]
    intro S T
    exact orthonormal_vec a hc hca hΩ hn hadj _ S T rfl
  let b' : HilbertBasis (Finset ι) ℂ E := HilbertBasis.mk horth hdense
  have hb' : ∀ S, b' S = vec c Ω S := fun S => by simp [b', HilbertBasis.coe_mk]
  set U : Γ ≃ₗᵢ[ℂ] E := B.repr.trans b'.repr.symm with hUdef
  have hU : ∀ S, U (B S) = vec c Ω S := fun S => by
    rw [hUdef, LinearIsometryEquiv.trans_apply, HilbertBasis.repr_self, ← hb', ← HilbertBasis.repr_self b']
    simp
  refine ⟨U, hU, fun j x => ?_⟩
  have key : ((U.toContinuousLinearEquiv : Γ →L[ℂ] E)).comp (fermiCre B j) = (c j).comp (U.toContinuousLinearEquiv : Γ →L[ℂ] E) := by
    refine ContinuousLinearMap.ext_on (s := Set.range B) (Submodule.dense_iff_topologicalClosure_eq_top.2 B.dense_span) ?_
    rintro _ ⟨S, rfl⟩
    simp only [ContinuousLinearMap.comp_apply]
    show U (fermiCre B j (B S)) = c j (U (B S))
    rw [hU, fermiCre_basis]
    by_cases hj : j ∈ S
    · rw [if_pos hj, map_zero]
      exact (cre_word_of_mem hc (by simpa using hj)).symm
    · rw [if_neg hj, map_smul, hU, cre_vec hc hj]
      rfl
  exact congrArg (fun f => f x) key

end Unitary

section Ladder

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- **Ladder operators from two real families of anticommuting fields**: if `p i`, `q i` satisfy
`{p i, p j} = {q i, q j} = 2 δ`, `{p i, q j} = 0`, then `a i = (p i + i q i)/2` and `c i = (p i - i q i)/2` satisfy the CAR. -/
lemma ladder_car [DecidableEq ι] (p q : ι → A)
    (hpp : ∀ i j, p i * p j + p j * p i = (2 * if i = j then (1 : ℂ) else 0) • (1 : A))
    (hqq : ∀ i j, q i * q j + q j * q i = (2 * if i = j then (1 : ℂ) else 0) • (1 : A))
    (hpq : ∀ i j, p i * q j + q j * p i = 0) (i j : ι) :
    ((1 / 2 : ℂ) • (p i - Complex.I • q i)) * ((1 / 2 : ℂ) • (p j - Complex.I • q j)) +
        ((1 / 2 : ℂ) • (p j - Complex.I • q j)) * ((1 / 2 : ℂ) • (p i - Complex.I • q i)) = 0 ∧
    ((1 / 2 : ℂ) • (p i + Complex.I • q i)) * ((1 / 2 : ℂ) • (p j - Complex.I • q j)) +
        ((1 / 2 : ℂ) • (p j - Complex.I • q j)) * ((1 / 2 : ℂ) • (p i + Complex.I • q i)) =
      (if i = j then (1 : ℂ) else 0) • (1 : A) := by
  have h1 := hpp i j
  have h2 := hqq i j
  have h3 := hpq i j
  have h4 := hpq j i
  constructor
  · simp only [smul_mul_smul_comm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_smul]
    linear_combination (norm := (match_scalars <;> (ring_nf; try simp only [Complex.I_sq]; try ring))) (1 / 4 : ℂ) • h1 - (1 / 4 : ℂ) • h2 - (Complex.I / 4) • h3 - (Complex.I / 4) • h4
  · simp only [smul_mul_smul_comm, mul_sub, mul_add, sub_mul, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub, smul_add, smul_smul]
    linear_combination (norm := (match_scalars <;> (ring_nf; try simp only [Complex.I_sq]; try ring))) (1 / 4 : ℂ) • h1 + (1 / 4 : ℂ) • h2 - (Complex.I / 4) • h3 + (Complex.I / 4) • h4

end Ladder

section FockLadder

variable {Γ : Type*} [NormedAddCommGroup Γ] [InnerProductSpace ℂ Γ] [CompleteSpace Γ]
  (B : HilbertBasis (Finset ι) ℂ Γ) {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  (b : HilbertBasis ι ℂ Z) (R : Z →ₗ[ℝ] Z)

/-- The real part of the field `φ(R eⱼ)`. -/
noncomputable def pField (j : ι) : Γ →L[ℂ] Γ := fockField B b (R (b j))

/-- The imaginary part `φ(R (i eⱼ))`. -/
noncomputable def qField (j : ι) : Γ →L[ℂ] Γ := fockField B b (R (Complex.I • b j))

/-- The annihilation operator of the transformed mode `j`: `(φ(R eⱼ) + i φ(R (i eⱼ)))/2`. -/
noncomputable def annR (j : ι) : Γ →L[ℂ] Γ := (1 / 2 : ℂ) • (pField B b R j + Complex.I • qField B b R j)

/-- The creation operator of the transformed mode `j`: `(φ(R eⱼ) - i φ(R (i eⱼ)))/2`. -/
noncomputable def creR (j : ι) : Γ →L[ℂ] Γ := (1 / 2 : ℂ) • (pField B b R j - Complex.I • qField B b R j)

lemma re_inner_basis [DecidableEq ι] (i j : ι) : (⟪b i, b j⟫_ℂ).re = if i = j then 1 else 0 := by
  rw [orthonormal_iff_ite.1 b.orthonormal i j]; split_ifs <;> simp

lemma re_inner_I_basis [DecidableEq ι] (i j : ι) :
    (⟪Complex.I • b i, Complex.I • b j⟫_ℂ).re = if i = j then 1 else 0 := by
  rw [inner_smul_left, inner_smul_right]
  simpa using re_inner_basis b i j

lemma re_inner_basis_I [DecidableEq ι] (i j : ι) : (⟪b i, Complex.I • b j⟫_ℂ).re = 0 := by
  rw [inner_smul_right]
  have := orthonormal_iff_ite.1 b.orthonormal i j
  split_ifs at this with h
  · rw [this]; simp
  · rw [this]; simp

variable (hR : ∀ w w', (⟪R w, R w'⟫_ℂ).re = (⟪w, w'⟫_ℂ).re)
include hR

/-- The ladder operators of the transformed modes satisfy the CAR. -/
lemma creR_annR_car [DecidableEq ι] (i j : ι) :
    creR B b R i * creR B b R j + creR B b R j * creR B b R i = 0 ∧
    annR B b R i * creR B b R j + creR B b R j * annR B b R i = (if i = j then (1 : ℂ) else 0) • (1 : Γ →L[ℂ] Γ) := by
  have key : ∀ w w' : Z, fockField B b (R w) * fockField B b (R w') + fockField B b (R w') * fockField B b (R w) =
      ((2 * (⟪w, w'⟫_ℂ).re : ℝ) : ℂ) • (1 : Γ →L[ℂ] Γ) := fun w w' => by
    rw [fockField_anticomm, hR]
  refine ladder_car (pField B b R) (qField B b R) ?_ ?_ ?_ i j
  · intro i j; rw [pField, pField, key, re_inner_basis b i j]; split_ifs <;> simp
  · intro i j; rw [qField, qField, key, re_inner_I_basis b i j]; split_ifs <;> simp
  · intro i j; rw [pField, qField, key, re_inner_basis_I b i j]; simp

omit hR in
lemma inner_field (w : Z) (x y : Γ) : ⟪fockField B b w x, y⟫_ℂ = ⟪x, fockField B b w y⟫_ℂ := by
  have h := isSelfAdjoint_fockField B b w
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at h
  rw [← ContinuousLinearMap.adjoint_inner_right, h]

omit hR in
/-- `annR j` is the adjoint of `creR j`. -/
lemma inner_annR_creR (j : ι) (x y : Γ) : ⟪annR B b R j x, y⟫_ℂ = ⟪x, creR B b R j y⟫_ℂ := by
  simp only [annR, creR, pField, qField, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
    inner_field B b]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  simp [Complex.conj_I, h2]
  ring

end FockLadder

end Lightlike.OperatorAlgebras.CARShale
