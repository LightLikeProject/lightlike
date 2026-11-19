import Lightlike.FieldTheory.Gaussian.Moments
import Physlib.QFT.PerturbationTheory.WickContraction.IsFull
import Physlib.QFT.PerturbationTheory.WickContraction.InsertAndContractNat

/-!
# Wick's theorem as a sum over pairings (FT1 stage 3)

`moment_eq_pairSum`: `E[x_{l₀} ⋯ x_{l_{n-1}}] = ∑_{c} ∏_{{p,q} ∈ c} S_{l_p l_q}`, the sum over the full Wick
contractions `c` of `n` points (Physlib's `WickContraction n` with `IsFull`, reused, not redefined). Proof: both
sides satisfy Isserlis' recursion (`moment_cons`); for the pairing sum, the recursion comes from `extractEquiv 0`
(the partner `j` of the first point) and `extractEquiv j` (the remaining contraction, whose only uncontracted point
is `j`) (`pairSum_succ_succ`).

Source: Tubaro–Zanella, *An introduction to Malliavin calculus*, arXiv:2502.07941, Theorem 2.19 (Isserlis
formula), p. 9: `E[ξ₁ ⋯ ξₙ] = ∑ ∏_k E[ξ_{i_k} ξ_{j_k}]` over the partitions of `{1, …, n}` into pairs, for centred
jointly Gaussian `ξ`; here `ξ_k = x_{l_k}` with `x ∼ N(0, S)`. The one-variable case is Borinsky (2018), §3.1, p. 22.
Difference from the source (weaker): `S` is positive definite, so degenerate Gaussian families are not covered.
-/

namespace Lightlike.FieldTheory

open WickContraction Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight of a Wick contraction of `n` points labelled by `x : Fin n → ι`. -/
noncomputable def pairWeight (S : Matrix ι ι ℝ) {n : ℕ} (x : Fin n → ι) (c : WickContraction n) : ℝ :=
  ∏ a : c.1, S (x (c.fstFieldOfContract a)) (x (c.sndFieldOfContract a))

/-- The pairing sum `∑_{c full} pairWeight S x c`. -/
noncomputable def pairSum (S : Matrix ι ι ℝ) {n : ℕ} (x : Fin n → ι) : ℝ :=
  ∑ c : {c : WickContraction n // c.IsFull}, pairWeight S x c.1

/-- Inserting an uncontracted point does not change the weight. -/
lemma pairWeight_insert_none (S : Matrix ι ι ℝ) {n : ℕ} (y : Fin n.succ → ι) (c : WickContraction n)
    (i : Fin n.succ) :
    pairWeight S y (c.insertAndContractNat i none) = pairWeight S (y ∘ i.succAbove) c := by
  unfold pairWeight
  refine (Fintype.prod_bijective (insertLift i none) (insertLift_none_bijective i) _ _ ?_).symm
  intro a
  simp [insertAndContractNat_fstFieldOfContract, insertAndContractNat_sndFieldOfContract]

/-- For a symmetric `S`, the weight of the pair `{p, q}` is `S_{x_p x_q}`. -/
lemma weight_pair (S : Matrix ι ι ℝ) (hS : S.IsSymm) {n : ℕ} (x : Fin n → ι) (c : WickContraction n) (a : c.1)
    {p q : Fin n} (hpq : a.1 = {p, q}) :
    S (x (c.fstFieldOfContract a)) (x (c.sndFieldOfContract a)) = S (x p) (x q) := by
  have h := c.finset_eq_fstFieldOfContract_sndFieldOfContract a
  rw [hpq] at h
  have hne := (c.fstFieldOfContract_lt_sndFieldOfContract a).ne
  have h1 : c.fstFieldOfContract a ∈ ({p, q} : Finset (Fin n)) := by rw [h]; simp
  have h2 : c.sndFieldOfContract a ∈ ({p, q} : Finset (Fin n)) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2]
  · rw [h1, h2]; exact hS.apply (x p) (x q)
  · exact absurd (h1.trans h2.symm) hne

/-- Inserting a point contracted with `j` multiplies the weight by `S_{y_i y_j}`. -/
lemma pairWeight_insert_some (S : Matrix ι ι ℝ) (hS : S.IsSymm) {n : ℕ} (y : Fin n.succ → ι)
    (c : WickContraction n) (i : Fin n.succ) (j : c.uncontracted) :
    pairWeight S y (c.insertAndContractNat i (some j)) =
      S (y i) (y (i.succAbove j)) * pairWeight S (y ∘ i.succAbove) c := by
  unfold pairWeight
  rw [← Fintype.prod_bijective (insertLiftSome i j) (insertLiftSome_bijective i j) _ _ (fun _ => rfl),
    Fintype.prod_sum_type]
  congr 1
  · simp only [Finset.univ_unique, Finset.prod_singleton]
    exact weight_pair S hS y _ _ rfl
  · refine Finset.prod_congr rfl fun a _ => ?_
    simp [insertLiftSome, insertAndContractNat_fstFieldOfContract, insertAndContractNat_sndFieldOfContract]

/-- The pairing sum as a sum over all contractions with an indicator. -/
lemma pairSum_eq_sum_ite (S : Matrix ι ι ℝ) {n : ℕ} (x : Fin n → ι) :
    pairSum S x = ∑ c : WickContraction n, if c.IsFull then pairWeight S x c else 0 := by
  unfold pairSum
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun c => by simp) _).symm

/-- Contractions of `m + 1` points whose only uncontracted point is `j` correspond to full contractions of
the other `m` points. -/
lemma sum_uncontracted_eq_singleton (S : Matrix ι ι ℝ) {m : ℕ} (z : Fin m.succ → ι) (j : Fin m.succ) :
    (∑ c : WickContraction m.succ, if c.uncontracted = {j} then pairWeight S z c else 0) =
      pairSum S (z ∘ j.succAbove) := by
  rw [pairSum_eq_sum_ite, ← (extractEquiv j).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_option]
  have hnone : ((extractEquiv j).symm ⟨c, none⟩).uncontracted = {j} ↔ c.IsFull := by
    rw [extractEquiv_symm_none_uncontracted]
    constructor
    · intro h
      unfold IsFull
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a ha
      have : j.succAbove a ∈ (insert j (c.uncontracted.map j.succAboveEmb) : Finset _) :=
        Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ ha)
      rw [h, Finset.mem_singleton] at this
      exact Fin.succAbove_ne j a this
    · intro h
      unfold IsFull at h
      rw [h]; simp
  have hsome : ∀ k : c.uncontracted, ¬ ((extractEquiv j).symm ⟨c, some k⟩).uncontracted = {j} := by
    intro k h
    have hj : j ∈ ((extractEquiv j).symm ⟨c, some k⟩).uncontracted := by rw [h]; exact Finset.mem_singleton_self j
    change j ∈ (insertAndContractNat c j (some k)).uncontracted at hj
    rw [insertAndContractNat_some_uncontracted] at hj
    obtain ⟨a, _, ha⟩ := Finset.mem_map.1 hj
    exact Fin.succAbove_ne j a ha
  simp only [hsome, if_false, Finset.sum_const_zero, add_zero]
  by_cases hc : c.IsFull
  · rw [if_pos (hnone.2 hc), if_pos hc]
    exact pairWeight_insert_none S z c j
  · rw [if_neg (fun h => hc (hnone.1 h)), if_neg hc]

/-- **The recursion of the pairing sum** (Isserlis' recursion for pairings). -/
theorem pairSum_succ_succ (S : Matrix ι ι ℝ) (hS : S.IsSymm) {n : ℕ} (y : Fin n.succ.succ → ι) :
    pairSum S y = ∑ j : Fin n.succ, S (y 0) (y j.succ) * pairSum S (y ∘ Fin.succ ∘ j.succAbove) := by
  rw [pairSum_eq_sum_ite, ← (extractEquiv 0).symm.sum_comp, Fintype.sum_sigma]
  -- the term `none` is never full: `0` stays uncontracted
  have hnone : ∀ c : WickContraction n.succ, ¬ ((extractEquiv 0).symm ⟨c, none⟩).IsFull := by
    intro c h
    have := self_mem_uncontracted_of_insertAndContractNat_none c 0
    unfold IsFull at h
    change (insertAndContractNat c 0 none).uncontracted = ∅ at h
    rw [h] at this
    exact Finset.notMem_empty _ this
  have hsome : ∀ (c : WickContraction n.succ) (k : c.uncontracted),
      ((extractEquiv 0).symm ⟨c, some k⟩).IsFull ↔ c.uncontracted = {k.1} := by
    intro c k
    unfold IsFull
    change (insertAndContractNat c 0 (some k)).uncontracted = ∅ ↔ _
    rw [insertAndContractNat_some_uncontracted, Finset.map_eq_empty, Finset.erase_eq_empty_iff]
    constructor
    · rintro (h | h)
      · exact absurd k.2 (Finset.eq_empty_iff_forall_notMem.1 h _)
      · exact h
    · intro h; exact Or.inr h
  have hstep : ∀ c : WickContraction n.succ,
      (∑ o : Option c.uncontracted, if ((extractEquiv 0).symm ⟨c, o⟩).IsFull then
        pairWeight S y ((extractEquiv 0).symm ⟨c, o⟩) else 0) =
      ∑ j : Fin n.succ, if c.uncontracted = {j} then
        S (y 0) (y j.succ) * pairWeight S (y ∘ Fin.succ) c else 0 := by
    intro c
    rw [Fintype.sum_option, if_neg (hnone c), zero_add]
    set F : Fin n.succ → ℝ := fun j => if c.uncontracted = {j} then
      S (y 0) (y j.succ) * pairWeight S (y ∘ Fin.succ) c else 0 with hF
    have e1 : ∀ k : c.uncontracted, (if ((extractEquiv 0).symm ⟨c, some k⟩).IsFull then
        pairWeight S y ((extractEquiv 0).symm ⟨c, some k⟩) else 0) = F k.1 := by
      intro k
      simp only [hF]
      by_cases h : c.uncontracted = {k.1}
      · rw [if_pos ((hsome c k).2 h), if_pos h]
        change pairWeight S y (insertAndContractNat c 0 (some k)) = _
        rw [pairWeight_insert_some S hS y c 0 k, Fin.succAbove_zero]
      · rw [if_neg (fun h' => h ((hsome c k).1 h')), if_neg h]
    rw [Fintype.sum_congr _ _ e1, Finset.sum_coe_sort c.uncontracted F]
    refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
    simp only [hF]
    rw [if_neg]
    intro h; exact hj (h ▸ Finset.mem_singleton_self j)
  simp_rw [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show y ∘ Fin.succ ∘ j.succAbove = (y ∘ Fin.succ) ∘ j.succAbove from rfl,
    ← sum_uncontracted_eq_singleton S (y ∘ Fin.succ) j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- Erasing an entry of `List.ofFn y`. -/
lemma eraseIdx_ofFn {α : Type*} {k : ℕ} (y : Fin (k + 1) → α) (j : Fin (k + 1)) :
    (List.ofFn y).eraseIdx j = List.ofFn (y ∘ j.succAbove) := by
  have hj : (j : ℕ) < (List.ofFn y).length := by rw [List.length_ofFn]; exact j.2
  refine List.ext_getElem ?_ fun t h1 h2 => ?_
  · rw [List.length_eraseIdx_of_lt hj]; simp
  rw [List.getElem_eraseIdx, List.getElem_ofFn]
  simp only [List.getElem_ofFn, Function.comp_apply]
  split_ifs with h
  · congr 1
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · exact h
  · congr 1
    rw [Fin.succAbove_of_le_castSucc]
    · rfl
    · simp only [Fin.le_def, Fin.val_castSucc]; omega

/-- Isserlis' recursion in the variables `x : Fin (n + 2) → ι`. -/
lemma moment_ofFn_succ_succ {S : Matrix ι ι ℝ} (hS : S.PosDef) {n : ℕ} (x : Fin n.succ.succ → ι) :
    moment S (List.ofFn x) = ∑ j : Fin n.succ, S (x 0) (x j.succ) * moment S (List.ofFn (x ∘ Fin.succ ∘ j.succAbove)) := by
  rw [List.ofFn_succ, moment_cons hS]
  refine Fintype.sum_equiv (finCongr (List.length_ofFn)) _ _ fun m => ?_
  rw [List.get_ofFn]
  congr 1
  exact congrArg (moment S) (eraseIdx_ofFn (x ∘ Fin.succ) (finCongr List.length_ofFn m))

/-- Wick's theorem for the moment of `List.ofFn x`. -/
theorem moment_ofFn_eq_pairSum {S : Matrix ι ι ℝ} (hS : S.PosDef) {n : ℕ} (x : Fin n → ι) :
    moment S (List.ofFn x) = pairSum S x := by
  have hsym : S.IsSymm := hS.isHermitian.isSymm
  have key : ∀ n (x : Fin n → ι), moment S (List.ofFn x) = pairSum S x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x
      match n, x, ih with
      | 0, x, _ =>
        rw [List.ofFn_zero, moment_nil, pairSum_eq_sum_ite, sum_WickContraction_nil]
        have hfull : (empty : WickContraction 0).IsFull := by
          unfold IsFull; exact Finset.eq_empty_of_isEmpty _
        rw [if_pos hfull]
        haveI : IsEmpty (empty : WickContraction 0).1 := ⟨fun a => by
          have := a.2; simp [empty] at this⟩
        unfold pairWeight
        exact (Fintype.prod_empty _).symm
      | 1, x, _ =>
        have h0 : moment S (List.ofFn x) = 0 := moment_odd hS 1 _ (by simp) (by decide)
        rw [h0]
        have hc := card_of_isfull_odd (n := 1) (by decide)
        haveI : IsEmpty {c : WickContraction 1 // c.IsFull} := Fintype.card_eq_zero_iff.1 hc
        unfold pairSum
        simp
      | n + 2, x, ih =>
        rw [moment_ofFn_succ_succ hS x, pairSum_succ_succ S hsym x]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ih n (by omega)]
  exact key n x

/-- **Wick's theorem** (Isserlis' theorem): the moments of the centred Gaussian measure with covariance `S`
are sums over the full Wick contractions (pairings) of the positions. -/
theorem moment_eq_pairSum {S : Matrix ι ι ℝ} (hS : S.PosDef) (l : List ι) :
    moment S l = pairSum S l.get := by
  conv_lhs => rw [← List.ofFn_get l]
  exact moment_ofFn_eq_pairSum hS _

end Lightlike.FieldTheory
