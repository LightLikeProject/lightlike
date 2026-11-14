import Lightlike.Recoupling.Invariant

/-!
# Networks of invariant tensors

A spin network with open legs is a family of node tensors whose legs are either open or joined in
pairs (internal edges). Its evaluation is the sum over the projections of the internal edges of
the product of the node tensors. This file proves that **a network of invariant tensors is an
invariant tensor of its open legs**, provided every internal edge joins an incoming to an outgoing
leg-end of the same spin (`isInv_netEval`). This is the algebraic form of gauge invariance used for
the Pachner moves.

## Main results

* `isInv_prod`: the product of a finite family of invariant tensors is invariant (on the disjoint
  union of their legs).
* `IsInv.contrAll`: contracting any finite set of pairs (incoming, outgoing) of legs keeps a tensor
  invariant. The proof splits the sum over the projections at one pair (`sum_piFinset_split`) and
  uses the shift identity `sum_pair_cancel`.
* `netEval`, `isInv_netEval`: the evaluation of a network and its invariance.

## References

- J. C. Baez, *Spin network states in gauge theory*, Adv. Math. 117, 253 (1996),
  arXiv:gr-qc/9411007: spin networks (edges labelled by representations, vertices by intertwining
  operators), whose states span the gauge-invariant functions of a connection.
- P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51, 110 (2019), arXiv:1902.08439, §9.1: spin networks.
-/

open Finset

namespace Lightlike.Recoupling

/-! ## Products over a family of nodes -/

section Prod

variable {N : Type*} [Fintype N] [DecidableEq N] {Λ : N → Type*} [∀ n, Fintype (Λ n)]
  [∀ n, DecidableEq (Λ n)]

omit [Fintype N] [∀ n, Fintype (Λ n)] in
lemma update_sigma_same (w : (Σ n, Λ n) → ℤ) (n : N) (l : Λ n) (v : ℤ) :
    (fun l' => Function.update w ⟨n, l⟩ v ⟨n, l'⟩) = Function.update (fun l' => w ⟨n, l'⟩) l v := by
  funext l'
  by_cases h : l' = l
  · subst h; simp
  · rw [Function.update_of_ne (fun he => h (eq_of_heq (Sigma.mk.inj_iff.mp he).2)),
      Function.update_of_ne h]

omit [Fintype N] [∀ n, Fintype (Λ n)] in
lemma update_sigma_ne (w : (Σ n, Λ n) → ℤ) {n n' : N} (h : n' ≠ n) (l : Λ n) (v : ℤ) :
    (fun l' => Function.update w ⟨n, l⟩ v ⟨n', l'⟩) = fun l' => w ⟨n', l'⟩ := by
  funext l'
  rw [Function.update_of_ne (fun he => h (Sigma.mk.inj_iff.mp he).1)]

/-- **The product of a family of invariant tensors is invariant**, on the disjoint union of their
legs. -/
theorem isInv_prod {j : ∀ n, Λ n → ℕ} {d : ∀ n, Λ n → Bool} {T : ∀ n, (Λ n → ℤ) → ℝ}
    (hT : ∀ n, IsInv (j n) (d n) (T n)) :
    IsInv (fun l : Σ n, Λ n => j l.1 l.2) (fun l => d l.1 l.2)
      (fun w => ∏ n, T n (fun l => w ⟨n, l⟩)) := by
  have key : ∀ (e : ∀ n, Λ n → Bool) (w : (Σ n, Λ n) → ℤ),
      ∑ l : Σ n, Λ n, raiseAt (fun l : Σ n, Λ n => j l.1 l.2) (fun l => e l.1 l.2)
        (fun w => ∏ n, T n (fun l => w ⟨n, l⟩)) w l =
      ∑ n, (∏ n' ∈ univ.erase n, T n' (fun l => w ⟨n', l⟩)) *
        ∑ l, raiseAt (j n) (e n) (T n) (fun l => w ⟨n, l⟩) l := by
    intro e w
    rw [Fintype.sum_sigma]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun l _ => ?_
    have hp : ∀ v : ℤ, ∏ n', T n' (fun l' => Function.update w ⟨n, l⟩ v ⟨n', l'⟩) =
        T n (Function.update (fun l' => w ⟨n, l'⟩) l v) *
          ∏ n' ∈ univ.erase n, T n' (fun l' => w ⟨n', l'⟩) := by
      intro v
      rw [← mul_prod_erase univ _ (mem_univ n), update_sigma_same]
      congr 1
      exact prod_congr rfl fun n' hn' => by rw [update_sigma_ne w (ne_of_mem_erase hn')]
    unfold raiseAt
    simp only [hp]
    split_ifs <;> ring
  refine ⟨fun w h l => ?_, fun w h => ?_, fun w => ?_, fun w => ?_⟩
  · exact (hT l.1).supp _ (prod_ne_zero_iff.mp h l.1 (mem_univ _)) l.2
  · rw [Fintype.sum_sigma]
    exact sum_eq_zero fun n _ => (hT n).weight _ (prod_ne_zero_iff.mp h n (mem_univ _))
  · rw [key d w]
    exact sum_eq_zero fun n _ => by rw [(hT n).raise, mul_zero]
  · rw [key (fun n l => !d n l) w]
    exact sum_eq_zero fun n _ => by rw [(hT n).lower, mul_zero]

end Prod

/-! ## Contraction of many pairs of legs -/

section ContrAll

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Splitting a sum over a box of projections at one coordinate `k`, for a summand that depends on
the other coordinates and, separately, on the value at `k`. -/
lemma sum_piFinset_split (B : κ → Finset ℤ) (k : κ) (g : ℤ → (κ → ℤ) → ℝ)
    (hg : ∀ a μ, g a μ = g a (Function.update μ k 0)) :
    ∑ μ ∈ Fintype.piFinset B, g (μ k) μ =
      ∑ μ ∈ Fintype.piFinset (Function.update B k {0}), ∑ a ∈ B k, g a μ := by
  rw [← sum_product']
  apply sum_nbij' (fun μ => (Function.update μ k 0, μ k)) (fun p => Function.update p.1 k p.2)
  · intro μ hμ
    simp only [mem_product, Fintype.mem_piFinset] at hμ ⊢
    refine ⟨fun k' => ?_, hμ k⟩
    by_cases h : k' = k
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h]; exact hμ k'
  · rintro ⟨μ, a⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h ⊢
    intro k'
    by_cases hk : k' = k
    · subst hk; simpa using h.2
    · rw [Function.update_of_ne hk]
      have := h.1 k'
      rwa [Function.update_of_ne hk] at this
  · intro μ _
    simp
  · rintro ⟨μ, a⟩ h
    simp only [mem_product, Fintype.mem_piFinset] at h
    have h0 : μ k = 0 := by simpa using h.1 k
    simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
    funext k'
    by_cases hk : k' = k
    · subst hk; simp [h0]
    · simp [Function.update_of_ne hk]
  · intro μ _
    exact hg _ _

/-- **Contraction of all pairs**: the pair `k` joins the leg-ends `inr (k, false)` and
`inr (k, true)`, of spin `jI k`. -/
noncomputable def contrAll (jI : κ → ℕ) (X : (ι ⊕ (κ × Bool) → ℤ) → ℝ) (m : ι → ℤ) : ℝ :=
  ∑ μ ∈ Fintype.piFinset (fun k => Icc (-(jI k : ℤ)) (jI k)), X (Sum.elim m fun p => μ p.1)

omit [Fintype ι] [Fintype κ] in
lemma update_elim_pair (m : ι → ℤ) (μ : κ → ℤ) (k : κ) (b : Bool) (v : ℤ) :
    Function.update (Sum.elim m fun p : κ × Bool => μ p.1) (Sum.inr (k, b)) v =
      Sum.elim m (fun p => if p = (k, b) then v else μ p.1) := by
  rw [Sum.update_elim_inr]
  congr 1
  funext p
  by_cases h : p = (k, b) <;> simp [h, Function.update]

lemma raise_contrAll {j : ι ⊕ (κ × Bool) → ℕ} {e : ι ⊕ (κ × Bool) → Bool}
    {X : (ι ⊕ (κ × Bool) → ℤ) → ℝ} {jI : κ → ℕ}
    (hsupp : ∀ m, X m ≠ 0 → ∀ i, AdmProj (j i) (m i)) (hX : ∀ m, ∑ x, raiseAt j e X m x = 0)
    (hj : ∀ k b, j (Sum.inr (k, b)) = jI k) (he : ∀ k, e (Sum.inr (k, true)) = !e (Sum.inr (k, false)))
    (m : ι → ℤ) :
    ∑ i, raiseAt (j ∘ Sum.inl) (e ∘ Sum.inl) (contrAll jI X) m i = 0 := by
  set B : κ → Finset ℤ := fun k => Icc (-(jI k : ℤ)) (jI k) with hB
  have hterm : ∀ i, raiseAt (j ∘ Sum.inl) (e ∘ Sum.inl) (contrAll jI X) m i =
      ∑ μ ∈ Fintype.piFinset B, raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inl i) := by
    intro i
    simp only [raiseAt, contrAll, Function.comp_apply, Sum.elim_inl, ← Sum.update_elim_inl]
    split_ifs
    · rw [mul_sum, ← sum_neg_distrib]
    · rw [mul_sum]
  simp only [hterm]
  rw [sum_comm]
  have hμ : ∀ μ : κ → ℤ, ∑ i, raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inl i) =
      -∑ k, (raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inr (k, false)) +
        raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inr (k, true))) := by
    intro μ
    have h := hX (Sum.elim m fun p => μ p.1)
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at h
    simp only [Fintype.sum_bool] at h
    rw [← eq_neg_iff_add_eq_zero] at h
    rw [h]
    congr 1
    refine sum_congr rfl fun k _ => ?_
    ring
  simp only [hμ, sum_neg_distrib, neg_eq_zero]
  rw [sum_comm]
  refine sum_eq_zero fun k _ => ?_
  -- the pair `k`
  set h : ℤ → ℤ → (κ → ℤ) → ℝ := fun p q μ =>
    X (Sum.elim m fun r => if r.1 = k then (if r.2 then q else p) else μ r.1) with hh
  have hhk : ∀ p q μ, h p q μ = h p q (Function.update μ k 0) := by
    intro p q μ
    simp only [hh]
    congr 1
    funext x
    rcases x with x | ⟨k', b⟩
    · rfl
    · by_cases hk : k' = k
      · simp [hk]
      · simp [hk]
  have hval : ∀ (μ : κ → ℤ) (b : Bool) (v : ℤ),
      X (Function.update (Sum.elim m fun p => μ p.1) (Sum.inr (k, b)) v) =
        if b then h (μ k) v μ else h v (μ k) μ := by
    intro μ b v
    rw [update_elim_pair]
    cases b <;> simp only [hh, ite_true, ite_false, Bool.false_eq_true] <;> congr 1 <;>
      funext x <;> rcases x with x | ⟨k', b'⟩ <;> [rfl; skip; rfl; skip] <;>
      by_cases hk : k' = k <;> cases b' <;> simp [hk]
  have hF : ∀ μ p q, h p q μ ≠ 0 → AdmProj (jI k) p ∧ AdmProj (jI k) q := fun μ p q hne => by
    have h1 := hsupp _ hne (Sum.inr (k, false))
    have h2 := hsupp _ hne (Sum.inr (k, true))
    simp only [Sum.elim_inr, ite_true, Bool.false_eq_true, ite_false, hj] at h1 h2
    exact ⟨h1, h2⟩
  have hsplit := fun (g : ℤ → (κ → ℤ) → ℝ) hg => sum_piFinset_split B k g hg
  rcases hb : e (Sum.inr (k, false)) with _ | _
  · have he' := he k
    rw [hb] at he'
    have := hsplit (fun a μ => rc (jI k) (a - 2) * h (a - 2) a μ - rc (jI k) a * h a (a + 2) μ)
      (fun a μ => by simp only [← hhk])
    have hR : ∀ μ, raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inr (k, false)) +
        raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inr (k, true)) =
        rc (jI k) (μ k - 2) * h (μ k - 2) (μ k) μ - rc (jI k) (μ k) * h (μ k) (μ k + 2) μ := by
      intro μ
      simp only [raiseAt, hb, he', Bool.not_false, Bool.false_eq_true, ite_false,
        ite_true, Sum.elim_inr, hj, hval]
      ring
    simp only [hR]
    rw [this]
    refine sum_eq_zero fun μ _ => sum_pair_cancel (jI k) (fun p q => h p q μ) (hF μ)
  · have he' := he k
    rw [hb] at he'
    have := hsplit (fun a μ => rc (jI k) (a - 2) * h a (a - 2) μ - rc (jI k) a * h (a + 2) a μ)
      (fun a μ => by simp only [← hhk])
    have hR : ∀ μ, raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inr (k, false)) +
        raiseAt j e X (Sum.elim m fun p => μ p.1) (Sum.inr (k, true)) =
        rc (jI k) (μ k - 2) * h (μ k) (μ k - 2) μ - rc (jI k) (μ k) * h (μ k + 2) (μ k) μ := by
      intro μ
      simp only [raiseAt, hb, he', Bool.not_true, Bool.false_eq_true, ite_false,
        ite_true, Sum.elim_inr, hj, hval]
      ring
    simp only [hR]
    rw [this]
    refine sum_eq_zero fun μ _ =>
      sum_pair_cancel (jI k) (fun p q => h q p μ) (fun p q hne => (hF μ q p hne).symm)

/-- **Contracting any set of pairs of legs** (each pair an incoming and an outgoing leg-end of the
same spin) keeps a tensor invariant. -/
theorem IsInv.contrAll {j : ι ⊕ (κ × Bool) → ℕ} {d : ι ⊕ (κ × Bool) → Bool}
    {X : (ι ⊕ (κ × Bool) → ℤ) → ℝ} {jI : κ → ℕ} (hX : IsInv j d X)
    (hj : ∀ k b, j (Sum.inr (k, b)) = jI k)
    (hd : ∀ k, d (Sum.inr (k, true)) = !d (Sum.inr (k, false))) :
    IsInv (j ∘ Sum.inl) (d ∘ Sum.inl) (Lightlike.Recoupling.contrAll jI X) := by
  refine ⟨fun m h i => ?_, fun m h => ?_, raise_contrAll hX.supp hX.raise hj hd,
    raise_contrAll (e := fun x => !d x) hX.supp hX.lower hj (fun k => by simp [hd k])⟩
  · obtain ⟨μ, -, hμ⟩ := exists_ne_zero_of_sum_ne_zero h
    simpa using hX.supp _ hμ (Sum.inl i)
  · obtain ⟨μ, -, hμ⟩ := exists_ne_zero_of_sum_ne_zero h
    have hw := hX.weight _ hμ
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type] at hw
    simp only [Fintype.sum_bool, Sum.elim_inl, Sum.elim_inr, hd] at hw
    have h0 : ∀ k, ((if (!d (Sum.inr (k, false))) = true then -μ k else μ k) +
        (if d (Sum.inr (k, false)) = true then -μ k else μ k)) = 0 := by
      intro k; cases d (Sum.inr (k, false)) <;> simp
    simp only [h0, sum_const_zero, add_zero] at hw
    simpa using hw

end ContrAll

/-! ## Networks -/

section Net

variable {ι κ N : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype N]
  [DecidableEq N] {Λ : N → Type*} [∀ n, Fintype (Λ n)] [∀ n, DecidableEq (Λ n)]

/-- The projection at a leg-end of a network: the open projection `m i` if the leg-end is the open
leg `i`, the internal projection `μ k` if it is an end of the internal edge `k`. -/
def legVal (e : (Σ n, Λ n) ≃ ι ⊕ (κ × Bool)) (m : ι → ℤ) (μ : κ → ℤ) (l : Σ n, Λ n) : ℤ :=
  Sum.elim m (fun p => μ p.1) (e l)

/-- **The evaluation of a network** with nodes `N` (leg-ends `Λ n`, tensors `T n`), open legs `ι`
and internal edges `κ` (spins `jI`): `e` says which leg-end is which open leg or which end
(`false`: incoming, `true`: outgoing) of which internal edge. -/
noncomputable def netEval (e : (Σ n, Λ n) ≃ ι ⊕ (κ × Bool)) (jI : κ → ℕ)
    (T : ∀ n, (Λ n → ℤ) → ℝ) (m : ι → ℤ) : ℝ :=
  ∑ μ ∈ Fintype.piFinset (fun k => Icc (-(jI k : ℤ)) (jI k)),
    ∏ n, T n (fun l => legVal e m μ ⟨n, l⟩)

/-- **A network of invariant tensors is invariant** on its open legs, if every leg-end has the spin
of its open leg or internal edge, open leg-ends have the direction of their open leg, and every
internal edge runs from an incoming to an outgoing leg-end. -/
theorem isInv_netEval (e : (Σ n, Λ n) ≃ ι ⊕ (κ × Bool)) {jO : ι → ℕ} {dO : ι → Bool}
    (jI : κ → ℕ) {j : ∀ n, Λ n → ℕ} {d : ∀ n, Λ n → Bool} {T : ∀ n, (Λ n → ℤ) → ℝ}
    (hT : ∀ n, IsInv (j n) (d n) (T n))
    (hj : ∀ l, j l.1 l.2 = Sum.elim jO (fun p => jI p.1) (e l))
    (hd : ∀ l, d l.1 l.2 = Sum.elim dO (fun p => p.2) (e l)) :
    IsInv jO dO (netEval e jI T) := by
  have hP := (isInv_prod hT).reindex e.symm
  have h1 := hP.contrAll (jI := jI) (fun k b => by simpa using hj (e.symm (Sum.inr (k, b))))
    (fun k => by
      have a := hd (e.symm (Sum.inr (k, true)))
      have b := hd (e.symm (Sum.inr (k, false)))
      simp only [Equiv.apply_symm_apply, Sum.elim_inr] at a b
      simp [Function.comp_apply, a, b])
  have ej : (fun l : Σ n, Λ n => j l.1 l.2) ∘ e.symm ∘ Sum.inl = jO := by
    funext i; simpa using hj (e.symm (Sum.inl i))
  have ed : (fun l : Σ n, Λ n => d l.1 l.2) ∘ e.symm ∘ Sum.inl = dO := by
    funext i; simpa using hd (e.symm (Sum.inl i))
  rw [Function.comp_assoc, ej, Function.comp_assoc, ed] at h1
  exact h1.congr fun m => rfl

end Net

end Lightlike.Recoupling
