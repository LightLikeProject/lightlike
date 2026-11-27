import Lightlike.SpinFoam.EPRLStateSum.VertexPerm

/-!
# Relabelling the nodes of the contraction on `K₅`

The edge projections `m : Fin 10 → ℤ` read by the nodes of `contract5` are antisymmetric: the node `a` reads `m_{ab}` on its leg `b` for
`a < b` and `-m_{ba}` for `b < a` (`legProj`). A permutation `π` of the nodes acts on the projections by `permProj π`, which is a bijection
of the boxes, and the contraction of the relabelled node tensors is the contraction of the old ones times `(-1)^J` for every link whose
orientation `π` reverses (`contract5_perm`; the sign `edgeSign_neg`, on the support of the parity).
-/

open Finset Lightlike.Recoupling Lightlike.SpinFoam

namespace Lightlike.SpinFoam.EPRLStateSum

lemma legProj_self (m : Fin 10 → ℤ) (a : Fin 5) : legProj m a a = 0 := by
  simp [legProj]

lemma legProj_lt (m : Fin 10 → ℤ) {a b : Fin 5} (h : a < b) : legProj m a b = m (eidx a b) := by
  simp [legProj, h]

lemma legProj_neg (m : Fin 10 → ℤ) {a b : Fin 5} (h : a ≠ b) : legProj m b a = - legProj m a b := by
  rcases lt_or_gt_of_ne h with hab | hab
  · simp [legProj, hab, not_lt_of_gt hab, hab.ne']
  · simp [legProj, hab, not_lt_of_gt hab, hab.ne]

/-- The index of the edge `eidx p q` of the pair `p < q` is the edge of that pair. -/
lemma epr_eidx : ∀ p q : Fin 5, p < q → epr (eidx p q) = (p, q) := by decide

lemma eidx_epr : ∀ e : Fin 10, eidx (epr e).1 (epr e).2 = e := by decide

lemma epr_lt : ∀ e : Fin 10, (epr e).1 < (epr e).2 := by decide

/-- A family of projections is determined by its readings on the pairs `p < q`. -/
lemma legProj_epr (m : Fin 10 → ℤ) (e : Fin 10) : legProj m (epr e).1 (epr e).2 = m e := by
  rw [legProj_lt m (epr_lt e), eidx_epr]

/-- The projections read after a relabelling `π` of the nodes. -/
def permProj (π : Equiv.Perm (Fin 5)) (m : Fin 10 → ℤ) : Fin 10 → ℤ :=
  fun e => legProj m (π (epr e).1) (π (epr e).2)

lemma legProj_permProj (π : Equiv.Perm (Fin 5)) (m : Fin 10 → ℤ) (a b : Fin 5) :
    legProj (permProj π m) a b = legProj m (π a) (π b) := by
  by_cases hab : a = b
  · subst hab; simp [legProj_self]
  · rcases lt_or_gt_of_ne hab with h | h
    · rw [legProj_lt _ h]
      unfold permProj
      rw [epr_eidx a b h]
    · rw [legProj_neg _ (Ne.symm hab), legProj_lt _ h]
      unfold permProj
      rw [epr_eidx b a h, legProj_neg m (fun h' => hab (π.injective h').symm)]

lemma permProj_symm_permProj (π : Equiv.Perm (Fin 5)) (m : Fin 10 → ℤ) : permProj π.symm (permProj π m) = m := by
  funext e
  show legProj (permProj π m) (π.symm (epr e).1) (π.symm (epr e).2) = m e
  rw [legProj_permProj]
  simp only [Equiv.apply_symm_apply]
  exact legProj_epr m e

lemma permProj_permProj_symm (π : Equiv.Perm (Fin 5)) (m : Fin 10 → ℤ) : permProj π (permProj π.symm m) = m := by
  have := permProj_symm_permProj π.symm m
  simpa using this

/-- The edge of the pair `{π a, π b}` for the edge `(a, b)`, `a < b`, of the relabelled structure. -/
def edgeMap (π : Equiv.Perm (Fin 5)) (e : Fin 10) : Fin 10 :=
  if π (epr e).1 < π (epr e).2 then eidx (π (epr e).1) (π (epr e).2) else eidx (π (epr e).2) (π (epr e).1)

lemma epr_edgeMap (π : Equiv.Perm (Fin 5)) (e : Fin 10) :
    epr (edgeMap π e) = if π (epr e).1 < π (epr e).2 then (π (epr e).1, π (epr e).2) else (π (epr e).2, π (epr e).1) := by
  unfold edgeMap
  split_ifs with h
  · exact epr_eidx _ _ h
  · exact epr_eidx _ _ (lt_of_le_of_ne (not_lt.1 h) (fun h' => by
      have := π.injective h'
      have := epr_lt e
      simp_all))

lemma edgeMap_injective (π : Equiv.Perm (Fin 5)) : Function.Injective (edgeMap π) := by
  intro e1 e2 h
  have h1 := epr_edgeMap π e1
  have h2 := epr_edgeMap π e2
  have hh : epr (edgeMap π e1) = epr (edgeMap π e2) := by rw [h]
  rw [h1, h2] at hh
  have l1 := epr_lt e1
  have l2 := epr_lt e2
  have hpi : ∀ x y : Fin 5, π x = π y ↔ x = y := fun x y => π.injective.eq_iff
  -- the pairs of `e₁` and `e₂` are equal, hence the edges
  suffices hp : epr e1 = epr e2 by
    have := congrArg (fun q : Fin 5 × Fin 5 => eidx q.1 q.2) hp
    simpa [eidx_epr] using this
  by_cases c1 : π (epr e1).1 < π (epr e1).2 <;> by_cases c2 : π (epr e2).1 < π (epr e2).2 <;>
    simp only [c1, c2, if_true, if_false, Prod.mk.injEq] at hh
  · exact Prod.ext (π.injective hh.1) (π.injective hh.2)
  · exfalso
    obtain ⟨a1, a2⟩ := hh
    have e1' := π.injective a1
    have e2' := π.injective a2
    rw [e1'] at l1
    rw [e2'] at l1
    exact absurd l1 (lt_asymm l2)
  · exfalso
    obtain ⟨a1, a2⟩ := hh
    have e1' := π.injective a1
    have e2' := π.injective a2
    rw [← e1', ← e2'] at l2
    exact absurd l1 (lt_asymm l2)
  · exact Prod.ext (π.injective hh.2) (π.injective hh.1)

/-- The exponent of the sign of the reversed links: `Σ J` over the pairs `π` inverts. -/
def invSum (J : Fin 5 → Fin 5 → ℕ) (π : Equiv.Perm (Fin 5)) : ℕ :=
  ∑ e : Fin 10, if π (epr e).2 < π (epr e).1 then J (π (epr e).1) (π (epr e).2) else 0

/-- **The edge weights of a relabelling**: on parity-valid projections, relabelling the nodes multiplies the product of the edge signs by `(-1)^J` for
every reversed link. -/
lemma edgeW_perm (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (π : Equiv.Perm (Fin 5)) (m : Fin 10 → ℤ)
    (hpar : ∀ e, ((jE J e : ℤ) - m e) % 2 = 0) :
    ∏ e' : Fin 10, edgeSign (J (π (epr e').1) (π (epr e').2)) (legProj m (π (epr e').1) (π (epr e').2)) =
      (-1 : ℝ) ^ invSum J π * ∏ e : Fin 10, edgeSign (jE J e) (m e) := by
  have hterm : ∀ e' : Fin 10, edgeSign (J (π (epr e').1) (π (epr e').2)) (legProj m (π (epr e').1) (π (epr e').2)) =
      (-1 : ℝ) ^ (if π (epr e').2 < π (epr e').1 then J (π (epr e').1) (π (epr e').2) else 0) *
        edgeSign (jE J (edgeMap π e')) (m (edgeMap π e')) := by
    intro e'
    have hr := epr_edgeMap π e'
    have hne : π (epr e').1 ≠ π (epr e').2 := fun h => by
      have := π.injective h
      have := epr_lt e'
      simp_all
    by_cases hc : π (epr e').1 < π (epr e').2
    · simp only [hc, if_true] at hr
      have hjE : jE J (edgeMap π e') = J (π (epr e').1) (π (epr e').2) := by
        unfold jE; rw [hr]
      rw [legProj_lt m hc, hjE, if_neg (not_lt_of_gt hc), pow_zero, one_mul]
      unfold edgeMap
      rw [if_pos hc]
    · have hc' : π (epr e').2 < π (epr e').1 := lt_of_le_of_ne (not_lt.1 hc) (Ne.symm hne)
      simp only [hc, if_false] at hr
      have hjE : jE J (edgeMap π e') = J (π (epr e').1) (π (epr e').2) := by
        unfold jE; rw [hr]; exact hJ _ _
      have hm : legProj m (π (epr e').1) (π (epr e').2) = - m (edgeMap π e') := by
        rw [legProj_neg m (Ne.symm hne), legProj_lt m hc']
        unfold edgeMap; rw [if_neg hc]
      rw [hm, if_pos hc', hjE]
      have hp := hpar (edgeMap π e')
      rw [hjE] at hp
      exact edgeSign_neg hp
  rw [Finset.prod_congr rfl fun e' _ => hterm e', Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  unfold invSum
  congr 1
  exact Equiv.prod_comp (Equiv.ofBijective (edgeMap π) (edgeMap_injective π).bijective_of_finite)
    (fun e => edgeSign (jE J e) (m e))

/-- The readings of a projection family in the box are bounded by the spins. -/
lemma legProj_mem (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (m : Fin 10 → ℤ)
    (hm : m ∈ Fintype.piFinset fun e : Fin 10 => Icc (-(jE J e : ℤ)) (jE J e)) (p q : Fin 5) :
    legProj m p q ∈ Icc (-(J p q : ℤ)) (J p q) := by
  by_cases hpq : p = q
  · subst hpq; simp [legProj_self]
  · rcases lt_or_gt_of_ne hpq with h | h
    · rw [legProj_lt m h]
      have := Fintype.mem_piFinset.1 hm (eidx p q)
      have hj : jE J (eidx p q) = J p q := by unfold jE; rw [epr_eidx p q h]
      rwa [hj] at this
    · rw [legProj_neg m (Ne.symm hpq), legProj_lt m h]
      have := Fintype.mem_piFinset.1 hm (eidx q p)
      have hj : jE J (eidx q p) = J p q := by unfold jE; rw [epr_eidx q p h]; exact hJ _ _
      rw [hj] at this
      simp only [mem_Icc] at this ⊢
      omega

/-- **The contraction on `K₅` under a relabelling of the nodes.** If the node tensors vanish at projections of the wrong parity, then
the contraction of the relabelled node tensors `T (π a) (μ ∘ π⁻¹)` with the relabelled spins `J (π a) (π b)` is the contraction of the old
ones times `(-1)^J` for every link whose orientation `π` reverses (`invSum`). -/
theorem contract5_perm (J : Fin 5 → Fin 5 → ℕ) (hJ : ∀ p q, J p q = J q p) (T : Fin 5 → (Fin 5 → ℤ) → ℝ)
    (hT : ∀ a μ, T a μ ≠ 0 → ∀ b, b ≠ a → ((J a b : ℤ) - μ b) % 2 = 0) (π : Equiv.Perm (Fin 5)) :
    contract5 (fun a b => J (π a) (π b)) (fun a μ => T (π a) (fun c => μ (π.symm c))) =
      (-1 : ℝ) ^ invSum J π * contract5 J T := by
  have hJ' : ∀ p q, (fun a b => J (π a) (π b)) p q = (fun a b => J (π a) (π b)) q p := fun p q => hJ _ _
  unfold contract5
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (permProj π.symm) (permProj π) ?_ ?_ ?_ ?_ ?_
  · intro m' hm'
    refine Fintype.mem_piFinset.2 fun e => ?_
    have := legProj_mem _ hJ' m' hm' (π.symm (epr e).1) (π.symm (epr e).2)
    simp only [Equiv.apply_symm_apply] at this
    exact this
  · intro m hm
    refine Fintype.mem_piFinset.2 fun e => ?_
    have := legProj_mem J hJ m hm (π (epr e).1) (π (epr e).2)
    exact this
  · intro m' _; exact permProj_permProj_symm π m'
  · intro m _; exact permProj_symm_permProj π m
  · intro m' hm'
    set m := permProj π.symm m' with hmdef
    have hm'eq : m' = permProj π m := (permProj_permProj_symm π m').symm
    have hG : ∏ a : Fin 5, T (π a) (fun c => legProj m' a (π.symm c)) = ∏ a : Fin 5, T a (legProj m a) := by
      rw [← Equiv.prod_comp π (fun a => T a (legProj m a))]
      refine Finset.prod_congr rfl fun a _ => ?_
      congr 1
      funext c
      rw [hmdef, legProj_permProj]
      simp
    rw [hG]
    by_cases h0 : ∏ a : Fin 5, T a (legProj m a) = 0
    · rw [h0]; simp
    · have hall : ∀ a, T a (legProj m a) ≠ 0 := fun a hz => h0 (Finset.prod_eq_zero (Finset.mem_univ a) hz)
      have hpar : ∀ e, ((jE J e : ℤ) - m e) % 2 = 0 := by
        intro e
        have := hT (epr e).1 (legProj m (epr e).1) (hall _) (epr e).2 (ne_of_gt (epr_lt e))
        rw [legProj_epr] at this
        exact this
      have hw : ∏ e' : Fin 10, edgeSign (jE (fun a b => J (π a) (π b)) e') (m' e') =
          (-1 : ℝ) ^ invSum J π * ∏ e : Fin 10, edgeSign (jE J e) (m e) := by
        rw [← edgeW_perm J hJ π m hpar]
        refine Finset.prod_congr rfl fun e' _ => ?_
        have : m' e' = legProj m (π (epr e').1) (π (epr e').2) := by
          rw [hm'eq]; rfl
        rw [this]; rfl
      rw [hw]
      ring

end Lightlike.SpinFoam.EPRLStateSum
