import Lightlike.GR.SpinorHelicity

/-!
# Colour-ordered MHV amplitudes: the Parke-Taylor formula and its symmetries

Gluons in colour order carry angle spinors `s : Fin n → (Fin 2 → ℂ)`; the cyclic denominator is
`⟨12⟩⟨23⟩ ⋯ ⟨n1⟩` (`cycDen`). The Parke-Taylor amplitude (Elvang-Huang (2.80)) with the two
negative-helicity gluons `i`, `j` is `⟨ij⟩⁴ / (⟨12⟩⟨23⟩ ⋯ ⟨n1⟩)` (`parkeTaylor`, the numerator spinors
passed separately, so that reordering the gluons does not move them).

* **Cyclic symmetry** (`parkeTaylor_rotate`, Elvang-Huang p. 25, property 1).
* **Reflection** `A_n[1 2 ⋯ n] = (−1)ⁿ A_n[n ⋯ 2 1]` (`parkeTaylor_rev`, property 2).
* **The U(1) decoupling identity** (`parkeTaylor_U1_decoupling`, (2.82)): the sum of the amplitudes with
  one gluon inserted in each of the cyclic slots of the others vanishes; the proof is the eikonal identity
  `Σ_a ⟨a, a+1⟩ / (⟨a ν⟩⟨ν, a+1⟩) = 0` (`eikonal_sum`), a telescoping sum by the Schouten identity.
* **Little-group weights** (`parkeTaylor_littleGroup_plus`, `parkeTaylor_littleGroup_minus`, (2.93)):
  `t⁻²` for a positive-helicity gluon, `t²` for a negative-helicity one (`cycDen_update_smul`).
* **The Kleiss-Kuijf relation at five points** (`parkeTaylor_KK5`, (2.85)).
* **The four-point amplitude in angle and in square brackets** (`parkeTaylor_four_eq_square`,
  (2.79) = (2.81)), with momentum conservation (`Conserved`, `contract_conserved`).

The Parke-Taylor expression is the MHV sector (2.80) of the colour-ordered gluon tree amplitudes; it is
taken here as a formula (its derivation from the Yang-Mills Feynman rules or by BCFW recursion is not
part of this file), and colour-ordered trees of general helicity are not defined.

## References

* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697: §2.5, p. 24, the Parke-Taylor amplitude
  (2.79)–(2.80) and Exercise 2.24 ((2.81)); p. 25, the cyclic and reflection properties, the U(1)
  decoupling identity (2.82), the Kleiss-Kuijf relations (2.83)–(2.85) and Exercise 2.27; the Schouten
  identity (2.48), p. 16; little-group weights (2.93), p. 28.
-/

open Matrix

noncomputable section

namespace Lightlike.SpinorHelicity

/-- The cyclic denominator `⟨s₁ s₂⟩⟨s₂ s₃⟩ ⋯ ⟨sₙ s₁⟩`. -/
def cycDen {n : ℕ} (s : Fin n → Fin 2 → ℂ) : ℂ := ∏ k, angleBr (s k) (s (finRotate n k))

/-- **The Parke-Taylor colour-ordered MHV amplitude** (Elvang-Huang (2.80)): `⟨ij⟩⁴ / (⟨12⟩ ⋯ ⟨n1⟩)`,
with `ti`, `tj` the angle spinors of the two negative-helicity gluons and `s` the angle spinors of all
gluons in colour order. -/
def parkeTaylor {n : ℕ} (ti tj : Fin 2 → ℂ) (s : Fin n → Fin 2 → ℂ) : ℂ :=
  angleBr ti tj ^ 4 / cycDen s

/-- **Cyclic symmetry** (Elvang-Huang p. 25): `A_n[2 ⋯ n 1] = A_n[1 2 ⋯ n]`. -/
theorem cycDen_rotate {n : ℕ} (s : Fin n → Fin 2 → ℂ) : cycDen (s ∘ finRotate n) = cycDen s := by
  unfold cycDen
  exact Equiv.prod_comp (finRotate n) (fun k => angleBr (s k) (s (finRotate n k)))

theorem parkeTaylor_rotate {n : ℕ} (ti tj : Fin 2 → ℂ) (s : Fin n → Fin 2 → ℂ) :
    parkeTaylor ti tj (s ∘ finRotate n) = parkeTaylor ti tj s := by
  rw [parkeTaylor, parkeTaylor, cycDen_rotate]

/-! ### Index lemmas for cyclic orders -/
lemma val_succAbove_succ {m : ℕ} (a j : Fin m) :
    ((a.succ.succAbove j : Fin (m + 1)) : ℕ) =
      if (j : ℕ) ≤ (a : ℕ) then (j : ℕ) else (j : ℕ) + 1 := by
  rcases Nat.lt_or_ge (j : ℕ) ((a : ℕ) + 1) with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using h)]
    split_ifs
    · simp only [Fin.val_castSucc]
    · omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using h)]
    split_ifs
    · omega
    · simp only [Fin.val_succ]

lemma finRotate_succAbove {m : ℕ} (a j : Fin m) :
    finRotate (m + 1) (a.succ.succAbove j) =
      if j = a then a.succ else a.succ.succAbove (finRotate m j) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos j).ne'
  have hj := j.isLt
  have ha := a.isLt
  by_cases hja : j = a
  · subst hja
    simp only [↓reduceIte]
    apply Fin.ext
    have hne : j.succ.succAbove j ≠ Fin.last (m' + 1) := by
      intro e; have := congrArg Fin.val e; rw [val_succAbove_succ] at this; simp at this; omega
    rw [coe_finRotate_of_ne_last hne, val_succAbove_succ]
    simp
  · simp only [hja, ↓reduceIte]
    have hja' : (j : ℕ) ≠ (a : ℕ) := fun e => hja (Fin.ext e)
    apply Fin.ext
    rw [coe_finRotate, val_succAbove_succ, val_succAbove_succ, coe_finRotate]
    simp only [Fin.ext_iff, val_succAbove_succ, Fin.val_last]
    split_ifs <;> omega

lemma finRotate_succ_eq {m : ℕ} (a : Fin m) :
    finRotate (m + 1) a.succ = a.succ.succAbove (finRotate m a) := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos a).ne'
  have ha := a.isLt
  apply Fin.ext
  rw [coe_finRotate, val_succAbove_succ, coe_finRotate]
  simp only [Fin.ext_iff, Fin.val_succ, Fin.val_last]
  split_ifs <;> omega

lemma rev_finRotate {n : ℕ} (k : Fin n) :
    Fin.rev (finRotate n k) = (finRotate n).symm (Fin.rev k) := by
  rw [Equiv.eq_symm_apply]
  rcases n with _ | n
  · exact k.elim0
  have hk := k.isLt
  apply Fin.ext
  rw [coe_finRotate, Fin.val_rev, Fin.val_rev, coe_finRotate]
  simp only [Fin.ext_iff, Fin.val_rev, Fin.val_last, coe_finRotate]
  split_ifs <;> omega

/-- **Reflection** (Elvang-Huang p. 25): reversing the colour order multiplies the denominator by `(−1)ⁿ`. -/
theorem cycDen_rev {n : ℕ} (s : Fin n → Fin 2 → ℂ) : cycDen (s ∘ Fin.rev) = (-1) ^ n * cycDen s := by
  unfold cycDen
  simp only [Function.comp_apply, rev_finRotate]
  calc ∏ k, angleBr (s (Fin.rev k)) (s ((finRotate n).symm (Fin.rev k)))
      = ∏ m, angleBr (s m) (s ((finRotate n).symm m)) :=
        Fintype.prod_equiv Fin.revPerm _ _ fun k => rfl
    _ = ∏ m, angleBr (s (finRotate n m)) (s m) :=
        (Fintype.prod_equiv (finRotate n) _ _ fun m => by simp only [Equiv.symm_apply_apply]).symm
    _ = ∏ m, ((-1) * angleBr (s m) (s (finRotate n m))) :=
        Finset.prod_congr rfl fun m _ => by rw [angleBr_antisymm]; ring
    _ = (-1) ^ n * ∏ m, angleBr (s m) (s (finRotate n m)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem parkeTaylor_rev {n : ℕ} (ti tj : Fin 2 → ℂ) (s : Fin n → Fin 2 → ℂ) :
    parkeTaylor ti tj (s ∘ Fin.rev) = (-1) ^ n * parkeTaylor ti tj s := by
  have h : ((-1 : ℂ) ^ n)⁻¹ = (-1) ^ n := by rw [← inv_pow, inv_neg, inv_one]
  rw [parkeTaylor, parkeTaylor, cycDen_rev, div_eq_mul_inv, mul_inv, h, div_eq_mul_inv]
  ring

/-! ## The U(1) decoupling identity -/

/-- **The eikonal identity**: for angle spinors `s` in cyclic order and `ν` with all `⟨s_a ν⟩ ≠ 0`,
`Σ_a ⟨s_a s_{a+1}⟩ / (⟨s_a ν⟩⟨ν s_{a+1}⟩) = 0` (a telescoping sum by Schouten (2.48)). -/
theorem eikonal_sum {m : ℕ} (s : Fin m → Fin 2 → ℂ) (ν : Fin 2 → ℂ) (hν : ∀ a, angleBr (s a) ν ≠ 0) :
    ∑ a, angleBr (s a) (s (finRotate m a)) /
      (angleBr (s a) ν * angleBr ν (s (finRotate m a))) = 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  -- a reference spinor `x` with `⟨ν x⟩ ≠ 0`
  have hν0 : ν ≠ 0 := by
    intro h; apply hν ⟨0, hm⟩; rw [h, angleBr_eq]; simp
  obtain ⟨x, hx⟩ : ∃ x : Fin 2 → ℂ, angleBr ν x ≠ 0 := by
    by_cases h1 : ν 1 = 0
    · refine ⟨![0, 1], ?_⟩
      have : ν 0 ≠ 0 := fun h0 => hν0 (by funext i; fin_cases i <;> simp [h0, h1])
      simpa [angleBr_eq] using this
    · refine ⟨![1, 0], ?_⟩
      simpa [angleBr_eq] using h1
  set g : (Fin 2 → ℂ) → ℂ := fun c => angleBr c x / (angleBr ν c * angleBr ν x) with hg
  have hterm : ∀ a, angleBr (s a) (s (finRotate m a)) /
      (angleBr (s a) ν * angleBr ν (s (finRotate m a))) = g (s (finRotate m a)) - g (s a) := by
    intro a
    have ha := hν a
    have hb := hν (finRotate m a)
    have ha' : angleBr ν (s a) ≠ 0 := by rw [angleBr_antisymm]; exact neg_ne_zero.2 ha
    have hb' : angleBr ν (s (finRotate m a)) ≠ 0 := by rw [angleBr_antisymm]; exact neg_ne_zero.2 hb
    simp only [hg]
    rw [div_sub_div _ _ (mul_ne_zero hb' hx) (mul_ne_zero ha' hx),
      div_eq_div_iff (mul_ne_zero ha hb') (mul_ne_zero (mul_ne_zero hb' hx) (mul_ne_zero ha' hx))]
    simp only [angleBr_eq]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib,
    Equiv.sum_comp (finRotate m) (fun a => g (s a)), sub_self]

/-- Inserting `ν` after the `a`-th gluon: the cyclic denominator gains `⟨s_a ν⟩⟨ν s_{a+1}⟩` and loses
`⟨s_a s_{a+1}⟩`. -/
theorem cycDen_insertNth {m : ℕ} (s : Fin m → Fin 2 → ℂ) (ν : Fin 2 → ℂ) (a : Fin m) :
    cycDen (Fin.insertNth a.succ ν s) * angleBr (s a) (s (finRotate m a)) =
      angleBr (s a) ν * angleBr ν (s (finRotate m a)) * cycDen s := by
  set t : Fin (m + 1) → Fin 2 → ℂ := Fin.insertNth a.succ ν s with ht
  have hT : ∀ j, t (a.succ.succAbove j) = s j := fun j => Fin.insertNth_apply_succAbove _ _ _ _
  have hP : t a.succ = ν := Fin.insertNth_apply_same _ _ _
  have hF : ∀ j, angleBr (t (a.succ.succAbove j)) (t (finRotate (m + 1) (a.succ.succAbove j))) =
      if j = a then angleBr (s j) ν else angleBr (s j) (s (finRotate m j)) := by
    intro j
    rw [finRotate_succAbove, hT]
    split_ifs with h
    · rw [hP]
    · rw [hT]
  have hden : cycDen t = angleBr ν (s (finRotate m a)) *
      ∏ j, (if j = a then angleBr (s j) ν else angleBr (s j) (s (finRotate m j))) := by
    unfold cycDen
    rw [Fin.prod_univ_succAbove _ a.succ, hP, finRotate_succ_eq, hT]
    exact congrArg _ (Finset.prod_congr rfl fun j _ => hF j)
  have hsplit := Finset.mul_prod_erase Finset.univ
    (fun j => if j = a then angleBr (s j) ν else angleBr (s j) (s (finRotate m j)))
    (Finset.mem_univ a)
  have hsplit' := Finset.mul_prod_erase Finset.univ
    (fun j => angleBr (s j) (s (finRotate m j))) (Finset.mem_univ a)
  have herase : ∏ j ∈ Finset.univ.erase a,
      (if j = a then angleBr (s j) ν else angleBr (s j) (s (finRotate m j))) =
        ∏ j ∈ Finset.univ.erase a, angleBr (s j) (s (finRotate m j)) :=
    Finset.prod_congr rfl fun j hj => by simp only [Finset.ne_of_mem_erase hj, ↓reduceIte]
  simp only [↓reduceIte] at hsplit
  rw [hden, ← hsplit, herase]
  unfold cycDen
  rw [← hsplit']
  ring

/-- **The U(1) decoupling identity** (Elvang-Huang (2.82)) for the Parke-Taylor amplitudes: inserting the
gluon `ν` in each of the cyclic slots of the colour-ordered gluons `s` and summing gives zero (for
nonvanishing brackets). -/
theorem parkeTaylor_U1_decoupling {m : ℕ} (ti tj : Fin 2 → ℂ) (s : Fin m → Fin 2 → ℂ)
    (ν : Fin 2 → ℂ) (hs : cycDen s ≠ 0) (hν : ∀ a, angleBr (s a) ν ≠ 0) :
    ∑ a : Fin m, parkeTaylor ti tj (Fin.insertNth a.succ ν s) = 0 := by
  have hpair : ∀ a, angleBr (s a) (s (finRotate m a)) ≠ 0 := fun a h =>
    hs (Finset.prod_eq_zero (Finset.mem_univ a) h)
  have hν' : ∀ a, angleBr ν (s (finRotate m a)) ≠ 0 := fun a => by
    rw [angleBr_antisymm]; exact neg_ne_zero.2 (hν _)
  have key : ∀ a, parkeTaylor ti tj (Fin.insertNth a.succ ν s) =
      angleBr ti tj ^ 4 / cycDen s * (angleBr (s a) (s (finRotate m a)) /
        (angleBr (s a) ν * angleBr ν (s (finRotate m a)))) := by
    intro a
    have hins := cycDen_insertNth s ν a
    have hden : cycDen (Fin.insertNth a.succ ν s) =
        angleBr (s a) ν * angleBr ν (s (finRotate m a)) * cycDen s /
          angleBr (s a) (s (finRotate m a)) := by
      rw [eq_div_iff (hpair a)]; exact hins
    rw [parkeTaylor, hden]
    field_simp [hν a, hν' a, hpair a, hs]
  rw [Finset.sum_congr rfl fun a _ => key a, ← Finset.mul_sum, eikonal_sum s ν hν, mul_zero]

/-! ## Little-group weights -/

lemma angleBr_smul_smul' (c d : ℂ) (a b : Fin 2 → ℂ) :
    angleBr (c • a) (d • b) = c * d * angleBr a b := by
  simp only [angleBr_eq, Pi.smul_apply, smul_eq_mul]; ring

/-- Scaling one angle spinor `|k⟩ ↦ t |k⟩` multiplies the cyclic denominator by `t²` (gluon `k` sits in
two adjacent brackets). -/
theorem cycDen_update_smul {n : ℕ} (s : Fin n → Fin 2 → ℂ) (k : Fin n) (t : ℂ) :
    cycDen (Function.update s k (t • s k)) = t ^ 2 * cycDen s := by
  have hs : Function.update s k (t • s k) = fun m => (if m = k then t else 1) • s m := by
    funext m
    by_cases h : m = k
    · subst h; simp
    · simp [h]
  unfold cycDen
  rw [hs]
  simp only [angleBr_smul_smul']
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k,
    ← Equiv.prod_comp (finRotate n).symm (fun m => if finRotate n m = k then t else 1)]
  simp only [Equiv.apply_symm_apply, Finset.prod_ite_eq' Finset.univ k, Finset.mem_univ,
    ↓reduceIte]
  ring

/-- **The little-group weights of the Parke-Taylor amplitude** (Elvang-Huang (2.93) with (2.80)): under
`|k⟩ ↦ t |k⟩` a positive-helicity gluon `k` gives `t⁻²` (weight `−2h = −2`), and a negative-helicity gluon
`k = i` gives `t²` (weight `−2h = +2`). -/
theorem parkeTaylor_littleGroup_plus {n : ℕ} (s : Fin n → Fin 2 → ℂ) (i j k : Fin n) (hki : k ≠ i)
    (hkj : k ≠ j) (t : ℂ) :
    parkeTaylor ((Function.update s k (t • s k)) i) ((Function.update s k (t • s k)) j)
        (Function.update s k (t • s k)) = t ^ (-2 : ℤ) * parkeTaylor (s i) (s j) s := by
  rw [Function.update_of_ne hki.symm, Function.update_of_ne hkj.symm, parkeTaylor, parkeTaylor,
    cycDen_update_smul, _root_.zpow_neg, zpow_two, div_eq_mul_inv, mul_inv, div_eq_mul_inv, pow_two]
  ring

theorem parkeTaylor_littleGroup_minus {n : ℕ} (s : Fin n → Fin 2 → ℂ) (i j : Fin n) (hij : i ≠ j)
    {t : ℂ} (ht : t ≠ 0) :
    parkeTaylor ((Function.update s i (t • s i)) i) ((Function.update s i (t • s i)) j)
        (Function.update s i (t • s i)) = t ^ (2 : ℤ) * parkeTaylor (s i) (s j) s := by
  rw [Function.update_self, Function.update_of_ne hij.symm, parkeTaylor, parkeTaylor,
    cycDen_update_smul]
  have h1 : angleBr (t • s i) (s j) = t * angleBr (s i) (s j) := by
    simp only [angleBr_eq, Pi.smul_apply, smul_eq_mul]; ring
  rw [h1, zpow_two, mul_pow, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
  field_simp

/-! ## The Kleiss-Kuijf relation at five points -/

/-- **The Kleiss-Kuijf relation (2.85) for the Parke-Taylor amplitudes** (Elvang-Huang p. 25, Exercise
2.27): `A₅[12345] + A₅[12354] + A₅[12435] + A₅[14235] = 0` (for nonvanishing brackets; it holds without
momentum conservation). -/
theorem parkeTaylor_KK5 (ti tj : Fin 2 → ℂ) (s : Fin 5 → Fin 2 → ℂ)
    (h : ∀ a b : Fin 5, a ≠ b → angleBr (s a) (s b) ≠ 0) :
    parkeTaylor ti tj ![s 0, s 1, s 2, s 3, s 4] + parkeTaylor ti tj ![s 0, s 1, s 2, s 4, s 3] +
      parkeTaylor ti tj ![s 0, s 1, s 3, s 2, s 4] + parkeTaylor ti tj ![s 0, s 3, s 1, s 2, s 4] = 0 := by
  have r0 : finRotate 5 0 = 1 := by decide
  have r1 : finRotate 5 1 = 2 := by decide
  have r2 : finRotate 5 2 = 3 := by decide
  have r3 : finRotate 5 3 = 4 := by decide
  have r4 : finRotate 5 4 = 0 := by decide
  simp only [parkeTaylor, cycDen, Fin.prod_univ_five, r0, r1, r2, r3, r4, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  have := h 0 1 (by decide); have := h 1 2 (by decide); have := h 2 3 (by decide)
  have := h 3 4 (by decide); have := h 4 0 (by decide); have := h 3 0 (by decide)
  have := h 2 4 (by decide); have := h 1 3 (by decide); have := h 3 2 (by decide)
  have := h 2 0 (by decide); have := h 0 3 (by decide); have := h 3 1 (by decide)
  have := h 4 3 (by decide)
  field_simp
  simp only [angleBr_eq]
  ring

/-! ## The four-point identity (2.79) = (2.81) -/

/-- Momentum conservation for `n` massless particles, all outgoing: `Σ λ_i λ̃_iᵀ = 0`. -/
def Conserved {n : ℕ} (l lt : Fin n → Fin 2 → ℂ) : Prop :=
  ∀ a b, ∑ i, l i a * lt i b = 0

/-- **Contraction with momentum conservation**: `Σ_i ⟨A i⟩[i B] = 0`. -/
theorem contract_conserved {n : ℕ} {l lt : Fin n → Fin 2 → ℂ} (h : Conserved l lt)
    (A B : Fin 2 → ℂ) : ∑ i, angleBr A (lt i) * squareBr (l i) B = 0 := by
  have e : ∀ i, angleBr A (lt i) * squareBr (l i) B =
      B 1 * A 1 * (l i 0 * lt i 0) - B 1 * A 0 * (l i 0 * lt i 1) -
        B 0 * A 1 * (l i 1 * lt i 0) + B 0 * A 0 * (l i 1 * lt i 1) := fun i => by
    simp only [angleBr_eq, squareBr_eq]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h 0 0, h 0 1,
    h 1 0, h 1 1]
  ring

/-- **The four-point MHV amplitude in angle and in square brackets** (Elvang-Huang (2.79) = (2.81),
Exercise 2.24): with momentum conservation, `⟨12⟩⁴/(⟨12⟩⟨23⟩⟨34⟩⟨41⟩) = [34]⁴/([12][23][34][41])`
(for nonvanishing brackets). -/
theorem parkeTaylor_four_eq_square {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt)
    (ha : ∀ a b : Fin 4, a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hs : ∀ a b : Fin 4, a ≠ b → squareBr (l a) (l b) ≠ 0) :
    parkeTaylor (lt 0) (lt 1) lt =
      squareBr (l 2) (l 3) ^ 4 / (squareBr (l 0) (l 1) * squareBr (l 1) (l 2) *
        squareBr (l 2) (l 3) * squareBr (l 3) (l 0)) := by
  have c := fun A B => contract_conserved h A B
  have c11 := c (lt 0) (l 0); have c22 := c (lt 1) (l 1); have c33 := c (lt 2) (l 2)
  have c44 := c (lt 3) (l 3); have c13 := c (lt 0) (l 2); have c24 := c (lt 1) (l 3)
  simp only [Fin.sum_univ_four] at c11 c22 c33 c44 c13 c24
  have r0 : finRotate 4 0 = 1 := by decide
  have r1 : finRotate 4 1 = 2 := by decide
  have r2 : finRotate 4 2 = 3 := by decide
  have r3 : finRotate 4 3 = 0 := by decide
  simp only [parkeTaylor, cycDen, Fin.prod_univ_four, r0, r1, r2, r3]
  have := ha 0 1 (by decide); have := ha 1 2 (by decide); have := ha 2 3 (by decide)
  have := ha 3 0 (by decide); have := hs 0 1 (by decide); have := hs 1 2 (by decide)
  have := hs 2 3 (by decide); have := hs 3 0 (by decide)
  have a00 : angleBr (lt 0) (lt 0) = 0 := by rw [angleBr_eq]; ring
  have a11 : angleBr (lt 1) (lt 1) = 0 := by rw [angleBr_eq]; ring
  have q22 : squareBr (l 2) (l 2) = 0 := by rw [squareBr_eq]; ring
  have q33 : squareBr (l 3) (l 3) = 0 := by rw [squareBr_eq]; ring
  have e3 : angleBr (lt 0) (lt 1) * squareBr (l 1) (l 2) =
      angleBr (lt 0) (lt 3) * squareBr (l 2) (l 3) := by
    rw [a00, q22, squareBr_antisymm (l 3) (l 2)] at c13
    linear_combination c13
  have e2 : angleBr (lt 1) (lt 2) * squareBr (l 2) (l 3) =
      angleBr (lt 0) (lt 1) * squareBr (l 0) (l 3) := by
    rw [a11, q33, angleBr_antisymm (lt 1) (lt 0)] at c24
    linear_combination c24
  have e1 : angleBr (lt 0) (lt 1) * squareBr (l 0) (l 1) =
      angleBr (lt 2) (lt 3) * squareBr (l 2) (l 3) := by
    simp only [angleBr_eq, squareBr_eq] at c11 c22 c33 c44 ⊢
    linear_combination (-c11 - c22 + c33 + c44) / 2
  have n1 : angleBr (lt 3) (lt 0) + angleBr (lt 0) (lt 3) = 0 := by
    rw [angleBr_antisymm (lt 3) (lt 0)]; ring
  have n2 : squareBr (l 0) (l 3) + squareBr (l 3) (l 0) = 0 := by
    rw [squareBr_antisymm (l 0) (l 3)]; ring
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero ‹_› ‹_›) ‹_›) ‹_›)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero ‹_› ‹_›) ‹_›) ‹_›)]
  linear_combination
    (angleBr (lt 0) (lt 1) ^ 3 * squareBr (l 0) (l 1) * squareBr (l 2) (l 3) *
      squareBr (l 3) (l 0)) * e3 +
    (angleBr (lt 0) (lt 1) ^ 2 * squareBr (l 2) (l 3) ^ 2 * squareBr (l 3) (l 0) *
      angleBr (lt 0) (lt 3)) * e1 -
    (squareBr (l 2) (l 3) ^ 3 * angleBr (lt 0) (lt 1) * angleBr (lt 2) (lt 3) *
      angleBr (lt 3) (lt 0)) * e2 +
    (angleBr (lt 0) (lt 1) ^ 2 * angleBr (lt 2) (lt 3) * squareBr (l 2) (l 3) ^ 3) *
      (angleBr (lt 0) (lt 3) * n2 - squareBr (l 0) (l 3) * n1)

end Lightlike.SpinorHelicity
