import Lightlike.FieldTheory.ZeroDim.GraphSplit
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The exponential formula in the algebra of graphs (Borinsky, Theorem 2.4.1, p. 18)

`lab c`: the number of labelled graphs in the class `c`; `X c = lab c/(n! k!)` (`X_eq_lab`) and the same for the
connected part (`Xc_eq_lab`). The number of components and connectedness are class invariants. The core identity
(`pow_Xc_eq`): `X_c^m (c) = [c has m components] · m! · lab c/(n! k!)`, by induction on `m`, splitting off one
component (`card_split`, via `glue` and `restrictL`); hence `e^{X_c} = X` (`expXc_eq_X`).

Borinsky's eq. (2.4.7) also writes the identity as `X_c = log X`. The logarithm is not defined in this algebra; the log
form is the same identity read through `log = exp⁻¹` on series with constant term `1`.
-/

open Finset MulAction

noncomputable section

namespace Lightlike.FieldTheory.GraphAlg

variable {n k : ℕ}

noncomputable instance : Fintype (LGraph n k) := Fintype.ofFinite _

open Classical in
/-- The labelled graphs in a class. -/
def labOf (c : GClass n k) : Finset (LGraph n k) := univ.filter fun Γ => (⟦Γ⟧ : GClass n k) = c

/-- **The number of labelled graphs** in a class. -/
def lab (c : GClass n k) : ℕ := (labOf c).card

lemma mem_labOf {c : GClass n k} {Γ : LGraph n k} : Γ ∈ labOf c ↔ (⟦Γ⟧ : GClass n k) = c := by
  classical
  simp [labOf]

lemma mem_labOf_iff_orbit {c : GClass n k} {Γ : LGraph n k} :
    Γ ∈ labOf c ↔ Γ ∈ orbit (Relabel n k) c.out := by
  rw [mem_labOf, ← orbitRel_apply, ← Quotient.eq (r := orbitRel (Relabel n k) (LGraph n k)), Quotient.out_eq]

lemma lab_eq_card_orbit (c : GClass n k) : lab c = Nat.card (orbit (Relabel n k) c.out) := by
  classical
  rw [lab, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun Γ => mem_labOf_iff_orbit)

/-- **`X(c) = lab c/(n! k!)`.** -/
theorem X_eq_lab (c : GClass n k) : X ⟨(n, k), c⟩ = lab c / (n.factorial * k.factorial) := by
  rw [X, autCard, inv_card_aut, lab_eq_card_orbit]

/-- Connectedness is a class invariant. -/
lemma isConnected_smul (g : Relabel n k) (Γ : LGraph n k) : IsConnected (g • Γ) ↔ IsConnected Γ := by
  unfold IsConnected
  have h := connOn_smul g Γ univ
  rwa [map_univ_equiv] at h

lemma isConnected_of_mem_labOf {c : GClass n k} {Γ : LGraph n k} (hΓ : Γ ∈ labOf c) :
    IsConnected Γ ↔ IsConnected c.out := by
  obtain ⟨g, rfl⟩ := mem_labOf_iff_orbit.1 hΓ
  exact isConnected_smul g _

lemma ncomp_of_mem_labOf {c : GClass n k} {Γ : LGraph n k} (hΓ : Γ ∈ labOf c) : ncomp Γ = ncomp c.out := by
  obtain ⟨g, rfl⟩ := mem_labOf_iff_orbit.1 hΓ
  exact ncomp_smul g _

open Classical in
/-- **`X_c(c) = [c connected] · lab c/(n! k!)`.** -/
theorem Xc_eq_lab (c : GClass n k) :
    Xc ⟨(n, k), c⟩ = if IsConnected c.out then (lab c : ℚ) / (n.factorial * k.factorial) else 0 := by
  rw [Xc]
  split_ifs with h
  · exact X_eq_lab c
  · rfl


section Split

open Classical

variable {A : Finset (Fin n)} {B : Finset (Fin k)} {n₁ k₁ n₂ k₂ : ℕ} (hA : A.card = n₁) (hk : B.card = k₁)
  (hA' : Aᶜ.card = n₂) (hk' : Bᶜ.card = k₂)

/-- The number of components of a glued graph with a connected first part. -/
lemma ncomp_glue {Γ₁ : LGraph n₁ k₁} {Γ₂ : LGraph n₂ k₂} (hconn : IsConnected Γ₁) :
    ncomp (glue A B hA hk hA' hk' Γ₁ Γ₂) = ncomp Γ₂ + 1 := by
  rw [ncomp, comps_glue hconn, card_insert_of_notMem, card_map, ncomp]
  intro hB
  obtain ⟨T, hT, hTB⟩ := mem_map.1 hB
  rw [comps, mem_filter] at hT
  obtain ⟨w, hw⟩ := hT.2.2.1
  have hv : embB Bᶜ hk' w ∈ (mapB₂ B hk') T := mem_map_of_mem (embB Bᶜ hk') hw
  rw [hTB] at hv
  exact mem_compl.1 (Bᶜ.orderIsoOfFin hk' w).2 hv

/-- The defining properties of the split-off component, from membership. -/
lemma split_props {c : GClass n k} {m : ℕ} {Γ : LGraph n k}
    (hΓ : Γ ∈ (labOf c).filter fun Γ => B ∈ comps Γ ∧ (∀ h, h ∈ A ↔ Γ.att h ∈ B) ∧ ncomp Γ = m + 1) :
    (∀ h, h ∈ A ↔ Γ.att h ∈ B) ∧ HalfEdge.Closed Γ.att Γ.inv B :=
  ⟨(mem_filter.1 hΓ).2.2.1, (mem_filter.1 (mem_filter.1 hΓ).2.1).2.1⟩

include hA hk hA' hk' in
/-- **Splitting off a component with vertices `B` and half-edges `A`**: the labelled graphs of class `c` with `m + 1`
components having `B` as a component with half-edge set `A` are the pairs (connected graph, graph with `m`
components) whose disjoint union has class `c`. -/
theorem card_split (c : GClass n k) (m : ℕ) :
    ((labOf c).filter fun Γ => B ∈ comps Γ ∧ (∀ h, h ∈ A ↔ Γ.att h ∈ B) ∧ ncomp Γ = m + 1).card =
      ((univ : Finset (LGraph n₁ k₁ × LGraph n₂ k₂)).filter fun p =>
        IsConnected p.1 ∧ ncomp p.2 = m ∧
          (⟨(n₁ + n₂, k₁ + k₂), unionC ⟦p.1⟧ ⟦p.2⟧⟩ : AnyClass) = ⟨(n, k), c⟩).card := by
  refine card_bij'
    (fun Γ hΓ => (restrictL Γ A B (split_props hΓ).1 (split_props hΓ).2 hA hk,
      restrictL Γ Aᶜ Bᶜ (fun x => by rw [mem_compl, mem_compl, (split_props hΓ).1])
        (closed_compl (split_props hΓ).2) hA' hk'))
    (fun p _ => glue A B hA hk hA' hk' p.1 p.2) ?_ ?_ ?_ ?_
  · intro Γ hΓ
    have hAB := (split_props hΓ).1
    have hBc := (mem_filter.1 (mem_filter.1 hΓ).2.1).2
    have hc := (mem_filter.1 hΓ).1
    have hm := (mem_filter.1 hΓ).2.2.2
    have hgl := glue_restrictL Γ hAB hBc.1 hA hk hA' hk'
    have hconn : IsConnected (restrictL Γ A B hAB hBc.1 hA hk) := by
      have h := (connOn_glue_iff (A := A) (B := B) (hA := hA) (hk := hk) (hA' := hA') (hk' := hk')
        (Γ₁ := restrictL Γ A B hAB hBc.1 hA hk)
        (Γ₂ := restrictL Γ Aᶜ Bᶜ (fun x => by rw [mem_compl, mem_compl, hAB]) (closed_compl hBc.1) hA' hk')).1
      rw [hgl] at h
      exact h hBc.2
    rw [mem_filter]
    refine ⟨mem_univ _, hconn, ?_, ?_⟩
    · have := ncomp_glue hA hk hA' hk' (Γ₂ := restrictL Γ Aᶜ Bᶜ (fun x => by rw [mem_compl, mem_compl, hAB])
        (closed_compl hBc.1) hA' hk') hconn
      rw [hgl, hm] at this
      exact (Nat.add_right_cancel this).symm
    · rw [← anyClass_glue hA hk hA' hk', hgl, mem_labOf.1 hc]
  · rintro ⟨Γ₁, Γ₂⟩ hp
    rw [mem_filter] at hp
    obtain ⟨-, hconn, hm, hcl⟩ := hp
    rw [mem_filter]
    refine ⟨?_, ?_, fun h => (glue_att_mem h).symm, ?_⟩
    · rw [mem_labOf]
      have := (anyClass_glue hA hk hA' hk' Γ₁ Γ₂).trans hcl
      exact eq_of_heq (Sigma.mk.inj this).2
    · rw [comps, mem_filter]
      exact ⟨mem_univ _, closed_glue, connOn_glue_iff.2 hconn⟩
    · rw [ncomp_glue hA hk hA' hk' hconn, hm]
  · intro Γ hΓ
    exact glue_restrictL Γ (split_props hΓ).1 (split_props hΓ).2 hA hk hA' hk'
  · rintro ⟨Γ₁, Γ₂⟩ -
    exact Prod.ext restrictL_glue restrictL_glue_compl

end Split


section Count

open Classical

/-- The number of pairs, grouped by the classes of the parts. -/
theorem card_pairs_eq_sum {n₁ k₁ n₂ k₂ : ℕ} (c : GClass n k) (m : ℕ) :
    ((univ : Finset (LGraph n₁ k₁ × LGraph n₂ k₂)).filter fun p =>
        IsConnected p.1 ∧ ncomp p.2 = m ∧
          (⟨(n₁ + n₂, k₁ + k₂), unionC ⟦p.1⟧ ⟦p.2⟧⟩ : AnyClass) = ⟨(n, k), c⟩).card =
      ∑ c₁ : GClass n₁ k₁, ∑ c₂ : GClass n₂ k₂,
        if IsConnected c₁.out ∧ ncomp c₂.out = m ∧
            (⟨(n₁ + n₂, k₁ + k₂), unionC c₁ c₂⟩ : AnyClass) = ⟨(n, k), c⟩ then lab c₁ * lab c₂ else 0 := by
  rw [card_eq_sum_card_fiberwise (f := fun p : LGraph n₁ k₁ × LGraph n₂ k₂ => ((⟦p.1⟧ : GClass n₁ k₁),
    (⟦p.2⟧ : GClass n₂ k₂))) (t := univ) (fun _ _ => mem_univ _), ← univ_product_univ, sum_product]
  refine sum_congr rfl fun c₁ _ => sum_congr rfl fun c₂ _ => ?_
  split_ifs with hcond
  · rw [lab, lab, ← card_product]
    congr 1
    ext ⟨Γ₁, Γ₂⟩
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_labOf, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨?_, ?_, ?_⟩, h1, h2⟩
      · rw [isConnected_of_mem_labOf (mem_labOf.2 h1)]; exact hcond.1
      · rw [ncomp_of_mem_labOf (mem_labOf.2 h2)]; exact hcond.2.1
      · rw [h1, h2]; exact hcond.2.2
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro ⟨Γ₁, Γ₂⟩ hmem hf
    rw [mem_filter] at hmem
    obtain ⟨-, hconn, hm, hcl⟩ := hmem
    simp only [Prod.mk.injEq] at hf
    obtain ⟨h1, h2⟩ := hf
    apply hcond
    refine ⟨?_, ?_, ?_⟩
    · rw [← isConnected_of_mem_labOf (mem_labOf.2 h1)]; exact hconn
    · rw [← ncomp_of_mem_labOf (mem_labOf.2 h2)]; exact hm
    · rw [← h1, ← h2]; exact hcl

/-- The components of a graph are at most its vertices. -/
lemma ncomp_le (Γ : LGraph n k) : ncomp Γ ≤ k := by
  have hne : ∀ S ∈ comps Γ, S.Nonempty := fun S hS => (mem_filter.1 hS).2.2.1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : comps Γ = ∅ := eq_empty_of_forall_notMem fun S hS => by
      obtain ⟨v, -⟩ := hne S hS; exact v.elim0
    simp [ncomp, h0]
  calc ncomp Γ ≤ (univ : Finset (Fin k)).card := by
        refine card_le_card_of_injOn (fun S => if h : S.Nonempty then S.min' h else ⟨0, hk⟩)
          (fun _ _ => mem_univ _) ?_
        intro S hS T hT hST
        simp only [dif_pos (hne S hS), dif_pos (hne T hT)] at hST
        have h1 : S.min' (hne S hS) ∈ S := min'_mem _ _
        have h2 : S.min' (hne S hS) ∈ T := by rw [hST]; exact min'_mem _ _
        exact (existsUnique_comp Γ _).unique ⟨hS, h1⟩ ⟨hT, h2⟩
    _ = k := by simp

end Count


section DoubleCount

open Classical

/-- **Double counting the pairs (graph, component).** -/
lemma card_mul_ncomp (c : GClass n k) (m : ℕ) :
    (m + 1) * ((labOf c).filter fun Γ => ncomp Γ = m + 1).card =
      ∑ B : Finset (Fin k), ∑ A : Finset (Fin n),
        ((labOf c).filter fun Γ => B ∈ comps Γ ∧ (∀ h, h ∈ A ↔ Γ.att h ∈ B) ∧ ncomp Γ = m + 1).card := by
  have hAeq : ∀ (Γ : LGraph n k) B (A : Finset (Fin n)), (∀ h, h ∈ A ↔ Γ.att h ∈ B) ↔ A = hedges Γ B :=
    fun Γ B A => ⟨fun h => by ext x; rw [h x, mem_hedges], by rintro rfl x; exact mem_hedges⟩
  have key : ∀ Γ ∈ labOf c, (∑ B : Finset (Fin k), ∑ A : Finset (Fin n),
      if B ∈ comps Γ ∧ (∀ h, h ∈ A ↔ Γ.att h ∈ B) ∧ ncomp Γ = m + 1 then (1 : ℕ) else 0) =
        if ncomp Γ = m + 1 then m + 1 else 0 := by
    intro Γ _
    simp_rw [hAeq Γ]
    split_ifs with hm
    · simp only [hm, and_true, eq_self_iff_true]
      have : ∀ B : Finset (Fin k), (∑ A : Finset (Fin n), if B ∈ comps Γ ∧ A = hedges Γ B then (1 : ℕ) else 0) =
          if B ∈ comps Γ then 1 else 0 := fun B => by
        by_cases hB : B ∈ comps Γ
        · simp [hB]
        · simp [hB]
      simp_rw [this]
      rw [sum_boole, ← hm, ncomp]
      simp
    · simp [hm]
  simp_rw [card_eq_sum_ones, sum_filter]
  calc (m + 1) * ∑ Γ ∈ labOf c, (if ncomp Γ = m + 1 then (1 : ℕ) else 0)
      = ∑ Γ ∈ labOf c, (if ncomp Γ = m + 1 then m + 1 else 0) := by
        rw [mul_sum]; exact sum_congr rfl fun Γ _ => by split_ifs <;> simp
    _ = ∑ Γ ∈ labOf c, ∑ B : Finset (Fin k), ∑ A : Finset (Fin n),
          (if B ∈ comps Γ ∧ (∀ h, h ∈ A ↔ Γ.att h ∈ B) ∧ ncomp Γ = m + 1 then (1 : ℕ) else 0) :=
        (sum_congr rfl key).symm
    _ = _ := by
        rw [sum_comm]
        exact sum_congr rfl fun B _ => sum_comm

end DoubleCount


section Exp

open Classical

lemma card_filter_ncomp (c : GClass n k) (j : ℕ) :
    ((labOf c).filter fun Γ => ncomp Γ = j).card = if ncomp c.out = j then lab c else 0 := by
  split_ifs with h
  · rw [lab]; congr 1
    exact filter_true_of_mem fun Γ hΓ => (ncomp_of_mem_labOf hΓ).trans h
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro Γ hΓ hj
    exact h ((ncomp_of_mem_labOf hΓ).symm.trans hj)

/-- The number of splits of a class into a connected part with `j` half-edges and `l` vertices and a part with `m`
components. -/
def splitCount (c : GClass n k) (m j l : ℕ) : ℕ :=
  ∑ c₁ : GClass j l, ∑ c₂ : GClass (n - j) (k - l),
    if IsConnected c₁.out ∧ ncomp c₂.out = m ∧
        (⟨(j + (n - j), l + (k - l)), unionC c₁ c₂⟩ : AnyClass) = ⟨(n, k), c⟩ then lab c₁ * lab c₂ else 0

lemma card_split_eq (c : GClass n k) (m : ℕ) (A : Finset (Fin n)) (B : Finset (Fin k)) :
    ((labOf c).filter fun Γ => B ∈ comps Γ ∧ (∀ h, h ∈ A ↔ Γ.att h ∈ B) ∧ ncomp Γ = m + 1).card =
      splitCount c m A.card B.card := by
  rw [card_split (A := A) (B := B) (n₂ := n - A.card) (k₂ := k - B.card) rfl rfl (by rw [card_compl, Fintype.card_fin])
    (by rw [card_compl, Fintype.card_fin]) c m, card_pairs_eq_sum]
  rfl

/-- **The counting identity**: `(m + 1) · lab c · [m + 1 components] = Σ_{j, l} C(n, j) C(k, l) · splits`. -/
lemma count_identity (c : GClass n k) (m : ℕ) :
    (m + 1) * (if ncomp c.out = m + 1 then lab c else 0) =
      ∑ j ∈ range (n + 1), ∑ l ∈ range (k + 1), n.choose j * (k.choose l * splitCount c m j l) := by
  have hpow : ∀ {r : ℕ} (g : ℕ → ℕ), ∑ S : Finset (Fin r), g S.card = ∑ j ∈ range (r + 1), r.choose j * g j :=
    fun g => by
      rw [← powerset_univ, sum_powerset_apply_card, card_univ, Fintype.card_fin]
      exact Finset.sum_congr rfl fun j _ => smul_eq_mul _ _
  rw [← card_filter_ncomp, card_mul_ncomp]
  simp_rw [card_split_eq]
  have h1 : ∀ B : Finset (Fin k), ∑ A : Finset (Fin n), splitCount c m A.card B.card =
      ∑ j ∈ range (n + 1), n.choose j * splitCount c m j B.card := fun B =>
    hpow (fun j => splitCount c m j B.card)
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact congrArg _ (hpow (fun l => splitCount c m j l))

/-- `LGraph 0 0` has exactly one element. -/
instance : Unique (LGraph 0 0) where
  default := ⟨Fin.elim0, Fin.elim0, fun x => x.elim0⟩
  uniq Γ := LGraph.ext (funext fun x => x.elim0) (funext fun x => x.elim0)

lemma pow_Xc_zero (c : GClass n k) :
    pow Xc 0 ⟨(n, k), c⟩ = (if ncomp c.out = 0 then ((Nat.factorial 0 : ℕ) * lab c : ℚ) else 0) /
      (n.factorial * k.factorial) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : n = 0 := by
      by_contra hn
      exact (c.out.att ⟨0, Nat.pos_of_ne_zero hn⟩).elim0
    have hcomp : ncomp c.out = 0 := Nat.le_zero.1 (ncomp_le _)
    have hlab : lab c = 1 := by
      rw [lab]
      have : labOf c = univ := eq_univ_of_forall fun Γ => mem_labOf.2 (by
        rw [Subsingleton.elim Γ c.out, Quotient.out_eq])
      rw [this, card_univ, Fintype.card_unique]
    simp [pow, one, hcomp, hlab]
  · have hne : ncomp c.out ≠ 0 := by
      obtain ⟨S, ⟨hS, -⟩, -⟩ := existsUnique_comp c.out ⟨0, hk⟩
      exact (card_pos.2 ⟨S, hS⟩).ne'
    have hgr : ((n, k) : ℕ × ℕ) ≠ (0, 0) := by intro h; simp at h; omega
    simp [pow, one, hne, hgr, hk.ne']

/-- **The powers of `X_c`**: `X_c^m (c) = [c has m components] · m! · lab c/(n! k!)`. -/
theorem pow_Xc_eq (m : ℕ) : ∀ {n k : ℕ} (c : GClass n k), pow Xc m ⟨(n, k), c⟩ =
    (if ncomp c.out = m then (m.factorial * lab c : ℚ) else 0) / (n.factorial * k.factorial) := by
  induction m with
  | zero => intro n k c; exact pow_Xc_zero c
  | succ m ih =>
    intro n k c
    have hterm : ∀ j ∈ range (n + 1), ∀ l ∈ range (k + 1),
        (∑ c₁ : GClass j l, ∑ c₂ : GClass (n - j) (k - l),
          if (⟨(j + (n - j), l + (k - l)), unionC c₁ c₂⟩ : AnyClass) = ⟨(n, k), c⟩ then
            Xc ⟨(j, l), c₁⟩ * pow Xc m ⟨(n - j, k - l), c₂⟩ else 0) =
          (m.factorial : ℚ) * splitCount c m j l /
            (j.factorial * l.factorial * ((n - j).factorial * (k - l).factorial)) := by
      intro j _ l _
      rw [splitCount, Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun c₁ _ => ?_
      rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun c₂ _ => ?_
      rw [Xc_eq_lab, ih]
      have hj : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hl : (l.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hj' : ((n - j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hl' : ((k - l).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      by_cases h1 : (⟨(j + (n - j), l + (k - l)), unionC c₁ c₂⟩ : AnyClass) = ⟨(n, k), c⟩
      · by_cases h2 : IsConnected c₁.out
        · by_cases h3 : ncomp c₂.out = m
          · rw [if_pos h1, if_pos h2, if_pos h3, if_pos ⟨h2, h3, h1⟩]
            push_cast
            field_simp
          · have hn : ¬(IsConnected c₁.out ∧ ncomp c₂.out = m ∧
                (⟨(j + (n - j), l + (k - l)), unionC c₁ c₂⟩ : AnyClass) = ⟨(n, k), c⟩) := fun h => h3 h.2.1
            rw [if_pos h1, if_neg h3, if_neg hn]
            simp
        · have hn : ¬(IsConnected c₁.out ∧ ncomp c₂.out = m ∧
              (⟨(j + (n - j), l + (k - l)), unionC c₁ c₂⟩ : AnyClass) = ⟨(n, k), c⟩) := fun h => h2 h.1
          rw [if_pos h1, if_neg h2, if_neg hn]
          simp
      · have hn : ¬(IsConnected c₁.out ∧ ncomp c₂.out = m ∧
            (⟨(j + (n - j), l + (k - l)), unionC c₁ c₂⟩ : AnyClass) = ⟨(n, k), c⟩) := fun h => h1 h.2.2
        rw [if_neg h1, if_neg hn]
        simp
    have hstep : pow Xc (m + 1) ⟨(n, k), c⟩ =
        ∑ j ∈ range (n + 1), ∑ l ∈ range (k + 1), (m.factorial : ℚ) * splitCount c m j l /
          (j.factorial * l.factorial * ((n - j).factorial * (k - l).factorial)) := by
      show mul Xc (pow Xc m) ⟨(n, k), c⟩ = _
      simp only [mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      exact Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => hterm j hj l hl
    rw [hstep]
    have hid := count_identity c m
    have hidQ : ((m + 1 : ℕ) : ℚ) * (if ncomp c.out = m + 1 then (lab c : ℚ) else 0) =
        ∑ j ∈ range (n + 1), ∑ l ∈ range (k + 1),
          (n.choose j : ℚ) * ((k.choose l : ℚ) * (splitCount c m j l : ℚ)) := by
      have := congrArg (fun x : ℕ => (x : ℚ)) hid
      simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] at this
      exact this
    have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hrhs : (if ncomp c.out = m + 1 then ((m + 1).factorial * lab c : ℚ) else 0) /
        (n.factorial * k.factorial) =
        (m.factorial : ℚ) * (((m + 1 : ℕ) : ℚ) * (if ncomp c.out = m + 1 then (lab c : ℚ) else 0)) /
          (n.factorial * k.factorial) := by
      congr 1
      split_ifs <;> push_cast [Nat.factorial_succ] <;> ring
    rw [hrhs, hidQ, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hlk : l ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hl)
    have hcn : (n.choose j : ℚ) * j.factorial * (n - j).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
    have hck : (k.choose l : ℚ) * l.factorial * (k - l).factorial = k.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hlk
    rw [← hcn, ← hck]
    have hj : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hl : (l.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hj' : ((n - j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hl' : ((k - l).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hcj : (n.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjn).ne'
    have hcl : (k.choose l : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hlk).ne'
    field_simp

/-- **Borinsky's Theorem 2.4.1, `X = e^{X_c}`**, in the algebra of graphs: at every isomorphism class of graphs,
the coefficient of `e^{X_c} = Σ_m X_c^m/m!` equals that of `X = Σ_Γ Γ/|Aut Γ|`. -/
theorem expXc_eq_X (c : AnyClass) : expXc c = X c := by
  obtain ⟨⟨n, k⟩, c⟩ := c
  rw [expXc, X_eq_lab]
  simp only
  simp_rw [pow_Xc_eq]
  rw [Finset.sum_eq_single (ncomp c.out)]
  · rw [if_pos rfl]
    have hm : ((ncomp c.out).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    field_simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_div, zero_div]
  · intro h
    exact absurd (mem_range.2 (Nat.lt_succ_of_le (ncomp_le _))) h

end Exp

end Lightlike.FieldTheory.GraphAlg
