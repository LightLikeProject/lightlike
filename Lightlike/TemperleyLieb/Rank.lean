import Mathlib
import Lightlike.TemperleyLieb.Window

/-!
# Coefficients of `e_j v` and the sorted-coordinates bound

`coeff_modelE_FT`, `coeff_modelE_TF`: the coefficient of `e_j v` at a sequence with bits `(0,1)` (resp. `(1,0)`) at
`j, j+1` in terms of `v`.  Consequently, if `e_j v = 0` then `v σ = q⁻¹ v σ'` for `σ` with bits `(1,0)` at `j, j+1`
and `σ'` the sequence with the bits swapped.
-/

namespace Lightlike.TemperleyLieb

open Finsupp
open scoped Classical

variable {k : Type*} [Field k]

/-- `e_j v` as a sum over the support. -/
lemma modelE_apply_eq_sum (q : kˣ) (j : ℕ) (v : ModelSpace k) :
    modelE q j v = v.sum (fun σ c => c • eBasis q j σ) := by
  conv_lhs => rw [← Finsupp.sum_single v]
  rw [map_finsuppSum]
  simp [modelE_single]

/-- The coefficient of `eBasis σ` at `τ`. -/
lemma eBasis_apply (q : kˣ) (j : ℕ) (σ τ : ℕ → Bool) :
    eBasis q j σ τ =
      if σ j = true ∧ σ (j + 1) = false then
        (if τ = set2 σ j false true then 1 else 0) - (q : k) * (if τ = σ then 1 else 0)
      else if σ j = false ∧ σ (j + 1) = true then
        (if τ = set2 σ j true false then 1 else 0) - ((q⁻¹ : kˣ) : k) * (if τ = σ then 1 else 0)
      else 0 := by
  unfold eBasis
  rcases h0 : σ j with _ | _ <;> rcases h1 : σ (j + 1) with _ | _ <;>
    simp [Finsupp.single_apply, eq_comm]

/-- If `eBasis ρ` has a nonzero coefficient at `σ` with bits `(1,0)` at `j, j+1`, then `ρ ∈ {σ, σ'}`. -/
lemma eBasis_ne_zero_cases (q : kˣ) {j : ℕ} {ρ σ : ℕ → Bool} (h0 : σ j = true) (h1 : σ (j + 1) = false)
    (h : eBasis q j ρ σ ≠ (0 : k)) : ρ = σ ∨ ρ = set2 σ j false true := by
  rw [eBasis_apply] at h
  by_cases hρ : ρ j = true ∧ ρ (j + 1) = false
  · rw [if_pos hρ] at h
    by_cases hσ : σ = set2 ρ j false true
    · exfalso
      have : σ j = false := by rw [hσ]; simp [set2]
      rw [h0] at this; exact Bool.noConfusion this
    · by_cases hσ2 : σ = ρ
      · left; exact hσ2.symm
      · exfalso; apply h; simp [hσ, hσ2]
  · rw [if_neg hρ] at h
    by_cases hρ2 : ρ j = false ∧ ρ (j + 1) = true
    · rw [if_pos hρ2] at h
      by_cases hσ : σ = set2 ρ j true false
      · right
        rw [hσ]
        funext n
        simp only [set2, Function.update_apply]
        split_ifs with a b <;> first | (subst_vars; simp_all) | rfl | (simp_all)
      · by_cases hσ2 : σ = ρ
        · exfalso; rw [← hσ2] at hρ2; rw [h0] at hρ2; exact Bool.noConfusion hρ2.1
        · exfalso; apply h; simp [hσ, hσ2]
    · rw [if_neg hρ2] at h; exact absurd rfl h

/-- The coefficient of `e_j v` at a sequence `σ` with bits `(1,0)` at `j, j+1`. -/
lemma modelE_coeff_TF (q : kˣ) {j : ℕ} (v : ModelSpace k) {σ : ℕ → Bool} (h0 : σ j = true)
    (h1 : σ (j + 1) = false) :
    (modelE q j v) σ = v (set2 σ j false true) - (q : k) * v σ := by
  have hne : set2 σ j false true ≠ σ := by
    intro h; have := congrFun h j; simp [set2] at this; rw [h0] at this; exact Bool.noConfusion this
  rw [modelE_apply_eq_sum, Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_of_support_subset v (s := v.support ∪ {σ, set2 σ j false true}) Finset.subset_union_left]
  · have hsub : ∑ x ∈ ({σ, set2 σ j false true} : Finset (ℕ → Bool)), v x * (eBasis q j x) σ =
        ∑ x ∈ v.support ∪ {σ, set2 σ j false true}, v x * (eBasis q j x) σ := by
      refine Finset.sum_subset Finset.subset_union_right ?_
      intro ρ _ hρ
      have : eBasis q j ρ σ = 0 := by
        by_contra hc
        rcases eBasis_ne_zero_cases q h0 h1 hc with h | h
        · exact hρ (by simp [h])
        · exact hρ (by simp [h])
      simp [this]
    rw [← hsub, Finset.sum_pair hne.symm]
    have e1 : eBasis q j σ σ = -(q : k) := by
      rw [eBasis_apply]; simp [h0, h1, hne.symm]
    have e2 : eBasis q j (set2 σ j false true) σ = 1 := by
      rw [eBasis_apply]
      have a0 : set2 σ j false true j = false := by simp [set2]
      have a1 : set2 σ j false true (j + 1) = true := by simp [set2]
      have a2 : set2 (set2 σ j false true) j true false = σ := by
        rw [set2_set2, ← set2_self σ j, h0, h1, set2_set2]
      simp [a0, a1, a2, hne.symm]
    rw [e1, e2]; ring
  · intro ρ _; simp

/-- If `e_j v = 0` then `v σ = q⁻¹ v σ'` for `σ` with bits `(1,0)` at `j, j+1`. -/
lemma kernel_relation (q : kˣ) {j : ℕ} {v : ModelSpace k} (hv : modelE q j v = 0) {σ : ℕ → Bool}
    (h0 : σ j = true) (h1 : σ (j + 1) = false) :
    v σ = ((q⁻¹ : kˣ) : k) * v (set2 σ j false true) := by
  have h := modelE_coeff_TF q v h0 h1
  rw [hv] at h
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h
  have hq : (q : k) * ((q⁻¹ : kˣ) : k) = 1 := by simp
  linear_combination ((q⁻¹ : kˣ) : k) * h - (v σ) * hq

/-- The sum of the positions of the ones below `N`. -/
def posSum (N : ℕ) (σ : ℕ → Bool) : ℕ := ∑ p ∈ Finset.range N, if σ p then p else 0

/-- Moving a one from `j` to `j + 1` increases the position sum by one. -/
lemma posSum_swap {N j : ℕ} (hj : j + 2 ≤ N) {σ : ℕ → Bool} (h0 : σ j = true) (h1 : σ (j + 1) = false) :
    posSum N (set2 σ j false true) = posSum N σ + 1 := by
  unfold posSum
  have hjN : j + 1 < N := by omega
  have e : ∀ f : ℕ → ℕ, ∑ p ∈ Finset.range N, f p =
      ∑ p ∈ (Finset.range N).erase j |>.erase (j + 1), f p + f j + f (j + 1) := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : j < N))]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hjN⟩ : j + 1 ∈ (Finset.range N).erase j)]
    ring
  rw [e, e (fun p => if σ p then p else 0)]
  have hsame : ∑ p ∈ ((Finset.range N).erase j).erase (j + 1),
      (if set2 σ j false true p then p else 0) = ∑ p ∈ ((Finset.range N).erase j).erase (j + 1),
      (if σ p then p else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : p ≠ j + 1 := (Finset.mem_erase.mp hp).1
    have hp2 : p ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    simp [set2, Function.update_apply, hp1, hp2]
  rw [hsame]
  simp [set2, h0, h1]
  ring

/-- Sorted with respect to the generators `J`: no `(1,0)` pattern at `j, j+1` for `j ∈ J`. -/
def SortedAt (J : ℕ → Prop) (σ : ℕ → Bool) : Prop := ∀ j, J j → ¬(σ j = true ∧ σ (j + 1) = false)

/-- **Sorted coordinates.** A vector in the common kernel of `e_j` (`j ∈ J`) vanishes on the window as soon as it
vanishes on the sorted sequences. -/
theorem zero_of_sorted (q : kˣ) {N : ℕ} {J : ℕ → Prop} (hJ : ∀ j, J j → j + 2 ≤ N)
    {v : ModelSpace k} (hv : ∀ j, J j → modelE q j v = 0)
    (hs : ∀ σ ∈ tailZero N, SortedAt J σ → v σ = 0) : ∀ σ ∈ tailZero N, v σ = 0 := by
  have hbound : ∀ σ ∈ tailZero N, posSum N σ ≤ N * N := by
    intro σ _
    unfold posSum
    calc ∑ p ∈ Finset.range N, (if σ p then p else 0) ≤ ∑ p ∈ Finset.range N, N := by
          refine Finset.sum_le_sum fun p hp => ?_
          split_ifs
          · exact (Finset.mem_range.mp hp).le
          · exact Nat.zero_le _
      _ = N * N := by simp [mul_comm]
  have key : ∀ m, ∀ σ ∈ tailZero N, N * N - posSum N σ = m → v σ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro σ hσ hm
      by_cases hsort : SortedAt J σ
      · exact hs σ hσ hsort
      · simp only [SortedAt, not_forall, not_not] at hsort
        obtain ⟨j, hjJ, h0, h1⟩ := hsort
        have hj := hJ j hjJ
        have hσ' : set2 σ j false true ∈ tailZero N := set2_mem_tailZero hj hσ _ _
        have hpos := posSum_swap hj h0 h1
        have hb := hbound _ hσ'
        have := ih (N * N - posSum N (set2 σ j false true)) (by omega) _ hσ' rfl
        rw [kernel_relation q (hv j hjJ) h0 h1, this, mul_zero]
  intro σ hσ
  exact key _ σ hσ rfl

/-- The number of ones of `σ` in the block `[s, s + L)`. -/
def onesIn (s L : ℕ) (σ : ℕ → Bool) : ℕ := ((Finset.Ico s (s + L)).filter (fun p => σ p = true)).card

/-- A monotone block (`1` stays `1`) has ones on all of `[p, s+L)` as soon as `σ p = 1`. -/
lemma block_mono (s L : ℕ) {σ : ℕ → Bool}
    (hm : ∀ p, s ≤ p → p + 1 < s + L → σ p = true → σ (p + 1) = true) {p : ℕ} (hp : s ≤ p)
    (hpL : p < s + L) (hσp : σ p = true) : ∀ r, p ≤ r → r < s + L → σ r = true := by
  intro r hpr hrL
  induction r, hpr using Nat.le_induction with
  | base => exact hσp
  | succ r hpr ih => exact hm r (by omega) (by omega) (ih (by omega))

/-- If `σ p = 1` and `τ p = 0` in monotone blocks then `σ` has more ones than `τ`. -/
lemma block_lt (s L : ℕ) {σ τ : ℕ → Bool}
    (hσ : ∀ p, s ≤ p → p + 1 < s + L → σ p = true → σ (p + 1) = true)
    (hτ : ∀ p, s ≤ p → p + 1 < s + L → τ p = true → τ (p + 1) = true) {p : ℕ} (hp : s ≤ p)
    (hpL : p < s + L) (h1 : σ p = true) (h0 : τ p = false) : onesIn s L τ < onesIn s L σ := by
  unfold onesIn
  have hall := block_mono s L hσ hp hpL h1
  have h_sub1 : Finset.Ico p (s + L) ⊆ (Finset.Ico s (s + L)).filter (fun r => σ r = true) := by
    intro r hr
    simp only [Finset.mem_Ico] at hr
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, hr.2⟩, hall r hr.1 hr.2⟩
  have h_sub2 : (Finset.Ico s (s + L)).filter (fun r => τ r = true) ⊆ Finset.Ico (p + 1) (s + L) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_Ico] at hr ⊢
    by_cases hrp : r ≤ p
    · exfalso
      have := block_mono s L hτ hr.1.1 hr.1.2 hr.2 p hrp hpL
      rw [h0] at this; exact Bool.noConfusion this
    · exact ⟨by omega, hr.1.2⟩
  have c1 := Finset.card_le_card h_sub1
  have c2 := Finset.card_le_card h_sub2
  simp only [Nat.card_Ico] at c1 c2
  omega

/-- A monotone (`1` stays `1`) block is determined by its number of ones. -/
lemma block_ext (s L : ℕ) {σ τ : ℕ → Bool}
    (hσ : ∀ p, s ≤ p → p + 1 < s + L → σ p = true → σ (p + 1) = true)
    (hτ : ∀ p, s ≤ p → p + 1 < s + L → τ p = true → τ (p + 1) = true)
    (hc : onesIn s L σ = onesIn s L τ) : ∀ p, s ≤ p → p < s + L → σ p = τ p := by
  intro p hp hpL
  rcases h1 : σ p with _ | _ <;> rcases h0 : τ p with _ | _
  · rfl
  · have := block_lt s L hτ hσ hp hpL h0 h1; omega
  · have := block_lt s L hσ hτ hp hpL h1 h0; omega
  · rfl

/-- The generators inside the two blocks `[0,a)` and `[a,a+b)`. -/
def Jab (a b : ℕ) (j : ℕ) : Prop := j + 2 ≤ a ∨ (a ≤ j ∧ j + 2 ≤ a + b)

/-- The sorted window sequences for the two blocks. -/
noncomputable def sortedSet (a b : ℕ) : Finset (ℕ → Bool) :=
  (tailZero_finite (a + b)).toFinset.filter (fun σ => SortedAt (Jab a b) σ)

/-- The number of sorted sequences is at most `(a+1)(b+1)`. -/
theorem card_sortedSet_le (a b : ℕ) : (sortedSet a b).card ≤ (a + 1) * (b + 1) := by
  have hinj : Set.InjOn (fun σ : ℕ → Bool => (onesIn 0 a σ, onesIn a b σ)) (sortedSet a b : Set (ℕ → Bool)) := by
    intro σ hσ τ hτ h
    simp only [sortedSet, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hσ hτ
    obtain ⟨hσw, hσs⟩ := hσ
    obtain ⟨hτw, hτs⟩ := hτ
    have h1 : onesIn 0 a σ = onesIn 0 a τ := (Prod.mk.inj h).1
    have h2 : onesIn a b σ = onesIn a b τ := (Prod.mk.inj h).2
    have m1 : ∀ {ρ : ℕ → Bool}, SortedAt (Jab a b) ρ →
        ∀ p, 0 ≤ p → p + 1 < 0 + a → ρ p = true → ρ (p + 1) = true := by
      intro ρ hρ p _ hp h
      by_contra hne
      have : ρ (p + 1) = false := by simpa using hne
      exact hρ p (Or.inl (by omega)) ⟨h, this⟩
    have m2 : ∀ {ρ : ℕ → Bool}, SortedAt (Jab a b) ρ →
        ∀ p, a ≤ p → p + 1 < a + b → ρ p = true → ρ (p + 1) = true := by
      intro ρ hρ p hp hpb h
      by_contra hne
      have : ρ (p + 1) = false := by simpa using hne
      exact hρ p (Or.inr ⟨hp, by omega⟩) ⟨h, this⟩
    have e1 := block_ext 0 a (m1 hσs) (m1 hτs) (by simpa [onesIn] using h1)
    have e2 := block_ext a b (m2 hσs) (m2 hτs) h2
    funext p
    by_cases hp : p < a
    · exact e1 p (Nat.zero_le _) (by omega)
    · by_cases hp2 : p < a + b
      · exact e2 p (by omega) (by omega)
      · rw [hσw p (by omega), hτw p (by omega)]
  have himg : (sortedSet a b).image (fun σ : ℕ → Bool => (onesIn 0 a σ, onesIn a b σ)) ⊆
      (Finset.range (a + 1)) ×ˢ (Finset.range (b + 1)) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨σ, _, rfl⟩ := hx
    simp only [Finset.mem_product, Finset.mem_range]
    constructor
    · unfold onesIn
      have := Finset.card_filter_le (Finset.Ico 0 (0 + a)) (fun p => σ p = true)
      rw [Nat.card_Ico] at this; omega
    · unfold onesIn
      have := Finset.card_filter_le (Finset.Ico a (a + b)) (fun p => σ p = true)
      rw [Nat.card_Ico] at this; omega
  calc (sortedSet a b).card = ((sortedSet a b).image _).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((Finset.range (a + 1)) ×ˢ (Finset.range (b + 1))).card := Finset.card_le_card himg
    _ = (a + 1) * (b + 1) := by simp

/-- **Rank bound (A)**: the common kernel of the block generators in the window has dimension at most
`(a+1)(b+1)`. -/
theorem finrank_kernel_le (q : kˣ) (a b : ℕ) (U : Submodule k (ModelSpace k)) (hU : U ≤ Win k (a + b))
    (hker : ∀ v ∈ U, ∀ j, Jab a b j → modelE q j v = 0) [FiniteDimensional k U] :
    Module.finrank k U ≤ (a + 1) * (b + 1) := by
  let Φ : U →ₗ[k] (↥(sortedSet a b) → k) :=
    { toFun := fun v σ => (v : ModelSpace k) (σ : ℕ → Bool)
      map_add' := fun v w => by funext σ; simp
      map_smul' := fun c v => by funext σ; simp }
  have hinj : Function.Injective Φ := by
    intro v w hvw
    have hvU := v.2
    have hwU := w.2
    set z : ModelSpace k := (v : ModelSpace k) - (w : ModelSpace k) with hzdef
    have hzker : ∀ j, Jab a b j → modelE q j z = 0 := by
      intro j hj
      rw [hzdef, map_sub, hker v hvU j hj, hker w hwU j hj, sub_zero]
    have hz : ∀ σ ∈ tailZero (a + b), z σ = 0 := by
      refine zero_of_sorted q (J := Jab a b) (fun j hj => by rcases hj with h | h <;> omega) hzker ?_
      intro σ hσ hs
      have hmem : σ ∈ sortedSet a b := by
        simp only [sortedSet, Finset.mem_filter, Set.Finite.mem_toFinset]
        exact ⟨hσ, hs⟩
      have := congrFun hvw ⟨σ, hmem⟩
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
      simp [hzdef, this]
    apply Subtype.ext
    ext σ
    by_cases hσ : σ ∈ tailZero (a + b)
    · have := hz σ hσ
      simp only [hzdef, Finsupp.coe_sub, Pi.sub_apply] at this
      exact sub_eq_zero.mp this
    · have h1 := (Finsupp.mem_supported' k (v : ModelSpace k)).mp (hU hvU) σ hσ
      have h2 := (Finsupp.mem_supported' k (w : ModelSpace k)).mp (hU hwU) σ hσ
      rw [h1, h2]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
  exact this.trans (card_sortedSet_le a b)

/-- If `eBasis ρ` has a nonzero coefficient at `σ` with bits `(0,1)` at `j, j+1`, then `ρ ∈ {σ, σ'}`. -/
lemma eBasis_ne_zero_cases_FT (q : kˣ) {j : ℕ} {ρ σ : ℕ → Bool} (h0 : σ j = false) (h1 : σ (j + 1) = true)
    (h : eBasis q j ρ σ ≠ (0 : k)) : ρ = σ ∨ ρ = set2 σ j true false := by
  rw [eBasis_apply] at h
  by_cases hρ : ρ j = true ∧ ρ (j + 1) = false
  · rw [if_pos hρ] at h
    by_cases hσ : σ = set2 ρ j false true
    · right
      rw [hσ]
      funext n
      simp only [set2, Function.update_apply]
      split_ifs with a b <;> first | (subst_vars; simp_all) | rfl | (simp_all)
    · by_cases hσ2 : σ = ρ
      · exfalso; rw [← hσ2] at hρ; rw [h0] at hρ; exact Bool.noConfusion hρ.1
      · exfalso; apply h; simp [hσ, hσ2]
  · rw [if_neg hρ] at h
    by_cases hρ2 : ρ j = false ∧ ρ (j + 1) = true
    · rw [if_pos hρ2] at h
      by_cases hσ : σ = set2 ρ j true false
      · exfalso
        have : σ j = true := by rw [hσ]; simp [set2]
        rw [h0] at this; exact Bool.noConfusion this
      · by_cases hσ2 : σ = ρ
        · left; exact hσ2.symm
        · exfalso; apply h; simp [hσ, hσ2]
    · rw [if_neg hρ2] at h; exact absurd rfl h

/-- The coefficient of `e_j v` at a sequence `σ` with bits `(0,1)` at `j, j+1`. -/
lemma modelE_coeff_FT (q : kˣ) {j : ℕ} (v : ModelSpace k) {σ : ℕ → Bool} (h0 : σ j = false)
    (h1 : σ (j + 1) = true) :
    (modelE q j v) σ = v (set2 σ j true false) - ((q⁻¹ : kˣ) : k) * v σ := by
  have hne : set2 σ j true false ≠ σ := by
    intro h; have := congrFun h j; simp [set2] at this; rw [h0] at this; exact Bool.noConfusion this
  rw [modelE_apply_eq_sum, Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_of_support_subset v (s := v.support ∪ {σ, set2 σ j true false}) Finset.subset_union_left]
  · have hsub : ∑ x ∈ ({σ, set2 σ j true false} : Finset (ℕ → Bool)), v x * (eBasis q j x) σ =
        ∑ x ∈ v.support ∪ {σ, set2 σ j true false}, v x * (eBasis q j x) σ := by
      refine Finset.sum_subset Finset.subset_union_right ?_
      intro ρ _ hρ
      have : eBasis q j ρ σ = 0 := by
        by_contra hc
        rcases eBasis_ne_zero_cases_FT q h0 h1 hc with h | h
        · exact hρ (by simp [h])
        · exact hρ (by simp [h])
      simp [this]
    rw [← hsub, Finset.sum_pair hne.symm]
    have e1 : eBasis q j σ σ = -((q⁻¹ : kˣ) : k) := by
      rw [eBasis_apply]; simp [h0, h1, hne.symm]
    have e2 : eBasis q j (set2 σ j true false) σ = 1 := by
      rw [eBasis_apply]
      have a0 : set2 σ j true false j = true := by simp [set2]
      have a1 : set2 σ j true false (j + 1) = false := by simp [set2]
      have a2 : set2 (set2 σ j true false) j false true = σ := by
        rw [set2_set2, ← set2_self σ j, h0, h1, set2_set2]
      simp [a0, a1, a2, hne.symm]
    rw [e1, e2]; ring
  · intro ρ _; simp

/-- `e_j v` vanishes at sequences with equal bits at `j, j+1`. -/
lemma modelE_coeff_eq (q : kˣ) {j : ℕ} (v : ModelSpace k) {σ : ℕ → Bool} (h : σ j = σ (j + 1)) :
    (modelE q j v) σ = 0 := by
  rw [modelE_apply_eq_sum, Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have : eBasis q j ρ σ = 0 := by
    rw [eBasis_apply]
    have hb : ∀ x y : Bool, σ = set2 ρ j x y → x ≠ y → False := by
      intro x y hσ hxy
      have e0 : σ j = x := by rw [hσ]; simp [set2]
      have e1 : σ (j + 1) = y := by rw [hσ]; simp [set2]
      rw [e0, e1] at h
      exact hxy h
    have hc : σ = ρ → ρ j ≠ ρ (j + 1) → False := by
      intro hσ hne
      rw [hσ] at h; exact hne h
    rcases hρ0 : ρ j with _ | _ <;> rcases hρ1 : ρ (j + 1) with _ | _ <;> simp only []
    · simp
    · by_cases h1 : σ = set2 ρ j true false
      · exact absurd (hb _ _ h1 (by simp)) id
      · by_cases h2 : σ = ρ
        · exact absurd (hc h2 (by simp [hρ0, hρ1])) id
        · simp [h1, h2]
    · by_cases h1 : σ = set2 ρ j false true
      · exact absurd (hb _ _ h1 (by simp)) id
      · by_cases h2 : σ = ρ
        · exact absurd (hc h2 (by simp [hρ0, hρ1])) id
        · simp [h1, h2]
    · simp
  show v ρ * _ = 0
  rw [this, mul_zero]

/-- A weighted count of the ones below `N`. -/
def onesSum (N : ℕ) (g : ℕ → ℕ) (σ : ℕ → Bool) : ℕ := ∑ p ∈ Finset.range N, if σ p then g p else 0

/-- Moving a one from `j` to `j+1`: `onesSum` of the swapped sequence plus `g j` equals `onesSum` plus `g (j+1)`. -/
lemma onesSum_swap {N j : ℕ} (hj : j + 2 ≤ N) (g : ℕ → ℕ) {σ : ℕ → Bool} (h0 : σ j = true)
    (h1 : σ (j + 1) = false) :
    onesSum N g (set2 σ j false true) + g j = onesSum N g σ + g (j + 1) := by
  unfold onesSum
  have hjN : j + 1 < N := by omega
  have e : ∀ f : ℕ → ℕ, ∑ p ∈ Finset.range N, f p =
      ∑ p ∈ (Finset.range N).erase j |>.erase (j + 1), f p + f j + f (j + 1) := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : j < N))]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hjN⟩ : j + 1 ∈ (Finset.range N).erase j)]
    ring
  rw [e, e (fun p => if σ p then g p else 0)]
  have hsame : ∑ p ∈ ((Finset.range N).erase j).erase (j + 1),
      (if set2 σ j false true p then g p else 0) = ∑ p ∈ ((Finset.range N).erase j).erase (j + 1),
      (if σ p then g p else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : p ≠ j + 1 := (Finset.mem_erase.mp hp).1
    have hp2 : p ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hp).2).1
    simp [set2, Function.update_apply, hp1, hp2]
  rw [hsame]
  simp [set2, h0, h1]
  ring

/-- The number of ones below `c`. -/
def wtCount (c : ℕ) (σ : ℕ → Bool) : ℕ := onesSum c (fun _ => 1) σ

/-- A swap `(1,0) → (0,1)` keeps the number of ones. -/
lemma wtCount_swap {c j : ℕ} (hj : j + 2 ≤ c) {σ : ℕ → Bool} (h0 : σ j = true) (h1 : σ (j + 1) = false) :
    wtCount c (set2 σ j false true) = wtCount c σ := by
  have := onesSum_swap hj (fun _ => 1) h0 h1
  simp only [wtCount]; omega

/-- The window sequences with `m` ones below `c`. -/
noncomputable def dickeSet (c m : ℕ) : Finset (ℕ → Bool) :=
  (tailZero_finite c).toFinset.filter (fun σ => wtCount c σ = m)

/-- The `q`-symmetric (Dicke) vector of weight `m` on `c` strands: `Σ q^{pos σ} |σ⟩`. -/
noncomputable def dicke (q : kˣ) (c m : ℕ) : ModelSpace k :=
  ∑ σ ∈ dickeSet c m, single σ ((q : k) ^ posSum c σ)

/-- The coefficients of the Dicke vector. -/
lemma dicke_apply (q : kˣ) (c m : ℕ) (τ : ℕ → Bool) :
    (dicke q c m : ModelSpace k) τ = if τ ∈ dickeSet c m then (q : k) ^ posSum c τ else 0 := by
  unfold dicke
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']


/-- Membership in the Dicke set. -/
lemma mem_dickeSet {c m : ℕ} {σ : ℕ → Bool} : σ ∈ dickeSet c m ↔ σ ∈ tailZero c ∧ wtCount c σ = m := by
  simp [dickeSet]

/-- Swapping the bits at `j, j+1 < c` preserves membership in the Dicke set. -/
lemma mem_dickeSet_swap {c m j : ℕ} (hj : j + 2 ≤ c) {σ : ℕ → Bool} (h0 : σ j = true) (h1 : σ (j + 1) = false) :
    set2 σ j false true ∈ dickeSet c m ↔ σ ∈ dickeSet c m := by
  rw [mem_dickeSet, mem_dickeSet]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨?_, by rw [← wtCount_swap hj h0 h1]; exact hb⟩
    intro n hn
    have := ha n hn
    simp only [set2, Function.update_apply] at this
    split_ifs at this <;> first | exact this | omega
  · rintro ⟨ha, hb⟩
    exact ⟨set2_mem_tailZero hj ha _ _, by rw [wtCount_swap hj h0 h1]; exact hb⟩

/-- **The Dicke vector is killed by `e_j`**, `j + 2 ≤ c`. -/
theorem modelE_dicke (q : kˣ) {c m j : ℕ} (hj : j + 2 ≤ c) : modelE q j (dicke q c m : ModelSpace k) = 0 := by
  have hq : (q : k) ≠ 0 := q.ne_zero
  ext τ
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  rcases h0 : τ j with _ | _ <;> rcases h1 : τ (j + 1) with _ | _
  · exact modelE_coeff_eq q _ (by rw [h0, h1])
  · -- bits (0,1): `τ''` has bits (1,0) and swapping it gives `τ`
    rw [modelE_coeff_FT q _ h0 h1, dicke_apply, dicke_apply]
    set τ' := set2 τ j true false with hτ'
    have hτ'0 : τ' j = true := by simp [hτ', set2]
    have hτ'1 : τ' (j + 1) = false := by simp [hτ', set2]
    have hback : set2 τ' j false true = τ := by
      rw [hτ', set2_set2, ← set2_self τ j, h0, h1, set2_set2]
    have hmem := mem_dickeSet_swap (c := c) (m := m) hj hτ'0 hτ'1
    rw [hback] at hmem
    have hpos : posSum c τ = posSum c τ' + 1 := by
      have := posSum_swap hj hτ'0 hτ'1
      rwa [hback] at this
    by_cases hτ : τ ∈ dickeSet c m
    · have hτ2 : τ' ∈ dickeSet c m := hmem.mp hτ
      rw [if_pos hτ, if_pos hτ2, hpos, pow_succ]
      have : ((q⁻¹ : kˣ) : k) * (q : k) = 1 := by simp
      linear_combination (-((q : k) ^ posSum c τ')) * this
    · have hτ2 : τ' ∉ dickeSet c m := fun h => hτ (hmem.mpr h)
      rw [if_neg hτ, if_neg hτ2]; simp
  · -- bits (1,0)
    rw [modelE_coeff_TF q _ h0 h1, dicke_apply, dicke_apply]
    have hmem := mem_dickeSet_swap (c := c) (m := m) hj h0 h1
    have hpos := posSum_swap hj h0 h1
    by_cases hτ : τ ∈ dickeSet c m
    · have hτ2 : set2 τ j false true ∈ dickeSet c m := hmem.mpr hτ
      rw [if_pos hτ, if_pos hτ2, hpos, pow_succ]
      ring
    · have hτ2 : set2 τ j false true ∉ dickeSet c m := fun h => hτ (hmem.mp h)
      rw [if_neg hτ, if_neg hτ2]; simp
  · exact modelE_coeff_eq q _ (by rw [h0, h1])

/-- The canonical sequence with `m` ones in front. -/
def frontOnes (m : ℕ) : ℕ → Bool := fun p => decide (p < m)

lemma frontOnes_mem {c m : ℕ} (h : m ≤ c) : frontOnes m ∈ tailZero c := by
  intro j hj; simp [frontOnes]; omega

lemma wtCount_frontOnes {c m : ℕ} (h : m ≤ c) : wtCount c (frontOnes m) = m := by
  unfold wtCount onesSum frontOnes
  have h2 : ∀ p : ℕ, (if decide (p < m) = true then 1 else 0) = (if p < m then 1 else 0) := by
    intro p; simp
  simp only [h2]
  rw [← Finset.card_filter]
  have h3 : (Finset.range c).filter (fun p => p < m) = Finset.range m := by
    ext p; simp; omega
  rw [h3]; simp

lemma frontOnes_mem_dickeSet {c m : ℕ} (h : m ≤ c) : frontOnes m ∈ dickeSet c m :=
  mem_dickeSet.mpr ⟨frontOnes_mem h, wtCount_frontOnes h⟩

/-- The Dicke vector is nonzero for `m ≤ c`. -/
theorem dicke_ne_zero (q : kˣ) {c m : ℕ} (h : m ≤ c) : (dicke q c m : ModelSpace k) ≠ 0 := by
  intro h0
  have := dicke_apply (k := k) q c m (frontOnes m)
  rw [h0, if_pos (frontOnes_mem_dickeSet h)] at this
  simp only [Finsupp.coe_zero, Pi.zero_apply] at this
  exact pow_ne_zero _ q.ne_zero this.symm

/-- The Dicke vectors of different weights are linearly independent. -/
theorem dicke_linearIndependent (q : kˣ) (c : ℕ) :
    LinearIndependent k (fun m : Fin (c + 1) => (dicke q c m : ModelSpace k)) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hle : (i : ℕ) ≤ c := by omega
  have h := congrArg (fun v : ModelSpace k => v (frontOnes i)) hg
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero,
    Pi.zero_apply] at h
  rw [Finset.sum_eq_single i] at h
  · rw [dicke_apply, if_pos (frontOnes_mem_dickeSet hle)] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ q.ne_zero)
  · intro j _ hji
    rw [dicke_apply, if_neg, mul_zero]
    intro hm
    rw [mem_dickeSet, wtCount_frontOnes hle] at hm
    exact hji (Fin.ext hm.2.symm)
  · intro hn; exact absurd hi hn

end Lightlike.TemperleyLieb
