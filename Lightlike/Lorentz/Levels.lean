module

public import Lightlike.Lorentz.SpinVectors

/-!
# The level spaces of the principal series

For `p, q ∈ ℕ` the **level space** `levelSpace p q ρ ⊆ L²(ℂ)` is spanned by the
`(p+1)(q+1)` functions

  `mono p q ρ a b (z) = (1+|z|²)^{iρ-1} (1+|z|²)^{-(p+q)/2} z^a z̄^b`,   `a ≤ p`, `b ≤ q`

(the charts of `N^{iρ-1-j} ζ^α ζ̄^β` with `|α| = p`, `|β| = q`). Facts used for the SU(2)
decomposition:

* `finrank_levelSpace_le`: its dimension is at most `(p+1)(q+1)`;
* `levelSpace_le_add`: the levels are nested, `levelSpace p q ≤ levelSpace (p+k) (q+k)`, because
  `1 + |z|² = 1 + z z̄`;
* `tlin_mem_levelSpace`: the spin-`(p+q)/2` vectors `tlin p q ρ x` lie in `levelSpace p q ρ`,
  because every term of the contraction `Λ` is `± z^a z̄^b` on the chart (`prod_lform_chart`).

References: W. Rühl, *The Lorentz Group and Harmonic Analysis* (Benjamin, 1970); A. W. Knapp,
*Representation Theory of Semisimple Groups* (Princeton, 1986), Chapter II.
-/

@[expose] public section

open Matrix Complex MeasureTheory Filter
open scoped ComplexConjugate

namespace Lightlike.Lorentz

open Lightlike.SU2

/-- `toLp` of a finite sum. -/
lemma toLp_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ)
    (hg : ∀ i, MemLp (g i) 2 volume) (hsum : MemLp (∑ i ∈ s, g i) 2 volume) :
    hsum.toLp (∑ i ∈ s, g i) = ∑ i ∈ s, (hg i).toLp (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MemLp.toLp_zero _
  | insert a s ha ih =>
    have h2 : MemLp (∑ i ∈ s, g i) 2 volume := memLp_finsetSum' s fun i _ => hg i
    have e : hsum.toLp (∑ i ∈ insert a s, g i) = ((hg a).add h2).toLp (g a + ∑ i ∈ s, g i) :=
      MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by simp [Finset.sum_insert ha])
    rw [e, MemLp.toLp_add (hg a) h2, ih h2, Finset.sum_insert ha]

/-- **The monomial functions** of the level `(p, q)`. -/
noncomputable def mono (p q : ℕ) (ρ : ℝ) (a b : ℕ) : ℂ → ℂ :=
  fun z => wgt p q ρ z * (z ^ a * conj z ^ b)

lemma continuous_mono (p q : ℕ) (ρ : ℝ) (a b : ℕ) : Continuous (mono p q ρ a b) :=
  (continuous_wgt p q ρ).mul (by fun_prop)

lemma norm_mono_le {p q a b : ℕ} (ha : a ≤ p) (hb : b ≤ q) (ρ : ℝ) (z : ℂ) :
    ‖mono p q ρ a b z‖ ≤ 1 * (1 + ‖z‖ ^ 2)⁻¹ := by
  set s := Real.sqrt (1 + ‖z‖ ^ 2)
  have hs1 : 1 ≤ s := one_le_sqrt z
  have hzs : ‖z‖ ≤ s := Real.le_sqrt_of_sq_le (by linarith)
  have hspos : 0 < s := by linarith
  rw [mono, norm_mul, norm_wgt, norm_mul, norm_pow, norm_pow, Complex.norm_conj]
  have h1 : ‖z‖ ^ a * ‖z‖ ^ b ≤ s ^ (p + q) := by
    calc ‖z‖ ^ a * ‖z‖ ^ b ≤ s ^ a * s ^ b := by gcongr
      _ = s ^ (a + b) := by rw [pow_add]
      _ ≤ s ^ (p + q) := pow_le_pow_right₀ hs1 (by omega)
  have hN : 0 < (1 + ‖z‖ ^ 2)⁻¹ := inv_pos.mpr (one_add_pos z)
  calc (1 + ‖z‖ ^ 2)⁻¹ * s⁻¹ ^ (p + q) * (‖z‖ ^ a * ‖z‖ ^ b)
      ≤ (1 + ‖z‖ ^ 2)⁻¹ * s⁻¹ ^ (p + q) * s ^ (p + q) := by gcongr
    _ = 1 * (1 + ‖z‖ ^ 2)⁻¹ := by rw [inv_pow]; field_simp

lemma memLp_mono {p q a b : ℕ} (ha : a ≤ p) (hb : b ≤ q) (ρ : ℝ) :
    MemLp (mono p q ρ a b) 2 volume :=
  memLp_of_bound (continuous_mono p q ρ a b) 1 (norm_mono_le ha hb ρ)

/-- The generators of the level space, indexed by `(a, b) ∈ [0, p] × [0, q]`. -/
noncomputable def monoL (p q : ℕ) (ρ : ℝ) (ab : Fin (p + 1) × Fin (q + 1)) : L2C :=
  (memLp_mono (Nat.lt_succ_iff.mp ab.1.isLt) (Nat.lt_succ_iff.mp ab.2.isLt) ρ).toLp
    (mono p q ρ ab.1 ab.2)

/-- **The level space** `span{(1+|z|²)^{iρ-1-(p+q)/2} z^a z̄^b : a ≤ p, b ≤ q}`. -/
noncomputable def levelSpace (p q : ℕ) (ρ : ℝ) : Submodule ℂ L2C :=
  Submodule.span ℂ (Set.range (monoL p q ρ))

lemma toLp_mono_mem {p q a b : ℕ} (ha : a ≤ p) (hb : b ≤ q) (ρ : ℝ) :
    (memLp_mono ha hb ρ).toLp (mono p q ρ a b) ∈ levelSpace p q ρ :=
  Submodule.subset_span ⟨(⟨a, by omega⟩, ⟨b, by omega⟩), rfl⟩

/-- **The dimension of a level space** is at most `(p+1)(q+1)`. -/
theorem finrank_levelSpace_le (p q : ℕ) (ρ : ℝ) :
    Module.finrank ℂ (levelSpace p q ρ) ≤ (p + 1) * (q + 1) := by
  have := finrank_range_le_card (R := ℂ) (monoL p q ρ)
  unfold levelSpace
  simpa [Set.finrank, Fintype.card_prod, Fintype.card_fin] using this

instance (p q : ℕ) (ρ : ℝ) : FiniteDimensional ℂ (levelSpace p q ρ) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-! ## Nesting -/

lemma wgt_succ (p q : ℕ) (ρ : ℝ) (z : ℂ) :
    wgt p q ρ z = wgt (p + 1) (q + 1) ρ z * (((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) := by
  have hs : Real.sqrt (1 + ‖z‖ ^ 2) ^ 2 = 1 + ‖z‖ ^ 2 := Real.sq_sqrt (one_add_pos z).le
  have hs0 : Real.sqrt (1 + ‖z‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (one_add_pos z)).ne'
  have key : (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p + q) =
      (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹ ^ (p + 1 + (q + 1)) * (1 + ‖z‖ ^ 2) := by
    set s := Real.sqrt (1 + ‖z‖ ^ 2)
    rw [show p + 1 + (q + 1) = (p + q) + 2 by ring, ← hs]
    have h2 : s⁻¹ ^ 2 * s ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hs0, one_pow]
    rw [pow_add s⁻¹ (p + q) 2]
    calc s⁻¹ ^ (p + q) = s⁻¹ ^ (p + q) * (s⁻¹ ^ 2 * s ^ 2) := by rw [h2, mul_one]
      _ = s⁻¹ ^ (p + q) * s⁻¹ ^ 2 * s ^ 2 := by ring
  simp only [wgt]
  rw [key]
  push_cast
  ring

lemma mono_succ (p q : ℕ) (ρ : ℝ) (a b : ℕ) :
    mono p q ρ a b = mono (p + 1) (q + 1) ρ a b + mono (p + 1) (q + 1) ρ (a + 1) (b + 1) := by
  funext z
  have hz : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [mono, Pi.add_apply, wgt_succ p q ρ z]
  push_cast at hz ⊢
  rw [hz]
  ring

lemma levelSpace_le_succ (p q : ℕ) (ρ : ℝ) : levelSpace p q ρ ≤ levelSpace (p + 1) (q + 1) ρ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  have ha : (a : ℕ) ≤ p := Nat.lt_succ_iff.mp a.isLt
  have hb : (b : ℕ) ≤ q := Nat.lt_succ_iff.mp b.isLt
  have h1 := memLp_mono (p := p + 1) (q := q + 1) (by omega : (a : ℕ) ≤ p + 1)
    (by omega : (b : ℕ) ≤ q + 1) ρ
  have h2 := memLp_mono (p := p + 1) (q := q + 1) (by omega : (a : ℕ) + 1 ≤ p + 1)
    (by omega : (b : ℕ) + 1 ≤ q + 1) ρ
  have e : monoL p q ρ (a, b) = h1.toLp _ + h2.toLp _ := by
    rw [monoL, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z => by rw [mono_succ])
  rw [SetLike.mem_coe, e]
  exact add_mem (toLp_mono_mem (by omega : (a : ℕ) ≤ p + 1) (by omega : (b : ℕ) ≤ q + 1) ρ)
    (toLp_mono_mem (by omega : (a : ℕ) + 1 ≤ p + 1) (by omega : (b : ℕ) + 1 ≤ q + 1) ρ)

/-- **The levels are nested**: `levelSpace p q ≤ levelSpace (p + k) (q + k)`. -/
theorem levelSpace_le_add (p q k : ℕ) (ρ : ℝ) :
    levelSpace p q ρ ≤ levelSpace (p + k) (q + k) ρ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans (levelSpace_le_succ (p + k) (q + k) ρ)

/-! ## The spin vectors lie in their level -/

lemma vec_chart_apply (z : ℂ) (c : Fin 2) : (![z, 1] : C2) c = if c = 0 then z else 1 := by
  fin_cases c <;> simp

lemma epsConj_chart_apply (z : ℂ) (c : Fin 2) :
    epsConj ![z, 1] c = if c = 1 then -conj z else 1 := by
  fin_cases c <;> simp [epsConj]

/-- **Every term of the contraction is a monomial on the chart**:
`∏_i η_i(z, 1)_{t_i} = (-1)^b z^a z̄^b` with `a ≤ p`, `b ≤ q`. -/
lemma prod_lform_chart (p q : ℕ) (t : Str (p + q)) :
    ∃ a ≤ p, ∃ b ≤ q, ∀ z : ℂ,
      ∏ i, lform p q i ![z, 1] (t i) = (-1) ^ b * (z ^ a * conj z ^ b) := by
  classical
  refine ⟨(Finset.univ.filter fun j : Fin p => t (Fin.castAdd q j) = 0).card, ?_,
    (Finset.univ.filter fun j : Fin q => t (Fin.natAdd p j) = 1).card, ?_, fun z => ?_⟩
  · exact (Finset.card_filter_le _ _).trans (by simp)
  · exact (Finset.card_filter_le _ _).trans (by simp)
  rw [Fin.prod_univ_add]
  simp only [lform, Fin.addCases_left, Fin.addCases_right, vec_chart_apply, epsConj_chart_apply]
  rw [Finset.prod_ite, Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [neg_pow]
  ring

/-- **The spin vectors lie in their level**: `tlin p q ρ x ∈ levelSpace p q ρ`. -/
theorem tlin_mem_levelSpace (p q : ℕ) (ρ : ℝ) (x : Fin (p + q + 1) → ℂ) :
    tlin p q ρ x ∈ levelSpace p q ρ := by
  classical
  choose a ha b hb hab using prod_lform_chart p q
  set v := emb (p + q) *ᵥ x
  let g : Str (p + q) → ℂ → ℂ := fun t => (v t * (-1) ^ b t) • mono p q ρ (a t) (b t)
  have hg : ∀ t, MemLp (g t) 2 volume := fun t => (memLp_mono (ha t) (hb t) ρ).const_smul _
  have heq : tfun p q ρ x = ∑ t, g t := by
    funext z
    simp only [tfun, chart_hvec, lam, Finset.sum_apply, g, Pi.smul_apply, smul_eq_mul, mono, hab,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => by ring
  have hsum : MemLp (∑ t, g t) 2 volume := by rw [← heq]; exact memLp_tfun p q ρ x
  have e : tlin p q ρ x = hsum.toLp (∑ t, g t) :=
    MemLp.toLp_congr (memLp_tfun p q ρ x) hsum (Eventually.of_forall fun z => by rw [heq])
  rw [e, toLp_finset_sum _ g hg hsum]
  refine Submodule.sum_mem _ fun t _ => ?_
  have : (hg t).toLp (g t) = (v t * (-1) ^ b t) • (memLp_mono (ha t) (hb t) ρ).toLp _ :=
    MemLp.toLp_const_smul _ _
  rw [this]
  exact Submodule.smul_mem _ _ (toLp_mono_mem (ha t) (hb t) ρ)

end Lightlike.Lorentz
