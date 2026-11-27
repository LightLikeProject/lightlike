import Mathlib
import Lightlike.Dirac.Flat
import Lightlike.Dirac.SpinConnection

/-!
# The even center of `Cl(ℝⁿ, -‖·‖²)` and the spin bivectors

The generators `cgen a = ι eₐ` of the Clifford algebra `Cl(ℝⁿ, -‖·‖²)` satisfy `cgen a ^ 2 = -1`
and anticommute.  This file proves:

* `mem_bot_of_commute_of_even`: an element of `Cl(ℝⁿ, -‖·‖²)` that is even (fixed by the grade
  involution) and commutes with every generator is a scalar.  The proof averages over conjugation
  by the generators: the monomials `cgen l₁ ⋯ cgen lₖ` (lists `l`) span the algebra, the average
  `x ↦ ½ (x - cgen a * x * cgen a)` fixes central elements and keeps or kills each monomial, and a
  monomial in which every index occurs an even number of times is `±1`.  Only the spanning
  property of the monomials is used, no basis.
* `eq_zero_of_commute_of_even_of_star`: if moreover `star x = -x`, then `x = 0`.  This is the
  Lie-algebra form of `ker (Spin(n) → SO(n)) = {±1}`.
* the spin bivector `clSpinForm A = ¼ ∑ₖₗ Aₖₗ eₖeₗ` of a matrix and its commutator with a
  generator, `[clSpinForm A, eₖ] = ∑ⱼ Aₖⱼ eⱼ` for skew `A` (`clSpinForm_comm`); in a Clifford module
  `ρ` it is `spinForm ρ A` (`map_clSpinForm`).

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter I, §2 and §6 (the Lie algebra of
  `Spin(n)` is spanned by the bivectors); no equation number is claimed.
-/

open CliffordAlgebra
open scoped Matrix

namespace Lightlike.Dirac

variable {n : ℕ}

/-- The generator `ι eₐ` of `Cl(ℝⁿ, -‖·‖²)`. -/
noncomputable def cgen (a : Fin n) : CliffordAlgebra (Qneg n) := ι (Qneg n) (e a)

/-- `eₐ² = -1` in the Clifford algebra. -/
lemma cgen_mul_self (a : Fin n) : cgen a * cgen a = -1 := by
  rw [cgen, ι_sq_scalar]
  simp [Qneg_apply, e]

/-- `eₐ e_b = -e_b eₐ` for `a ≠ b`. -/
lemma cgen_mul_swap {a b : Fin n} (hab : a ≠ b) : cgen a * cgen b = -(cgen b * cgen a) := by
  have h := ι_mul_ι_add_swap (Q := Qneg n) (e a) (e b)
  have hin : inner ℝ (e a) (e b) = 0 := by
    simp [e, EuclideanSpace.inner_single_left, hab.symm]
  have hp : QuadraticMap.polar (Qneg n) (e a) (e b) = 0 := by
    simp only [QuadraticMap.polar, Qneg_apply, norm_add_sq_real, hin]
    ring
  rw [hp, map_zero] at h
  simpa [cgen] using eq_neg_of_add_eq_zero_left h

/-- The monomial `cgen l₁ * ⋯ * cgen lₖ` of a list of indices. -/
noncomputable def mono (l : List (Fin n)) : CliffordAlgebra (Qneg n) := (l.map cgen).prod

@[simp] lemma mono_nil : mono ([] : List (Fin n)) = 1 := rfl

@[simp] lemma mono_cons (a : Fin n) (l : List (Fin n)) : mono (a :: l) = cgen a * mono l := by
  simp [mono]

lemma mono_append (l l' : List (Fin n)) : mono (l ++ l') = mono l * mono l' := by
  simp [mono]

/-- Moving a generator through a monomial: `eₐ m = (-1)^(|l| + #a) m eₐ`, where `#a` counts the
occurrences of `a` in `l` (only the parity of `|l| - #a`, the number of other factors, matters). -/
lemma cgen_mul_mono (a : Fin n) (l : List (Fin n)) :
    cgen a * mono l = ((-1 : ℝ) ^ (l.length + l.count a)) • (mono l * cgen a) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [mono_cons, List.length_cons, List.count_cons]
    by_cases hb : b = a
    · subst hb
      simp only [beq_self_eq_true, ite_true]
      have hp : ((-1 : ℝ) ^ (l.length + 1 + (l.count b + 1))) = (-1) ^ (l.length + l.count b) := by
        rw [show l.length + 1 + (l.count b + 1) = l.length + l.count b + 2 by ring, pow_add]
        simp
      rw [hp, mul_assoc (cgen b) (mono l), ← mul_smul_comm, ← ih]
    · have hb' : (b == a) = false := by simpa using hb
      simp only [hb', Bool.false_eq_true, ite_false, add_zero]
      rw [← mul_assoc, cgen_mul_swap (Ne.symm hb), neg_mul, mul_assoc, ih, mul_smul_comm,
        ← mul_assoc, show l.length + 1 + l.count a = l.length + l.count a + 1 by ring, pow_succ,
        mul_neg_one, neg_smul]

/-- Conjugating a monomial by a generator: `eₐ m eₐ = -(-1)^(|l| + #a) m`. -/
lemma cgen_mono_cgen (a : Fin n) (l : List (Fin n)) :
    cgen a * mono l * cgen a = -(((-1 : ℝ) ^ (l.length + l.count a)) • mono l) := by
  rw [cgen_mul_mono, smul_mul_assoc, mul_assoc, cgen_mul_self, mul_neg_one, smul_neg]

/-- The average over conjugation by `eₐ`: `x ↦ ½ (x - eₐ x eₐ)`. -/
noncomputable def cavg (a : Fin n) : CliffordAlgebra (Qneg n) →ₗ[ℝ] CliffordAlgebra (Qneg n) :=
  (1 / 2 : ℝ) • (LinearMap.id - (LinearMap.mulLeft ℝ (cgen a)).comp (LinearMap.mulRight ℝ (cgen a)))

lemma cavg_apply (a : Fin n) (x : CliffordAlgebra (Qneg n)) :
    cavg a x = (1 / 2 : ℝ) • (x - cgen a * x * cgen a) := by
  simp [cavg, mul_assoc]

/-- The average fixes an element commuting with `eₐ`. -/
lemma cavg_of_commute {a : Fin n} {x : CliffordAlgebra (Qneg n)} (hx : cgen a * x = x * cgen a) :
    cavg a x = x := by
  rw [cavg_apply, hx, mul_assoc, cgen_mul_self, mul_neg_one, sub_neg_eq_add, ← two_smul ℝ x,
    smul_smul]
  norm_num

/-- The average keeps a monomial if `|l| + #a` is even and kills it otherwise. -/
lemma cavg_mono (a : Fin n) (l : List (Fin n)) :
    cavg a (mono l) = if Even (l.length + l.count a) then mono l else 0 := by
  rw [cavg_apply, cgen_mono_cgen, sub_neg_eq_add]
  split_ifs with h
  · rw [h.neg_one_pow, one_smul, ← two_smul ℝ (mono l), smul_smul]; norm_num
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow, neg_one_smul, add_neg_cancel, smul_zero]

/-- The grade involution on a monomial: `involute m = (-1)^|l| m`. -/
lemma involute_mono (l : List (Fin n)) :
    involute (mono l) = ((-1 : ℝ) ^ l.length) • mono l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [mono_cons, map_mul, ih, List.length_cons, pow_succ, cgen, involute_ι]
    rw [mul_smul_comm, neg_mul, smul_neg, mul_neg_one, neg_smul]

/-- The even projection `x ↦ ½ (x + involute x)`. -/
noncomputable def ceven : CliffordAlgebra (Qneg n) →ₗ[ℝ] CliffordAlgebra (Qneg n) :=
  (1 / 2 : ℝ) • (LinearMap.id + (involute : CliffordAlgebra (Qneg n) →ₐ[ℝ] _).toLinearMap)

lemma ceven_apply (x : CliffordAlgebra (Qneg n)) : ceven x = (1 / 2 : ℝ) • (x + involute x) := by
  simp [ceven]

lemma ceven_of_involute {x : CliffordAlgebra (Qneg n)} (hx : involute x = x) : ceven x = x := by
  rw [ceven_apply, hx, ← two_smul ℝ x, smul_smul]; norm_num

lemma ceven_mono (l : List (Fin n)) :
    ceven (mono l) = if Even l.length then mono l else 0 := by
  rw [ceven_apply, involute_mono]
  split_ifs with h
  · rw [h.neg_one_pow, one_smul, ← two_smul ℝ (mono l), smul_smul]; norm_num
  · rw [(Nat.not_even_iff_odd.mp h).neg_one_pow, neg_one_smul, add_neg_cancel, smul_zero]

/-- The span of the monomials of a set of lists. -/
noncomputable def monoSpan (G : Set (List (Fin n))) : Submodule ℝ (CliffordAlgebra (Qneg n)) :=
  Submodule.span ℝ (mono '' G)

/-- The monomials span the Clifford algebra. -/
theorem monoSpan_univ : monoSpan (Set.univ : Set (List (Fin n))) = ⊤ := by
  refine eq_top_iff.mpr ?_
  rintro x -
  have hmul : ∀ y z, y ∈ monoSpan (Set.univ : Set (List (Fin n))) →
      z ∈ monoSpan (Set.univ : Set (List (Fin n))) →
      y * z ∈ monoSpan (Set.univ : Set (List (Fin n))) := by
    intro y z hy hz
    have h := Submodule.mul_mem_mul hy hz
    rw [monoSpan, Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨u, ⟨l, -, rfl⟩, w, ⟨l', -, rfl⟩, rfl⟩
    exact ⟨l ++ l', trivial, mono_append l l'⟩
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨[], trivial, rfl⟩)
  | ι v =>
    have hv : v = ∑ a, v a • e a := by
      simpa [e] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v).symm
    rw [hv, map_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨[a], trivial, by simp [cgen]⟩)
  | mul y z hy hz => exact hmul y z hy hz
  | add y z hy hz => exact Submodule.add_mem _ hy hz

/-- The average over `eₐ` maps the span of `G` into the span of the lists of `G` whose
`|l| + #a` is even. -/
lemma cavg_mem {G : Set (List (Fin n))} (a : Fin n) {x : CliffordAlgebra (Qneg n)}
    (hx : x ∈ monoSpan G) :
    cavg a x ∈ monoSpan (G ∩ {l | Even (l.length + l.count a)}) := by
  have hle : monoSpan G ≤ (monoSpan (G ∩ {l | Even (l.length + l.count a)})).comap (cavg a) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, cavg_mono]
    split_ifs with h
    · exact Submodule.subset_span ⟨l, ⟨hl, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  exact hle hx

lemma ceven_mem {G : Set (List (Fin n))} {x : CliffordAlgebra (Qneg n)} (hx : x ∈ monoSpan G) :
    ceven x ∈ monoSpan (G ∩ {l | Even l.length}) := by
  have hle : monoSpan G ≤ (monoSpan (G ∩ {l | Even l.length})).comap ceven := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ceven_mono]
    split_ifs with h
    · exact Submodule.subset_span ⟨l, ⟨hl, h⟩, rfl⟩
    · exact Submodule.zero_mem _
  exact hle hx

/-- Removing one occurrence of `a` from a monomial containing it costs a scalar:
`eₐ m = r m'` with `m'` the monomial of `l.erase a`. -/
lemma cgen_mul_mono_erase {a : Fin n} {l : List (Fin n)} (ha : a ∈ l) :
    ∃ r : ℝ, cgen a * mono l = r • mono (l.erase a) := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    by_cases hb : b = a
    · subst hb
      refine ⟨-1, ?_⟩
      rw [mono_cons, ← mul_assoc, cgen_mul_self, List.erase_cons_head]
      simp
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hb
        · exact h
      obtain ⟨r, hr⟩ := ih ha'
      refine ⟨-r, ?_⟩
      rw [List.erase_cons_tail (by simpa using hb), mono_cons, mono_cons, ← mul_assoc,
        cgen_mul_swap (Ne.symm hb), neg_mul, mul_assoc, hr, mul_smul_comm, neg_smul]

/-- A monomial in which every index occurs an even number of times is a scalar (in fact `±1`). -/
theorem mono_mem_bot_of_even_count :
    ∀ (l : List (Fin n)), (∀ a, Even (l.count a)) →
      mono l ∈ (⊥ : Subalgebra ℝ (CliffordAlgebra (Qneg n))) := by
  intro l
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | _ k ih =>
    intro hc
    match l, hlen with
    | [], _ => exact Subalgebra.one_mem _
    | a :: t, hlen =>
      have hca : Odd (t.count a) := by
        have := hc a
        rw [List.count_cons_self] at this
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp this)
      have hat : a ∈ t := List.count_pos_iff.mp (Nat.pos_of_ne_zero fun h => by
        rw [h] at hca; exact (Nat.not_odd_zero hca))
      obtain ⟨r, hr⟩ := cgen_mul_mono_erase hat
      rw [mono_cons, hr]
      refine Subalgebra.smul_mem _ (ih (t.erase a).length ?_ (t.erase a) rfl fun b => ?_) r
      · rw [List.length_erase_of_mem hat, ← hlen, List.length_cons]
        have := List.length_pos_of_mem hat
        omega
      · by_cases hb : b = a
        · subst hb
          rw [List.count_erase_self]
          obtain ⟨m, hm⟩ := hca
          rw [hm]
          simp
        · rw [List.count_erase_of_ne hb]
          have := hc b
          rwa [List.count_cons_of_ne (Ne.symm hb)] at this

/-- **The even center is the scalars.**  An even element of `Cl(ℝⁿ, -‖·‖²)` that commutes with
every generator is a scalar. -/
theorem mem_bot_of_commute_of_even {x : CliffordAlgebra (Qneg n)}
    (hc : ∀ a, cgen a * x = x * cgen a) (he : involute x = x) :
    x ∈ (⊥ : Subalgebra ℝ (CliffordAlgebra (Qneg n))) := by
  have hT : ∀ T : Finset (Fin n),
      x ∈ monoSpan {l : List (Fin n) | ∀ a ∈ T, Even (l.length + l.count a)} := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : {l : List (Fin n) | ∀ a ∈ (∅ : Finset (Fin n)), Even (l.length + l.count a)} =
          Set.univ := by ext l; simp
      rw [this, monoSpan_univ]
      trivial
    | insert a T _ ih =>
      have h := cavg_mem a ih
      rw [cavg_of_commute (hc a)] at h
      refine Submodule.span_mono ?_ h
      rintro _ ⟨l, ⟨hl, hla⟩, rfl⟩
      refine ⟨l, fun b hb => ?_, rfl⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hla
      · exact hl b hb
  have h := ceven_mem (hT Finset.univ)
  rw [ceven_of_involute he] at h
  have hle : monoSpan ({l : List (Fin n) | ∀ a ∈ Finset.univ, Even (l.length + l.count a)} ∩
      {l | Even l.length}) ≤ Subalgebra.toSubmodule (⊥ : Subalgebra ℝ (CliffordAlgebra (Qneg n))) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, ⟨hl, hlen⟩, rfl⟩
    refine mono_mem_bot_of_even_count l fun a => ?_
    have := hl a (Finset.mem_univ a)
    exact (Nat.even_add.mp this).mp hlen
  exact hle h

/-- **No central part in the Lie algebra of `Spin(n)`.**  An even element that commutes with every
generator and satisfies `star x = -x` is zero. -/
theorem eq_zero_of_commute_of_even_of_star {x : CliffordAlgebra (Qneg n)}
    (hc : ∀ a, cgen a * x = x * cgen a) (he : involute x = x) (hs : star x = -x) : x = 0 := by
  obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp (mem_bot_of_commute_of_even hc he)
  rw [star_algebraMap] at hs
  have h2 : (2 : ℝ) • algebraMap ℝ (CliffordAlgebra (Qneg n)) r = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hs]
    exact neg_add_cancel _
  have := (smul_eq_zero.mp h2).resolve_left two_ne_zero
  exact this

/-! ## Spin bivectors -/

/-- The spin bivector `¼ ∑ₖₗ Aₖₗ eₖ eₗ` of a matrix, in the Clifford algebra. -/
noncomputable def clSpinForm (A : Matrix (Fin n) (Fin n) ℝ) : CliffordAlgebra (Qneg n) :=
  (1 / 4 : ℝ) • ∑ i, ∑ j, A i j • (cgen i * cgen j)

/-- In a Clifford module the spin bivector acts as `spinForm`. -/
theorem map_clSpinForm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep n V) (A : Matrix (Fin n) (Fin n) ℝ) : ρ (clSpinForm A) = spinForm ρ A := by
  simp [clSpinForm, spinForm, map_sum, map_smul, gam, cgen]

/-- The commutator of a bivector with a generator: `[eᵢeⱼ, eₖ] = 2δᵢₖ eⱼ - 2δⱼₖ eᵢ`. -/
lemma cgen_comm_pair (i j k : Fin n) :
    cgen i * cgen j * cgen k - cgen k * (cgen i * cgen j) =
      (if i = k then (2 : ℝ) • cgen j else 0) - (if j = k then (2 : ℝ) • cgen i else 0) := by
  by_cases hik : i = k <;> by_cases hjk : j = k
  · subst hik; subst hjk
    simp [mul_assoc]
  · subst hik
    have h1 := cgen_mul_self i
    have hba : cgen j * cgen i = -(cgen i * cgen j) := cgen_mul_swap hjk
    have key : cgen i * cgen j * cgen i = cgen j := by
      rw [mul_assoc, hba, mul_neg, ← mul_assoc, h1]; simp
    have key2 : cgen i * (cgen i * cgen j) = -cgen j := by
      rw [← mul_assoc, h1]; simp
    rw [key, key2]
    simp [hjk, two_smul]
  · subst hjk
    have h1 := cgen_mul_self j
    have hba : cgen j * cgen i = -(cgen i * cgen j) := cgen_mul_swap (Ne.symm hik)
    have key : cgen i * cgen j * cgen j = -cgen i := by
      rw [mul_assoc, h1]; simp
    have key2 : cgen j * (cgen i * cgen j) = cgen i := by
      rw [← mul_assoc, hba, neg_mul, mul_assoc, h1]; simp
    rw [key, key2]
    simp [hik, two_smul]
    abel
  · have hca : cgen k * cgen i = -(cgen i * cgen k) := cgen_mul_swap (Ne.symm hik)
    have hcb : cgen k * cgen j = -(cgen j * cgen k) := cgen_mul_swap (Ne.symm hjk)
    have h4 : cgen k * (cgen i * cgen j) = cgen i * cgen j * cgen k := by
      rw [← mul_assoc, hca, neg_mul, mul_assoc, hcb, mul_neg, neg_neg, ← mul_assoc]
    simp [hik, hjk, h4]

/-- For a skew matrix `A`, `[clSpinForm A, eₖ] = ∑ⱼ Aₖⱼ eⱼ`. -/
theorem clSpinForm_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, A i j = -A j i) (k : Fin n) :
    clSpinForm A * cgen k - cgen k * clSpinForm A = ∑ j, A k j • cgen j := by
  have h : clSpinForm A * cgen k - cgen k * clSpinForm A =
      (1 / 4 : ℝ) • ∑ i, ∑ j, A i j • (cgen i * cgen j * cgen k - cgen k * (cgen i * cgen j)) := by
    simp only [clSpinForm, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum,
      ← smul_sub, ← Finset.sum_sub_distrib]
  rw [h]
  simp only [cgen_comm_pair, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero, smul_smul]
  rw [Finset.sum_comm (f := fun x x_1 => if x_1 = k then (A x x_1 * 2) • cgen x else 0)]
  have e1 : ∀ (g : Fin n → Fin n → CliffordAlgebra (Qneg n)),
      ∑ x, ∑ y, (if x = k then g x y else 0) = ∑ y, g k y := by
    intro g
    simp [Finset.sum_ite_eq']
  have e2 : ∀ j, A j k = - A k j := fun j => by rw [hA j k]
  rw [e1 (fun x y => (A x y * 2) • cgen y), e1 (fun x y => (A y x * 2) • cgen y)]
  simp only [e2]
  rw [← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sub_smul, smul_smul]
  congr 1
  ring

/-- The spin bivector is even. -/
lemma involute_clSpinForm (A : Matrix (Fin n) (Fin n) ℝ) : involute (clSpinForm A) = clSpinForm A := by
  simp [clSpinForm, map_sum, map_smul, cgen, involute_ι]

/-- For a skew matrix the spin bivector is anti-self-adjoint: `star (clSpinForm A) = -clSpinForm A`. -/
lemma star_clSpinForm {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, A i j = -A j i) :
    star (clSpinForm A) = -clSpinForm A := by
  have hs : ∀ i j : Fin n, star (cgen i * cgen j) = cgen j * cgen i := by
    intro i j
    simp [cgen, star_mul, star_ι]
  unfold clSpinForm
  simp only [CliffordAlgebra.star_smul, star_sum, hs]
  rw [Finset.sum_comm, ← smul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hA j i, neg_smul]

/-! ## Tangent vectors to `Spin(n)` -/

/-- The inverse conjugation: if `s eₐ s⋆ = ∑_b R_ab e_b` with `Rᵀ R = 1`, then
`s⋆ eₐ s = ∑_c R_ca e_c`. -/
theorem star_conj_cgen {s : CliffordAlgebra (Qneg n)} (hs : s ∈ spinGroup (Qneg n))
    {R : Matrix (Fin n) (Fin n) ℝ} (hRR : Rᵀ * R = 1)
    (hconj : ∀ a, s * cgen a * star s = ∑ b, R a b • cgen b) (a : Fin n) :
    star s * cgen a * s = ∑ c, R c a • cgen c := by
  have hss : star s * s = 1 := spinGroup.star_mul_self_of_mem hs
  have hc : ∀ c, star s * (∑ b, R c b • cgen b) * s = cgen c := by
    intro c
    rw [← hconj c, ← mul_assoc, ← mul_assoc, hss, one_mul, mul_assoc, hss, mul_one]
  have hsum : ∑ c, R c a • cgen c = star s * (∑ b, (∑ c, R c a * R c b) • cgen b) * s := by
    simp only [Finset.sum_smul, ← smul_smul]
    rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum, mul_smul_comm, smul_mul_assoc, hc c]
  have hδ : ∀ b, ∑ c, R c a * R c b = if a = b then 1 else 0 := by
    intro b
    have := congrFun (congrFun hRR a) b
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  rw [hsum]
  simp only [hδ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Conjugating a spin bivector: `s (clSpinForm M) s⋆ = clSpinForm (Rᵀ M R)`. -/
theorem conj_clSpinForm {s : CliffordAlgebra (Qneg n)} (hs : s ∈ spinGroup (Qneg n))
    {R : Matrix (Fin n) (Fin n) ℝ} (hconj : ∀ a, s * cgen a * star s = ∑ b, R a b • cgen b)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    s * clSpinForm M * star s = clSpinForm (Rᵀ * M * R) := by
  have hss : star s * s = 1 := spinGroup.star_mul_self_of_mem hs
  have hpair : ∀ k l, s * (cgen k * cgen l) * star s =
      ∑ b, ∑ d, (R k b * R l d) • (cgen b * cgen d) := by
    intro k l
    have : s * (cgen k * cgen l) * star s = (s * cgen k * star s) * (s * cgen l * star s) := by
      rw [show (s * cgen k * star s) * (s * cgen l * star s) =
        s * cgen k * (star s * s) * cgen l * star s by simp only [mul_assoc], hss]
      simp only [mul_one, mul_assoc]
    rw [this, hconj k, hconj l, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_mul_smul_comm]
  have sum4 : ∀ f : Fin n → Fin n → Fin n → Fin n → CliffordAlgebra (Qneg n),
      ∑ k, ∑ l, ∑ b, ∑ d, f k l b d = ∑ b, ∑ d, ∑ k, ∑ l, f k l b d := by
    intro f
    calc ∑ k, ∑ l, ∑ b, ∑ d, f k l b d = ∑ k, ∑ b, ∑ l, ∑ d, f k l b d :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k, ∑ b, ∑ d, ∑ l, f k l b d :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
      _ = ∑ b, ∑ k, ∑ d, ∑ l, f k l b d := Finset.sum_comm
      _ = ∑ b, ∑ d, ∑ k, ∑ l, f k l b d := Finset.sum_congr rfl fun b _ => Finset.sum_comm
  have hentry : ∀ b d, (Rᵀ * M * R) b d = ∑ k, ∑ l, M k l * (R k b * R l d) := by
    intro b d
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hL : s * clSpinForm M * star s =
      (1 / 4 : ℝ) • ∑ k, ∑ l, M k l • (s * (cgen k * cgen l) * star s) := by
    simp only [clSpinForm, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  rw [hL, clSpinForm]
  congr 1
  simp only [hpair, Finset.smul_sum, smul_smul, hentry, Finset.sum_smul]
  exact sum4 _

/-- **Tangent vectors to `Spin(n)` are spin bivectors.**  Let `s ∈ Spin(n)` lift the frame change
`R` (`s eₐ s⋆ = ∑_b R_ab e_b`, `Rᵀ R = 1`) and let `δ` be a tangent vector to a curve of such
lifts: even, with `δ s⋆ + s δ⋆ = 0` (the derivative of `s s⋆ = 1`) and
`δ eₐ s⋆ + s eₐ δ⋆ = ∑_b Ṙ_ab e_b` (the derivative of the conjugation), where `Rᵀ Ṙ` is skew.
Then `δ = clSpinForm (Rᵀ Ṙ) · s`. -/
theorem spin_tangent_eq {s δ : CliffordAlgebra (Qneg n)} (hs : s ∈ spinGroup (Qneg n))
    {R Rd : Matrix (Fin n) (Fin n) ℝ} (hRR : Rᵀ * R = 1)
    (hconj : ∀ a, s * cgen a * star s = ∑ b, R a b • cgen b)
    (hskew : ∀ i j, (Rᵀ * Rd) i j = -(Rᵀ * Rd) j i)
    (h1 : δ * star s + s * star δ = 0) (h2 : involute δ = δ)
    (h3 : ∀ a, δ * cgen a * star s + s * cgen a * star δ = ∑ b, Rd a b • cgen b) :
    δ = clSpinForm (Rᵀ * Rd) * s := by
  have hss : star s * s = 1 := spinGroup.star_mul_self_of_mem hs
  set η := δ * star s with hη
  have hsd : s * star δ = -η := eq_neg_of_add_eq_zero_right h1
  have hη_star : star η = -η := by rw [hη, star_mul, star_star, hsd]
  have hη_even : involute η = η := by
    rw [hη, map_mul, h2, spinGroup.involute_eq (spinGroup.star_mem hs)]
  have hy : ∀ a, η * (s * cgen a * star s) - (s * cgen a * star s) * η = ∑ b, Rd a b • cgen b := by
    intro a
    have e1 : η * (s * cgen a * star s) = δ * cgen a * star s := by
      rw [hη, show δ * star s * (s * cgen a * star s) = δ * (star s * s) * cgen a * star s by
        simp only [mul_assoc], hss, mul_one]
    have e2 : (s * cgen a * star s) * η = -(s * cgen a * star δ) := by
      rw [show s * cgen a * star δ = s * cgen a * (star s * s) * star δ by rw [hss, mul_one],
        show s * cgen a * (star s * s) * star δ = (s * cgen a * star s) * (s * star δ) by
          simp only [mul_assoc], hsd, mul_neg, neg_neg]
    rw [e1, e2, sub_neg_eq_add, h3 a]
  have hgen : ∀ c, cgen c = ∑ a, R a c • (s * cgen a * star s) := by
    intro c
    simp only [hconj, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have hδ : ∀ b, ∑ a, R a c * R a b = if c = b then 1 else 0 := by
      intro b
      have := congrFun (congrFun hRR c) b
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    simp only [← Finset.sum_smul, hδ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have hcomm : ∀ c, η * cgen c - cgen c * η = ∑ b, (Rᵀ * Rd) c b • cgen b := by
    intro c
    rw [hgen c, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, hy, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Matrix.mul_apply, Matrix.transpose_apply]
  set β := clSpinForm (Rᵀ * Rd)
  have hβ := clSpinForm_comm hskew
  have hx0 : η - β = 0 := by
    refine eq_zero_of_commute_of_even_of_star (fun c => ?_) ?_ ?_
    · have h := hcomm c
      have h' := hβ c
      have : (η - β) * cgen c - cgen c * (η - β) = 0 := by
        rw [sub_mul, mul_sub]
        rw [show η * cgen c - β * cgen c - (cgen c * η - cgen c * β) =
          (η * cgen c - cgen c * η) - (β * cgen c - cgen c * β) by abel, h, h', sub_self]
      exact (sub_eq_zero.mp this).symm
    · rw [map_sub, hη_even, involute_clSpinForm]
    · rw [star_sub, hη_star, star_clSpinForm hskew, neg_sub_neg, neg_sub]
  have hηβ : η = β := sub_eq_zero.mp hx0
  calc δ = δ * (star s * s) := by rw [hss, mul_one]
    _ = η * s := by rw [hη, mul_assoc]
    _ = β * s := by rw [hηβ]

end Lightlike.Dirac
