import Lightlike.OperatorAlgebras.FiniteCAR
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.Matrix
/-!
# Uniqueness of the representations of the CAR over `ℝ²ⁿ` (Dereziński, Theorem 10)

J. Dereziński, arXiv:math-ph/0511030 (read): Section 4.1, pp. 14-15 (eq. (26), representations of the CAR, irreducibility:
"the only closed subspace of `H` preserved by `φ(y)` for all `y` is `{0}` and `H`"), Section 4.2, p. 16 (the Jordan-Wigner
representation), Theorem 10, part 1, p. 17: a representation `(φ₁, …, φ₂ₙ)` of the CAR over `ℝ²ⁿ` in a Hilbert space `H` is
unitarily equivalent to `(Jordan-Wigner) ⊗ 1_K` for a Hilbert space `K`, and it is irreducible iff `K = ℂ`.

The proof here is the standard one by creation words on the vacuum space `K = ⋂ⱼ ker aⱼ`
(`aⱼ = (φ_{2j} + iφ_{2j+1})/2`):

* `cWord c x = c₀^{x₀} c₁^{x₁} ⋯` (ordered creation words), `aWord a x` (the reversed annihilation words, the adjoints) and
  `vacProj a c = a₀c₀ a₁c₁ ⋯` (the projection onto `K`), defined one site at a time, in any ring;
* `sum_cWord_vacProj_aWord`: the resolution of the identity `∑ₓ cWord x · vacProj · aWord x = 1`;
* `inner_cWord`: the vectors `cWord x v`, `v ∈ K`, are orthonormal across configurations;
* `carCreation_cWord`, `carAnnihilation_cWord`: `aⱼ*` and `aⱼ` act on `cWord x v` by the Jordan-Wigner matrices.

`carUnitary` is the unitary `L²(configurations; K) ≅ ⊗ⁿℂ² ⊗ K → E`, `f ↦ ∑ₓ cWord x (f x)`
(`car_unitarily_equivalent_jordanWigner`); `isIrreducibleCAR_iff` is the irreducibility criterion of Theorem 10 (for `E ≠ {0}`),
`isIrreducibleCAR_jordanWigner` the irreducibility of the Jordan-Wigner representation, `car_irreducible_unitarily_equivalent`
Corollary 2, and `car_odd_unitarily_equivalent` Theorem 10, part 2 (over `ℝ²ⁿ⁺¹`: the last generator is `Iₙ ⊗ T` for a
self-adjoint unitary `T` of `K`, `Iₙ = σ₃ ⊗ ⋯ ⊗ σ₃` the Jordan-Wigner parity).

Representation: `⊗ⁿℂ² ⊗ K` is `L²(configurations; K)` (`PiLp 2`), with `B ⊗ 1_K` acting by `(B ⊗ 1) f x = ∑ᵧ B x y f y`
(`tensorOne`); indices are 0-based (`φ_{2j}, φ_{2j+1}` for the source's `φ_{2j-1}, φ_{2j}`).
-/

open scoped InnerProductSpace Kronecker
open Matrix

namespace Lightlike.OperatorAlgebras

/-! ### Creation and annihilation words in a ring -/

section Words

variable {A : Type*} [Ring A]

/-- **The CAR in creation-annihilation form** for families `a, c : Fin n → A`:
`aᵢcⱼ + cⱼaᵢ = δᵢⱼ`, `aᵢaⱼ + aⱼaᵢ = 0`, `cᵢcⱼ + cⱼcᵢ = 0`. -/
structure IsCARPairs {n : ℕ} (a c : Fin n → A) : Prop where
  ac : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0
  aa : ∀ i j, a i * a j + a j * a i = 0
  cc : ∀ i j, c i * c j + c j * c i = 0

lemma IsCARPairs.tail {n : ℕ} {a c : Fin (n + 1) → A} (h : IsCARPairs a c) :
    IsCARPairs (Fin.tail a) (Fin.tail c) where
  ac i j := by
    have := h.ac i.succ j.succ
    simp only [Fin.succ_inj] at this
    exact this
  aa i j := h.aa i.succ j.succ
  cc i j := h.cc i.succ j.succ

lemma IsCARPairs.ac_self {n : ℕ} {a c : Fin n → A} (h : IsCARPairs a c) (i : Fin n) : a i * c i + c i * a i = 1 := by
  simpa using h.ac i i

lemma IsCARPairs.ac_ne {n : ℕ} {a c : Fin n → A} (h : IsCARPairs a c) {i j : Fin n} (hij : i ≠ j) :
    a i * c j = -(c j * a i) := by
  have := h.ac i j
  rw [if_neg hij] at this
  exact eq_neg_of_add_eq_zero_left this

lemma IsCARPairs.ca_ne {n : ℕ} {a c : Fin n → A} (h : IsCARPairs a c) {i j : Fin n} (hij : i ≠ j) :
    c j * a i = -(a i * c j) := by
  rw [h.ac_ne hij, neg_neg]

variable [Module ℂ A]

lemma eq_zero_of_add_self {x : A} (h : x + x = 0) : x = 0 := by
  have : (2 : ℂ) • x = 0 := by rw [two_smul, h]
  simpa using this

lemma IsCARPairs.aa_self {n : ℕ} {a c : Fin n → A} (h : IsCARPairs a c) (i : Fin n) : a i * a i = 0 :=
  eq_zero_of_add_self (h.aa i i)

lemma IsCARPairs.cc_self {n : ℕ} {a c : Fin n → A} (h : IsCARPairs a c) (i : Fin n) : c i * c i = 0 :=
  eq_zero_of_add_self (h.cc i i)

end Words

section Words2

variable {A : Type*} [Ring A]

/-- **The ordered creation word** `c₀^{x₀} c₁^{x₁} ⋯ c_{n-1}^{x_{n-1}}` of a configuration `x`. -/
def cWord : {n : ℕ} → (Fin n → A) → (Fin n → Fin 2) → A
  | 0, _, _ => 1
  | _ + 1, c, x => (if x 0 = 1 then c 0 else 1) * cWord (Fin.tail c) (Fin.tail x)

/-- **The reversed annihilation word** `a_{n-1}^{x_{n-1}} ⋯ a₀^{x₀}` (the adjoint of `cWord`). -/
def aWord : {n : ℕ} → (Fin n → A) → (Fin n → Fin 2) → A
  | 0, _, _ => 1
  | _ + 1, a, x => aWord (Fin.tail a) (Fin.tail x) * (if x 0 = 1 then a 0 else 1)

/-- **The vacuum projection** `a₀c₀ a₁c₁ ⋯ a_{n-1}c_{n-1}`. -/
def vacProj : {n : ℕ} → (Fin n → A) → (Fin n → A) → A
  | 0, _, _ => 1
  | _ + 1, a, c => a 0 * c 0 * vacProj (Fin.tail a) (Fin.tail c)

/-- The sign `(-1)^{|x|}` of a configuration. -/
def wordSign : {n : ℕ} → (Fin n → Fin 2) → ℤ
  | 0, _ => 1
  | _ + 1, x => (if x 0 = 1 then -1 else 1) * wordSign (Fin.tail x)

lemma cWord_cons {n : ℕ} (c : Fin (n + 1) → A) (s : Fin 2) (x : Fin n → Fin 2) :
    cWord c (Fin.cons s x) = (if s = 1 then c 0 else 1) * cWord (Fin.tail c) x := by
  simp only [cWord, Fin.cons_zero, Fin.tail_cons]

lemma aWord_cons {n : ℕ} (a : Fin (n + 1) → A) (s : Fin 2) (x : Fin n → Fin 2) :
    aWord a (Fin.cons s x) = aWord (Fin.tail a) x * (if s = 1 then a 0 else 1) := by
  simp only [aWord, Fin.cons_zero, Fin.tail_cons]

lemma vacProj_succ {n : ℕ} (a c : Fin (n + 1) → A) :
    vacProj a c = a 0 * c 0 * vacProj (Fin.tail a) (Fin.tail c) := rfl

lemma cWord_zero : ∀ {n : ℕ} (c : Fin n → A), cWord c (fun _ => 0) = 1
  | 0, _ => rfl
  | n + 1, c => by
    rw [show (fun _ => (0 : Fin 2)) = Fin.cons (0 : Fin 2) (fun _ : Fin n => (0 : Fin 2)) from
      (Fin.cons_self_tail _).symm, cWord_cons, if_neg (by decide), one_mul, cWord_zero]

lemma aWord_zero : ∀ {n : ℕ} (a : Fin n → A), aWord a (fun _ => 0) = 1
  | 0, _ => rfl
  | n + 1, a => by
    rw [show (fun _ => (0 : Fin 2)) = Fin.cons (0 : Fin 2) (fun _ : Fin n => (0 : Fin 2)) from
      (Fin.cons_self_tail _).symm, aWord_cons, if_neg (by decide), mul_one, aWord_zero]

/-- An element anticommuting with every `cₖ` passes through a creation word up to the sign `(-1)^{|x|}`. -/
lemma mul_cWord {n : ℕ} {z : A} {c : Fin n → A} (hz : ∀ k, z * c k = -(c k * z)) (x : Fin n → Fin 2) :
    z * cWord c x = wordSign x • (cWord c x * z) := by
  induction n with
  | zero => simp [cWord, wordSign]
  | succ n ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have ih' := ih (c := Fin.tail c) (fun k => hz k.succ) x'
    rw [cWord_cons, wordSign, Fin.cons_zero, Fin.tail_cons]
    rcases fin_two_eq_zero_or_one s with rfl | rfl
    · simp only [ite_fin_zero, ite_true, ite_false, one_mul, ih']
    · rw [ite_fin_one, ite_fin_one, ← mul_assoc, hz 0, neg_mul, mul_assoc, ih', mul_smul_comm, neg_one_mul, neg_smul,
        ← mul_assoc]

/-- An element commuting with every `cₖ` commutes with every creation word. -/
lemma commute_cWord {n : ℕ} {z : A} {c : Fin n → A} (hz : ∀ k, z * c k = c k * z) (x : Fin n → Fin 2) :
    z * cWord c x = cWord c x * z := by
  induction n with
  | zero => simp [cWord]
  | succ n ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have ih' := ih (c := Fin.tail c) (fun k => hz k.succ) x'
    rw [cWord_cons]
    rcases fin_two_eq_zero_or_one s with rfl | rfl
    · simp only [ite_fin_zero, ite_true, ite_false, one_mul, ih']
    · rw [ite_fin_one, ← mul_assoc, hz 0, mul_assoc, ih', mul_assoc]

lemma commute_aWord {n : ℕ} {z : A} {a : Fin n → A} (hz : ∀ k, z * a k = a k * z) (x : Fin n → Fin 2) :
    z * aWord a x = aWord a x * z := by
  induction n with
  | zero => simp [aWord]
  | succ n ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have ih' := ih (a := Fin.tail a) (fun k => hz k.succ) x'
    rw [aWord_cons]
    rcases fin_two_eq_zero_or_one s with rfl | rfl
    · simp only [ite_fin_zero, ite_true, ite_false, mul_one, ih']
    · rw [ite_fin_one, ← mul_assoc, ih', mul_assoc, hz 0, mul_assoc]

lemma commute_vacProj {n : ℕ} {z : A} {a c : Fin n → A} (ha : ∀ k, z * a k = a k * z) (hc : ∀ k, z * c k = c k * z) :
    z * vacProj a c = vacProj a c * z := by
  induction n with
  | zero => simp [vacProj]
  | succ n ih =>
    rw [vacProj_succ, ← mul_assoc, ← mul_assoc, ha 0, mul_assoc (a 0), hc 0, ← mul_assoc, mul_assoc (a 0 * c 0),
      ih (a := Fin.tail a) (c := Fin.tail c) (fun k => ha k.succ) (fun k => hc k.succ)]
    simp only [mul_assoc]

/-- `a₀c₀` commutes with the later `aₖ` and `cₖ`. -/
lemma IsCARPairs.commute_a0c0_a {n : ℕ} {a c : Fin (n + 1) → A} (h : IsCARPairs a c) (k : Fin n) :
    a 0 * c 0 * a k.succ = a k.succ * (a 0 * c 0) := by
  have h1 : a 0 * a k.succ = -(a k.succ * a 0) := eq_neg_of_add_eq_zero_left (h.aa 0 k.succ)
  have h2 : c 0 * a k.succ = -(a k.succ * c 0) := h.ca_ne (Fin.succ_ne_zero k)
  rw [mul_assoc, h2, mul_neg, ← mul_assoc, h1, neg_mul, neg_neg, mul_assoc]

lemma IsCARPairs.commute_a0c0_c {n : ℕ} {a c : Fin (n + 1) → A} (h : IsCARPairs a c) (k : Fin n) :
    a 0 * c 0 * c k.succ = c k.succ * (a 0 * c 0) := by
  have h1 : c 0 * c k.succ = -(c k.succ * c 0) := eq_neg_of_add_eq_zero_left (h.cc 0 k.succ)
  have h2 : a 0 * c k.succ = -(c k.succ * a 0) := h.ac_ne (Fin.succ_ne_zero k).symm
  rw [mul_assoc, h1, mul_neg, ← mul_assoc, h2, neg_mul, neg_neg, mul_assoc]

lemma sum_configs_succ {M : Type*} [AddCommMonoid M] {n : ℕ} (g : (Fin (n + 1) → Fin 2) → M) :
    ∑ y, g y = ∑ y : Fin n → Fin 2, (g (Fin.cons 0 y) + g (Fin.cons 1 y)) := by
  rw [← (Fin.consEquiv (fun _ => Fin 2)).sum_comp, Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
  rfl

variable [Module ℂ A]

/-- **The resolution of the identity** `∑ₓ cWord x · vacProj · aWord x = 1`. -/
theorem sum_cWord_vacProj_aWord {n : ℕ} {a c : Fin n → A} (h : IsCARPairs a c) :
    ∑ x, cWord c x * vacProj a c * aWord a x = 1 := by
  induction n with
  | zero => simp [cWord, vacProj, aWord]
  | succ n ih =>
    have hT := ih h.tail
    have hW : ∀ y, a 0 * c 0 * cWord (Fin.tail c) y = cWord (Fin.tail c) y * (a 0 * c 0) :=
      commute_cWord (fun k => h.commute_a0c0_c k)
    have hac := h.ac_self 0
    have hcc := h.cc_self 0
    rw [sum_configs_succ]
    simp only [cWord_cons, aWord_cons, vacProj_succ, ite_fin_zero, ite_true, ite_false, ite_fin_one, one_mul, mul_one]
    have e0 : ∀ y, cWord (Fin.tail c) y * (a 0 * c 0 * vacProj (Fin.tail a) (Fin.tail c)) * aWord (Fin.tail a) y =
        a 0 * c 0 * (cWord (Fin.tail c) y * vacProj (Fin.tail a) (Fin.tail c) * aWord (Fin.tail a) y) := by
      intro y
      rw [← mul_assoc (cWord (Fin.tail c) y) (a 0 * c 0), ← hW y]
      simp only [mul_assoc]
    have e1 : ∀ y, c 0 * cWord (Fin.tail c) y * (a 0 * c 0 * vacProj (Fin.tail a) (Fin.tail c)) *
        (aWord (Fin.tail a) y * a 0) =
        c 0 * (a 0 * c 0 * (cWord (Fin.tail c) y * vacProj (Fin.tail a) (Fin.tail c) * aWord (Fin.tail a) y)) * a 0 := by
      intro y
      rw [← e0 y]
      simp only [mul_assoc]
    simp only [e0, e1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hT, mul_one]
    have e2 : c 0 * (a 0 * c 0) * a 0 = c 0 * a 0 := by
      rw [show a 0 * c 0 = 1 - c 0 * a 0 from eq_sub_of_add_eq hac, mul_sub, sub_mul, mul_one, ← mul_assoc (c 0) (c 0),
        hcc, zero_mul, zero_mul, sub_zero]
    rw [e2, hac]

/-- `aⱼ vacProj = 0`: the vacuum projection maps into the vacuum space. -/
theorem mul_vacProj_eq_zero {n : ℕ} {a c : Fin n → A} (h : IsCARPairs a c) (j : Fin n) : a j * vacProj a c = 0 := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [vacProj_succ, ← mul_assoc, ← mul_assoc, h.aa_self, zero_mul, zero_mul]
    · rw [vacProj_succ, ← mul_assoc, ← h.commute_a0c0_a k, mul_assoc, show a k.succ = Fin.tail a k from rfl,
        ih h.tail k, mul_zero]

end Words2

/-! ### Vectors: orthonormality and the Jordan-Wigner action -/

section Vectors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `a₀` kills the creation words of the later sites on the vacuum of `a₀`. -/
lemma IsCARPairs.a0_cWord_tail {n : ℕ} {a c : Fin (n + 1) → (E →L[ℂ] E)} (h : IsCARPairs a c) {v : E}
    (hv : a 0 v = 0) (y : Fin n → Fin 2) : a 0 (cWord (Fin.tail c) y v) = 0 := by
  have := mul_cWord (z := a 0) (c := Fin.tail c) (fun k => h.ac_ne (Fin.succ_ne_zero k).symm) y
  rw [← ContinuousLinearMap.mul_apply, this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, hv,
    map_zero, smul_zero]

lemma IsCARPairs.a0_c0_apply {n : ℕ} {a c : Fin (n + 1) → (E →L[ℂ] E)} (h : IsCARPairs a c) {u : E} (hu : a 0 u = 0) :
    a 0 (c 0 u) = u := by
  have := congrArg (fun T : E →L[ℂ] E => T u) (h.ac_self 0)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, hu, map_zero, add_zero,
    ContinuousLinearMap.one_apply] at this
  exact this

/-- **Orthonormality**: `⟪cWord x v, cWord y w⟫ = δₓᵧ ⟪v, w⟫` for vacuum vectors `v, w`. -/
theorem inner_cWord {n : ℕ} {a c : Fin n → (E →L[ℂ] E)} (h : IsCARPairs a c)
    (hadj : ∀ j p q, ⟪a j p, q⟫_ℂ = ⟪p, c j q⟫_ℂ) {v w : E} (hv : ∀ j, a j v = 0) (hw : ∀ j, a j w = 0)
    (x y : Fin n → Fin 2) : ⟪cWord c x v, cWord c y w⟫_ℂ = if x = y then ⟪v, w⟫_ℂ else 0 := by
  induction n with
  | zero => simp [cWord, Subsingleton.elim x y]
  | succ n ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    obtain ⟨t, y', rfl⟩ : ∃ t y', y = Fin.cons t y' := ⟨y 0, Fin.tail y, (Fin.cons_self_tail y).symm⟩
    have ih' := ih h.tail (fun j p q => hadj j.succ p q) (fun j => hv j.succ) (fun j => hw j.succ) x' y'
    have hu := h.a0_cWord_tail (hv 0) x'
    have hu' := h.a0_cWord_tail (hw 0) y'
    have hadj' : ∀ p q, ⟪c 0 p, q⟫_ℂ = ⟪p, a 0 q⟫_ℂ := fun p q => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    simp only [cWord_cons, Fin.cons_inj]
    rcases fin_two_eq_zero_or_one s with rfl | rfl <;> rcases fin_two_eq_zero_or_one t with rfl | rfl
    · simp only [ite_fin_zero, ite_true, ite_false, one_mul]
      simpa using ih'
    · rw [ite_fin_zero, ite_fin_one, one_mul, ContinuousLinearMap.mul_apply, ← hadj, hu, inner_zero_left]
      simp
    · rw [ite_fin_one, ite_fin_zero, one_mul, ContinuousLinearMap.mul_apply, hadj', hu', inner_zero_right]
      simp
    · rw [ite_fin_one, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← hadj, h.a0_c0_apply hu]
      simpa using ih'

/-- `⟪aWord x p, q⟫ = ⟪p, cWord x q⟫`. -/
theorem inner_aWord {n : ℕ} {a c : Fin n → (E →L[ℂ] E)} (hadj : ∀ j p q, ⟪a j p, q⟫_ℂ = ⟪p, c j q⟫_ℂ)
    (x : Fin n → Fin 2) (p q : E) : ⟪aWord a x p, q⟫_ℂ = ⟪p, cWord c x q⟫_ℂ := by
  induction n generalizing p q with
  | zero => simp [aWord, cWord]
  | succ n ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [aWord_cons, cWord_cons, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ih (a := Fin.tail a) (c := Fin.tail c) (fun j p q => hadj j.succ p q)]
    split_ifs
    · exact hadj 0 _ _
    · rfl

theorem inner_vacProj {n : ℕ} {a c : Fin n → (E →L[ℂ] E)} (h : IsCARPairs a c)
    (hadj : ∀ j p q, ⟪a j p, q⟫_ℂ = ⟪p, c j q⟫_ℂ) (p q : E) : ⟪vacProj a c p, q⟫_ℂ = ⟪p, vacProj a c q⟫_ℂ := by
  induction n generalizing p q with
  | zero => simp [vacProj]
  | succ n ih =>
    have hadj' : ∀ p q, ⟪c 0 p, q⟫_ℂ = ⟪p, a 0 q⟫_ℂ := fun p q => by
      rw [← inner_conj_symm, ← hadj, inner_conj_symm]
    have hcomm := commute_vacProj (z := a 0 * c 0) (a := Fin.tail a) (c := Fin.tail c) (fun k => h.commute_a0c0_a k)
      (fun k => h.commute_a0c0_c k)
    rw [vacProj_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hadj, hadj',
      ih h.tail (fun j p q => hadj j.succ p q), ← ContinuousLinearMap.mul_apply (a 0) (c 0),
      ← ContinuousLinearMap.mul_apply, ← hcomm, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]

theorem vacProj_apply_of_vacuum {n : ℕ} {a c : Fin n → (E →L[ℂ] E)} (h : IsCARPairs a c) {u : E}
    (hu : ∀ j, a j u = 0) : vacProj a c u = u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [vacProj_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ih h.tail (fun j => hu j.succ), h.a0_c0_apply (hu 0)]

/-- `vacProj (aWord x (cWord y v)) = δₓᵧ v` for a vacuum vector `v`. -/
theorem vacProj_aWord_cWord {n : ℕ} {a c : Fin n → (E →L[ℂ] E)} (h : IsCARPairs a c)
    (hadj : ∀ j p q, ⟪a j p, q⟫_ℂ = ⟪p, c j q⟫_ℂ) {v : E} (hv : ∀ j, a j v = 0) (x y : Fin n → Fin 2) :
    vacProj a c (aWord a x (cWord c y v)) = if x = y then v else 0 := by
  set z := vacProj a c (aWord a x (cWord c y v)) - (if x = y then v else 0) with hz
  have hzK : ∀ j, a j z = 0 := by
    intro j
    rw [hz, map_sub, ← ContinuousLinearMap.mul_apply, mul_vacProj_eq_zero h j, ContinuousLinearMap.zero_apply,
      zero_sub, neg_eq_zero]
    split_ifs
    · exact hv j
    · exact map_zero _
  have horth : ∀ u, (∀ j, a j u = 0) → ⟪u, z⟫_ℂ = 0 := by
    intro u hu
    rw [hz, inner_sub_right, ← inner_vacProj h hadj, vacProj_apply_of_vacuum h hu, ← inner_conj_symm, inner_aWord hadj,
      inner_conj_symm, inner_cWord h hadj hu hv]
    split_ifs <;> simp
  have := horth z hzK
  rw [inner_self_eq_zero, sub_eq_zero] at this
  exact this

/-- The Jordan-Wigner matrix entries at the first site. -/
lemma jw_entry {n : ℕ} (B : Matrix (Fin 2) (Fin 2) ℂ) (C : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (y x : Fin (n + 1) → Fin 2) :
    (B ⊗ₖ C).submatrix (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm y x =
      B (y 0) (x 0) * C (Fin.tail y) (Fin.tail x) := rfl

/-- **The creation operators act by the Jordan-Wigner matrices**:
`aⱼ* (cWord x v) = ∑ᵧ (aⱼ*)_{JW, y x} cWord y v`. -/
theorem carCreation_cWord {n : ℕ} {a c : Fin n → (E →L[ℂ] E)} (h : IsCARPairs a c) {v : E} (hv : ∀ j, a j v = 0) :
    ∀ (j : Fin n) (x : Fin n → Fin 2),
      c j (cWord c x v) = ∑ y, carCreation (jordanWigner n) j y x • cWord c y v := by
  induction n with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    intro j x
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [sum_configs_succ]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [carCreation_jordanWigner_zero, jw_entry, Fin.cons_zero, Fin.tail_cons, one_apply, cWord_cons,
        mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      rcases fin_two_eq_zero_or_one s with rfl | rfl
      · simp [pauli1, pauli2, ContinuousLinearMap.mul_apply]
        norm_num
      · simp [pauli1, pauli2, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (c 0) (c 0),
          h.cc_self 0]
    · have hck : c k.succ * c 0 = -(c 0 * c k.succ) := eq_neg_of_add_eq_zero_left (h.cc k.succ 0)
      have ih' := ih h.tail (fun j => hv j.succ) k x'
      simp only [carCreation_jordanWigner_succ, jw_entry, Fin.cons_zero, Fin.tail_cons, cWord_cons]
      rcases fin_two_eq_zero_or_one s with rfl | rfl
      · simp only [ite_fin_zero, ite_true, ite_false, ite_fin_one, one_mul, pauli3]
        rw [show c k.succ = Fin.tail c k from rfl, ih']
        simp [ContinuousLinearMap.mul_apply]
      · simp only [ite_fin_zero, ite_true, ite_false, ite_fin_one, one_mul, pauli3]
        rw [← ContinuousLinearMap.mul_apply, ← mul_assoc, hck, neg_mul, mul_assoc, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.mul_apply, show c k.succ = Fin.tail c k from rfl, ContinuousLinearMap.mul_apply, ih', map_sum]
        simp [ContinuousLinearMap.mul_apply, Finset.sum_neg_distrib]

/-- **The annihilation operators act by the Jordan-Wigner matrices**. -/
theorem carAnnihilation_cWord {n : ℕ} {a c : Fin n → (E →L[ℂ] E)} (h : IsCARPairs a c) {v : E}
    (hv : ∀ j, a j v = 0) :
    ∀ (j : Fin n) (x : Fin n → Fin 2),
      a j (cWord c x v) = ∑ y, carAnnihilation (jordanWigner n) j y x • cWord c y v := by
  induction n with
  | zero => intro j; exact j.elim0
  | succ n ih =>
    intro j x
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [sum_configs_succ]
    have hu := h.a0_cWord_tail (hv 0) x'
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [carAnnihilation_jordanWigner_zero, jw_entry, Fin.cons_zero, Fin.tail_cons, one_apply, cWord_cons,
        mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      rcases fin_two_eq_zero_or_one s with rfl | rfl
      · simp [pauli1, pauli2, ContinuousLinearMap.mul_apply, hu]
      · simp only [ite_fin_one, ite_true, ite_false, ContinuousLinearMap.mul_apply, h.a0_c0_apply hu]
        simp [pauli1, pauli2, ContinuousLinearMap.mul_apply]
        norm_num
    · have hak : a k.succ * c 0 = -(c 0 * a k.succ) := h.ac_ne (Fin.succ_ne_zero k)
      have ih' := ih h.tail (fun j => hv j.succ) k x'
      simp only [carAnnihilation_jordanWigner_succ, jw_entry, Fin.cons_zero, Fin.tail_cons, cWord_cons]
      rcases fin_two_eq_zero_or_one s with rfl | rfl
      · simp only [ite_fin_zero, ite_true, ite_false, ite_fin_one, one_mul, pauli3]
        rw [show a k.succ = Fin.tail a k from rfl, ih']
        simp [ContinuousLinearMap.mul_apply]
      · simp only [ite_fin_zero, ite_true, ite_false, ite_fin_one, one_mul, pauli3]
        rw [← ContinuousLinearMap.mul_apply, ← mul_assoc, hak, neg_mul, mul_assoc, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.mul_apply, show a k.succ = Fin.tail a k from rfl, ContinuousLinearMap.mul_apply, ih', map_sum]
        simp [ContinuousLinearMap.mul_apply, Finset.sum_neg_distrib]

end Vectors

open scoped InnerProductSpace Kronecker
open Matrix

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **A representation of the CAR** over `ℝᵐ` by bounded operators on an inner product space `E`
(Dereziński (26), p. 14, for the canonical basis): symmetric `φ b` with `φ a φ b + φ b φ a = 2 δₐᵦ`. -/
structure IsCAROn {m : ℕ} (φ : Fin m → (E →L[ℂ] E)) : Prop where
  symm : ∀ b v w, ⟪φ b v, w⟫_ℂ = ⟪v, φ b w⟫_ℂ
  anticomm : ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : E →L[ℂ] E) else 0

/-- On a Hilbert space the symmetry condition is self-adjointness. -/
lemma isCAROn_iff [CompleteSpace E] {m : ℕ} (φ : Fin m → (E →L[ℂ] E)) :
    IsCAROn φ ↔ (∀ b, IsSelfAdjoint (φ b)) ∧
      ∀ a b, φ a * φ b + φ b * φ a = if a = b then (2 : ℂ) • (1 : E →L[ℂ] E) else 0 := by
  constructor
  · intro h
    exact ⟨fun b => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr (h.symm b), h.anticomm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun b => (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp (h1 b), h2⟩

/-- **Irreducibility** (Dereziński, p. 15): the only closed subspaces preserved by every `φ b` are `{0}` and `E`. -/
def IsIrreducibleCAR {m : ℕ} (φ : Fin m → (E →L[ℂ] E)) : Prop :=
  ∀ W : Submodule ℂ E, IsClosed (W : Set E) → (∀ b, ∀ w ∈ W, φ b w ∈ W) → W = ⊥ ∨ W = ⊤

/-- **The vacuum space** `K = ⋂ⱼ ker aⱼ`. -/
noncomputable def carVacuum {n : ℕ} (φ : Fin (2 * n) → (E →L[ℂ] E)) : Submodule ℂ E :=
  ⨅ j, LinearMap.ker ((carAnnihilation φ j : E →L[ℂ] E) : E →ₗ[ℂ] E)

lemma mem_carVacuum {n : ℕ} {φ : Fin (2 * n) → (E →L[ℂ] E)} {v : E} :
    v ∈ carVacuum φ ↔ ∀ j, carAnnihilation φ j v = 0 := by
  simp [carVacuum, Submodule.mem_iInf]

lemma isClosed_carVacuum {n : ℕ} (φ : Fin (2 * n) → (E →L[ℂ] E)) : IsClosed (carVacuum φ : Set E) := by
  rw [carVacuum, Submodule.coe_iInf]
  exact isClosed_iInter fun j => ContinuousLinearMap.isClosed_ker (carAnnihilation φ j)

lemma IsCAROn.isCARPairs {n : ℕ} {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) :
    IsCARPairs (carAnnihilation φ) (carCreation φ) where
  ac i j := carAnnihilation_carCreation h.anticomm i j
  aa i j := carAnnihilation_anticomm h.anticomm i j
  cc i j := carCreation_anticomm h.anticomm i j

lemma IsCAROn.adj {n : ℕ} {φ : Fin (2 * n) → (E →L[ℂ] E)} (h : IsCAROn φ) (j : Fin n) (p q : E) :
    ⟪carAnnihilation φ j p, q⟫_ℂ = ⟪p, carCreation φ j q⟫_ℂ := by
  simp only [carAnnihilation, carCreation, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right, majorana, h.symm]
  simp [Complex.conj_I, sub_eq_add_neg, mul_add, show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]

/-- `B ⊗ 1_K` on `⊗ⁿℂ² ⊗ K ≅ L²(κ; K)`: `(B ⊗ 1) f x = ∑ᵧ B x y f y`. -/
noncomputable def tensorOne {κ : Type*} [Fintype κ] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (B : Matrix κ κ ℂ) : PiLp 2 (fun _ : κ => V) →ₗ[ℂ] PiLp 2 (fun _ : κ => V) where
  toFun f := WithLp.toLp 2 (fun x => ∑ y, B x y • f y)
  map_add' f g := by
    ext x
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' r f := by
    ext x
    simp [Finset.smul_sum, smul_comm r]

lemma tensorOne_apply {κ : Type*} [Fintype κ] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (B : Matrix κ κ ℂ) (f : PiLp 2 (fun _ : κ => V)) (x : κ) : tensorOne B f x = ∑ y, B x y • f y := rfl

variable {n : ℕ} {φ : Fin (2 * n) → (E →L[ℂ] E)}

/-- The map `L²(configurations; K) → E`, `f ↦ ∑ₓ cWord x (f x)`. -/
noncomputable def carFockMap (φ : Fin (2 * n) → (E →L[ℂ] E)) :
    PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum φ) →ₗ[ℂ] E where
  toFun f := ∑ x, cWord (carCreation φ) x (f x : E)
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' r f := by simp [Finset.smul_sum]

lemma carFockMap_apply (f : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum φ)) :
    carFockMap φ f = ∑ x, cWord (carCreation φ) x (f x : E) := rfl

lemma inner_carFockMap (h : IsCAROn φ) (f g : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum φ)) :
    ⟪carFockMap φ f, carFockMap φ g⟫_ℂ = ⟪f, g⟫_ℂ := by
  rw [carFockMap_apply, carFockMap_apply, PiLp.inner_apply, sum_inner]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [inner_sum]
  have hx : ∀ y, ⟪cWord (carCreation φ) x (f x : E), cWord (carCreation φ) y (g y : E)⟫_ℂ =
      if x = y then ⟪(f x : E), (g y : E)⟫_ℂ else 0 := fun y =>
    inner_cWord h.isCARPairs h.adj (mem_carVacuum.mp (f x).2) (mem_carVacuum.mp (g y).2) x y
  simp_rw [hx]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Submodule.coe_inner]

lemma carFockMap_surjective (h : IsCAROn φ) : Function.Surjective (carFockMap φ) := by
  intro e
  have hK : ∀ x, vacProj (carAnnihilation φ) (carCreation φ) (aWord (carAnnihilation φ) x e) ∈ carVacuum φ := by
    intro x
    rw [mem_carVacuum]
    intro j
    rw [← ContinuousLinearMap.mul_apply, mul_vacProj_eq_zero h.isCARPairs j, ContinuousLinearMap.zero_apply]
  refine ⟨WithLp.toLp 2 (fun x => ⟨_, hK x⟩), ?_⟩
  have := congrArg (fun T : E →L[ℂ] E => T e) (sum_cWord_vacProj_aWord h.isCARPairs)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at this
  rw [carFockMap_apply]
  exact this

/-- **The unitary** `⊗ⁿℂ² ⊗ K ≅ L²(configurations; K) → E` of Theorem 10. -/
noncomputable def carUnitary (h : IsCAROn φ) : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum φ) ≃ₗᵢ[ℂ] E :=
  LinearIsometryEquiv.ofSurjective ((carFockMap φ).isometryOfInner (inner_carFockMap h)) (carFockMap_surjective h)

lemma carUnitary_apply (h : IsCAROn φ) (f : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum φ)) :
    carUnitary h f = carFockMap φ f := rfl

/-- A single `φ b` acts on the creation words by the Jordan-Wigner matrix. -/
lemma IsCAROn.apply_cWord (h : IsCAROn φ) {v : E} (hv : v ∈ carVacuum φ) (b : Fin (2 * n)) (x : Fin n → Fin 2) :
    φ b (cWord (carCreation φ) x v) = ∑ y, jordanWigner n b y x • cWord (carCreation φ) y v := by
  have hv' := mem_carVacuum.mp hv
  have hA := carAnnihilation_cWord h.isCARPairs hv'
  have hC := carCreation_cWord h.isCARPairs hv'
  obtain ⟨j, s, hb⟩ := exists_majorana_index b
  rcases fin_two_eq_zero_or_one s with rfl | rfl
  · rw [show φ b = majorana φ j 0 from by rw [majorana, hb], show jordanWigner n b = majorana (jordanWigner n) j 0 from
      by rw [majorana, hb], majorana_zero_eq, majorana_zero_eq, ContinuousLinearMap.add_apply, hA, hC,
      ← Finset.sum_add_distrib]
    simp [add_smul]
  · rw [show φ b = majorana φ j 1 from by rw [majorana, hb], show jordanWigner n b = majorana (jordanWigner n) j 1 from
      by rw [majorana, hb], majorana_one_eq, majorana_one_eq, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, hA, hC, ← Finset.sum_sub_distrib, Finset.smul_sum]
    simp [sub_smul, smul_sub, smul_smul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    module

/-- **Dereziński, Theorem 10, part 1** (intertwining): `U (JW_b ⊗ 1_K) = φ_b U`. -/
theorem carUnitary_intertwines (h : IsCAROn φ) (b : Fin (2 * n))
    (f : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum φ)) :
    carUnitary h (tensorOne (jordanWigner n b) f) = φ b (carUnitary h f) := by
  rw [carUnitary_apply, carUnitary_apply, carFockMap_apply, carFockMap_apply, map_sum]
  have hx : ∀ x, φ b (cWord (carCreation φ) x (f x : E)) =
      ∑ y, jordanWigner n b y x • cWord (carCreation φ) y (f x : E) := fun x => h.apply_cWord (f x).2 b x
  simp_rw [hx, tensorOne_apply, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  rw [Finset.sum_comm]

/-- **Dereziński, Theorem 10, part 1**: every representation `(φ₁, …, φ₂ₙ)` of the CAR over `ℝ²ⁿ` is unitarily
equivalent to `(Jordan-Wigner) ⊗ 1_K` for a Hilbert space `K` (here the vacuum space, closed in `E`). -/
theorem car_unitarily_equivalent_jordanWigner (h : IsCAROn φ) :
    ∃ U : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum φ) ≃ₗᵢ[ℂ] E,
      ∀ b f, U (tensorOne (jordanWigner n b) f) = φ b (U f) :=
  ⟨carUnitary h, carUnitary_intertwines h⟩

/-- Invariance of a subspace under every `φ b` passes to `aⱼ`, `aⱼ*`, the words and the vacuum projection. -/
lemma invariant_words {W : Submodule ℂ E} (hW : ∀ b, ∀ w ∈ W, φ b w ∈ W) :
    (∀ j, ∀ w ∈ W, carAnnihilation φ j w ∈ W) ∧ (∀ j, ∀ w ∈ W, carCreation φ j w ∈ W) := by
  constructor <;> intro j w hw <;>
    simp only [carAnnihilation, carCreation, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, majorana] <;>
    first
    | exact W.smul_mem _ (W.add_mem (hW _ w hw) (W.smul_mem _ (hW _ w hw)))
    | exact W.smul_mem _ (W.sub_mem (hW _ w hw) (W.smul_mem _ (hW _ w hw)))

lemma invariant_cWord {m : ℕ} {W : Submodule ℂ E} {c : Fin m → (E →L[ℂ] E)} (hc : ∀ j, ∀ w ∈ W, c j w ∈ W)
    (x : Fin m → Fin 2) : ∀ w ∈ W, cWord c x w ∈ W := by
  induction m with
  | zero => intro w hw; simpa [cWord] using hw
  | succ m ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    intro w hw
    rw [cWord_cons, ContinuousLinearMap.mul_apply]
    have := ih (c := Fin.tail c) (fun j => hc j.succ) x' w hw
    split_ifs
    · exact hc 0 _ this
    · exact this

lemma invariant_aWord {m : ℕ} {W : Submodule ℂ E} {a : Fin m → (E →L[ℂ] E)} (ha : ∀ j, ∀ w ∈ W, a j w ∈ W)
    (x : Fin m → Fin 2) : ∀ w ∈ W, aWord a x w ∈ W := by
  induction m with
  | zero => intro w hw; simpa [aWord] using hw
  | succ m ih =>
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    intro w hw
    rw [aWord_cons, ContinuousLinearMap.mul_apply]
    refine ih (a := Fin.tail a) (fun j => ha j.succ) x' _ ?_
    split_ifs
    · exact ha 0 _ hw
    · exact hw

lemma invariant_vacProj {m : ℕ} {W : Submodule ℂ E} {a c : Fin m → (E →L[ℂ] E)} (ha : ∀ j, ∀ w ∈ W, a j w ∈ W)
    (hc : ∀ j, ∀ w ∈ W, c j w ∈ W) : ∀ w ∈ W, vacProj a c w ∈ W := by
  induction m with
  | zero => intro w hw; simpa [vacProj] using hw
  | succ m ih =>
    intro w hw
    rw [vacProj_succ, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
    exact ha 0 _ (hc 0 _ (ih (a := Fin.tail a) (c := Fin.tail c) (fun j => ha j.succ) (fun j => hc j.succ) w hw))

/-- **Dereziński, Theorem 10, part 1** (irreducibility): for `E ≠ {0}`, the representation is irreducible iff the
multiplicity space `K` is one-dimensional (`K ≅ ℂ`). -/
theorem isIrreducibleCAR_iff [Nontrivial E] (h : IsCAROn φ) :
    IsIrreducibleCAR φ ↔ Module.finrank ℂ (carVacuum φ) = 1 := by
  have hP := h.isCARPairs
  have hQN : ∀ {v : E}, v ∈ carVacuum φ → ∀ x y, vacProj (carAnnihilation φ) (carCreation φ)
      (aWord (carAnnihilation φ) x (cWord (carCreation φ) y v)) = if x = y then v else 0 :=
    fun hv x y => vacProj_aWord_cWord hP h.adj (mem_carVacuum.mp hv) x y
  constructor
  · intro hirr
    -- `K ≠ 0`
    obtain ⟨v, hvK, hv0⟩ : ∃ v ∈ carVacuum φ, v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨e, he⟩ := exists_ne (0 : E)
      obtain ⟨f, rfl⟩ := carFockMap_surjective h e
      apply he
      rw [carFockMap_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hcon _ (f x).2, map_zero]
    -- the span of the words on `v` is closed and invariant, hence everything
    set W := Submodule.span ℂ (Set.range fun x => cWord (carCreation φ) x v) with hWdef
    have hWinv : ∀ b, ∀ w ∈ W, φ b w ∈ W := by
      intro b w hw
      refine Submodule.span_induction (p := fun w _ => φ b w ∈ W) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨x, rfl⟩
        rw [h.apply_cWord hvK b x]
        exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
      · simp
      · intro u w _ _ hu hw; rw [map_add]; exact W.add_mem hu hw
      · intro r u _ hu; rw [map_smul]; exact W.smul_mem r hu
    have hWclosed : IsClosed (W : Set E) := by
      haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
      exact W.closed_of_finiteDimensional
    have hvW : v ∈ W := by
      rw [show v = cWord (carCreation φ) (fun _ => 0) v by rw [cWord_zero, ContinuousLinearMap.one_apply]]
      exact Submodule.subset_span ⟨_, rfl⟩
    have hWtop : W = ⊤ := by
      rcases hirr W hWclosed hWinv with hb | ht
      · exact absurd ((Submodule.mem_bot ℂ).mp (hb ▸ hvW)) hv0
      · exact ht
    have hKle : carVacuum φ ≤ ℂ ∙ v := by
      intro w hw
      have hwW : w ∈ W := hWtop ▸ Submodule.mem_top
      obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwW
      have := congrArg (fun u => vacProj (carAnnihilation φ) (carCreation φ) (aWord (carAnnihilation φ) (fun _ => 0) u)) hα
      simp only [map_sum, map_smul, hQN hvK] at this
      rw [aWord_zero, ContinuousLinearMap.one_apply, vacProj_apply_of_vacuum hP (mem_carVacuum.mp hw)] at this
      rw [← this, Finset.sum_eq_single (fun _ => 0) (fun y _ hy => by rw [if_neg (Ne.symm hy), smul_zero])
        (by simp), if_pos rfl]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hKeq : carVacuum φ = ℂ ∙ v :=
      le_antisymm hKle ((Submodule.span_singleton_le_iff_mem v _).mpr hvK)
    rw [hKeq]
    exact finrank_span_singleton hv0
  · intro h1 W _ hW
    obtain ⟨hWa, hWc⟩ := invariant_words hW
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨f, rfl⟩ := carFockMap_surjective h w
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hw0
      rw [carFockMap_apply]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hcon x, Submodule.coe_zero, map_zero]
    -- `f x₀ = vacProj (aWord x₀ w) ∈ W`
    have hfx : (f x₀ : E) ∈ W := by
      have hmem := invariant_vacProj hWa hWc _ (invariant_aWord hWa x₀ _ hwW)
      rw [carFockMap_apply, map_sum, map_sum] at hmem
      have hq : ∀ y, vacProj (carAnnihilation φ) (carCreation φ) (aWord (carAnnihilation φ) x₀
          (cWord (carCreation φ) y (f y : E))) = if x₀ = y then (f y : E) else 0 := fun y => hQN (f y).2 x₀ y
      simp only [hq] at hmem
      rwa [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)] at hmem
    -- `K = ℂ f x₀ ⊆ W`, hence every word on `K` lies in `W`
    have hKW : ∀ u ∈ carVacuum φ, u ∈ W := by
      intro u hu
      obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero' (f x₀) hx₀).mp h1 ⟨u, hu⟩
      have : u = r • (f x₀ : E) := by rw [← Submodule.coe_smul, hr]
      rw [this]
      exact W.smul_mem r hfx
    rw [eq_top_iff]
    intro e _
    obtain ⟨g, rfl⟩ := carFockMap_surjective h e
    rw [carFockMap_apply]
    exact W.sum_mem fun x _ => invariant_cWord hWc x _ (hKW _ (g x).2)

end Hilbert

open scoped InnerProductSpace Kronecker
open Matrix

/-! ### Corollary 2: irreducible representations over `ℝ²ⁿ` are unitarily equivalent -/

section Cor2

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The pointwise extension of a unitary `J : K ≃ K'` to `L²(κ; K) ≃ L²(κ; K')` commutes with `B ⊗ 1`. -/
lemma piLpCongrRight_tensorOne {κ : Type*} [Fintype κ] {K K' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] (J : K ≃ₗᵢ[ℂ] K') (B : Matrix κ κ ℂ) (f : PiLp 2 (fun _ : κ => K)) :
    LinearIsometryEquiv.piLpCongrRight 2 (fun _ => J) (tensorOne B f) =
      tensorOne B (LinearIsometryEquiv.piLpCongrRight 2 (fun _ => J) f) := by
  ext x
  simp [tensorOne_apply, LinearIsometryEquiv.piLpCongrRight_apply, map_sum, map_smul]

/-- **Dereziński, Corollary 2, p. 17** (for `ℝ²ⁿ` with its canonical basis): two irreducible representations of the CAR over
`ℝ²ⁿ` on nonzero spaces are unitarily equivalent. -/
theorem car_irreducible_unitarily_equivalent {n : ℕ} [Nontrivial E] [Nontrivial F] {φ : Fin (2 * n) → (E →L[ℂ] E)}
    {ψ : Fin (2 * n) → (F →L[ℂ] F)} (hφ : IsCAROn φ) (hψ : IsCAROn ψ) (hφi : IsIrreducibleCAR φ)
    (hψi : IsIrreducibleCAR ψ) : ∃ V : E ≃ₗᵢ[ℂ] F, ∀ b v, V (φ b v) = ψ b (V v) := by
  have h1 := (isIrreducibleCAR_iff hφ).mp hφi
  have h2 := (isIrreducibleCAR_iff hψ).mp hψi
  haveI : FiniteDimensional ℂ (carVacuum φ) := Module.finite_of_finrank_eq_succ h1
  haveI : FiniteDimensional ℂ (carVacuum ψ) := Module.finite_of_finrank_eq_succ h2
  let J : carVacuum φ ≃ₗᵢ[ℂ] carVacuum ψ :=
    (stdOrthonormalBasis ℂ (carVacuum φ)).equiv (stdOrthonormalBasis ℂ (carVacuum ψ)) (finCongr (h1.trans h2.symm))
  refine ⟨((carUnitary hφ).symm.trans (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin n → Fin 2 => J))).trans
    (carUnitary hψ), fun b v => ?_⟩
  obtain ⟨f, rfl⟩ := (carUnitary hφ).surjective v
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [← carUnitary_intertwines hφ, LinearIsometryEquiv.symm_apply_apply, piLpCongrRight_tensorOne,
    carUnitary_intertwines hψ]

end Cor2

/-! ### Theorem 10, part 2: representations over `ℝ²ⁿ⁺¹` -/

section Odd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The Jordan-Wigner parity** `Iₙ = σ₃ ⊗ ⋯ ⊗ σ₃` (Dereziński, p. 16). -/
noncomputable def jwParity : (n : ℕ) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ
  | 0 => 1
  | n + 1 => (pauli3 ⊗ₖ jwParity n).submatrix (Fin.consEquiv (fun _ => Fin 2)).symm (Fin.consEquiv (fun _ => Fin 2)).symm

/-- `Iₙ` is diagonal with the sign `(-1)^{|x|}` of the configuration. -/
lemma jwParity_apply : ∀ (n : ℕ) (y x : Fin n → Fin 2), jwParity n y x = if y = x then (wordSign x : ℂ) else 0
  | 0, y, x => by rw [Subsingleton.elim y x]; simp [jwParity, wordSign]
  | n + 1, y, x => by
    obtain ⟨t, y', rfl⟩ : ∃ t y', y = Fin.cons t y' := ⟨y 0, Fin.tail y, (Fin.cons_self_tail y).symm⟩
    obtain ⟨s, x', rfl⟩ : ∃ s x', x = Fin.cons s x' := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [jwParity, jw_entry, Fin.cons_zero, Fin.cons_zero, Fin.tail_cons, Fin.tail_cons, jwParity_apply n, wordSign,
      Fin.cons_zero, Fin.tail_cons]
    simp only [Fin.cons_inj]
    rcases fin_two_eq_zero_or_one t with rfl | rfl <;> rcases fin_two_eq_zero_or_one s with rfl | rfl <;>
      by_cases hxy : y' = x' <;> simp [pauli3, hxy]

/-- `B ⊗ T` on `L²(κ; K)`: `(B ⊗ T) f x = ∑ᵧ B x y T (f y)`. -/
noncomputable def tensorOp {κ : Type*} [Fintype κ] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (B : Matrix κ κ ℂ) (T : V →L[ℂ] V) : PiLp 2 (fun _ : κ => V) →ₗ[ℂ] PiLp 2 (fun _ : κ => V) where
  toFun f := WithLp.toLp 2 (fun x => ∑ y, B x y • T (f y))
  map_add' f g := by
    ext x
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' r f := by
    ext x
    simp [Finset.smul_sum, smul_comm r]

lemma tensorOp_apply {κ : Type*} [Fintype κ] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (B : Matrix κ κ ℂ) (T : V →L[ℂ] V) (f : PiLp 2 (fun _ : κ => V)) (x : κ) :
    tensorOp B T f x = ∑ y, B x y • T (f y) := rfl

variable {n : ℕ} {ψ : Fin (2 * n + 1) → (E →L[ℂ] E)}

lemma IsCAROn.castSucc (h : IsCAROn ψ) : IsCAROn (fun b : Fin (2 * n) => ψ b.castSucc) where
  symm b := h.symm _
  anticomm a b := by
    rw [h.anticomm]
    simp only [Fin.castSucc_inj]

/-- The last generator anticommutes with the creation and annihilation operators of the first `2n`. -/
lemma IsCAROn.last_anticomm (h : IsCAROn ψ) (j : Fin n) :
    ψ (Fin.last _) * carCreation (fun b : Fin (2 * n) => ψ b.castSucc) j =
        -(carCreation (fun b : Fin (2 * n) => ψ b.castSucc) j * ψ (Fin.last _)) ∧
      ψ (Fin.last _) * carAnnihilation (fun b : Fin (2 * n) => ψ b.castSucc) j =
        -(carAnnihilation (fun b : Fin (2 * n) => ψ b.castSucc) j * ψ (Fin.last _)) := by
  have hb : ∀ b : Fin (2 * n), ψ (Fin.last _) * ψ b.castSucc = -(ψ b.castSucc * ψ (Fin.last _)) := fun b => by
    have := h.anticomm (Fin.last _) b.castSucc
    rw [if_neg (Fin.castSucc_lt_last b).ne'] at this
    exact eq_neg_of_add_eq_zero_left this
  constructor <;>
    simp only [carCreation, carAnnihilation, majorana, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_sub, sub_mul,
      hb, smul_neg, neg_add, neg_sub, smul_add, smul_sub] <;>
    abel

/-- **Dereziński, Theorem 10, part 2, p. 17**: a representation `(φ₁, …, φ₂ₙ₊₁)` of the CAR over `ℝ²ⁿ⁺¹` is unitarily
equivalent to `(Jordan-Wigner) ⊗ 1_K` on the first `2n` generators and `Iₙ ⊗ T` on the last, for a self-adjoint unitary `T`
of `K` (`T = 1 ⊕ -1` on `K = K₊ ⊕ K₋`, `K± = ker (T ∓ 1)`, `involution_decomposition`). -/
theorem car_odd_unitarily_equivalent (h : IsCAROn ψ) :
    ∃ (U : PiLp 2 (fun _ : Fin n → Fin 2 => carVacuum (fun b : Fin (2 * n) => ψ b.castSucc)) ≃ₗᵢ[ℂ] E)
      (T : carVacuum (fun b : Fin (2 * n) => ψ b.castSucc) →L[ℂ] carVacuum (fun b : Fin (2 * n) => ψ b.castSucc)),
      T * T = 1 ∧ (∀ v w, ⟪T v, w⟫_ℂ = ⟪v, T w⟫_ℂ) ∧
      (∀ b f, U (tensorOne (jordanWigner n b) f) = ψ b.castSucc (U f)) ∧
      ∀ f, U (tensorOp (jwParity n) T f) = ψ (Fin.last _) (U f) := by
  set φ : Fin (2 * n) → (E →L[ℂ] E) := fun b => ψ b.castSucc with hφdef
  have hφ : IsCAROn φ := h.castSucc
  have hK : ∀ v : carVacuum φ, ψ (Fin.last _) (v : E) ∈ carVacuum φ := by
    intro v
    rw [mem_carVacuum]
    intro j
    rw [← ContinuousLinearMap.mul_apply, show carAnnihilation φ j * ψ (Fin.last _) =
      -(ψ (Fin.last _) * carAnnihilation φ j) from by rw [(h.last_anticomm j).2, neg_neg],
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply, mem_carVacuum.mp v.2 j, map_zero, neg_zero]
  let T : carVacuum φ →L[ℂ] carVacuum φ := ((ψ (Fin.last _)).comp (carVacuum φ).subtypeL).codRestrict _ hK
  have hT : ∀ v, (T v : E) = ψ (Fin.last _) v := fun v => rfl
  refine ⟨carUnitary hφ, T, ?_, ?_, carUnitary_intertwines hφ, ?_⟩
  · ext v
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hT]
    rw [← ContinuousLinearMap.mul_apply]
    have := h.anticomm (Fin.last _) (Fin.last _)
    rw [if_pos rfl, ← two_smul ℂ (ψ (Fin.last _) * ψ (Fin.last _))] at this
    rw [smul_right_injective _ (two_ne_zero : (2 : ℂ) ≠ 0) this, ContinuousLinearMap.one_apply]
  · intro v w
    rw [Submodule.coe_inner, Submodule.coe_inner, hT, hT, h.symm]
  · intro f
    rw [carUnitary_apply, carUnitary_apply, carFockMap_apply, carFockMap_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hw := mul_cWord (z := ψ (Fin.last _)) (c := carCreation φ) (fun k => (h.last_anticomm k).1) x
    rw [← ContinuousLinearMap.mul_apply (ψ (Fin.last _)), hw, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.mul_apply, tensorOp_apply]
    simp only [jwParity_apply, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Submodule.coe_smul,
      hT, map_smul]
    rw [Int.cast_smul_eq_zsmul]

/-- A self-adjoint unitary `T` splits `K` into the orthogonal eigenspaces `K₊ = ker (T - 1)` and `K₋ = ker (T + 1)`. -/
theorem involution_decomposition {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (T : K →L[ℂ] K)
    (hT : T * T = 1) (hs : ∀ v w, ⟪T v, w⟫_ℂ = ⟪v, T w⟫_ℂ) :
    LinearMap.ker ((T - 1 : K →L[ℂ] K) : K →ₗ[ℂ] K) ⊔ LinearMap.ker ((T + 1 : K →L[ℂ] K) : K →ₗ[ℂ] K) = ⊤ ∧
      ∀ u ∈ LinearMap.ker ((T - 1 : K →L[ℂ] K) : K →ₗ[ℂ] K), ∀ w ∈ LinearMap.ker ((T + 1 : K →L[ℂ] K) : K →ₗ[ℂ] K), ⟪u, w⟫_ℂ = 0 := by
  have hTT : ∀ v, T (T v) = v := fun v => by rw [← ContinuousLinearMap.mul_apply, hT, ContinuousLinearMap.one_apply]
  constructor
  · rw [eq_top_iff]
    intro v _
    have hv : v = (1 / 2 : ℂ) • (v + T v) + (1 / 2 : ℂ) • (v - T v) := by module
    rw [hv]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        map_smul, map_add, hTT,
        add_comm (T v) v, sub_self]
    · rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
        map_smul, map_sub, hTT,
        ← smul_add, show T v - v + (v - T v) = 0 by abel, smul_zero]
  · intro u hu w hw
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      sub_eq_zero] at hu
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      add_eq_zero_iff_eq_neg] at hw
    have h1 : ⟪u, w⟫_ℂ = -⟪u, w⟫_ℂ := by
      conv_lhs => rw [← hu]
      rw [hs, hw, inner_neg_right]
    have h2 : (2 : ℂ) * ⟪u, w⟫_ℂ = 0 := by rw [two_mul]; nth_rewrite 1 [h1]; ring
    simpa using h2

end Odd

/-- A matrix representation of the CAR is a representation by operators on Euclidean space. -/
theorem IsCARRep.isCAROn_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} {φ : Fin m → Matrix ι ι ℂ}
    (h : IsCARRep φ) : IsCAROn (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (φ a)) where
  symm b := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (by
    rw [IsSelfAdjoint, ← map_star, star_eq_conjTranspose, h.selfAdjoint b])
  anticomm a b := by
    have := congrArg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (h.anticomm a b)
    simp only [map_add, map_mul] at this
    rw [this]
    split_ifs <;> simp

/-- The Jordan-Wigner representation, on Euclidean space. -/
theorem isCAROn_jordanWigner (n : ℕ) : IsCAROn (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a)) :=
  (isCARRep_jordanWigner n).isCAROn_toEuclideanCLM

/-- **The Jordan-Wigner representation is irreducible**: by Theorem 10 its multiplicity space has dimension
`2ⁿ / 2ⁿ = 1`. -/
theorem isIrreducibleCAR_jordanWigner (n : ℕ) :
    IsIrreducibleCAR (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a)) := by
  have h := isCAROn_jordanWigner n
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n → Fin 2)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by rw [finrank_euclideanSpace]; exact Fintype.card_pos)
  rw [isIrreducibleCAR_iff h]
  have h1 := ((WithLp.linearEquiv 2 ℂ (∀ _ : Fin n → Fin 2,
    carVacuum (fun a => Matrix.toEuclideanCLM (𝕜 := ℂ) (jordanWigner n a)))).symm.trans
      (carUnitary h).toLinearEquiv).finrank_eq
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, finrank_euclideanSpace] at h1
  exact (Nat.mul_eq_left Fintype.card_pos.ne').mp h1

end Lightlike.OperatorAlgebras
