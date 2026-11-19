import Lightlike.FieldTheory.ZeroDim.GraphEval
import Lightlike.FieldTheory.ZeroDim.MapsEGF
import Physlib.Mathematics.ForMathlib.Fin.Involutions

/-!
# The Feynman rules of zero-dimensional field theory with a source (Borinsky, Chapter 7, pp. 116-117)

Borinsky writes the partition function of a scalar theory with interaction `V` and source `j` as the formal integral
`Z(ħ, j) = ∫ dx/√(2πħ) e^{(-x²/2 + V(x) + xj)/ħ}`, "a formal expansion in `ħ` and `j`", and states that
`W(ħ, j) := ħ log Z(ħ, j)` generates the connected diagrams "as stated in Theorem 2.4.1" (p. 117).

Here the vertex weights are a sequence `μ d` in a commutative `ℚ`-algebra (`μ 1 = j` for the source, `μ d = λ_d` for
`V = Σ_d λ_d x^d/d!`). Expanding `e^{(V + xj)/ħ} = Σ_k (Σ_d μ_d x^d/d!)^k/(k! ħ^k)` and integrating `x^n` against the
Gaussian (`(n - 1)!! ħ^{n/2}` for `n` even, `0` for `n` odd), the coefficient of `ħ^{n/2 - k}` coming from `k` vertices
with `n` half-edges in all is `(n - 1)!! [x^n] (Σ_d μ_d x^d/d!)^k / k!`. `formalZ μ` records it as the coefficient of
`X^n Y^k` (`X^n Y^k` stands for `ħ^{n/2 - k}`; the tree graphs give negative powers of `ħ`, so the grading by `n`
and `k` keeps the series formal).

* `fweight μ Γ`: a labelled graph with no legs has the weight `∏_v μ (deg v)`, a graph with a leg the weight `0`; it
  is invariant under relabelling and multiplicative under disjoint union (`isMultWeight_fwC`).
* `gen_X_eq_formalZ`: **`Z` is the sum over all leg-free graphs of their weight over `|Aut Γ|`** (Borinsky's
  Proposition 3.1.1, p. 23, with a source and an arbitrary potential).
* `coeff_formalZ_eq_exp`: **`Z = exp(W/ħ)` with `W/ħ` the sum over the connected graphs**: coefficientwise,
  `Z = Σ_m (W/ħ)^m/m!` with `W/ħ = gen (fwC μ) X_c`.

The logarithm of the bivariate series is not used: `W = ħ log Z` is the same identity read through `log = exp⁻¹` on
series with constant term `1` (the constant term of `formalZ` is `1`, from the empty graph).
-/

open Finset PowerSeries MulAction

noncomputable section

namespace Lightlike.FieldTheory.GraphAlg

variable {A : Type*} [CommRing A] [Algebra ℚ A] {n k : ℕ}

/-- The **degree** of a vertex: the number of half-edges attached to it. -/
def deg (Γ : LGraph n k) (v : Fin k) : ℕ := (univ.filter fun h => Γ.att h = v).card

/-- A graph **has no legs**: its involution has no fixed points. -/
def Legless (Γ : LGraph n k) : Prop := ∀ h, Γ.inv h ≠ h

open Classical in
/-- **The Feynman weight** of a labelled graph: `∏_v μ (deg v)` if it has no legs, `0` otherwise. -/
def fweight (μ : ℕ → A) (Γ : LGraph n k) : A := if Legless Γ then ∏ v, μ (deg Γ v) else 0

lemma deg_smul (g : Relabel n k) (Γ : LGraph n k) (v : Fin k) : deg (g • Γ) v = deg Γ (g.2.symm v) := by
  unfold deg
  refine (Finset.card_equiv g.1 fun h => ?_).symm
  simp only [mem_filter, mem_univ, true_and, smul_att, Function.comp_apply, Equiv.symm_apply_apply]
  exact (Equiv.apply_eq_iff_eq_symm_apply g.2).symm

lemma legless_smul (g : Relabel n k) (Γ : LGraph n k) : Legless (g • Γ) ↔ Legless Γ := by
  unfold Legless
  simp only [smul_inv, Function.comp_apply]
  constructor
  · intro H h hh
    apply H (g.1 h)
    rw [Equiv.symm_apply_apply, hh]
  · intro H h hh
    apply H (g.1.symm h)
    have := congrArg g.1.symm hh
    rwa [Equiv.symm_apply_apply] at this

/-- The Feynman weight is invariant under relabelling. -/
theorem fweight_smul (μ : ℕ → A) (g : Relabel n k) (Γ : LGraph n k) : fweight μ (g • Γ) = fweight μ Γ := by
  classical
  unfold fweight
  simp only [legless_smul, deg_smul]
  split_ifs
  · exact Equiv.prod_comp g.2.symm (fun v => μ (deg Γ v))
  · rfl

/-- The Feynman weight of a class, through a representative. -/
def fwC (μ : ℕ → A) (c : AnyClass) : A := fweight μ c.2.out

lemma fwC_mk (μ : ℕ → A) (Γ : LGraph n k) : fwC μ ⟨(n, k), ⟦Γ⟧⟩ = fweight μ Γ := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel (Relabel n k) (LGraph n k)) Γ
  rw [fwC]
  simp only
  rw [← hg, fweight_smul]

lemma fweight_of_mem_labOf (μ : ℕ → A) {c : GClass n k} {Γ : LGraph n k} (hΓ : Γ ∈ labOf c) :
    fweight μ Γ = fwC μ ⟨(n, k), c⟩ := by
  rw [← mem_labOf.1 hΓ, fwC_mk]

section Union

variable {n₁ k₁ n₂ k₂ : ℕ} (Γ₁ : LGraph n₁ k₁) (Γ₂ : LGraph n₂ k₂)

lemma union_att_castAdd (i : Fin n₁) : (union Γ₁ Γ₂).att (Fin.castAdd n₂ i) = Fin.castAdd k₂ (Γ₁.att i) := by
  simp [union]

lemma union_att_natAdd (i : Fin n₂) : (union Γ₁ Γ₂).att (Fin.natAdd n₁ i) = Fin.natAdd k₁ (Γ₂.att i) := by
  simp [union]

lemma union_inv_castAdd (i : Fin n₁) : (union Γ₁ Γ₂).inv (Fin.castAdd n₂ i) = Fin.castAdd n₂ (Γ₁.inv i) := by
  simp [union]

lemma union_inv_natAdd (i : Fin n₂) : (union Γ₁ Γ₂).inv (Fin.natAdd n₁ i) = Fin.natAdd n₁ (Γ₂.inv i) := by
  simp [union]

lemma deg_union_castAdd (v : Fin k₁) : deg (union Γ₁ Γ₂) (Fin.castAdd k₂ v) = deg Γ₁ v := by
  unfold deg
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  simp only [union_att_castAdd, union_att_natAdd, Fin.castAdd_inj]
  have : ∀ i : Fin n₂, (Fin.natAdd k₁ (Γ₂.att i) = Fin.castAdd k₂ v) = False := fun i =>
    eq_false (fun h => by have := congrArg Fin.val h; simp at this; omega)
  simp [this]

lemma deg_union_natAdd (v : Fin k₂) : deg (union Γ₁ Γ₂) (Fin.natAdd k₁ v) = deg Γ₂ v := by
  unfold deg
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  simp only [union_att_castAdd, union_att_natAdd, Fin.natAdd_inj]
  have : ∀ i : Fin n₁, (Fin.castAdd k₂ (Γ₁.att i) = Fin.natAdd k₁ v) = False := fun i =>
    eq_false (fun h => by have := congrArg Fin.val h; simp at this; omega)
  simp [this]

lemma legless_union : Legless (union Γ₁ Γ₂) ↔ Legless Γ₁ ∧ Legless Γ₂ := by
  unfold Legless
  constructor
  · intro H
    refine ⟨fun i hi => H (Fin.castAdd n₂ i) ?_, fun i hi => H (Fin.natAdd n₁ i) ?_⟩
    · rw [union_inv_castAdd, hi]
    · rw [union_inv_natAdd, hi]
  · rintro ⟨H₁, H₂⟩ h
    refine Fin.addCases (fun i => ?_) (fun i => ?_) h
    · rw [union_inv_castAdd]; exact fun e => H₁ i (Fin.castAdd_injective _ _ e)
    · rw [union_inv_natAdd]; exact fun e => H₂ i (Fin.natAdd_injective _ _ e)

/-- The Feynman weight is multiplicative under disjoint union. -/
theorem fweight_union (μ : ℕ → A) : fweight μ (union Γ₁ Γ₂) = fweight μ Γ₁ * fweight μ Γ₂ := by
  classical
  unfold fweight
  rw [Fin.prod_univ_add]
  simp only [deg_union_castAdd, deg_union_natAdd]
  by_cases h₁ : Legless Γ₁ <;> by_cases h₂ : Legless Γ₂ <;>
    simp [legless_union, h₁, h₂]

end Union

/-- **The Feynman weight is a multiplicative weight on the classes.** -/
theorem isMultWeight_fwC (μ : ℕ → A) : IsMultWeight (fwC μ) where
  union {n₁ k₁ n₂ k₂} c₁ c₂ := by
    induction c₁ using Quotient.inductionOn with
    | h Γ₁ =>
      induction c₂ using Quotient.inductionOn with
      | h Γ₂ =>
        show fwC μ ⟨(n₁ + n₂, k₁ + k₂), ⟦union Γ₁ Γ₂⟧⟩ = _
        rw [fwC_mk, fwC_mk, fwC_mk, fweight_union]
  empty c := by
    classical
    rw [fwC]
    unfold fweight
    split_ifs with h
    · simp
    · exact (h (by intro x; exact x.elim0)).elim

/-- `(n - 1)!!` for `n` even, `0` for `n` odd: the number of fixed-point-free involutions of `Fin n`. -/
def dfact (n : ℕ) : ℕ := if Even n then (n - 1).doubleFactorial else 0

lemma card_fpf_involutions (n : ℕ) :
    Fintype.card {f : Fin n → Fin n // Function.Involutive f ∧ ∀ i, f i ≠ i} = dfact n := by
  unfold dfact
  split_ifs with h
  · exact Physlib.Fin.involutionNoFixed_card_even n h
  · exact Physlib.Fin.involutionNoFixed_card_odd n (Nat.not_even_iff_odd.1 h)

/-- A labelled graph is an attachment map and an involution. -/
def equivAttInv : LGraph n k ≃ (Fin n → Fin k) × {f : Fin n → Fin n // Function.Involutive f} where
  toFun Γ := (Γ.att, ⟨Γ.inv, Γ.invol⟩)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The sum of the Feynman weights over all labelled graphs**: `(n - 1)!! · n! [x^n] (Σ_d μ_d x^d/d!)^k`. -/
theorem sum_fweight (μ : ℕ → A) :
    ∑ Γ : LGraph n k, fweight μ Γ =
      algebraMap ℚ A (dfact n : ℚ) * (algebraMap ℚ A (n.factorial : ℚ) * coeff n (egf μ ^ k)) := by
  classical
  rw [← equivAttInv.symm.sum_comp, Fintype.sum_prod_type]
  have hw : ∀ (f : Fin n → Fin k) (i : {f : Fin n → Fin n // Function.Involutive f}),
      fweight μ (equivAttInv.symm (f, i)) =
        (∏ v, μ ((univ.filter fun h => f h = v).card)) * (if ∀ h, i.1 h ≠ h then (1 : A) else 0) := by
    intro f i
    unfold fweight
    by_cases h : ∀ h, i.1 h ≠ h
    · rw [if_pos (show Legless (equivAttInv.symm (f, i)) from h), if_pos h, mul_one]
      rfl
    · rw [if_neg (show ¬Legless (equivAttInv.symm (f, i)) from h), if_neg h, mul_zero]
  simp_rw [hw, ← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_maps_prod_fiber n (fun _ => μ), Fin.prod_const]
  have hc : (∑ i : {f : Fin n → Fin n // Function.Involutive f}, if ∀ h, i.1 h ≠ h then (1 : A) else 0) =
      algebraMap ℚ A (dfact n : ℚ) := by
    rw [Finset.sum_boole, map_natCast, ← card_fpf_involutions]
    congr 1
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun f : Fin n → Fin n => Function.Involutive f)
      (fun f => ∀ i, f i ≠ i))
  rw [hc]
  ring

/-- **The weighted sum over the leg-free graphs with `n` half-edges and `k` vertices**, each over `|Aut Γ|`:
`(n - 1)!! [x^n] (Σ_d μ_d x^d/d!)^k / k!`. -/
theorem coeff_gen_fwC_X (μ : ℕ → A) (n k : ℕ) :
    coeff k (coeff n (gen (fwC μ) X)) =
      algebraMap ℚ A ((dfact n : ℚ) / k.factorial) * coeff n (egf μ ^ k) := by
  classical
  rw [coeff_gen]
  have h1 : ∀ c : GClass n k, algebraMap ℚ A (X ⟨(n, k), c⟩) * fwC μ ⟨(n, k), c⟩ =
      algebraMap ℚ A ((n.factorial : ℚ) * k.factorial)⁻¹ * ∑ Γ ∈ labOf c, fweight μ Γ := by
    intro c
    rw [X_eq_lab, Finset.sum_congr rfl fun Γ hΓ => fweight_of_mem_labOf μ hΓ, Finset.sum_const, ← lab,
      nsmul_eq_mul, div_eq_mul_inv, map_mul, map_natCast]
    ring
  simp_rw [h1, ← Finset.mul_sum]
  rw [show (∑ c : GClass n k, ∑ Γ ∈ labOf c, fweight μ Γ) = ∑ Γ : LGraph n k, fweight μ Γ from
    Finset.sum_fiberwise univ (fun Γ => (⟦Γ⟧ : GClass n k)) (fweight μ), sum_fweight]
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  congr 1
  congr 1
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hk : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp

/-- **The formal partition function with a source** (Borinsky, p. 116), with vertex weights `μ`: the coefficient of
`X^n Y^k` (standing for `ħ^{n/2 - k}`) is the Gaussian moment `(n - 1)!!` of `x^n` times the coefficient of `x^n` in
`(Σ_d μ_d x^d/d!)^k/k!`, i.e. the term of `∫ dx/√(2πħ) e^{-x²/(2ħ)} (V(x) + xj)^k/(k! ħ^k)` with `x^n`, for
`μ 1 = j` and `μ d = λ_d`. -/
def formalZ (μ : ℕ → A) : PowerSeries (PowerSeries A) :=
  PowerSeries.mk fun n => PowerSeries.mk fun k =>
    algebraMap ℚ A ((dfact n : ℚ) / k.factorial) * coeff n (egf μ ^ k)

/-- **The partition function is the sum over the leg-free graphs with `1/|Aut Γ|`** (Borinsky's Proposition 3.1.1,
p. 23, for an arbitrary potential with a source). -/
theorem gen_X_eq_formalZ (μ : ℕ → A) : gen (fwC μ) X = formalZ μ := by
  ext n k
  rw [coeff_gen_fwC_X]
  simp [formalZ]

/-- **`W = ħ log Z` generates the connected graphs** (Borinsky, p. 117, "as stated in Theorem 2.4.1"), in the form
`Z = exp(W/ħ)`: coefficientwise, `Z = Σ_m (W/ħ)^m/m!` with `W/ħ = gen (fwC μ) X_c`, the weighted sum over the
connected leg-free graphs with `1/|Aut γ|`. -/
theorem coeff_formalZ_eq_exp (μ : ℕ → A) (n k : ℕ) :
    coeff k (coeff n (formalZ μ)) =
      ∑ m ∈ range (k + 1), algebraMap ℚ A ((m.factorial : ℚ)⁻¹) * coeff k (coeff n (gen (fwC μ) Xc ^ m)) := by
  rw [← gen_X_eq_formalZ, coeff_gen_X (isMultWeight_fwC μ)]

end Lightlike.FieldTheory.GraphAlg
