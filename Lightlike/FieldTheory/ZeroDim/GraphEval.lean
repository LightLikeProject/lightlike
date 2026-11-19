import Lightlike.FieldTheory.ZeroDim.GraphExp
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Feynman rules on the algebra of graphs: multiplicative weights and their generating functions

A weight `w` on the isomorphism classes of graphs with values in a commutative `ℚ`-algebra `A` is **multiplicative**
(`IsMultWeight`) if it is `1` on the empty graph and multiplies under disjoint union. Its generating function sends a
formal sum of graphs `a` to the bivariate power series `gen w a = Σ_{n, k} (Σ_{c with n half-edges, k vertices}
a(c) w(c)) X^n Y^k` (`gen`), finite in every coefficient. It is multiplicative (`gen_mul`, `gen_one`, `gen_pow`), so
the exponential formula `X = e^{X_c}` (`expXc_eq_X`) becomes, for every multiplicative weight (Borinsky, Theorem 2.4.1
with the Feynman rules applied, as used in Chapter 7, p. 117):

* `coeff_gen_X`: `gen w X = Σ_m (gen w X_c)^m / m!` coefficientwise, where the terms with `m > k` vanish at `Y^k`
  (`coeff_gen_pow_Xc_eq_zero`): the weighted sum over all graphs is the exponential of the weighted sum over the
  connected graphs.
-/

open Finset PowerSeries

noncomputable section

namespace Lightlike.FieldTheory.GraphAlg

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- A weight on isomorphism classes is **multiplicative**: `1` on the empty graph and `w(Γ₁ ⊔ Γ₂) = w(Γ₁) w(Γ₂)`. -/
structure IsMultWeight (w : AnyClass → A) : Prop where
  union : ∀ {n₁ k₁ n₂ k₂ : ℕ} (c₁ : GClass n₁ k₁) (c₂ : GClass n₂ k₂),
    w ⟨(n₁ + n₂, k₁ + k₂), unionC c₁ c₂⟩ = w ⟨(n₁, k₁), c₁⟩ * w ⟨(n₂, k₂), c₂⟩
  empty : ∀ c : GClass 0 0, w ⟨(0, 0), c⟩ = 1

/-- **The generating function** of a formal sum of graphs under a weight: the coefficient of `X^n Y^k` is the
weighted sum over the classes with `n` half-edges and `k` vertices. -/
def gen (w : AnyClass → A) (a : GAlg) : PowerSeries (PowerSeries A) :=
  PowerSeries.mk fun n => PowerSeries.mk fun k =>
    ∑ c : GClass n k, algebraMap ℚ A (a ⟨(n, k), c⟩) * w ⟨(n, k), c⟩

variable {w : AnyClass → A}

lemma coeff_gen (a : GAlg) (n k : ℕ) :
    coeff k (coeff n (gen w a)) = ∑ c : GClass n k, algebraMap ℚ A (a ⟨(n, k), c⟩) * w ⟨(n, k), c⟩ := by
  simp [gen]

open Classical in
/-- Summing an indicator of a class over the classes of the same size. -/
lemma sum_class_ite {p q : ℕ × ℕ} (h : p = q) (u : GClass p.1 p.2) (f : AnyClass → A) :
    ∑ c : GClass q.1 q.2, (if (⟨p, u⟩ : AnyClass) = ⟨q, c⟩ then f ⟨q, c⟩ else 0) = f ⟨p, u⟩ := by
  subst h
  have : ∀ c : GClass p.1 p.2, ((⟨p, u⟩ : AnyClass) = ⟨p, c⟩) ↔ u = c := fun c => by
    constructor
    · intro hc; exact eq_of_heq (Sigma.mk.inj hc).2
    · rintro rfl; rfl
  simp_rw [this]
  simp

/-- **The generating function is multiplicative.** -/
theorem gen_mul (hw : IsMultWeight w) (a b : GAlg) : gen w (mul a b) = gen w a * gen w b := by
  ext n k
  rw [coeff_gen, PowerSeries.coeff_mul, map_sum]
  simp_rw [PowerSeries.coeff_mul, coeff_gen, Finset.sum_mul_sum]
  simp only [mul, map_sum, apply_ite (algebraMap ℚ A), map_zero, map_mul, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  have h : ((p.1 + p.2, q.1 + q.2) : ℕ × ℕ) = (n, k) := by
    rw [mem_antidiagonal] at hp hq; rw [hp, hq]
  refine (sum_class_ite h (unionC c₁ c₂) (fun d => algebraMap ℚ A (a ⟨(p.1, q.1), c₁⟩) *
    algebraMap ℚ A (b ⟨(p.2, q.2), c₂⟩) * w d)).trans ?_
  rw [hw.union]
  ring

/-- The empty graph is the only graph with no half-edges and no vertices. -/
instance : Unique (GClass 0 0) where
  default := ⟦default⟧
  uniq c := Quotient.inductionOn c fun Γ => by rw [Subsingleton.elim Γ default]

/-- **The generating function of the unit** is `1`. -/
theorem gen_one (hw : IsMultWeight w) : gen w one = 1 := by
  ext n k
  rw [coeff_gen, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl, PowerSeries.coeff_one]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, Fintype.sum_unique, one, if_pos rfl, map_one, one_mul, hw.empty]
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [one, if_neg (by simp [hk]), map_zero, zero_mul]
  · rw [if_neg hn, map_zero]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [one, if_neg (by simp [hn]), map_zero, zero_mul]

/-- **The generating function of a power** is the power of the generating function. -/
theorem gen_pow (hw : IsMultWeight w) (a : GAlg) (m : ℕ) : gen w (pow a m) = gen w a ^ m := by
  induction m with
  | zero => rw [pow, gen_one hw, _root_.pow_zero]
  | succ m ih => rw [pow, gen_mul hw, ih, _root_.pow_succ, mul_comm]

/-- The powers of `X_c` beyond the number of vertices vanish. -/
theorem coeff_gen_pow_Xc_eq_zero (hw : IsMultWeight w) {m n k : ℕ} (hm : k < m) :
    coeff k (coeff n (gen w Xc ^ m)) = 0 := by
  rw [← gen_pow hw, coeff_gen]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [pow_Xc_eq, if_neg (by have := ncomp_le c.out; omega), zero_div, map_zero, zero_mul]

/-- **The exponential formula under a multiplicative weight**: the weighted sum over all graphs is the exponential
of the weighted sum over the connected graphs, coefficientwise (`m` runs to the number of vertices; the further terms
vanish by `coeff_gen_pow_Xc_eq_zero`). -/
theorem coeff_gen_X (hw : IsMultWeight w) (n k : ℕ) :
    coeff k (coeff n (gen w X)) =
      ∑ m ∈ range (k + 1), algebraMap ℚ A ((m.factorial : ℚ)⁻¹) * coeff k (coeff n (gen w Xc ^ m)) := by
  simp_rw [← gen_pow hw, coeff_gen, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← expXc_eq_X, expXc]
  simp only [map_sum, Finset.sum_mul, div_eq_mul_inv, map_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

end Lightlike.FieldTheory.GraphAlg
