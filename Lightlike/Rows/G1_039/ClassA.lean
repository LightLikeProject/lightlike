import Lightlike.Rows.G1_039.Scaling

/-!
# Class A: the six normal forms

For `a = 0` the diagonal matrix `n = diag(λ₀, λ₁, λ₂)` is brought, by rescaling the basis
(`λ_i ↦ sign λ_i`), permuting the basis vectors and a global sign change `n ↦ -n`, to one of the six
normal forms `0` (Bianchi I), `diag(1,0,0)` (II), `diag(1,-1,0)` (VI₀), `diag(1,1,0)` (VII₀),
`diag(1,1,-1)` (VIII), `diag(1,1,1)` (IX).

## Main results

* `Lightlike.Rows.G1_039.exists_sign_scale`: rescaling a diagonal `n` to entries in `{0, ±1}`.
* `Lightlike.Rows.G1_039.exists_classA_normal`: the six class A normal forms.

## References

* heinzle-uggla-2009a (Section 3)
-/

namespace Lightlike.Rows.G1_039

open Matrix

theorem exists_scale_one (x : ℝ) :
    ∃ e : ℝ, e ≠ 0 ∧ (x = 0 → x * e ^ 2 = 0) ∧ (0 < x → x * e ^ 2 = 1) ∧
      (x < 0 → x * e ^ 2 = -1) := by
  by_cases h0 : x = 0
  · exact ⟨1, one_ne_zero, fun _ => by simp [h0], fun h => absurd h0 h.ne', fun h => absurd h0 h.ne⟩
  · have hpos : 0 < |x| := abs_pos.mpr h0
    have hs : 0 < Real.sqrt |x| := Real.sqrt_pos.mpr hpos
    have hsq : (1 / Real.sqrt |x|) ^ 2 = 1 / |x| := by
      rw [div_pow, Real.sq_sqrt hpos.le, one_pow]
    refine ⟨1 / Real.sqrt |x|, by positivity, fun h => absurd h h0, fun h => ?_, fun h => ?_⟩
    · rw [hsq, abs_of_pos h]
      field_simp
    · rw [hsq, abs_of_neg h]
      field_simp

/-- Rescaling a diagonal bracket so that all entries of `n` become `0` or `±1` (with the same
sign as before). -/
theorem exists_sign_scale (l : Fin 3 → ℝ) :
    ∃ d s : Fin 3 → ℝ, (∀ i, d i ≠ 0) ∧ (∀ i, l i * d i ^ 2 / (d 0 * d 1 * d 2) = s i) ∧
      ∀ i, (l i = 0 ∧ s i = 0) ∨ (0 < l i ∧ s i = 1) ∨ (l i < 0 ∧ s i = -1) := by
  choose e he0 he1 he2 he3 using fun i => exists_scale_one (l i)
  have hD : e 0 * e 1 * e 2 ≠ 0 := mul_ne_zero (mul_ne_zero (he0 0) (he0 1)) (he0 2)
  refine ⟨fun i => e i / (e 0 * e 1 * e 2),
    fun i => if l i = 0 then 0 else if 0 < l i then 1 else -1, fun i => div_ne_zero (he0 i) hD,
    fun i => ?_, fun i => ?_⟩
  · have key : l i * (e i / (e 0 * e 1 * e 2)) ^ 2 /
        (e 0 / (e 0 * e 1 * e 2) * (e 1 / (e 0 * e 1 * e 2)) * (e 2 / (e 0 * e 1 * e 2))) =
        l i * e i ^ 2 := by
      have := he0 0
      have := he0 1
      have := he0 2
      field_simp
    simp only
    rw [key]
    rcases lt_trichotomy (l i) 0 with h | h | h
    · rw [he3 i h]
      simp [h.ne, not_lt.mpr h.le]
    · rw [he1 i h]
      simp [h]
    · rw [he2 i h]
      simp [h.ne', h]
  · rcases lt_trichotomy (l i) 0 with h | h | h
    · right; right; exact ⟨h, by simp [h.ne, not_lt.mpr h.le]⟩
    · left; exact ⟨h, by simp [h]⟩
    · right; left; exact ⟨h, by simp [h.ne', h]⟩

/-- The six normal forms of the diagonal of `n` in class A. -/
def ClassANormal (t : Fin 3 → ℝ) : Prop :=
  t = ![0, 0, 0] ∨ t = ![1, 0, 0] ∨ t = ![1, -1, 0] ∨ t = ![1, 1, 0] ∨ t = ![1, 1, -1] ∨
    t = ![1, 1, 1]

/-- `ClassAGood x y z`: `diag(x, y, z)` with `a = 0` is isomorphic to a class A normal form. -/
def ClassAGood (x y z : ℝ) : Prop :=
  ∃ t : Fin 3 → ℝ, ClassANormal t ∧ BracketIso (diagonal ![x, y, z]) 0 (diagonal t) 0

theorem ClassAGood.sw01 {x y z : ℝ} (h : ClassAGood y x z) : ClassAGood x y z := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, BracketIso.trans ?_ h⟩
  have h1 := bracketIso_swap01 ![x, y, z] 0
  have e : (![-(0 : V3) 1, -(0 : V3) 0, -(0 : V3) 2] : V3) = 0 := by
    ext i
    fin_cases i <;> simp
  rw [e] at h1
  simpa using h1

theorem ClassAGood.sw12 {x y z : ℝ} (h : ClassAGood x z y) : ClassAGood x y z := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, BracketIso.trans ?_ h⟩
  have h1 := bracketIso_swap12 ![x, y, z] 0
  have e : (![-(0 : V3) 0, -(0 : V3) 2, -(0 : V3) 1] : V3) = 0 := by
    ext i
    fin_cases i <;> simp
  rw [e] at h1
  simpa using h1

theorem ClassAGood.neg {x y z : ℝ} (h : ClassAGood (-x) (-y) (-z)) : ClassAGood x y z := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, BracketIso.trans ?_ h⟩
  have h1 := bracketIso_diagonal_scale ![x, y, z] 0 (fun _ => -1) (fun _ => by norm_num)
  have e1 : (fun i : Fin 3 => ![x, y, z] i * (-1 : ℝ) ^ 2 / (-1 * -1 * -1)) = ![-x, -y, -z] := by
    funext i
    fin_cases i <;> simp [div_neg]
  have e2 : (fun i : Fin 3 => (0 : V3) i / (-1 : ℝ)) = 0 := by
    funext i
    simp
  beta_reduce at h1
  rw [e1, e2] at h1
  exact h1

theorem classAGood_base (x y z : ℝ) (h : ClassANormal ![x, y, z]) : ClassAGood x y z :=
  ⟨![x, y, z], h, BracketIso.refl _ _⟩

/-- Integer-indexed version of `ClassAGood` (so that case analysis is cheap). -/
structure ClassAGoodZ (p q r : ℤ) : Prop where
  good : ClassAGood p q r

theorem ClassAGoodZ.sw01 {p q r : ℤ} (h : ClassAGoodZ q p r) : ClassAGoodZ p q r :=
  ⟨ClassAGood.sw01 h.good⟩

theorem ClassAGoodZ.sw12 {p q r : ℤ} (h : ClassAGoodZ p r q) : ClassAGoodZ p q r :=
  ⟨ClassAGood.sw12 h.good⟩

theorem ClassAGoodZ.neg {p q r : ℤ} (h : ClassAGoodZ (-p) (-q) (-r)) : ClassAGoodZ p q r := by
  refine ⟨ClassAGood.neg ?_⟩
  simpa using h.good

theorem classAGoodZ_all (p q r : ℤ) (hp : p = 0 ∨ p = 1 ∨ p = -1) (hq : q = 0 ∨ q = 1 ∨ q = -1)
    (hr : r = 0 ∨ r = 1 ∨ r = -1) : ClassAGoodZ p q r := by
  have b0 : ClassAGoodZ 0 0 0 := ⟨by simpa using classAGood_base 0 0 0 (by simp [ClassANormal])⟩
  have b1 : ClassAGoodZ 1 0 0 := ⟨by simpa using classAGood_base 1 0 0 (by simp [ClassANormal])⟩
  have b2 : ClassAGoodZ 1 (-1) 0 :=
    ⟨by simpa using classAGood_base 1 (-1) 0 (by simp [ClassANormal])⟩
  have b3 : ClassAGoodZ 1 1 0 := ⟨by simpa using classAGood_base 1 1 0 (by simp [ClassANormal])⟩
  have b4 : ClassAGoodZ 1 1 (-1) :=
    ⟨by simpa using classAGood_base 1 1 (-1) (by simp [ClassANormal])⟩
  have b5 : ClassAGoodZ 1 1 1 := ⟨by simpa using classAGood_base 1 1 1 (by simp [ClassANormal])⟩
  have c1 : ClassAGoodZ (-1) 0 0 := ClassAGoodZ.neg (by simpa using b1)
  have c2 : ClassAGoodZ (-1) 1 0 := ClassAGoodZ.neg (by simpa using b2)
  have c3 : ClassAGoodZ (-1) (-1) 0 := ClassAGoodZ.neg (by simpa using b3)
  have c4 : ClassAGoodZ (-1) (-1) 1 := ClassAGoodZ.neg (by simpa using b4)
  have c5 : ClassAGoodZ (-1) (-1) (-1) := ClassAGoodZ.neg (by simpa using b5)
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    rcases hr with rfl | rfl | rfl <;>
    solve_by_elim (maxDepth := 8) [ClassAGoodZ.sw01, ClassAGoodZ.sw12]

theorem classAGood_all (x y z : ℝ) (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1)
    (hz : z = 0 ∨ z = 1 ∨ z = -1) : ClassAGood x y z := by
  have key : ∀ x : ℝ, (x = 0 ∨ x = 1 ∨ x = -1) → ∃ p : ℤ, x = p ∧ (p = 0 ∨ p = 1 ∨ p = -1) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨1, by simp, by simp⟩
    · exact ⟨-1, by simp, by simp⟩
  obtain ⟨p, rfl, hp⟩ := key x hx
  obtain ⟨q, rfl, hq⟩ := key y hy
  obtain ⟨r, rfl, hr⟩ := key z hz
  exact (classAGoodZ_all p q r hp hq hr).good

/-- Every class A diagonal bracket is isomorphic to one of the six normal forms. -/
theorem exists_classA_normal (l : Fin 3 → ℝ) :
    ∃ t : Fin 3 → ℝ, ClassANormal t ∧ BracketIso (diagonal l) 0 (diagonal t) 0 := by
  obtain ⟨d, s, hd, hs, hsign⟩ := exists_sign_scale l
  have hs' : ∀ i, s i = 0 ∨ s i = 1 ∨ s i = -1 := by
    intro i
    rcases hsign i with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨t, ht, h⟩ := classAGood_all (s 0) (s 1) (s 2) (hs' 0) (hs' 1) (hs' 2)
  refine ⟨t, ht, BracketIso.trans ?_ h⟩
  have h1 := bracketIso_diagonal_scale l 0 d hd
  have e1 : (fun i => l i * d i ^ 2 / (d 0 * d 1 * d 2)) = ![s 0, s 1, s 2] := by
    funext i
    rw [hs i]
    fin_cases i <;> rfl
  have e2 : (fun i => (0 : V3) i / d i) = 0 := by
    funext i
    simp
  rw [e1, e2] at h1
  exact h1

end Lightlike.Rows.G1_039
