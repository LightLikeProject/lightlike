import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Proof by reflection: sparse Laurent polynomials over `ℤ`

A computable normaliser for Laurent polynomials in eight variables with integer coefficients
(`Poly`), with soundness lemmas `eval_add`, `eval_neg`, `eval_scale`, `eval_mul` in any
commutative field with non-zero variables. A polynomial identity is checked by computing
`(lhs - rhs).isEmpty` with `decide +kernel`, which adds no axiom beyond Lean's standard ones.
Used for the cleared coefficient identities of the q-Racah recurrence (`RacahCert0.lean` to `RacahCert12.lean`).
-/

namespace Lightlike.TV.Refl

/-- A Laurent monomial in 8 variables. -/
structure Mono where
  /-- Exponent of variable `0` in the monomial. -/
  e0 : ℤ
  /-- Exponent of variable `1` in the monomial. -/
  e1 : ℤ
  /-- Exponent of variable `2` in the monomial. -/
  e2 : ℤ
  /-- Exponent of variable `3` in the monomial. -/
  e3 : ℤ
  /-- Exponent of variable `4` in the monomial. -/
  e4 : ℤ
  /-- Exponent of variable `5` in the monomial. -/
  e5 : ℤ
  /-- Exponent of variable `6` in the monomial. -/
  e6 : ℤ
  /-- Exponent of variable `7` in the monomial. -/
  e7 : ℤ
deriving DecidableEq

/-- Product of two monomials: the exponents add. -/
def Mono.mul (m n : Mono) : Mono :=
  ⟨m.e0 + n.e0, m.e1 + n.e1, m.e2 + n.e2, m.e3 + n.e3, m.e4 + n.e4, m.e5 + n.e5, m.e6 + n.e6,
    m.e7 + n.e7⟩

/-- lexicographic comparison: `0` less, `1` equal, `2` greater. -/
def cmpZ (a b : ℤ) : ℕ :=
  match a - b with
  | Int.ofNat 0 => 1
  | Int.ofNat (_ + 1) => 2
  | Int.negSucc _ => 0

theorem cmpZ_eq {a b : ℤ} (h : cmpZ a b = 1) : a = b := by
  unfold cmpZ at h
  split at h
  · rename_i heq; have : a - b = 0 := by simpa using heq
    omega
  · simp at h
  · simp at h

/-- Total order on monomials, as a natural-number code, used to keep polynomials sorted. -/
def Mono.cmp (m n : Mono) : ℕ :=
  if m.e0 ≠ n.e0 then cmpZ m.e0 n.e0 else
  if m.e1 ≠ n.e1 then cmpZ m.e1 n.e1 else
  if m.e2 ≠ n.e2 then cmpZ m.e2 n.e2 else
  if m.e3 ≠ n.e3 then cmpZ m.e3 n.e3 else
  if m.e4 ≠ n.e4 then cmpZ m.e4 n.e4 else
  if m.e5 ≠ n.e5 then cmpZ m.e5 n.e5 else
  if m.e6 ≠ n.e6 then cmpZ m.e6 n.e6 else cmpZ m.e7 n.e7

theorem Mono.eq_of_cmp {m n : Mono} (h : m.cmp n = 1) : m = n := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := m
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := n
  simp only [Mono.cmp] at h
  simp only [Mono.mk.injEq]
  split_ifs at h <;> (have := cmpZ_eq h; omega)

/-- A Laurent polynomial in the eight variables, as a list of monomials with integer coefficients. -/
abbrev Poly := List (Mono × ℤ)

section Eval
variable {K : Type*} [Field K]

/-- the 8 variable values -/
structure Env (K : Type*) where
  /-- Value assigned to variable `0`. -/
  v0 : K
  /-- Value assigned to variable `1`. -/
  v1 : K
  /-- Value assigned to variable `2`. -/
  v2 : K
  /-- Value assigned to variable `3`. -/
  v3 : K
  /-- Value assigned to variable `4`. -/
  v4 : K
  /-- Value assigned to variable `5`. -/
  v5 : K
  /-- Value assigned to variable `6`. -/
  v6 : K
  /-- Value assigned to variable `7`. -/
  v7 : K

/-- The environment assigns nonzero values to all eight variables. -/
structure Env.NZ (E : Env K) : Prop where
  h0 : E.v0 ≠ 0
  h1 : E.v1 ≠ 0
  h2 : E.v2 ≠ 0
  h3 : E.v3 ≠ 0
  h4 : E.v4 ≠ 0
  h5 : E.v5 ≠ 0
  h6 : E.v6 ≠ 0
  h7 : E.v7 ≠ 0

/-- Value of a monomial in an environment. -/
def Mono.eval (E : Env K) (m : Mono) : K :=
  E.v0 ^ m.e0 * E.v1 ^ m.e1 * E.v2 ^ m.e2 * E.v3 ^ m.e3 * E.v4 ^ m.e4 * E.v5 ^ m.e5 *
    E.v6 ^ m.e6 * E.v7 ^ m.e7

theorem Mono.eval_mul {E : Env K} (hE : E.NZ) (m n : Mono) :
    (m.mul n).eval E = m.eval E * n.eval E := by
  unfold Mono.eval Mono.mul
  simp only [zpow_add₀ hE.h0, zpow_add₀ hE.h1, zpow_add₀ hE.h2, zpow_add₀ hE.h3, zpow_add₀ hE.h4,
    zpow_add₀ hE.h5, zpow_add₀ hE.h6, zpow_add₀ hE.h7]
  ring

/-- Value of a polynomial in an environment. -/
def Poly.eval (E : Env K) : Poly → K
  | [] => 0
  | (m, a) :: p => (a : K) * m.eval E + Poly.eval E p

end Eval

/-- merge-add with fuel -/
def addP : ℕ → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, p, [] => p
  | f + 1, (m, a) :: p, (n, b) :: q =>
    match m.cmp n with
    | 0 => (m, a) :: addP f p ((n, b) :: q)
    | 1 => if a + b = 0 then addP f p q else (m, a + b) :: addP f p q
    | _ => (n, b) :: addP f ((m, a) :: p) q

theorem eval_append {K : Type*} [Field K] (E : Env K) (p q : Poly) :
    Poly.eval E (p ++ q) = Poly.eval E p + Poly.eval E q := by
  induction p with
  | nil => simp [Poly.eval]
  | cons t p ih => obtain ⟨m, a⟩ := t; simp [Poly.eval, ih]; ring

theorem eval_addP {K : Type*} [Field K] (E : Env K) :
    ∀ (f : ℕ) (p q : Poly), Poly.eval E (addP f p q) = Poly.eval E p + Poly.eval E q := by
  intro f
  induction f with
  | zero => intro p q; simp [addP, eval_append]
  | succ f ih =>
    intro p q
    rcases p with _ | ⟨⟨m, a⟩, p⟩
    · simp [addP, Poly.eval]
    rcases q with _ | ⟨⟨n, b⟩, q⟩
    · simp [addP, Poly.eval]
    simp only [addP]
    split
    · simp [Poly.eval, ih]; ring
    · rename_i hc
      have hmn := Mono.eq_of_cmp hc
      subst hmn
      split_ifs with hab
      · simp only [Poly.eval, ih]
        have : (a : K) = -(b : K) := by
          have : (a + b : ℤ) = 0 := hab
          have h2 : ((a + b : ℤ) : K) = 0 := by rw [this]; simp
          push_cast at h2; linear_combination h2
        rw [this]; ring
      · simp [Poly.eval, ih]; ring
    · simp [Poly.eval, ih]; ring


/-- Sum of two polynomials. -/
def add (p q : Poly) : Poly := addP (p.length + q.length + 1) p q

/-- A polynomial multiplied by a monomial with an integer coefficient. -/
def scale (t : Mono × ℤ) (q : Poly) : Poly := q.map fun s => (t.1.mul s.1, t.2 * s.2)

/-- Negative of a polynomial. -/
def neg (p : Poly) : Poly := p.map fun s => (s.1, -s.2)

/-- divide and conquer product, `f` bounds the depth (any value is sound). -/
def mulAux : ℕ → Poly → Poly → Poly
  | 0, p, q => p.foldr (fun t acc => add (scale t q) acc) []
  | _ + 1, [], _ => []
  | _ + 1, [t], q => scale t q
  | f + 1, p, q => add (mulAux f (p.take (p.length / 2)) q) (mulAux f (p.drop (p.length / 2)) q)

/-- Product of two polynomials. -/
def mul (p q : Poly) : Poly := mulAux (p.length + 1) p q

theorem eval_add {K : Type*} [Field K] (E : Env K) (p q : Poly) :
    Poly.eval E (add p q) = Poly.eval E p + Poly.eval E q := eval_addP E _ p q

theorem eval_neg {K : Type*} [Field K] (E : Env K) (p : Poly) :
    Poly.eval E (neg p) = - Poly.eval E p := by
  induction p with
  | nil => simp [neg, Poly.eval]
  | cons t p ih => obtain ⟨m, a⟩ := t; simp only [neg, List.map_cons] at ih ⊢; simp [Poly.eval] at ih ⊢; rw [ih]; ring

theorem eval_scale {K : Type*} [Field K] {E : Env K} (hE : E.NZ) (t : Mono × ℤ) (q : Poly) :
    Poly.eval E (scale t q) = ((t.2 : ℤ) : K) * Mono.eval E t.1 * Poly.eval E q := by
  induction q with
  | nil => simp [scale, Poly.eval]
  | cons s q ih =>
    obtain ⟨n, b⟩ := s
    simp only [scale, List.map_cons] at ih ⊢
    simp only [Poly.eval, Mono.eval_mul hE] at ih ⊢
    rw [ih]; push_cast; ring

theorem eval_mulAux {K : Type*} [Field K] {E : Env K} (hE : E.NZ) :
    ∀ (f : ℕ) (p q : Poly), Poly.eval E (mulAux f p q) = Poly.eval E p * Poly.eval E q := by
  intro f
  induction f with
  | zero =>
    intro p q
    induction p with
    | nil => simp [mulAux, Poly.eval]
    | cons t p ih =>
      simp only [mulAux, List.foldr_cons] at ih ⊢
      rw [eval_add, eval_scale hE, ih]
      obtain ⟨m, a⟩ := t
      simp [Poly.eval]; ring
  | succ f ih =>
    intro p q
    rcases p with _ | ⟨t, _ | ⟨t2, p⟩⟩
    · simp [mulAux, Poly.eval]
    · rw [mulAux, eval_scale hE]; obtain ⟨m, a⟩ := t; simp [Poly.eval]
    · rw [mulAux, eval_add, ih, ih, ← add_mul, ← eval_append, List.take_append_drop]
      all_goals simp
  
theorem eval_mul {K : Type*} [Field K] {E : Env K} (hE : E.NZ) (p q : Poly) :
    Poly.eval E (mul p q) = Poly.eval E p * Poly.eval E q := eval_mulAux hE _ p q

end Lightlike.TV.Refl
