import Mathlib
import Lightlike.TemperleyLieb.QNumbers
import Lightlike.TemperleyLieb.Expansion

/-!
# The Kauffman–Lins recoupling coefficient

Kauffman and Lins (*Temperley–Lieb recoupling theory and invariants of 3-manifolds*, 1994, Chapters 6
and 7; not read here, the formulas are fixed by the numerical comparison below) evaluate the theta net and the
tetrahedral net of Jones–Wenzl projectors as explicit quantum-factorial expressions, and the
recoupling coefficient of the two bracketings of three blocks as `Tet · Δ_i / (θ θ)`. This file
defines these expressions over a field, with `[n] = qb q n` and `[n]! = qfac q n` of `QNumbers`:

* `thetaKL q a b c = (-1)^s [s+1]! [s-c]! [s-a]! [s-b]! / ([a]! [b]! [c]!)`, `s = (a+b+c)/2`
  (the theta net of the colours `a, b, c`, doubled spins);
* `deltaKL q n = (-1)^n [n+1]` (the loop value of the projector `p_n`);
* `tetKL q a b c D i j`, the tetrahedral net with faces `(a,b,i), (i,c,D), (b,c,j), (a,j,D)`:
  `(Π_{l,k} [B_l - F_k]! / ([a]! [b]! [c]! [D]! [i]! [j]!)) · Σ_z (-1)^z [z+1]! / (Π_k [z - F_k]! Π_l [B_l - z]!)`,
  with the face half-perimeters `F_k` and the sums `B_l` of two pairs of opposite edges, halved;
* `klCoef q a b c e d f d'`, in the indexing of `Fc` (`Expansion.lean`): blocks `a, b, c`, the first
  bracketing with `e` arcs between `a, b` (channel `i = a+b-2e`) and `d` arcs between `i, c` (total
  `D = i+c-2d`), the second with `f` arcs between `b, c` (channel `j = b+c-2f`) and `d'` arcs between
  `a, j`; it is `tetKL · deltaKL i / (thetaKL a b i · thetaKL i c D)` on the admissible indices and
  `0` elsewhere.

Numerical evidence (not proof): with the library's model of the Temperley–Lieb operators re-implemented
on bit strings at a random complex `q`, `Fc q a b c e d f d' = klCoef q a b c e d f d'` in all 342 admissible
cases with `a, b, c ≤ 3` (error at most `1.2e-15`, signs included), and `kapRec = thetaKL / deltaKL`
(`kapRec_eq`). The identity `Fc = klCoef` is the target of the recursion in the third block; `FcEqKL k` states it
for a field `k` (a statement, not an assumption of this file).
-/

namespace Lightlike.TemperleyLieb

open Finset

variable {k : Type*} [Field k]

/-- The theta net `θ(a, b, c)` of Kauffman–Lins (doubled spins, `s = (a+b+c)/2`). -/
noncomputable def thetaKL (q : kˣ) (a b c : ℕ) : k :=
  (-1) ^ ((a + b + c) / 2) * qfac q ((a + b + c) / 2 + 1) * qfac q ((a + b + c) / 2 - c) *
    qfac q ((a + b + c) / 2 - a) * qfac q ((a + b + c) / 2 - b) / (qfac q a * qfac q b * qfac q c)

/-- The loop value `Δ_n = (-1)^n [n+1]` of the projector on `n` strands. -/
noncomputable def deltaKL (q : kˣ) (n : ℕ) : k := (-1) ^ n * qb q (n + 1)

/-- The summand of the tetrahedral net at `z`, for the face sums `F₁ … F₄` and the opposite-pair sums
`B₁ B₂ B₃`: `(-1)^z [z+1]! / (Π [z - F_k]! Π [B_l - z]!)` (used for `max F ≤ z ≤ min B`). -/
noncomputable def tetTerm (q : kˣ) (F₁ F₂ F₃ F₄ B₁ B₂ B₃ z : ℕ) : k :=
  (-1) ^ z * qfac q (z + 1) /
    (qfac q (z - F₁) * qfac q (z - F₂) * qfac q (z - F₃) * qfac q (z - F₄) *
      (qfac q (B₁ - z) * qfac q (B₂ - z) * qfac q (B₃ - z)))

/-- The prefactor `Π_{l,k} [B_l - F_k]! / ([a]! [b]! [c]! [D]! [i]! [j]!)` of the tetrahedral net. -/
noncomputable def tetPre (q : kˣ) (a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ : ℕ) : k :=
  (qfac q (B₁ - F₁) * qfac q (B₁ - F₂) * qfac q (B₁ - F₃) * qfac q (B₁ - F₄)) *
    (qfac q (B₂ - F₁) * qfac q (B₂ - F₂) * qfac q (B₂ - F₃) * qfac q (B₂ - F₄)) *
    (qfac q (B₃ - F₁) * qfac q (B₃ - F₂) * qfac q (B₃ - F₃) * qfac q (B₃ - F₄)) /
    (qfac q a * qfac q b * qfac q c * qfac q D * qfac q i * qfac q j)

/-- **The tetrahedral net** of Kauffman–Lins with the faces `(a,b,i), (i,c,D), (b,c,j), (a,j,D)`; the
opposite edge pairs are `(a,c), (b,D), (i,j)`. -/
noncomputable def tetKL (q : kˣ) (a b c D i j : ℕ) : k :=
  let F₁ := (a + b + i) / 2
  let F₂ := (i + c + D) / 2
  let F₃ := (b + c + j) / 2
  let F₄ := (a + j + D) / 2
  let B₁ := (b + D + i + j) / 2
  let B₂ := (a + c + i + j) / 2
  let B₃ := (a + b + c + D) / 2
  tetPre q a b c D i j F₁ F₂ F₃ F₄ B₁ B₂ B₃ *
    ∑ z ∈ Icc (max (max F₁ F₂) (max F₃ F₄)) (min B₁ (min B₂ B₃)), tetTerm q F₁ F₂ F₃ F₄ B₁ B₂ B₃ z

/-- The admissible indices of `klCoef`: both bracketings exist and have the same total channel. -/
def KLAdm (a b c e d f d' : ℕ) : Prop :=
  e ≤ min a b ∧ d ≤ min (a + b - 2 * e) c ∧ f ≤ min b c ∧ d' ≤ min a (b + c - 2 * f) ∧
    a + b - 2 * e + c - 2 * d = a + (b + c - 2 * f) - 2 * d'

instance (a b c e d f d' : ℕ) : Decidable (KLAdm a b c e d f d') := by
  unfold KLAdm; infer_instance

/-- **The Kauffman–Lins recoupling coefficient** in the indexing of `Fc`: `Tet · Δ_i / (θ(a,b,i) θ(i,c,D))`
with `i = a+b-2e`, `D = i+c-2d`, `j = b+c-2f`, and `0` on non-admissible indices. -/
noncomputable def klCoef (q : kˣ) (a b c e d f d' : ℕ) : k :=
  if KLAdm a b c e d f d' then
    tetKL q a b c (a + b - 2 * e + c - 2 * d) (a + b - 2 * e) (b + c - 2 * f) * deltaKL q (a + b - 2 * e) /
      (thetaKL q a b (a + b - 2 * e) * thetaKL q (a + b - 2 * e) c (a + b - 2 * e + c - 2 * d))
  else 0

/-- **The statement `Fc = klCoef`** over the field `k`: at every `q` with `q^{2n} ≠ 1` for `1 ≤ n ≤ 2(a + b + c) + 6`,
the recoupling coefficient `Fc` of the Temperley–Lieb model equals the Kauffman–Lins coefficient on the admissible
indices. It is proved for every field of characteristic zero by `Fc_eq_klCoef` (`RecouplingKL.lean`); stated at
generic `q`, it is recorded here for the results that use it; the genericity
bound is the one the proof by the recursion in the third block needs (its telescoping certificate uses quantum
integers up to `a + 2b + c + 3`). At `q = e^{iπ/r}` the identities are reached by the limit `θ → π/r`, where every
such finite condition holds. -/
def FcEqKL (k : Type*) [Field k] : Prop :=
  ∀ (q : kˣ) (a b c e d f d' : ℕ), (∀ n, 1 ≤ n → n ≤ 2 * (a + b + c) + 6 → (q : k) ^ (2 * n) ≠ 1) →
    KLAdm a b c e d f d' → Fc q a b c e d f d' = klCoef q a b c e d f d'

end Lightlike.TemperleyLieb
