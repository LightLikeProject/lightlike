import Lightlike.TuraevViro.QSixJ

/-!
# The quantum 15j symbol at a root of unity (QU2)

The 15j symbol of the first kind (`Lightlike.Recoupling.fifteenJ`, a sum over one spin `x` of five 6j symbols) with the
6j symbols replaced by the quantum 6j symbols `qSixJ` at `q = e^{iπ/r}` and the weight `x + 1` by the quantum dimension
`[x + 1]_q`: the vertex weight of the Crane-Yetter state sum (Crane, Kauffman, Yetter, *J. Knot Theory Ramifications* 6
(1997) 177; not read, no comparison with it is claimed).

* `qFifteenJ r a b c`: `(-1)^(S/2) Σ_x [x+1] Π_t {a_t b_t x; b_{t+1} a_{t+1} c_t}_q`, closure `(a₅, b₅) = (b₀, a₀)`;
* `qFifteenJ_eq_zero_of_not_adm`: the symbol vanishes unless every term has admissible triads, here the triad `(a₀ b₀ x)`
  restricted to the first six-j symbol (for all `x` the first factor needs `qAdm r (a 0) (b 0) x`);
* `qFifteenJ_zero`: all spins zero give `1` at every level `r ≥ 2`.

The Crane-Yetter state sum on a 4-complex and its invariance under the Pachner moves are NOT here; invariance needs the
q-Biedenharn-Elliott identity (`qBiedenharnElliott`, `Lightlike.TV`), a hypothesis of this library.
-/

open Finset

namespace Lightlike.TV

/-- The **quantum 15j symbol of the first kind** (doubled spins) at `q = e^{iπ/r}`. -/
noncomputable def qFifteenJ (r : ℕ) (a b c : Fin 5 → ℕ) : ℝ :=
  (-1) ^ ((∑ t, (a t + b t + c t)) / 2) *
    ∑ x ∈ range (a 0 + b 0 + 1), qnum r (x + 1) *
      (qSixJ r (a 0) (b 0) x (b 1) (a 1) (c 0) * qSixJ r (a 1) (b 1) x (b 2) (a 2) (c 1) *
        qSixJ r (a 2) (b 2) x (b 3) (a 3) (c 2) * qSixJ r (a 3) (b 3) x (b 4) (a 4) (c 3) *
          qSixJ r (a 4) (b 4) x (a 0) (b 0) (c 4))

/-- The terms of the quantum 15j symbol vanish unless the triad `(a₀ b₀ x)` is admissible. -/
lemma qFifteenJ_term_eq_zero {r : ℕ} {a b c : Fin 5 → ℕ} {x : ℕ} (h : ¬ qAdm r (a 0) (b 0) x) :
    qSixJ r (a 0) (b 0) x (b 1) (a 1) (c 0) = 0 := by
  by_contra hne
  exact h (qSixJ_ok hne).1

/-- **The quantum 15j symbol of all zero spins is `1`.** -/
theorem qFifteenJ_zero (r : ℕ) (hr : 2 ≤ r) : qFifteenJ r 0 0 0 = 1 := by
  have h6 : qSixJ r 0 0 0 0 0 0 = 1 := by
    have hadm : qAdm r 0 0 0 := ⟨by simp [Pentagon.Tri], by omega⟩
    simp [qSixJ, hadm, qDelta, qRacahSum, qRacahTerm, qfact, invQFact, qnum_one hr]
  have hq : qnum r 1 = 1 := qnum_one hr
  simp [qFifteenJ, h6, hq]

end Lightlike.TV
