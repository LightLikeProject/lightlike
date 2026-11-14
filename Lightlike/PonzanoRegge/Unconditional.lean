module

public import Lightlike.PonzanoRegge.Amplitude
public import Lightlike.PonzanoRegge.BEZero

/-!
# The 2-3 move without hypotheses

`weight_move23` needs the one instance `BEAt col A B C D E` of Biedenharn–Elliott that the
colouring uses. `Lightlike.Pentagon.biedenharnElliott_pos` proves that instance whenever the six edges
`AD, AE, BE, CD, AB, CA` carry nonzero spin (the BE letters `a, b, c, e, p, r`). So for those
colourings the Ponzano–Regge weight is invariant under the 2-3 move **unconditionally**.

Since `Lightlike.Pentagon.biedenharnElliott` (`BEZero.lean`) proves the identity for **all** spins, the
theorems below make the 2-3 invariance unconditional for every colouring, and for the cut-off
amplitude.
-/

@[expose] public section

open Finset

namespace Lightlike.PR

variable {V : Type*} [DecidableEq V]

/-- `BEAt` holds when the six edges `AD, AE, BE, CD, AB, CA` carry nonzero spin. -/
theorem beAt_of_pos (col : Colouring V) {A B C D E : V} (hAD : 0 < col {A, D})
    (hAE : 0 < col {A, E}) (hBE : 0 < col {B, E}) (hCD : 0 < col {C, D}) (hAB : 0 < col {A, B})
    (hCA : 0 < col {C, A}) : BEAt col A B C D E :=
  Lightlike.Pentagon.biedenharnElliott_pos hAD hAE hBE hCD hAB hCA

/-- **Unconditional 2-3 invariance** of the Ponzano–Regge weight, for every colouring with nonzero
spins on `AD, AE, BE, CD, AB, CA` (any spins, including zero, elsewhere). -/
theorem weight_move23_of_pos (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E)
    (col : Colouring V) (hAD : 0 < col {A, D}) (hAE : 0 < col {A, E}) (hBE : 0 < col {B, E})
    (hCD : 0 < col {C, D}) (hAB : 0 < col {A, B}) (hCA : 0 < col {C, A}) :
    weight K col = ∑ x ∈ range (col {A, D} + col {A, E} + 1),
      weight (move23 K h) (Function.update col {D, E} x) :=
  weight_move23 K h col (beAt_of_pos col hAD hAE hBE hCD hAB hCA)

/-- **The 2-3 Pachner move leaves the Ponzano–Regge weight invariant**, with no hypothesis: for
every complex, every admissible 2-3 move and every colouring. -/
theorem weight_move23_unconditional (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E)
    (col : Colouring V) :
    weight K col = ∑ x ∈ range (col {A, D} + col {A, E} + 1),
      weight (move23 K h) (Function.update col {D, E} x) :=
  weight_move23 K h col (beAt_of_biedenharnElliott Lightlike.Pentagon.biedenharnElliott col A B C D E)

/-- The same with the new edge summed over all spins (`tsum`), unconditionally. -/
theorem weight_move23_tsum_unconditional (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) (col : Colouring V) :
    ∑' x, weight (move23 K h) (Function.update col {D, E} x) = weight K col :=
  weight_move23_tsum Lightlike.Pentagon.biedenharnElliott K h col

/-- **The cut-off Ponzano–Regge amplitude of `K` equals the sum over the new edge of the 2-3
move**, unconditionally. Only the edges of `K` are cut off at `L`; the new edge `DE` is summed
over all its spins (`tsum`, of finite support), so this is not an equality of two cut-off
amplitudes. -/
theorem amplitude_move23_unconditional (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) (L : ℕ) :
    amplitude K L = ∑ c ∈ K.edges.pi (fun _ => range (L + 1)),
      ∑' x, weight (move23 K h)
        (Function.update (fun e => if he : e ∈ K.edges then c e he else 0) {D, E} x) :=
  amplitude_move23 Lightlike.Pentagon.biedenharnElliott K h L

end Lightlike.PR
