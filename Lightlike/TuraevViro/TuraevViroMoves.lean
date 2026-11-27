import Lightlike.TuraevViro.TuraevViro
import Lightlike.TuraevViro.Reflect.QDougallAll
import Lightlike.TuraevViro.QBiedenharnElliott

/-!
# Turaev–Viro invariance under the 2-3 and 1-4 moves, given q-Biedenharn–Elliott

`turaevViro_move14` takes two hypotheses, q-Biedenharn–Elliott and q-orthogonality. q-orthogonality is
a theorem at every level (`qOrthogonality_proved`), so the invariance under both moves is stated here
with q-Biedenharn–Elliott as the only hypothesis. This is a separate module because `TuraevViro.lean`
cannot import the file that proves orthogonality.

## Main results

* `turaevViro_move23_of_BE`: invariance under the 2-3 move, given `qBiedenharnElliott`.
* `turaevViro_move14_of_BE`: invariance under the 1-4 move, given `qBiedenharnElliott` only.
* `turaevViro_move23_all`, `turaevViro_move14_all`: the invariance under both moves at every level `r ≥ 2`,
  with no hypothesis (q-Biedenharn–Elliott is `qBiedenharnElliott_all`).
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

variable {r : ℕ} (hr : 2 ≤ r)

/-- **Turaev–Viro is invariant under the 2-3 move**, given q-Biedenharn–Elliott: the statement of
`turaevViro_move23`, placed next to the 1-4 move. -/
theorem turaevViro_move23_of_BE (hBE : qBiedenharnElliott hr) {V : Type*} [DecidableEq V]
    (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) :
    turaevViro hr (move23 K h) = turaevViro hr K :=
  turaevViro_move23 hr hBE K h

/-- **Turaev–Viro is invariant under the 1-4 move**, given q-Biedenharn–Elliott only:
q-orthogonality is `qOrthogonality_proved`. -/
theorem turaevViro_move14_of_BE (hBE : qBiedenharnElliott hr) {V : Type*} [DecidableEq V]
    (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) :
    turaevViro hr (move14 K h) = turaevViro hr K :=
  turaevViro_move14 hr hBE (Lightlike.TV.Refl.qOrthogonality_proved hr) K h

/-- **Turaev–Viro is invariant under the 2-3 move** at every level `r ≥ 2`, with no hypothesis. -/
theorem turaevViro_move23_all {V : Type*} [DecidableEq V] (K : Complex3 V) {A B C D E : V}
    (h : IsMove23 K A B C D E) : turaevViro hr (move23 K h) = turaevViro hr K :=
  turaevViro_move23_of_BE hr (qBiedenharnElliott_all hr) K h

/-- **Turaev–Viro is invariant under the 1-4 move** at every level `r ≥ 2`, with no hypothesis. -/
theorem turaevViro_move14_all {V : Type*} [DecidableEq V] (K : Complex3 V) {A B C D E : V}
    (h : IsMove14 K A B C D E) : turaevViro hr (move14 K h) = turaevViro hr K :=
  turaevViro_move14_of_BE hr (qBiedenharnElliott_all hr) K h

end Lightlike.TV
