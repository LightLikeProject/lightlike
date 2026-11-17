import Lightlike.TuraevViro.TuraevViroMoves
import Lightlike.TuraevViro.LevelOne

/-!
# Non-vacuity of the Turaev–Viro invariance given q-Biedenharn–Elliott

The hypothesis `qBiedenharnElliott` holds at level `r = 3` (`qBiedenharnElliott_three`), so the two
theorems of `TuraevViroMoves` apply there and give invariance with no remaining hypothesis.
-/

namespace Lightlike.TV
open Lightlike.Pentagon Lightlike.PR

/-- The 1-4 move at level `3`, from the new form with only `qBiedenharnElliott`. -/
theorem turaevViro_move14_of_BE_three {V : Type*} [DecidableEq V] (K : Complex3 V)
    {A B C D E : V} (h : IsMove14 K A B C D E) :
    turaevViro (r := 3) (by norm_num) (move14 K h) = turaevViro (r := 3) (by norm_num) K :=
  turaevViro_move14_of_BE (by norm_num) qBiedenharnElliott_three K h

/-- The 2-3 move at level `3`, from the new form. -/
theorem turaevViro_move23_of_BE_three {V : Type*} [DecidableEq V] (K : Complex3 V)
    {A B C D E : V} (h : IsMove23 K A B C D E) :
    turaevViro (r := 3) (by norm_num) (move23 K h) = turaevViro (r := 3) (by norm_num) K :=
  turaevViro_move23_of_BE (by norm_num) qBiedenharnElliott_three K h

end Lightlike.TV
