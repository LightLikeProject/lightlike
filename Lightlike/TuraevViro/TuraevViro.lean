import Lightlike.TuraevViro.Model
import Lightlike.TuraevViro.QSixJ

/-!
# The Turaev–Viro state sum

At `q = e^{iπ/r}` (`r ≥ 3`), the Turaev–Viro model (*Topology* 31 (1992) 865) is Ponzano–Regge
with three changes:
* integers become quantum integers;
* 6j symbols become quantum 6j symbols;
* spins are cut off at level `r - 2`.

Every sum is then finite, and the state sum is normalised by `W⁻¹` per vertex, with
`W = Σ_J [J + 1]²`.

## Main results

* `tvModel r`: the 6j model. Proven here: the fusion count (`tv_count`, from `sum_qAdm_qnum`) and
  that all dimensions are positive (`tv_dim_ne`).
* `turaevViro r K`: the normalised state sum of a complex `K`.
* `turaevViro_move23`: invariant under the 2-3 move, **given** `qBiedenharnElliott r`.
* `turaevViro_move14`: invariant under the 1-4 move, **given** `qBiedenharnElliott r` and
  `qOrthogonality r`.

## Implementation notes

**Hypotheses.** `qBiedenharnElliott r` and `qOrthogonality r`, the q-analogues of the identities
proven classically for the Ponzano–Regge model. They are proven for `r = 3`
(`qBiedenharnElliott_three`, `qOrthogonality_three`, `LevelOne.lean`); for `r ≥ 4` they are the
proof tasks T-QU1-P1 to P6 (`Tasks/QU/`). The classical proofs go through sl₂ Clebsch–Gordan
coefficients (Physlib). The quantum proofs would need U_q(sl₂) representation theory or
q-hypergeometric summation, and neither exists in Mathlib or Physlib.

Evidence: `scripts/tv_check.py` verifies both, and the moves themselves, at `r = 3, …, 6` to
40 digits. Replacing quantum dimensions by integers breaks all of them.

## References

* `turaev-1994`, Chapter VI (6j symbols) and Chapter VII (state sums).
-/

open Finset Lightlike.Pentagon Lightlike.PR

namespace Lightlike.TV

/-- **The Turaev–Viro 6j model** at `q = e^{iπ/r}`: colours `0, …, r - 2`, the q-6j symbol,
quantum dimensions `[J + 1]`, admissibility at level `r - 2`. -/
noncomputable def tvModel (r : ℕ) (hr : 2 ≤ r) : Model where
  N := r - 1
  f := qSixJ r
  dim J := qnum r (J + 1)
  ok := qAdm r
  okDec := fun _ _ _ => inferInstance
  ok_tri := fun h => h.1
  ok_swap12 := qAdm_swap12
  ok_swap23 := qAdm_swap23
  ok_lt := fun h => by unfold qAdm Tri at h; omega
  f_ok := qSixJ_ok
  swap12 := qSixJ_swap12 r
  swap23 := qSixJ_swap23 r
  flip12 := qSixJ_flip12 r

variable {r : ℕ} (hr : 2 ≤ r)

/-- The fusion count holds for the Turaev–Viro model (proven). -/
theorem tv_count : (tvModel r hr).Count := fun p d hp hd =>
  sum_qAdm_qnum hr (by simp only [tvModel] at hp; omega) (by simp only [tvModel] at hd; omega)

/-- All quantum dimensions `[J + 1]`, `J ≤ r - 2`, are positive (proven). -/
theorem tv_dim_ne : ∀ J, J < (tvModel r hr).N → (tvModel r hr).dim J ≠ 0 := fun J hJ =>
  (qnum_pos hr (by omega) (by simp only [tvModel] at hJ; omega)).ne'

/-- The q-Biedenharn–Elliott identity at `q = e^{iπ/r}` (**hypothesis**; checked numerically). -/
def qBiedenharnElliott : Prop := (tvModel r hr).BE

/-- Diagonal q-6j orthogonality at `q = e^{iπ/r}` (**hypothesis**; checked numerically). -/
def qOrthogonality : Prop := (tvModel r hr).Orth

/-- **The Turaev–Viro state sum** `W^{-#vertices} Σ_colourings ∏ (-1)^J [J+1] ∏ signs ∏ {6j}_q`. -/
noncomputable def turaevViro {V : Type*} [DecidableEq V] (K : Complex3 V) : ℝ := (tvModel r hr).Z K

/-- **Turaev–Viro is invariant under the 2-3 move**, given q-Biedenharn–Elliott. -/
theorem turaevViro_move23 (hBE : qBiedenharnElliott hr) {V : Type*} [DecidableEq V]
    (K : Complex3 V) {A B C D E : V} (h : IsMove23 K A B C D E) :
    turaevViro hr (move23 K h) = turaevViro hr K :=
  (tvModel r hr).Z_move23 hBE K h

/-- **Turaev–Viro is invariant under the 1-4 move**, given q-Biedenharn–Elliott and
q-orthogonality. -/
theorem turaevViro_move14 (hBE : qBiedenharnElliott hr) (hOrth : qOrthogonality hr)
    {V : Type*} [DecidableEq V] (K : Complex3 V) {A B C D E : V} (h : IsMove14 K A B C D E) :
    turaevViro hr (move14 K h) = turaevViro hr K :=
  (tvModel r hr).Z_move14 hBE hOrth (tv_count hr) (tv_dim_ne hr)
    (by simp only [tvModel]; omega) K h

end Lightlike.TV
