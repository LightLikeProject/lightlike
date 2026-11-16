import Lightlike.TuraevViro.Reflect.SixJCoef
import Lightlike.TuraevViro.Reflect.SixJVanish
import Lightlike.TuraevViro.Reflect.SixJRec

/-!
# The recurrence of the q-6j symbol in one colour, in closed form

For fixed `j₁, j₂, j₄, j₅, q` let `Sj y` be the q-Racah sum `SR` of the 6j tuple with third colour
`y` (an integer, so that `y - 2` makes sense at the lower end). With `s = (j₁+j₂+x)/2` and
`t = (j₄+j₅+x)/2` the recurrence in `x` has the coefficients

* `Na = [s-j₂+1][s-j₁+1][t-j₄+1][t-j₅+1]`, `Nc = [s+1][t+1][s-x+1][t-x+1]`,
* `Q₀,Q₁,Q₂ = [x], [x+1], [x+2]` (all times `δ = u - u⁻¹`),
* the middle coefficient `bn` and the eigenvalue `ck (u^(1+q))`,

and only the eigenvalue depends on `q`.
-/

set_option maxRecDepth 100000

namespace Lightlike.TV.Refl

open Lightlike.TV Finset

/-- `bk (u^n)`. -/
noncomputable def bz (r : ℕ) (n : ℤ) : ℂ := bk (uC r ^ n)

/-- `ck (u^n)`. -/
noncomputable def cz (r : ℕ) (n : ℤ) : ℂ := ck (uC r ^ n)

/-- The q-Racah sum of the 6j tuple with third colour `y` (an integer). -/
noncomputable def Sj (r j1 j2 j4 j5 q : ℕ) (y : ℤ) : ℝ :=
  SR r (((j1 : ℤ) + j2 + y) / 2) (((j1 : ℤ) + j5 + q) / 2) (((j4 : ℤ) + j2 + q) / 2)
    (((j4 : ℤ) + j5 + y) / 2) (((j1 : ℤ) + j2 + j4 + j5) / 2) ((y + j2 + j5 + q) / 2)
    ((y + j1 + q + j4) / 2)

lemma qRacahSum_eq_Sj (r j1 j2 x j4 j5 q : ℕ) :
    qRacahSum r j1 j2 x j4 j5 q = Sj r j1 j2 j4 j5 q (x : ℤ) := by
  rw [qRacahSum_eq_SR]
  unfold Sj
  congr 1
  omega

/-- Numerator coefficients and denominators, in terms of `s = (j₁+j₂+x)/2`, `t = (j₄+j₅+x)/2`. -/
noncomputable def jNa (r : ℕ) (j1 j2 j4 j5 s t : ℤ) : ℂ :=
  bz r (s - j2 + 1) * bz r (s - j1 + 1) * bz r (t - j4 + 1) * bz r (t - j5 + 1)

/-- The coefficient `Nc` of the 6j recurrence. -/
noncomputable def jNc (r : ℕ) (x s t : ℤ) : ℂ :=
  bz r (s + 1) * bz r (t + 1) * bz r (s - x + 1) * bz r (t - x + 1)

/-- The middle numerator `bn` of the 6j recurrence. -/
noncomputable def jbn (r : ℕ) (j1 j2 j4 j5 x : ℤ) : ℂ :=
  (cz r (j1 + 1) * cz r (j4 + 1) + cz r (j2 + 1) * cz r (j5 + 1)) * cz r (x + 1)
    - (uC r + (uC r)⁻¹) * (cz r (j1 + 1) * cz r (j5 + 1) + cz r (j2 + 1) * cz r (j4 + 1))

section
variable (r : ℕ) (a1 a2 a3 a4 b2 b3 : ℤ)

lemma rcR_fNa' (e1 e2 e3 e4 : ℤ) (h1 : 1 - a3 + b3 = e1) (h2 : 1 - a2 + b2 = e2)
    (h3 : 1 - a3 + b2 = e3) (h4 : 1 - a2 + b3 = e4) :
    rcR r a1 a2 a3 a4 b2 b3 fNa = bz r e1 * bz r e2 * bz r e3 * bz r e4 := by
  subst h1 h2 h3 h4; exact rcR_fNa r a1 a2 a3 a4 b2 b3

lemma rcR_fNc' (e1 e2 e3 e4 : ℤ) (h1 : 1 + a1 = e1) (h2 : 1 + a4 = e2)
    (h3 : 1 + a1 + a2 + a3 - b2 - b3 = e3) (h4 : 1 + a2 + a3 + a4 - b2 - b3 = e4) :
    rcR r a1 a2 a3 a4 b2 b3 fNc = bz r e1 * bz r e2 * bz r e3 * bz r e4 := by
  subst h1 h2 h3 h4; exact rcR_fNc r a1 a2 a3 a4 b2 b3

lemma rcR_fCq' (e : ℤ) (h : 1 - a1 - a4 + b2 + b3 = e) :
    rcR r a1 a2 a3 a4 b2 b3 fCq = cz r e := by
  subst h; exact rcR_fCq r a1 a2 a3 a4 b2 b3

lemma rcR_fQ0' (e : ℤ) (h : b2 + b3 - a2 - a3 = e) :
    rcR r a1 a2 a3 a4 b2 b3 fQ0 = bz r e := by
  subst h; exact rcR_fQ0 r a1 a2 a3 a4 b2 b3

lemma rcR_fQ1' (e : ℤ) (h : 1 + b2 + b3 - a2 - a3 = e) :
    rcR r a1 a2 a3 a4 b2 b3 fQ1 = bz r e := by
  subst h; exact rcR_fQ1 r a1 a2 a3 a4 b2 b3

lemma rcR_fQ2' (e : ℤ) (h : 2 + b2 + b3 - a2 - a3 = e) :
    rcR r a1 a2 a3 a4 b2 b3 fQ2 = bz r e := by
  subst h; exact rcR_fQ2 r a1 a2 a3 a4 b2 b3

lemma rcR_fbn' (j1 j2 j4 j5 x : ℤ) (h1 : 1 + a1 + a2 - b2 = j1 + 1)
    (h2 : 1 + a3 + a4 - b2 = j4 + 1) (h3 : 1 + a1 + a3 - b3 = j2 + 1)
    (h4 : 1 + a2 + a4 - b3 = j5 + 1) (h5 : 1 - a2 - a3 + b2 + b3 = x + 1) :
    rcR r a1 a2 a3 a4 b2 b3 fbn = jbn r j1 j2 j4 j5 x := by
  rw [rcR_fbn, h1, h2, h3, h4, h5]; rfl

end

/-- **The recurrence of the q-6j symbol in its third colour**, in closed form. The hypotheses
`1 ≤ x ≤ r - 3` keep the quantum integers `[x], [x+1], [x+2]` nonzero. -/
theorem sixj_row {r : ℕ} (hr : 2 ≤ r) (j1 j2 x j4 j5 q : ℕ) (h1 : qAdm r j1 j2 x)
    (h2 : qAdm r j1 j5 q) (h3 : qAdm r j4 j2 q) (h4 : qAdm r j4 j5 x) (hx1 : 1 ≤ x)
    (hx2 : x + 3 ≤ r) :
    2 * (jNa r j1 j2 j4 j5 (((j1 : ℤ) + j2 + x) / 2) (((j4 : ℤ) + j5 + x) / 2) / 2 /
          (bz r (x + 1) * bz r (x + 2))) * (Sj r j1 j2 j4 j5 q (x + 2) : ℂ)
      + 2 * (jbn r j1 j2 j4 j5 x / (2 * bz r x * bz r (x + 2))) * (Sj r j1 j2 j4 j5 q x : ℂ)
      + 2 * (jNc r x (((j1 : ℤ) + j2 + x) / 2) (((j4 : ℤ) + j5 + x) / 2) / 2 /
          (bz r x * bz r (x + 1))) * (Sj r j1 j2 j4 j5 q (x - 2) : ℂ)
      - cz r (1 + q) * (Sj r j1 j2 j4 j5 q x : ℂ) = 0 := by
  unfold qAdm Lightlike.Pentagon.Tri at h1 h2 h3 h4
  have key := real_recurrence hr (((j1 : ℤ) + j2 + x) / 2) (((j1 : ℤ) + j5 + q) / 2)
    (((j4 : ℤ) + j2 + q) / 2) (((j4 : ℤ) + j5 + x) / 2) (((j1 : ℤ) + j2 + j4 + j5) / 2)
    (((x : ℤ) + j2 + j5 + q) / 2) (((x : ℤ) + j1 + q + j4) / 2) (by omega)
    ((max (max ((j1 + j2 + x) / 2) ((j1 + j5 + q) / 2)) (max ((j4 + j2 + q) / 2) ((j4 + j5 + x) / 2)) - 1 : ℕ))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
    (by intro k hk0 hk2 hdvd; have := Int.le_of_dvd (by omega) hdvd; omega)
  rw [rcR_fNa' r _ _ _ _ _ _ (((j1 : ℤ) + j2 + x) / 2 - j2 + 1) (((j1 : ℤ) + j2 + x) / 2 - j1 + 1)
      (((j4 : ℤ) + j5 + x) / 2 - j4 + 1) (((j4 : ℤ) + j5 + x) / 2 - j5 + 1)
      (by omega) (by omega) (by omega) (by omega),
    rcR_fNc' r _ _ _ _ _ _ (((j1 : ℤ) + j2 + x) / 2 + 1) (((j4 : ℤ) + j5 + x) / 2 + 1)
      (((j1 : ℤ) + j2 + x) / 2 - x + 1) (((j4 : ℤ) + j5 + x) / 2 - x + 1)
      (by omega) (by omega) (by omega) (by omega),
    rcR_fCq' r _ _ _ _ _ _ (1 + q) (by omega),
    rcR_fQ0' r _ _ _ _ _ _ x (by omega), rcR_fQ1' r _ _ _ _ _ _ (x + 1) (by omega),
    rcR_fQ2' r _ _ _ _ _ _ (x + 2) (by omega),
    rcR_fbn' r _ _ _ _ _ _ j1 j2 j4 j5 x (by omega) (by omega) (by omega) (by omega)
      (by omega)] at key
  have ep : Sj r j1 j2 j4 j5 q (x + 2) = SR r (((j1 : ℤ) + j2 + x) / 2 + 1) (((j1 : ℤ) + j5 + q) / 2)
      (((j4 : ℤ) + j2 + q) / 2) (((j4 : ℤ) + j5 + x) / 2 + 1) (((j1 : ℤ) + j2 + j4 + j5) / 2)
      (((x : ℤ) + j2 + j5 + q) / 2 + 1) (((x : ℤ) + j1 + q + j4) / 2 + 1) := by
    unfold Sj; congr 1 <;> omega
  have em : Sj r j1 j2 j4 j5 q (x - 2) = SR r (((j1 : ℤ) + j2 + x) / 2 - 1) (((j1 : ℤ) + j5 + q) / 2)
      (((j4 : ℤ) + j2 + q) / 2) (((j4 : ℤ) + j5 + x) / 2 - 1) (((j1 : ℤ) + j2 + j4 + j5) / 2)
      (((x : ℤ) + j2 + j5 + q) / 2 - 1) (((x : ℤ) + j1 + q + j4) / 2 - 1) := by
    unfold Sj; congr 1 <;> omega
  rw [ep, em]
  unfold jNa jNc
  exact key

end Lightlike.TV.Refl
