import Lightlike.Rows.G3_261.BCJ

/-!
# The four-point KLT relation from BCJ numerators

Row G3-261 (T-PG7). With `s = s₁₂`, `t = s₁₃`, `u = s₁₄` (particles `0,1,2,3` here), the colour-ordered
Parke-Taylor amplitudes `A[1234] = pt1234`, `A[1243] = pt1243` and the kinematic numerators
`n_s, n_t, n_u` of a cubic-graph representation `A[1234] = n_u/u - n_s/s`, `A[1243] = n_s/s - n_t/t`
satisfying the kinematic Jacobi identity `n_s + n_t + n_u = 0`, we prove

* `klt_algebra`: the pure rational identity `n_s²/s + n_t²/t + n_u²/u = -s A[1234] A[1243]`
  (the double copy `n ↦ n²`, i.e. the Kawai-Lewellen-Tye relation at four points);
* `bcjNum_jacobi`, `bcjNum_amp_1234`, `bcjNum_amp_1243`: the numerators `n_s = 0`, `n_t = -t A[1243]`,
  `n_u = u A[1234]` satisfy the Jacobi identity (this is the BCJ relation `bcj_four`) and reproduce the
  amplitudes;
* `klt_four`: with momentum conservation and nonvanishing brackets,
  `n_s²/s + n_t²/t + n_u²/u = -s₁₂ A[1234] A[1243]`.

## References

* H. Kawai, D. C. Lewellen, S.-H. H. Tye, *A relation between tree amplitudes of closed and open
  strings* (1986).
* Z. Bern, J. J. M. Carrasco, H. Johansson, *New relations for gauge-theory amplitudes* (`bcj-2008`).
* H. Elvang, Y. Huang, *Scattering Amplitudes*, arXiv:1308.1697, (3.30).
-/

noncomputable section

namespace Lightlike.Rows.G3_261

open Lightlike.SpinorHelicity

/-- **Four-point KLT as a rational identity.** If `s + t + u = 0`, the numerators satisfy the kinematic
Jacobi identity `n_s + n_t + n_u = 0` and give the amplitudes `A = n_u/u - n_s/s`,
`B = n_s/s - n_t/t`, then the double copy is `n_s²/s + n_t²/t + n_u²/u = -s A B`. -/
theorem klt_algebra {s t u ns nt nu A B : ℂ} (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0)
    (hsum : s + t + u = 0) (jac : ns + nt + nu = 0)
    (hA : A = nu / u - ns / s) (hB : B = ns / s - nt / t) :
    ns ^ 2 / s + nt ^ 2 / t + nu ^ 2 / u = -s * A * B := by
  have hu' : u = -s - t := by linear_combination hsum
  have hnu : nu = -ns - nt := by linear_combination jac
  subst hA hB
  rw [hnu]
  rw [hu'] at hu ⊢
  field_simp
  ring

/-- The BCJ numerator `n_s = 0` of the `s`-channel graph. -/
def bcjNumS (_l _lt : Fin 4 → Fin 2 → ℂ) : ℂ := 0

/-- The BCJ numerator `n_t = -s₁₃ A[1243]` of the `t`-channel graph. -/
def bcjNumT (l lt : Fin 4 → Fin 2 → ℂ) : ℂ := -(sBr l lt 0 2 * pt1243 lt)

/-- The BCJ numerator `n_u = s₁₄ A[1234]` of the `u`-channel graph. -/
def bcjNumU (l lt : Fin 4 → Fin 2 → ℂ) : ℂ := sBr l lt 0 3 * pt1234 lt

/-- The kinematic Jacobi identity `n_s + n_t + n_u = 0` for the BCJ numerators; it is the BCJ amplitude
relation `bcj_four`. -/
theorem bcjNum_jacobi {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt)
    (ha : ∀ a b : Fin 4, a ≠ b → angleBr (lt a) (lt b) ≠ 0) :
    bcjNumS l lt + bcjNumT l lt + bcjNumU l lt = 0 := by
  have := bcj_four h ha
  simp only [bcjNumS, bcjNumT, bcjNumU]
  linear_combination this

/-- The numerators reproduce `A[1234] = n_u/u - n_s/s`. -/
theorem bcjNum_amp_1234 (l lt : Fin 4 → Fin 2 → ℂ) (hs : sBr l lt 0 1 ≠ 0) (hu : sBr l lt 0 3 ≠ 0) :
    pt1234 lt = bcjNumU l lt / sBr l lt 0 3 - bcjNumS l lt / sBr l lt 0 1 := by
  simp only [bcjNumS, bcjNumU]
  field_simp
  ring

/-- The numerators reproduce `A[1243] = n_s/s - n_t/t`. -/
theorem bcjNum_amp_1243 (l lt : Fin 4 → Fin 2 → ℂ) (hs : sBr l lt 0 1 ≠ 0) (ht : sBr l lt 0 2 ≠ 0) :
    pt1243 lt = bcjNumS l lt / sBr l lt 0 1 - bcjNumT l lt / sBr l lt 0 2 := by
  simp only [bcjNumS, bcjNumT]
  field_simp
  ring

/-- All three Mandelstam variables are nonzero when all angle and square brackets are. -/
theorem sBr_ne_zero {l lt : Fin 4 → Fin 2 → ℂ}
    (ha : ∀ a b : Fin 4, a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hq : ∀ a b : Fin 4, a ≠ b → squareBr (l a) (l b) ≠ 0) (i j : Fin 4) (hij : i ≠ j) :
    sBr l lt i j ≠ 0 :=
  mul_ne_zero (ha i j hij) (hq j i hij.symm)

/-- **Four-point KLT relation** (Kawai-Lewellen-Tye, in the BCJ double-copy form): with momentum
conservation and nonvanishing angle and square brackets, the double copy of the BCJ numerators
is `-s₁₂ A[1234] A[1243]`. -/
theorem klt_four {l lt : Fin 4 → Fin 2 → ℂ} (h : Conserved l lt)
    (ha : ∀ a b : Fin 4, a ≠ b → angleBr (lt a) (lt b) ≠ 0)
    (hq : ∀ a b : Fin 4, a ≠ b → squareBr (l a) (l b) ≠ 0) :
    bcjNumS l lt ^ 2 / sBr l lt 0 1 + bcjNumT l lt ^ 2 / sBr l lt 0 2 +
        bcjNumU l lt ^ 2 / sBr l lt 0 3 =
      -sBr l lt 0 1 * pt1234 lt * pt1243 lt := by
  have hs := sBr_ne_zero ha hq 0 1 (by decide)
  have ht := sBr_ne_zero ha hq 0 2 (by decide)
  have hu := sBr_ne_zero ha hq 0 3 (by decide)
  exact klt_algebra hs ht hu (sBr_sum_zero h) (bcjNum_jacobi h ha)
    (bcjNum_amp_1234 l lt hs hu) (bcjNum_amp_1243 l lt hs ht)

end Lightlike.Rows.G3_261
