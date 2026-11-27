import Mathlib
import Lightlike.TuraevViro.QSixJLimit
import Lightlike.TuraevViro.QSixJGenericBE
import Lightlike.TemperleyLieb.RecouplingKL

/-!
# The q-Biedenharn–Elliott identity at every level

`qBiedenharnElliott_all` proves the q-Biedenharn–Elliott identity `qBiedenharnElliott hr` for every level
`r ≥ 2`, with no hypothesis. The route:

* the recoupling coefficient `Fc` of the Temperley–Lieb model is the Kauffman–Lins coefficient at generic `q`
  (`TemperleyLieb.Fc_eq_klCoef`, the statement `TemperleyLieb.FcEqKL ℂ`);
* with it, the Temperley–Lieb pentagon gives the generic Biedenharn–Elliott identity `GenBE θ` at every angle
  with `sin (nθ) ≠ 0` for `1 ≤ n ≤ 2S + 4` (`genBE_of_generic`);
* these finitely many conditions hold on a punctured neighbourhood of `π / r` (`eventually_sin_ne`: at a zero
  of `sin (nθ)` its derivative `n cos (nθ)` does not vanish), and the limit `θ → π / r` gives the identity at
  the root of unity (`qBiedenharnElliott_of_genBE`).
-/

open Filter Topology

namespace Lightlike.TV

/-- `sin (nθ)` does not vanish on a punctured neighbourhood of any point, for `n ≥ 1`. -/
theorem eventually_sin_ne (x : ℝ) {n : ℕ} (hn : 1 ≤ n) : ∀ᶠ θ in 𝓝[≠] x, Real.sin (n * θ) ≠ 0 := by
  have hf : HasDerivAt (fun θ => Real.sin (n * θ)) (Real.cos (n * x) * n) x := by
    simpa using ((hasDerivAt_id x).const_mul (n : ℝ)).sin
  by_cases h0 : Real.sin (n * x) = 0
  · have hc : Real.cos (n * x) ≠ 0 := by
      intro hc
      have := Real.sin_sq_add_cos_sq (n * x)
      rw [h0, hc] at this
      norm_num at this
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    exact hf.eventually_ne (c := 0) (mul_ne_zero hc hn0)
  · exact (hf.continuousAt.eventually_ne h0).filter_mono nhdsWithin_le_nhds

/-- **The generic Biedenharn–Elliott identity near `π / r`**: on a punctured neighbourhood of every angle. -/
theorem eventually_genBE (x : ℝ) (a b c d e f p q r' : ℕ) : ∀ᶠ θ in 𝓝[≠] x, GenBE θ a b c d e f p q r' := by
  have h : ∀ᶠ θ in 𝓝[≠] x, ∀ n ∈ Finset.Icc (1 : ℕ) (2 * (a + b + c + d + e + f + p + q + r') + 4),
      Real.sin ((n : ℝ) * θ) ≠ 0 :=
    (Filter.eventually_all_finset _).mpr fun n hn => eventually_sin_ne x (Finset.mem_Icc.mp hn).1
  exact h.mono fun θ hθ => genBE_of_generic TemperleyLieb.Fc_eq_klCoef θ a b c d e f p q r'
    fun n h1 h2 => hθ n (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- **q-Biedenharn–Elliott** for every `r ≥ 2`. -/
theorem qBiedenharnElliott_all {r : ℕ} (hr : 2 ≤ r) : qBiedenharnElliott hr :=
  qBiedenharnElliott_of_genBE hr fun a b c d e f p q r' => eventually_genBE _ a b c d e f p q r'

end Lightlike.TV
