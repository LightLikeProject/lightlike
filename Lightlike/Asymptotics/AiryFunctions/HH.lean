import Lightlike.Asymptotics.AiryFunctions.Airy

/-!
# Hartle–Hawking and Vilenkin wave functions as Airy solutions (row G2-019)

In the Airy variable `x` the minisuperspace Wheeler–DeWitt equation of closed FLRW with `Λ`
(in the region where the potential is linear) reads `ψ'' = x ψ`.  The two boundary conditions
select
* Hartle–Hawking: `ψ_HH = Ai` (real, no-boundary, decaying under the barrier);
* Vilenkin: `ψ_V = Ai + i Bi` (complex, tunnelling).

We prove that both solve the equation (`ℂ`-valued functions of a real variable), that the
Hartle–Hawking current `Im(ψ̄ ψ')` vanishes while the Vilenkin current equals `1/π ≠ 0`
(from the Wronskian `airy_wronskian`), and that the equation is preserved by the affine change
of variable `x = c q + s` (with `ψ'' = c² (c q + s) ψ`).  The WKB asymptotics are in `WKB.lean`.
-/

noncomputable section

namespace Lightlike.Airy

open Complex ComplexConjugate

/-- Hartle–Hawking wave function in the Airy variable: `Ai`, viewed as `ℂ`-valued. -/
def hhWave (x : ℝ) : ℂ := (airyAi x : ℂ)
/-- Derivative of the Hartle–Hawking wave function. -/
def hhWaveDeriv (x : ℝ) : ℂ := (airyAiDeriv x : ℂ)
/-- Vilenkin wave function in the Airy variable: `Ai + i Bi`. -/
def vilenkinWave (x : ℝ) : ℂ := (airyAi x : ℂ) + I * (airyBi x : ℂ)
/-- Derivative of the Vilenkin wave function. -/
def vilenkinWaveDeriv (x : ℝ) : ℂ := (airyAiDeriv x : ℂ) + I * (airyBiDeriv x : ℂ)

theorem hhWave_hasDerivAt (x : ℝ) : HasDerivAt hhWave (hhWaveDeriv x) x :=
  (airyAi_hasDerivAt x).ofReal_comp

theorem hhWaveDeriv_hasDerivAt (x : ℝ) : HasDerivAt hhWaveDeriv ((x : ℂ) * hhWave x) x := by
  have := (airyAiDeriv_hasDerivAt x).ofReal_comp
  refine this.congr_deriv ?_
  simp [hhWave]

theorem vilenkinWave_hasDerivAt (x : ℝ) : HasDerivAt vilenkinWave (vilenkinWaveDeriv x) x :=
  (airyAi_hasDerivAt x).ofReal_comp.add ((airyBi_hasDerivAt x).ofReal_comp.const_mul I)

theorem vilenkinWaveDeriv_hasDerivAt (x : ℝ) :
    HasDerivAt vilenkinWaveDeriv ((x : ℂ) * vilenkinWave x) x := by
  have := (airyAiDeriv_hasDerivAt x).ofReal_comp.add
    ((airyBiDeriv_hasDerivAt x).ofReal_comp.const_mul I)
  refine this.congr_deriv ?_
  simp only [vilenkinWave]
  push_cast
  ring

/-- Hartle–Hawking current `Im(ψ̄ ψ')` vanishes. -/
theorem hhWave_current (x : ℝ) : (conj (hhWave x) * hhWaveDeriv x).im = 0 := by
  simp [hhWave, hhWaveDeriv, ← Complex.ofReal_mul, Complex.conj_ofReal]

/-- Vilenkin current `Im(ψ̄ ψ') = Ai Bi' − Ai' Bi = 1/π`. -/
theorem vilenkinWave_current (x : ℝ) :
    (conj (vilenkinWave x) * vilenkinWaveDeriv x).im = 1 / Real.pi := by
  rw [← airy_wronskian x]
  simp [vilenkinWave, vilenkinWaveDeriv, Complex.mul_im, Complex.mul_re]
  ring

/-- The Vilenkin current is nonzero (an outgoing/ingoing flux), unlike the Hartle–Hawking one. -/
theorem vilenkinWave_current_ne_zero (x : ℝ) :
    (conj (vilenkinWave x) * vilenkinWaveDeriv x).im ≠ 0 := by
  rw [vilenkinWave_current]
  exact one_div_ne_zero Real.pi_ne_zero

/-- Affine rescaling `x = c q + s`: if `y'' = x y` then `f(q) = y(c q + s)` satisfies
`f'' = c² (c q + s) f`, with `f' = c · y'(c q + s)`. -/
theorem scaled_hasDerivAt (c s : ℝ) {y y' : ℝ → ℂ}
    (h : ∀ x : ℝ, HasDerivAt y (y' x) x) (h' : ∀ x : ℝ, HasDerivAt y' ((x : ℂ) * y x) x)
    (q : ℝ) :
    HasDerivAt (fun q : ℝ => y (c * q + s)) ((c : ℂ) * y' (c * q + s)) q ∧
    HasDerivAt (fun q : ℝ => (c : ℂ) * y' (c * q + s))
      ((c : ℂ) ^ 2 * (((c * q + s : ℝ) : ℂ)) * y (c * q + s)) q := by
  have hl : HasDerivAt (fun q : ℝ => c * q + s) c q := by
    simpa using ((hasDerivAt_id q).const_mul c).add_const s
  constructor
  · have := (h (c * q + s)).scomp q hl
    refine this.congr_deriv ?_
    simp [Complex.real_smul]
  · have := ((h' (c * q + s)).scomp q hl).const_mul (c : ℂ)
    refine this.congr_deriv ?_
    simp only [Complex.real_smul]
    ring

end Lightlike.Airy
