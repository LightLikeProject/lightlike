import Lightlike.Asymptotics.Saddle

/-!
# Assembling the Ponzano–Regge formula

`PR.PonzanoReggeFormula` follows from two statements, stated here as propositions (nothing is
assumed: they appear only as hypotheses of `ponzanoReggeFormula_of`):

* `RacahFormula`: Racah's single-sum formula `{6j}(J) = Δ(J) · racahSum J` for Physlib's
  `sixJSym` at integer spins `J`. It is proven in `Racah.lean` (`racahFormula`), which gives
  `ponzanoReggeFormula_of_racahSumAsymptotics`;
* `RacahSumAsymptotics`: the saddle-point asymptotics of Racah's alternating sum,
  `√(√vol2(ℓ)) e^{−D(ℓ)} racahSum(λj) − cos(S_Regge(ℓ) + π/4) / (√(12π) (2π)²) → 0` with
  `ℓ = λj + ½` (from milestone SP2 and the saddle algebra of `Saddle.lean`).

The rest is proven here: Stirling's formula in midpoint form for the prefactor,
`Δ(λj) e^{D(ℓ)} → (2π)²` (`tendsto_racahDelta_mul_exp`), and the combination of the limits.

Spins are ordinary integers here (`J : Fin 6 → ℕ`); Physlib's `sixJSym` takes doubled spins
`2J`. Labelling as in `PonzanoRegge/`: faces `(J₀ J₁ J₂), (J₀ J₄ J₅), (J₃ J₁ J₅), (J₃ J₄ J₂)`.
-/

open Real Filter Topology PhyslibAlpha.Sl2

namespace Lightlike.Asymptotics

/-- The four face sums (triad sums) of integer spins. -/
def faceN (J : Fin 6 → ℕ) (i : Fin 4) : ℕ :=
  ![J 0 + J 1 + J 2, J 0 + J 4 + J 5, J 3 + J 1 + J 5, J 3 + J 4 + J 2] i

/-- The three sums of four spins avoiding an opposite pair. -/
def quadN (J : Fin 6 → ℕ) (k : Fin 3) : ℕ :=
  ![J 0 + J 1 + J 3 + J 4, J 1 + J 2 + J 4 + J 5, J 2 + J 0 + J 5 + J 3] k

/-- **Racah's alternating sum** `Σ_t (−1)^t (t+1)! / (∏ᵢ (t − aᵢ)! ∏ₖ (bₖ − t)!)`, with `aᵢ` the
face sums, `bₖ` the sums `quadN`, and `1/n! = 0` for negative `n` (Physlib's `invFact`). -/
noncomputable def racahSum (J : Fin 6 → ℕ) : ℝ :=
  ∑ t ∈ Finset.range (quadN J 0 + 1), (-1 : ℝ) ^ t * ((t + 1).factorial : ℝ) *
    (∏ i, invFact ((t : ℤ) - faceN J i)) * ∏ k, invFact ((quadN J k : ℤ) - t)

/-- The triangle coefficient `Δ(abc) = √((a+b−c)! (a−b+c)! (−a+b+c)! / (a+b+c+1)!)`. -/
noncomputable def triadDelta (a b c : ℕ) : ℝ :=
  √(((a + b - c).factorial * (a + c - b).factorial * (b + c - a).factorial : ℝ) /
    (a + b + c + 1).factorial)

/-- Racah's prefactor `∏_faces Δ(face)`. -/
noncomputable def racahDelta (J : Fin 6 → ℕ) : ℝ :=
  triadDelta (J 0) (J 1) (J 2) * triadDelta (J 0) (J 4) (J 5) * triadDelta (J 3) (J 1) (J 5) *
    triadDelta (J 3) (J 4) (J 2)

/-- **Racah's formula** for Physlib's 6j symbol at integer spins: for four triangular faces,
`{J₀ J₁ J₂; J₃ J₄ J₅} = Δ(J) · racahSum J`. -/
def RacahFormula : Prop :=
  ∀ J : Fin 6 → ℕ, PR.IsTriad (J 0) (J 1) (J 2) → PR.IsTriad (J 0) (J 4) (J 5) →
    PR.IsTriad (J 3) (J 1) (J 5) → PR.IsTriad (J 3) (J 4) (J 2) →
    sixJSym (2 * J 0) (2 * J 1) (2 * J 2) (2 * J 3) (2 * J 4) (2 * J 5) = racahDelta J * racahSum J

/-- The real edge lengths `j` of integer spins. -/
def toReal (j : Fin 6 → ℕ) : Fin 6 → ℝ := fun e => (j e : ℝ)

/-- **The saddle-point asymptotics of Racah's sum**, in the geometry of `ℓ = λj + ½`: for every
Euclidean tetrahedron with integer edges `j`,
`√(√vol2(ℓ)) e^{−D(ℓ)} racahSum(λj) − cos(S_Regge(ℓ) + π/4) / (√(12π) (2π)²) → 0`.
(`1/(√(12π)(2π)²) = 2 (2π)^{−5/2} / √24`.) -/
def RacahSumAsymptotics : Prop :=
  ∀ j : Fin 6 → ℕ, IsEuclid (toReal j) →
    Tendsto (fun lam : ℕ =>
      √(√(vol2l (PR.lengths j lam))) * Real.exp (-prefactorRate (PR.lengths j lam)) *
          racahSum (fun e => lam * j e) -
        Real.cos (PR.reggeAction (PR.lengths j lam) + π / 4) / (√(12 * π) * (2 * π) ^ 2))
      atTop (𝓝 0)

/-! ## Strict faces -/

/-- A degenerate face forces `vol2 ≤ 0`: for `c = a + b`,
`144 vol2 = −(a²b + ab² − ad² + af² − be² + bf²)²`. -/
lemma vol2_of_degenerate (a b d e f : ℝ) :
    PR.vol2 a b (a + b) d e f = -(a ^ 2 * b + a * b ^ 2 - a * d ^ 2 + a * f ^ 2 - b * e ^ 2 +
      b * f ^ 2) ^ 2 / 144 := by
  unfold PR.vol2; ring

/-- The twelve degenerate faces: `ℓ_z = ℓ_x + ℓ_y` forces `vol2 ≤ 0` (minus a square). -/
lemma vol2l_nonpos_2_0_1 (l : Fin 6 → ℝ) (h : l 2 = l 0 + l 1) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 1 + l 0 * l 1 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 5 ^ 2 - l 1 * l 4 ^ 2 + l 1 * l 5 ^ 2) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 1 + l 0 * l 1 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 5 ^ 2 - l 1 * l 4 ^ 2 + l 1 * l 5 ^ 2); linarith

lemma vol2l_nonpos_1_0_2 (l : Fin 6 → ℝ) (h : l 1 = l 0 + l 2) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 2 + l 0 * l 2 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 4 ^ 2 + l 2 * l 4 ^ 2 - l 2 * l 5 ^ 2) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 2 + l 0 * l 2 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 4 ^ 2 + l 2 * l 4 ^ 2 - l 2 * l 5 ^ 2); linarith

lemma vol2l_nonpos_0_1_2 (l : Fin 6 → ℝ) (h : l 0 = l 1 + l 2) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 1 ^ 2 * l 2 + l 1 * l 2 ^ 2 + l 1 * l 3 ^ 2 - l 1 * l 4 ^ 2 + l 2 * l 3 ^ 2 - l 2 * l 5 ^ 2) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 1 ^ 2 * l 2 + l 1 * l 2 ^ 2 + l 1 * l 3 ^ 2 - l 1 * l 4 ^ 2 + l 2 * l 3 ^ 2 - l 2 * l 5 ^ 2); linarith

lemma vol2l_nonpos_5_0_4 (l : Fin 6 → ℝ) (h : l 5 = l 0 + l 4) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 4 + l 0 * l 2 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 4 ^ 2 - l 1 ^ 2 * l 4 + l 2 ^ 2 * l 4) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 4 + l 0 * l 2 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 4 ^ 2 - l 1 ^ 2 * l 4 + l 2 ^ 2 * l 4); linarith

lemma vol2l_nonpos_4_0_5 (l : Fin 6 → ℝ) (h : l 4 = l 0 + l 5) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 5 + l 0 * l 1 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 5 ^ 2 + l 1 ^ 2 * l 5 - l 2 ^ 2 * l 5) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 5 + l 0 * l 1 ^ 2 - l 0 * l 3 ^ 2 + l 0 * l 5 ^ 2 + l 1 ^ 2 * l 5 - l 2 ^ 2 * l 5); linarith

lemma vol2l_nonpos_0_4_5 (l : Fin 6 → ℝ) (h : l 0 = l 4 + l 5) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 1 ^ 2 * l 4 + l 2 ^ 2 * l 5 - l 3 ^ 2 * l 4 - l 3 ^ 2 * l 5 - l 4 ^ 2 * l 5 - l 4 * l 5 ^ 2) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 1 ^ 2 * l 4 + l 2 ^ 2 * l 5 - l 3 ^ 2 * l 4 - l 3 ^ 2 * l 5 - l 4 ^ 2 * l 5 - l 4 * l 5 ^ 2); linarith

lemma vol2l_nonpos_5_3_1 (l : Fin 6 → ℝ) (h : l 5 = l 3 + l 1) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 3 - l 1 ^ 2 * l 3 - l 1 * l 2 ^ 2 - l 1 * l 3 ^ 2 + l 1 * l 4 ^ 2 - l 2 ^ 2 * l 3) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 3 - l 1 ^ 2 * l 3 - l 1 * l 2 ^ 2 - l 1 * l 3 ^ 2 + l 1 * l 4 ^ 2 - l 2 ^ 2 * l 3); linarith

lemma vol2l_nonpos_1_3_5 (l : Fin 6 → ℝ) (h : l 1 = l 3 + l 5) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 3 + l 2 ^ 2 * l 5 - l 3 ^ 2 * l 5 - l 3 * l 4 ^ 2 - l 3 * l 5 ^ 2 - l 4 ^ 2 * l 5) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 3 + l 2 ^ 2 * l 5 - l 3 ^ 2 * l 5 - l 3 * l 4 ^ 2 - l 3 * l 5 ^ 2 - l 4 ^ 2 * l 5); linarith

lemma vol2l_nonpos_3_1_5 (l : Fin 6 → ℝ) (h : l 3 = l 1 + l 5) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 1 + l 0 ^ 2 * l 5 + l 1 ^ 2 * l 5 - l 1 * l 4 ^ 2 + l 1 * l 5 ^ 2 - l 2 ^ 2 * l 5) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 1 + l 0 ^ 2 * l 5 + l 1 ^ 2 * l 5 - l 1 * l 4 ^ 2 + l 1 * l 5 ^ 2 - l 2 ^ 2 * l 5); linarith

lemma vol2l_nonpos_2_3_4 (l : Fin 6 → ℝ) (h : l 2 = l 3 + l 4) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 3 + l 1 ^ 2 * l 4 - l 3 ^ 2 * l 4 - l 3 * l 4 ^ 2 - l 3 * l 5 ^ 2 - l 4 * l 5 ^ 2) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 3 + l 1 ^ 2 * l 4 - l 3 ^ 2 * l 4 - l 3 * l 4 ^ 2 - l 3 * l 5 ^ 2 - l 4 * l 5 ^ 2); linarith

lemma vol2l_nonpos_4_3_2 (l : Fin 6 → ℝ) (h : l 4 = l 3 + l 2) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 3 - l 1 ^ 2 * l 2 - l 1 ^ 2 * l 3 - l 2 ^ 2 * l 3 - l 2 * l 3 ^ 2 + l 2 * l 5 ^ 2) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 3 - l 1 ^ 2 * l 2 - l 1 ^ 2 * l 3 - l 2 ^ 2 * l 3 - l 2 * l 3 ^ 2 + l 2 * l 5 ^ 2); linarith

lemma vol2l_nonpos_3_4_2 (l : Fin 6 → ℝ) (h : l 3 = l 4 + l 2) : vol2l l ≤ 0 := by
  have e : vol2l l = -(l 0 ^ 2 * l 2 + l 0 ^ 2 * l 4 - l 1 ^ 2 * l 4 + l 2 ^ 2 * l 4 + l 2 * l 4 ^ 2 - l 2 * l 5 ^ 2) ^ 2 / 144 := by
    simp only [vol2l, PR.vol2]; rw [h]; ring
  rw [e]; have := sq_nonneg (l 0 ^ 2 * l 2 + l 0 ^ 2 * l 4 - l 1 ^ 2 * l 4 + l 2 ^ 2 * l 4 + l 2 * l 4 ^ 2 - l 2 * l 5 ^ 2); linarith

/-- A strict triangle inequality from a weak one and `vol2 > 0`. -/
lemma strict_of_weak {l : Fin 6 → ℝ} {x y z : Fin 6} (hv : 0 < vol2l l) (hw : l z ≤ l x + l y)
    (hd : l z = l x + l y → vol2l l ≤ 0) : 0 < l x + l y - l z := by
  rcases lt_or_eq_of_le hw with h | h
  · linarith
  · exact absurd hv (not_lt.mpr (hd h))

/-- **The hypotheses of `PR.PonzanoReggeFormula` give a Euclidean tetrahedron**: the weak triangle
inequalities on the four faces and `vol2 > 0` imply the twelve strict ones. -/
theorem isEuclid_toReal {j : Fin 6 → ℕ} (h1 : PR.IsTriad (j 0) (j 1) (j 2))
    (h2 : PR.IsTriad (j 0) (j 4) (j 5)) (h3 : PR.IsTriad (j 3) (j 1) (j 5))
    (h4 : PR.IsTriad (j 3) (j 4) (j 2)) (hv : 0 < vol2l (toReal j)) : IsEuclid (toReal j) := by
  obtain ⟨a1, a2, a3⟩ := h1; obtain ⟨b1, b2, b3⟩ := h2
  obtain ⟨c1, c2, c3⟩ := h3; obtain ⟨d1, d2, d3⟩ := h4
  have w : ∀ {p q r : ℕ}, r ≤ p + q → (r : ℝ) ≤ p + q := fun h => by exact_mod_cast h
  have s1 := strict_of_weak (x := 3) (y := 4) (z := 2) hv (by simpa [toReal] using w d1)
    (vol2l_nonpos_2_3_4 _)
  have s2 := strict_of_weak (x := 4) (y := 5) (z := 0) hv (by simpa [toReal] using w b2)
    (vol2l_nonpos_0_4_5 _)
  have s3 := strict_of_weak (x := 3) (y := 5) (z := 1) hv (by simpa [toReal, add_comm] using w c3)
    (vol2l_nonpos_1_3_5 _)
  have s4 := strict_of_weak (x := 1) (y := 3) (z := 5) hv (by simpa [toReal, add_comm] using w c1)
    (fun h => vol2l_nonpos_5_3_1 _ (by rw [h]; ring))
  have s5 := strict_of_weak (x := 1) (y := 2) (z := 0) hv (by simpa [toReal] using w a2)
    (vol2l_nonpos_0_1_2 _)
  have s6 := strict_of_weak (x := 2) (y := 3) (z := 4) hv (by simpa [toReal, add_comm] using w d3)
    (fun h => vol2l_nonpos_4_3_2 _ (by rw [h]; ring))
  have s7 := strict_of_weak (x := 0) (y := 4) (z := 5) hv (by simpa [toReal] using w b1)
    (vol2l_nonpos_5_0_4 _)
  have s8 := strict_of_weak (x := 2) (y := 4) (z := 3) hv (by simpa [toReal, add_comm] using w d2)
    (fun h => vol2l_nonpos_3_4_2 _ (by rw [h]; ring))
  have s9 := strict_of_weak (x := 0) (y := 2) (z := 1) hv (by simpa [toReal] using w a3)
    (vol2l_nonpos_1_0_2 _)
  have s10 := strict_of_weak (x := 0) (y := 1) (z := 2) hv (by simpa [toReal] using w a1)
    (vol2l_nonpos_2_0_1 _)
  have s11 := strict_of_weak (x := 1) (y := 5) (z := 3) hv (by simpa [toReal] using w c2)
    (vol2l_nonpos_3_1_5 _)
  have s12 := strict_of_weak (x := 0) (y := 5) (z := 4) hv (by simpa [toReal] using w b3)
    (vol2l_nonpos_4_0_5 _)
  refine ⟨fun i k => ?_, hv⟩
  fin_cases i <;> fin_cases k <;> simp [faceSum, quadSum] <;> linarith

/-! ## Stirling's formula in midpoint form -/

/-- The midpoint Stirling approximation `√(2π) x^x e^{−x}` of `Γ(x + ½)`. -/
noncomputable def midStirling (x : ℝ) : ℝ := √(2 * π) * Real.exp (x * Real.log x - x)

lemma midStirling_pos (x : ℝ) : 0 < midStirling x := by
  unfold midStirling; positivity

/-- **Midpoint Stirling**: `n! / (√(2π) (n+½)^{n+½} e^{−(n+½)}) → 1`. -/
theorem tendsto_factorial_div_midStirling :
    Tendsto (fun n : ℕ => (n.factorial : ℝ) / midStirling (n + 1 / 2)) atTop (𝓝 1) := by
  -- `n! / (√(2πn) (n/e)^n) → 1`
  have hS : Tendsto (fun n : ℕ => Stirling.stirlingSeq n / √π) atTop (𝓝 1) := by
    have := Stirling.tendsto_stirlingSeq_sqrt_pi.div_const √π
    rwa [div_self (Real.sqrt_pos.mpr Real.pi_pos).ne'] at this
  -- the correction `exp(½ − (n+½) log(1 + ½/n)) → 1`
  have hlog : Tendsto (fun n : ℕ => ((n : ℝ) + 1 / 2) * Real.log (1 + (1 / 2) / n)) atTop
      (𝓝 (1 / 2)) := by
    have h1 := (Real.tendsto_mul_log_one_add_div_atTop (1 / 2)).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * Real.log (1 + (1 / 2) / n)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (1 : ℝ) + (1 / 2) / n) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := (1 / 2 : ℝ))).div_atTop tendsto_natCast_atTop_atTop)
      have := ((Real.continuousAt_log one_ne_zero).tendsto.comp this).const_mul (1 / 2 : ℝ)
      simpa using this
    have := h1.add h2
    simp only [add_zero, Function.comp] at this
    refine this.congr fun n => ?_
    ring
  have hC : Tendsto (fun n : ℕ => Real.exp (1 / 2 - ((n : ℝ) + 1 / 2) * Real.log (1 + (1 / 2) / n)))
      atTop (𝓝 1) := by
    have := (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hlog)
    rw [sub_self, Real.exp_zero] at this
    exact this
  have hSC := hS.mul hC
  rw [mul_one] at hSC
  refine hSC.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Stirling.stirlingSeq]
  have hlogsum : Real.log ((n : ℝ) + 1 / 2) = Real.log n + Real.log (1 + (1 / 2) / n) := by
    rw [← Real.log_mul hn'.ne' (by positivity)]; congr 1; field_simp
  have hpow : ((n : ℝ) / Real.exp 1) ^ n = Real.exp (n * Real.log n - n) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < ((n : ℝ) / Real.exp 1) ^ n), Real.log_pow,
      Real.log_div hn'.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring_nf
  have hsq : √(2 * (n : ℝ)) * √π = √(2 * π) * Real.exp (1 / 2 * Real.log n) := by
    rw [← Real.sqrt_mul (by positivity), show 2 * (n : ℝ) * π = 2 * π * n by ring,
      Real.sqrt_mul (by positivity) (n : ℝ)]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn']
    ring_nf
  have key : √(2 * (n : ℝ)) * Real.exp (n * Real.log n - n) * √π =
      √(2 * π) * Real.exp ((n : ℝ) * Real.log n - n + 1 / 2 * Real.log n) := by
    rw [mul_right_comm, hsq, mul_assoc, ← Real.exp_add]; ring_nf
  unfold midStirling
  rw [div_div, hpow, key, hlogsum,
    show ((n : ℝ) + 1 / 2) * (Real.log n + Real.log (1 + 1 / 2 / n)) - (n + 1 / 2) =
      ((n : ℝ) * Real.log n - n + 1 / 2 * Real.log n) -
        (1 / 2 - ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / 2 / n)) by ring, Real.exp_sub]
  field_simp
  rw [← Real.exp_add, ← Real.exp_add]
  ring_nf

/-- Midpoint Stirling along `λ ↦ λ m` for `m ≥ 1`. -/
lemma tendsto_factorial_div_midStirling_mul {m : ℕ} (hm : 0 < m) :
    Tendsto (fun lam : ℕ => ((lam * m).factorial : ℝ) / midStirling ((lam * m : ℕ) + 1 / 2)) atTop
      (𝓝 1) :=
  tendsto_factorial_div_midStirling.comp
    (tendsto_atTop_mono (fun lam => Nat.le_mul_of_pos_right lam hm) tendsto_id)

/-- Midpoint Stirling along `λ ↦ λ m + 1`. -/
lemma tendsto_factorial_div_midStirling_mul_add_one {m : ℕ} (hm : 0 < m) :
    Tendsto (fun lam : ℕ => ((lam * m + 1).factorial : ℝ) / midStirling ((lam * m + 1 : ℕ) + 1 / 2))
      atTop (𝓝 1) :=
  tendsto_factorial_div_midStirling.comp (tendsto_atTop_mono
    (fun lam => le_trans (Nat.le_mul_of_pos_right lam hm) (Nat.le_succ _)) tendsto_id)

/-- The Stirling ratio `r(n) = n! / (√(2π) (n+½)^{n+½} e^{−(n+½)})`. -/
noncomputable def stirRatio (n : ℕ) : ℝ := (n.factorial : ℝ) / midStirling (n + 1 / 2)

lemma stirRatio_pos (n : ℕ) : 0 < stirRatio n := by
  unfold stirRatio; have := midStirling_pos ((n : ℝ) + 1 / 2); positivity

/-- The exact identity behind the prefactor of one face: for `U + V + W + 1 = N`,
`(U! V! W! / N!) exp(F) = 2π r(U) r(V) r(W) / r(N)` with
`F = (N+½) log(N+½) − Σ (T+½) log(T+½)` over `T = U, V, W`. -/
lemma face_identity (U V W N : ℕ) (hN : U + V + W + 1 = N) :
    ((U.factorial * V.factorial * W.factorial : ℝ) / N.factorial) *
      Real.exp (((N : ℝ) + 1 / 2) * Real.log ((N : ℝ) + 1 / 2) -
        ((W : ℝ) + 1 / 2) * Real.log ((W : ℝ) + 1 / 2) -
        ((V : ℝ) + 1 / 2) * Real.log ((V : ℝ) + 1 / 2) -
        ((U : ℝ) + 1 / 2) * Real.log ((U : ℝ) + 1 / 2)) =
      2 * π * (stirRatio U * stirRatio V * stirRatio W / stirRatio N) := by
  have hN' : (N : ℝ) = U + V + W + 1 := by rw [← hN]; push_cast; ring
  set P : ℝ → ℝ := fun x => x * Real.log x - x with hP
  have hF : ((N : ℝ) + 1 / 2) * Real.log ((N : ℝ) + 1 / 2) -
      ((W : ℝ) + 1 / 2) * Real.log ((W : ℝ) + 1 / 2) -
      ((V : ℝ) + 1 / 2) * Real.log ((V : ℝ) + 1 / 2) -
      ((U : ℝ) + 1 / 2) * Real.log ((U : ℝ) + 1 / 2) =
      P ((N : ℝ) + 1 / 2) - P ((U : ℝ) + 1 / 2) - P ((V : ℝ) + 1 / 2) - P ((W : ℝ) + 1 / 2) := by
    simp only [hP]; rw [hN']; ring
  rw [hF, Real.exp_sub, Real.exp_sub, Real.exp_sub]
  unfold stirRatio midStirling
  simp only [hP]
  have h2 : √(2 * π) ^ 2 = 2 * π := Real.sq_sqrt (by positivity)
  have hpos : ∀ x : ℝ, 0 < Real.exp x := Real.exp_pos
  field_simp
  rw [h2]

lemma exp_half_eq_sqrt (x : ℝ) : Real.exp (x / 2) = √(Real.exp x) := by
  rw [← Real.sqrt_sq (Real.exp_pos (x / 2)).le, sq, ← Real.exp_add]; ring_nf

/-- `faceRate` at the lengths `λa + ½, λb + ½, λc + ½`, in terms of the integers
`U = λ(a+b−c), V = λ(a+c−b), W = λ(b+c−a), N = λ(a+b+c) + 1`. -/
lemma faceRate_scaled {a b c : ℕ} (hab : c ≤ a + b) (hac : b ≤ a + c) (hbc : a ≤ b + c) (lam : ℕ) :
    faceRate ((lam : ℝ) * a + 1 / 2) ((lam : ℝ) * b + 1 / 2) ((lam : ℝ) * c + 1 / 2) =
      (((lam * (a + b + c) + 1 : ℕ) : ℝ) + 1 / 2) * Real.log (((lam * (a + b + c) + 1 : ℕ) : ℝ) + 1 / 2) -
        (((lam * (b + c - a) : ℕ) : ℝ) + 1 / 2) * Real.log (((lam * (b + c - a) : ℕ) : ℝ) + 1 / 2) -
        (((lam * (a + c - b) : ℕ) : ℝ) + 1 / 2) * Real.log (((lam * (a + c - b) : ℕ) : ℝ) + 1 / 2) -
        (((lam * (a + b - c) : ℕ) : ℝ) + 1 / 2) * Real.log (((lam * (a + b - c) : ℕ) : ℝ) + 1 / 2) := by
  have h1 : (lam : ℝ) * a + 1 / 2 + ((lam : ℝ) * b + 1 / 2) + ((lam : ℝ) * c + 1 / 2) =
      ((lam * (a + b + c) + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
  have h2 : -((lam : ℝ) * a + 1 / 2) + ((lam : ℝ) * b + 1 / 2) + ((lam : ℝ) * c + 1 / 2) =
      ((lam * (b + c - a) : ℕ) : ℝ) + 1 / 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hbc]; push_cast; ring
  have h3 : (lam : ℝ) * a + 1 / 2 - ((lam : ℝ) * b + 1 / 2) + ((lam : ℝ) * c + 1 / 2) =
      ((lam * (a + c - b) : ℕ) : ℝ) + 1 / 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hac]; push_cast; ring
  have h4 : (lam : ℝ) * a + 1 / 2 + ((lam : ℝ) * b + 1 / 2) - ((lam : ℝ) * c + 1 / 2) =
      ((lam * (a + b - c) : ℕ) : ℝ) + 1 / 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hab]; push_cast; ring
  unfold faceRate
  rw [h1, h2, h3, h4]

/-- `Δ(λa, λb, λc)` in terms of `U, V, W, N`. -/
lemma triadDelta_scaled (a b c lam : ℕ) :
    triadDelta (lam * a) (lam * b) (lam * c) =
      √(((lam * (a + b - c)).factorial * (lam * (a + c - b)).factorial *
        (lam * (b + c - a)).factorial : ℝ) / (lam * (a + b + c) + 1).factorial) := by
  unfold triadDelta
  simp only [← Nat.mul_add, ← Nat.mul_sub]

/-- **The prefactor of one face**: for a strict triangle `(a, b, c)` of integers,
`Δ(λa, λb, λc) · exp(½ faceRate(λa+½, λb+½, λc+½)) → √(2π)`. -/
theorem tendsto_triadDelta_mul_exp {a b c : ℕ} (hab : c < a + b) (hac : b < a + c)
    (hbc : a < b + c) :
    Tendsto (fun lam : ℕ => triadDelta (lam * a) (lam * b) (lam * c) *
      Real.exp (faceRate ((lam : ℝ) * a + 1 / 2) ((lam : ℝ) * b + 1 / 2) ((lam : ℝ) * c + 1 / 2) / 2))
      atTop (𝓝 √(2 * π)) := by
  have key : ∀ lam : ℕ, triadDelta (lam * a) (lam * b) (lam * c) *
      Real.exp (faceRate ((lam : ℝ) * a + 1 / 2) ((lam : ℝ) * b + 1 / 2) ((lam : ℝ) * c + 1 / 2) / 2) =
      √(2 * π * (stirRatio (lam * (a + b - c)) * stirRatio (lam * (a + c - b)) *
        stirRatio (lam * (b + c - a)) / stirRatio (lam * (a + b + c) + 1))) := by
    intro lam
    have hsum : lam * (a + b - c) + lam * (a + c - b) + lam * (b + c - a) + 1 =
        lam * (a + b + c) + 1 := by
      rw [← Nat.mul_add, ← Nat.mul_add]; congr 2; omega
    rw [triadDelta_scaled, exp_half_eq_sqrt, faceRate_scaled hab.le hac.le hbc.le,
      ← Real.sqrt_mul (by positivity), face_identity _ _ _ _ hsum]
  simp_rw [key]
  have hlim : Tendsto (fun lam : ℕ => 2 * π * (stirRatio (lam * (a + b - c)) *
      stirRatio (lam * (a + c - b)) * stirRatio (lam * (b + c - a)) /
        stirRatio (lam * (a + b + c) + 1))) atTop (𝓝 (2 * π * (1 * 1 * 1 / 1))) := by
    refine tendsto_const_nhds.mul ((((tendsto_factorial_div_midStirling_mul (by omega)).mul
      (tendsto_factorial_div_midStirling_mul (by omega))).mul
        (tendsto_factorial_div_midStirling_mul (by omega))).div
          (tendsto_factorial_div_midStirling_mul_add_one (by omega)) one_ne_zero)
  simp only [mul_one, div_one] at hlim
  exact (Real.continuous_sqrt.tendsto _).comp hlim

/-- The twelve strict triangle inequalities of a Euclidean tetrahedron with integer edges, in `ℕ`. -/
lemma IsEuclid.strict_nat {j : Fin 6 → ℕ} (h : IsEuclid (toReal j)) :
    (j 2 < j 0 + j 1 ∧ j 1 < j 0 + j 2 ∧ j 0 < j 1 + j 2) ∧
    (j 5 < j 0 + j 4 ∧ j 4 < j 0 + j 5 ∧ j 0 < j 4 + j 5) ∧
    (j 5 < j 3 + j 1 ∧ j 1 < j 3 + j 5 ∧ j 3 < j 1 + j 5) ∧
    (j 2 < j 3 + j 4 ∧ j 4 < j 3 + j 2 ∧ j 3 < j 4 + j 2) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := quadSum_sub_faceSum (toReal j)
  have p : ∀ i k, 0 < quadSum (toReal j) k - faceSum (toReal j) i := fun i k => sub_pos.mpr (h.lt i k)
  have q1 := p 0 0; have q2 := p 0 1; have q3 := p 0 2; have q4 := p 1 0; have q5 := p 1 1
  have q6 := p 1 2; have q7 := p 2 0; have q8 := p 2 1; have q9 := p 2 2; have q10 := p 3 0
  have q11 := p 3 1; have q12 := p 3 2
  rw [e1] at q1; rw [e2] at q2; rw [e3] at q3; rw [e4] at q4; rw [e5] at q5; rw [e6] at q6
  rw [e7] at q7; rw [e8] at q8; rw [e9] at q9; rw [e10] at q10; rw [e11] at q11; rw [e12] at q12
  simp only [toReal] at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    · rw [← Nat.cast_lt (α := ℝ)]; push_cast; linarith

/-- **The prefactor**: `Δ(λj) · e^{D(λj + ½)} → (2π)²`. -/
theorem tendsto_racahDelta_mul_exp {j : Fin 6 → ℕ} (h : IsEuclid (toReal j)) :
    Tendsto (fun lam : ℕ => racahDelta (fun e => lam * j e) *
      Real.exp (prefactorRate (PR.lengths j lam))) atTop (𝓝 ((2 * π) ^ 2)) := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ := h.strict_nat
  have f0 := tendsto_triadDelta_mul_exp a1 a2 a3
  have f1 := tendsto_triadDelta_mul_exp b1 b2 b3
  have f2 := tendsto_triadDelta_mul_exp c1 c2 c3
  have f3 := tendsto_triadDelta_mul_exp d1 d2 d3
  have hlim := ((f0.mul f1).mul f2).mul f3
  have hval : √(2 * π) * √(2 * π) * √(2 * π) * √(2 * π) = (2 * π) ^ 2 := by
    rw [← sq, sq_sqrt (by positivity)]; ring_nf; rw [sq_sqrt (by positivity)]; ring
  rw [hval] at hlim
  refine hlim.congr fun lam => ?_
  simp only [racahDelta, prefactorRate_eq_faces, PR.lengths]
  rw [show (1 / 2 : ℝ) * (faceRate ((lam : ℝ) * j 0 + 1 / 2) ((lam : ℝ) * j 1 + 1 / 2) ((lam : ℝ) * j 2 + 1 / 2) +
      faceRate ((lam : ℝ) * j 0 + 1 / 2) ((lam : ℝ) * j 4 + 1 / 2) ((lam : ℝ) * j 5 + 1 / 2) +
      faceRate ((lam : ℝ) * j 3 + 1 / 2) ((lam : ℝ) * j 1 + 1 / 2) ((lam : ℝ) * j 5 + 1 / 2) +
      faceRate ((lam : ℝ) * j 3 + 1 / 2) ((lam : ℝ) * j 4 + 1 / 2) ((lam : ℝ) * j 2 + 1 / 2)) =
      faceRate ((lam : ℝ) * j 0 + 1 / 2) ((lam : ℝ) * j 1 + 1 / 2) ((lam : ℝ) * j 2 + 1 / 2) / 2 +
      faceRate ((lam : ℝ) * j 0 + 1 / 2) ((lam : ℝ) * j 4 + 1 / 2) ((lam : ℝ) * j 5 + 1 / 2) / 2 +
      faceRate ((lam : ℝ) * j 3 + 1 / 2) ((lam : ℝ) * j 1 + 1 / 2) ((lam : ℝ) * j 5 + 1 / 2) / 2 +
      faceRate ((lam : ℝ) * j 3 + 1 / 2) ((lam : ℝ) * j 4 + 1 / 2) ((lam : ℝ) * j 2 + 1 / 2) / 2
      by ring, Real.exp_add, Real.exp_add, Real.exp_add]
  ring

/-- **The Ponzano–Regge formula from Racah's formula and the asymptotics of Racah's sum.** Both
hypotheses are explicit propositions of this file; this theorem does the rest: the Euclidean
geometry of the hypotheses of `PR.PonzanoReggeFormula`, Stirling's formula for the prefactor, and
the combination of the limits. -/
theorem ponzanoReggeFormula_of (hR : RacahFormula) (hS : RacahSumAsymptotics) :
    PR.PonzanoReggeFormula := by
  intro j h1 h2 h3 h4 hv
  have hE : IsEuclid (toReal j) := isEuclid_toReal h1 h2 h3 h4 hv
  have hX := hS j hE
  have hW := tendsto_racahDelta_mul_exp hE
  -- Racah's formula at the scaled spins
  have hsc : ∀ {a b c : ℕ}, PR.IsTriad a b c → ∀ lam : ℕ, PR.IsTriad (lam * a) (lam * b) (lam * c) :=
    fun {a b c} h lam => ⟨by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h.1,
      by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h.2.1,
      by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ h.2.2⟩
  have hRac : ∀ lam : ℕ, PR.sixJScaled j lam =
      racahDelta (fun e => lam * j e) * racahSum (fun e => lam * j e) := fun lam => by
    have := hR (fun e => lam * j e) (hsc h1 lam) (hsc h2 lam) (hsc h3 lam) (hsc h4 lam)
    simp only [PR.sixJScaled, mul_assoc] at this ⊢
    exact this
  set K : ℝ := √(12 * π) * (2 * π) ^ 2 with hK
  have hKpos : 0 < K := by positivity
  -- the two pieces of the error
  have t1 : Tendsto (fun lam : ℕ => √(12 * π) * (racahDelta (fun e => lam * j e) *
      Real.exp (prefactorRate (PR.lengths j lam))) *
      (√(√(vol2l (PR.lengths j lam))) * Real.exp (-prefactorRate (PR.lengths j lam)) *
          racahSum (fun e => lam * j e) -
        Real.cos (PR.reggeAction (PR.lengths j lam) + π / 4) / K)) atTop (𝓝 0) := by
    have := ((tendsto_const_nhds (x := √(12 * π))).mul hW).mul hX
    simpa using this
  have t2 : Tendsto (fun lam : ℕ => Real.cos (PR.reggeAction (PR.lengths j lam) + π / 4) *
      (√(12 * π) * (racahDelta (fun e => lam * j e) * Real.exp (prefactorRate (PR.lengths j lam))) / K
        - 1)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun lam : ℕ => √(12 * π) * (racahDelta (fun e => lam * j e) *
        Real.exp (prefactorRate (PR.lengths j lam))) / K - 1) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := √(12 * π))).mul hW).div_const K |>.sub_const 1
      rwa [← hK, div_self hKpos.ne', sub_self] at this
    have hb : IsBoundedUnder (· ≤ ·) atTop
        (norm ∘ fun lam : ℕ => Real.cos (PR.reggeAction (PR.lengths j lam) + π / 4)) :=
      isBoundedUnder_of ⟨1, fun lam => by simpa using Real.abs_cos_le_one _⟩
    have := hlim.zero_mul_isBoundedUnder_le hb
    refine this.congr fun lam => ?_
    ring
  have t12 := t1.add t2
  rw [add_zero] at t12
  refine t12.congr fun lam => ?_
  rw [hRac lam]
  have hsq : √(12 * π * √(PR.vol2 (PR.lengths j lam 0) (PR.lengths j lam 1) (PR.lengths j lam 2)
      (PR.lengths j lam 3) (PR.lengths j lam 4) (PR.lengths j lam 5))) =
      √(12 * π) * √(√(vol2l (PR.lengths j lam))) := Real.sqrt_mul (by positivity) _
  rw [hsq]
  have he : Real.exp (prefactorRate (PR.lengths j lam)) * Real.exp (-prefactorRate (PR.lengths j lam)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp
  linear_combination (√(12 * π) * racahDelta (fun e => lam * j e) * √(√(vol2l (PR.lengths j lam))) *
    racahSum (fun e => lam * j e) * K) * he

end Lightlike.Asymptotics
