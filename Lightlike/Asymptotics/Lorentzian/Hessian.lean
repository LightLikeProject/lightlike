import Lightlike.Asymptotics.Lorentzian.Critical

/-!
# The second variation of the Lorentzian triangle action

The Hessian of the action at a critical point, as in Section 4.2.3 and Appendix A of Barrett,
Dowdall, Fairbairn, Hellmann and Pereira (2010), is built from the second variation of the
triangle factor `e^{S}` (`triFactor`) of one triangle. Along the line `Z + tW` the first
variation is `triFactor · lineLogDeriv` (`hasDerivAt_triFactor`), and the second variation is
obtained by differentiating `lineLogDeriv`:

`hessLine = -n (⟨W,ξ⟩/⟨Z,ξ⟩)² - (n + 2ip) (‖W‖²/‖Z‖² - 2 (Re⟨Z,W⟩)²/‖Z‖⁴)`

(`hasDerivAt_lineLogDeriv`). Hence `d²/dt² triFactor = triFactor · (lineLogDeriv² + hessLine)`
at `t = 0` (`hasDerivAt_deriv_triFactor_line`).
-/

open Complex
open scoped ComplexConjugate

namespace Lightlike.Asymptotics.Lorentzian

/-- The logarithmic derivative of `triFactor` along the line `Z + tW`, at `t = 0`. -/
noncomputable def lineLogDeriv (n : ℕ) (p : ℝ) (Z ξ W : Spinor) : ℂ :=
  (n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) -
    ((n : ℂ) + 2 * Complex.I * p) * (((inner ℂ Z W).re / ‖Z‖ ^ 2 : ℝ) : ℂ)

/-- The derivative of `lineLogDeriv` along the line, at `t = 0`. -/
noncomputable def hessLine (n : ℕ) (p : ℝ) (Z ξ W : Spinor) : ℂ :=
  -(n : ℂ) * (inner ℂ W ξ / inner ℂ Z ξ) ^ 2 -
    ((n : ℂ) + 2 * Complex.I * p) *
      ((‖W‖ ^ 2 / ‖Z‖ ^ 2 - 2 * (inner ℂ Z W).re ^ 2 / ‖Z‖ ^ 4 : ℝ) : ℂ)

lemma re_inner_line (Z W : Spinor) (t : ℝ) :
    (inner ℂ (Z + t • W) W).re = (inner ℂ Z W).re + t * ‖W‖ ^ 2 := by
  rw [inner_add_left, Complex.add_re, ← Complex.coe_smul, inner_smul_left,
    inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- **The second variation along a line.** The log derivative along `Z + tW` is differentiable at
`t = 0` with derivative `hessLine`. -/
theorem hasDerivAt_lineLogDeriv (n : ℕ) (p : ℝ) {Z ξ : Spinor} (W : Spinor) (hZ : Z ≠ 0)
    (h1 : inner ℂ Z ξ ≠ 0) :
    HasDerivAt (fun t : ℝ => lineLogDeriv n p (Z + t • W) ξ W) (hessLine n p Z ξ W) 0 := by
  have hN : 0 < ‖Z‖ ^ 2 := by positivity
  set a := inner ℂ Z ξ with ha
  set b := inner ℂ W ξ with hb
  set R := (inner ℂ Z W).re with hR
  set w := ‖W‖ ^ 2 with hw
  set N := ‖Z‖ ^ 2 with hNdef
  have hfun : (fun t : ℝ => lineLogDeriv n p (Z + t • W) ξ W) = fun t : ℝ =>
      (n : ℂ) * (b / (a + (t : ℂ) * b)) -
        ((n : ℂ) + 2 * Complex.I * p) *
          (((R + t * w) / (N + 2 * t * R + t ^ 2 * w) : ℝ) : ℂ) := by
    funext t
    simp only [lineLogDeriv, inner_line_left Z W ξ t, re_inner_line Z W t, norm_line_sq Z W t, ha,
      hb, hR, hw, hNdef]
  rw [hfun]
  have hg : HasDerivAt (fun t : ℝ => a + (t : ℂ) * b) b 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const b).const_add a
    simpa using this
  have hq := (hasDerivAt_const (0 : ℝ) b).div hg (by simpa using h1)
  have hq' := hq.const_mul (n : ℂ)
  have hnum : HasDerivAt (fun t : ℝ => R + t * w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w).const_add R
  have hden : HasDerivAt (fun t : ℝ => N + 2 * t * R + t ^ 2 * w) (2 * R) 0 := by
    have h2 := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * R)).const_add N
    have h3 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const w
    convert h2.add h3 using 1
    · funext t; simp; ring
    · simp
  have hr := hnum.div hden (by simpa using hN.ne')
  have hr' := (hr.ofReal_comp).const_mul ((n : ℂ) + 2 * Complex.I * p)
  refine (hq'.sub hr').congr_deriv ?_
  have h4 : ‖Z‖ ^ 4 = N ^ 2 := by rw [hNdef]; ring
  simp only [hessLine, h4, ← hb, ← ha, ← hR, ← hw, ← hNdef]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  clear_value a b R w N
  field_simp
  have hai : a⁻¹ ^ 2 * a ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ h1]; simp
  have hNi : (N : ℂ)⁻¹ ^ 2 * (N : ℂ) ^ 2 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hNc]; simp
  linear_combination (-(N : ℂ) ^ 2 * n * b ^ 2) * hai +
    ((2 * n * (R : ℂ) ^ 2 + 4 * Complex.I * p * (R : ℂ) ^ 2) * a ^ 2 -
      ((n : ℂ) + 2 * Complex.I * p) * w * a ^ 2 * N) * hNi

/-- The first variation of `triFactor` along `Z + tW`, at any parameter `s` where the
overlaps do not vanish. -/
theorem hasDerivAt_triFactor_line (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (W : Spinor) (s : ℝ)
    (hZ : Z + s • W ≠ 0) (hZ' : Z' ≠ 0) (h1 : inner ℂ (Z + s • W) ξ ≠ 0)
    (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    HasDerivAt (fun t : ℝ => triFactor n p (Z + t • W) ξ Z' ξ')
      (triFactor n p (Z + s • W) ξ Z' ξ' * lineLogDeriv n p (Z + s • W) ξ W) s := by
  have hd := hasDerivAt_triFactor n p (ξ := ξ) (Z' := Z') (ξ' := ξ') W hZ hZ' h1 h2
  rw [← sub_self s] at hd
  have hd' := HasDerivAt.comp_sub_const s s hd
  convert hd' using 1
  funext t
  simp only [sub_smul, add_assoc]
  congr 2
  abel
  rfl

/-- **The second variation of the triangle factor.** Along `Z + tW` the derivative of
`triFactor` is differentiable at `t = 0`, with second derivative
`triFactor · (lineLogDeriv² + hessLine)`. -/
theorem hasDerivAt_deriv_triFactor_line (n : ℕ) (p : ℝ) {Z ξ Z' ξ' : Spinor} (W : Spinor)
    (hZ : Z ≠ 0) (hZ' : Z' ≠ 0) (h1 : inner ℂ Z ξ ≠ 0) (h2 : inner ℂ (jMap ξ') Z' ≠ 0) :
    HasDerivAt (deriv fun t : ℝ => triFactor n p (Z + t • W) ξ Z' ξ')
      (triFactor n p Z ξ Z' ξ' *
        (lineLogDeriv n p Z ξ W ^ 2 + hessLine n p Z ξ W)) 0 := by
  have hc : Continuous fun s : ℝ => Z + s • W := by fun_prop
  have hev1 : ∀ᶠ s : ℝ in nhds 0, Z + s • W ≠ 0 := by
    have := (hc.continuousAt (x := 0)).eventually_ne (by simpa using hZ)
    simpa using this
  have hc2 : Continuous fun s : ℝ => inner ℂ (Z + s • W) ξ := by
    simp only [inner_line_left]; fun_prop
  have hev2 : ∀ᶠ s : ℝ in nhds 0, inner ℂ (Z + s • W) ξ ≠ 0 := by
    have := (hc2.continuousAt (x := 0)).eventually_ne (by simpa using h1)
    simpa using this
  have hF := hasDerivAt_triFactor_line n p (ξ := ξ) (Z' := Z') (ξ' := ξ') W 0
    (by simpa using hZ) hZ' (by simpa using h1) h2
  have hL := hasDerivAt_lineLogDeriv n p W hZ h1
  have hprod := (hF.mul hL)
  have heq : (deriv fun t : ℝ => triFactor n p (Z + t • W) ξ Z' ξ') =ᶠ[nhds 0]
      fun s => triFactor n p (Z + s • W) ξ Z' ξ' * lineLogDeriv n p (Z + s • W) ξ W := by
    filter_upwards [hev1, hev2] with s hs1 hs2
    exact (hasDerivAt_triFactor_line n p (ξ := ξ) (Z' := Z') (ξ' := ξ') W s hs1 hZ' hs2 h2).deriv
  refine (hprod.congr_of_eventuallyEq heq).congr_deriv ?_
  simp
  ring

/-- The scalar `(β × α) · n̂` for `c = β + iα` and the spin vector `n̂ = spinVec ξ`. -/
noncomputable def crossSpin (c : Fin 3 → ℂ) (ξ : Spinor) : ℝ :=
  ((c 1).re * (c 2).im - (c 2).re * (c 1).im) * spinVec ξ 0 +
    ((c 2).re * (c 0).im - (c 0).re * (c 2).im) * spinVec ξ 1 +
    ((c 0).re * (c 1).im - (c 1).re * (c 0).im) * spinVec ξ 2

/-- `4 ‖L† ξ‖² = (Σ |c_i|²) ‖ξ‖² + 2 (β × α) · n̂` for `L = gen c`, `c = β + iα`. -/
lemma norm_adjoint_gen_sq (c : Fin 3 → ℂ) (ξ : Spinor) :
    4 * ‖LinearMap.adjoint (gen c) ξ‖ ^ 2 =
      (∑ i, ‖c i‖ ^ 2) * ‖ξ‖ ^ 2 + 2 * crossSpin c ξ := by
  rw [adjoint_gen]
  simp only [crossSpin, Fin.sum_univ_three, spinVec, EuclideanSpace.norm_eq, Fin.sum_univ_two,
    gen_apply_zero, gen_apply_one]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.div_re,
    Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- **The second variation of a triangle factor under `X ↦ X exp(tL)`**, `L = gen c`, at a point
where `Z` is parallel to `ξ` (BDFHP Appendix A, one triangle). With `n̂ = spinVec ξ`,
`c = β + iα` and `B = ½ β · n̂`:
`-n (½ c · n̂)² - (n + 2ip) (¼ (|β|² + |α|² + 2 (β × α) · n̂) - 2 B²)`. -/
noncomputable def hessGroup (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) (ξ : Spinor) : ℂ :=
  -(n : ℂ) * ((1 / 2 : ℂ) * ∑ i, c i * (spinVec ξ i : ℂ)) ^ 2 -
    ((n : ℂ) + 2 * Complex.I * p) *
      (((1 / 4 : ℝ) * ((∑ i, ‖c i‖ ^ 2) + 2 * crossSpin c ξ) -
        2 * ((1 / 2 : ℝ) * ∑ i, ((c i).re * spinVec ξ i : ℝ)) ^ 2 : ℝ) : ℂ)

/-- `hessLine` along the group variation `Z = λξ`, `W = L†Z` is `hessGroup`. -/
theorem hessLine_group (n : ℕ) (p : ℝ) (c : Fin 3 → ℂ) {ξ : Spinor} {lam : ℂ} (hlam : lam ≠ 0)
    (hξ : ‖ξ‖ = 1) :
    hessLine n p (lam • ξ) ξ (LinearMap.adjoint (gen c) (lam • ξ)) = hessGroup n p c ξ := by
  have hin : inner ℂ ξ ξ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hξ]; simp
  have hl : inner ℂ (lam • ξ) ξ = conj lam := by
    rw [inner_smul_left, hin, mul_one]
  have hW : inner ℂ (LinearMap.adjoint (gen c) (lam • ξ)) ξ =
      conj lam * inner ℂ ξ (gen c ξ) := by
    rw [LinearMap.adjoint_inner_left, inner_smul_left]
  have hZW : inner ℂ (lam • ξ) (LinearMap.adjoint (gen c) (lam • ξ)) =
      conj (conj lam * lam * inner ℂ ξ (gen c ξ)) := by
    rw [← inner_conj_symm, LinearMap.adjoint_inner_left, map_smul, inner_smul_left,
      inner_smul_right]
    simp
    ring
  have hnl : ‖lam • ξ‖ ^ 2 = ‖lam‖ ^ 2 := by rw [norm_smul, hξ, mul_one]
  have hlam0 : ‖lam‖ ^ 2 ≠ 0 := by positivity
  have hq : (inner ℂ ξ (gen c ξ)).re = (1 / 2 : ℝ) * ∑ i, ((c i).re * spinVec ξ i : ℝ) := by
    rw [inner_gen_self]
    simp [Complex.re_sum, Finset.mul_sum]
  have hre : (inner ℂ (lam • ξ) (LinearMap.adjoint (gen c) (lam • ξ))).re =
      ‖lam‖ ^ 2 * (inner ℂ ξ (gen c ξ)).re := by
    rw [hZW, Complex.conj_re, Complex.conj_mul']
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hWn : ‖LinearMap.adjoint (gen c) (lam • ξ)‖ ^ 2 =
      ‖lam‖ ^ 2 * ‖LinearMap.adjoint (gen c) ξ‖ ^ 2 := by
    rw [map_smul, norm_smul, mul_pow]
  have hnorm := norm_adjoint_gen_sq c ξ
  rw [hξ, one_pow, mul_one] at hnorm
  have hnorm' : ‖LinearMap.adjoint (gen c) ξ‖ ^ 2 =
      (1 / 4 : ℝ) * ((∑ i, ‖c i‖ ^ 2) + 2 * crossSpin c ξ) := by linarith
  have hc : (conj lam) ≠ 0 := by simpa using hlam
  unfold hessLine hessGroup
  rw [hW, hl, hre, hnl, hWn, hq, inner_gen_self, hnorm']
  have e1 : conj lam * ((1 / 2 : ℂ) * ∑ i, c i * (spinVec ξ i : ℂ)) / conj lam =
      (1 / 2 : ℂ) * ∑ i, c i * (spinVec ξ i : ℂ) := by field_simp
  have e2 : (‖lam‖ ^ 2 * ((1 / 4 : ℝ) * ((∑ i, ‖c i‖ ^ 2) + 2 * crossSpin c ξ)) / ‖lam‖ ^ 2 -
      2 * (‖lam‖ ^ 2 * ((1 / 2 : ℝ) * ∑ i, ((c i).re * spinVec ξ i : ℝ))) ^ 2 / ‖lam‖ ^ 4 : ℝ) =
      (1 / 4 : ℝ) * ((∑ i, ‖c i‖ ^ 2) + 2 * crossSpin c ξ) -
        2 * ((1 / 2 : ℝ) * ∑ i, ((c i).re * spinVec ξ i : ℝ)) ^ 2 := by
    field_simp
  have h4 : ‖lam • ξ‖ ^ 4 = ‖lam‖ ^ 4 := by rw [norm_smul, hξ, mul_one]
  rw [h4, e1, e2]

/-- Trust check: a rotation about the axis of `e0`, `c = (0, 0, i)`, only changes the phase of
`Z`; the second variation is `-i p / 2`. -/
example (n : ℕ) (p : ℝ) :
    hessGroup n p (fun i => if i = 2 then Complex.I else 0) e0 = -(Complex.I * p / 2) := by
  simp [hessGroup, crossSpin, Fin.sum_univ_three, spinVec_e0]
  linear_combination (-(n : ℂ) / 4) * Complex.I_sq

/-- Wrong-model control: the boost `c = (0, 0, 1)` along the same axis gives the opposite sign,
`+i p / 2`, so `hessGroup` distinguishes boosts from rotations. -/
example (n : ℕ) (p : ℝ) :
    hessGroup n p (fun i => if i = 2 then (1 : ℂ) else 0) e0 = Complex.I * p / 2 := by
  simp [hessGroup, crossSpin, Fin.sum_univ_three, spinVec_e0]
  ring

end Lightlike.Asymptotics.Lorentzian
