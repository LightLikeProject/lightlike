module

public import Lightlike.Lorentz.SL2RPrincipal
public import Lightlike.Lorentz.SL2RDiscrete

/-!
# The Casimir operator of SL(2,ℝ) on the principal and discrete series

The Lie algebra `sl(2,ℝ)` has the basis `E = [[0,1],[0,0]]`, `F = [[0,0],[1,0]]`,
`H = diag(1,-1)` with `[E, F] = H`, and its Casimir element is `Ω = H²/4 + (EF + FE)/2`. The
one-parameter subgroups `upper t = exp(tE)`, `lower t = exp(tF)` and `expH t = exp(tH)` give the
derived actions as derivatives at `t = 0` (`derivAlong`), and `casimir A` is `Ω` built from
them.

## Main results

* `derivAlong_lower`, `derivAlong_upper`, `derivAlong_expH`: on the principal series
  `P^{ε,iν}` (`act ε ν`, any complex `ν`) the generators act on differentiable functions by
  `F = d/dx`, `E = (iν - 1) x - x² d/dx`, `H = (1 - iν) + 2x d/dx`.
* `commutator_principal`: `[E, F] = H` on twice-differentiable functions, so the derived action
  respects the Lie bracket.
* `casimir_principal`: **`Ω = -(1 + ν²)/4`** on twice-differentiable functions. For real `ν`
  (the unitary principal series) this is `≤ -1/4`.
* `derivAlong_lower_D`, `derivAlong_upper_D`, `derivAlong_expH_D`, `commutator_discrete` and
  `casimir_discrete`: for the weight-`n` action `actC n` on functions holomorphic on the upper
  half-plane, `F = d/dw`, `E = -n w - w² d/dw`, `H = n + 2w d/dw`, `[E, F] = H` and
  **`Ω = (n/2)(n/2 - 1)`**.
* `casimir_lowestVec`: the nonzero vector `(w + i)⁻ⁿ` of `A²_n` has Casimir eigenvalue
  `(n/2)(n/2 - 1)`.

With `j = -s/2`, where `s = 1 - iν` or `s = n` is the homogeneity in the `H` action, both values
are `j(j + 1)`, the normalisation used for JT gravity (`C = -1/4 - (ν/2)²` on the principal
series, `C = h(h - 1)` with `h = n/2` on the discrete series). The Casimir separates the two
families: `Ω ≤ -1/4` on the unitary principal series and `Ω ≥ 0` on `D_n⁺` for `n ≥ 2`
(`casimir_principal_le`, `casimir_discrete_nonneg`).

The derivatives are pointwise, as for `SL(2,ℂ)` in `Homogeneous.lean`: the identities are
those of differential operators on smooth functions, not statements about unbounded operators
on `L²`.

References: A. W. Knapp, *Representation Theory of Semisimple Groups* (Princeton, 1986),
Ch. II §§4–5; S. Lang, *SL₂(ℝ)* (Springer, 1985), Ch. VI.
-/

@[expose] public section

open Complex Filter Topology Set

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-! ## Derived actions and the Casimir operator -/

/-- The one-parameter subgroup `exp(tH) = diag(eᵗ, e⁻ᵗ)`. -/
def expH (t : ℝ) : SL2R := diagSL (Real.exp t) (Real.exp_pos t).ne'

/-- The derivative at `t = 0` of an action `A` along a curve `γ`, evaluated pointwise: the
derived action of the tangent vector `γ'(0)` on a function `f`. -/
def derivAlong {X : Type*} (A : SL2R → (X → ℂ) → X → ℂ) (γ : ℝ → SL2R) (f : X → ℂ) (x : X) :
    ℂ :=
  deriv (fun t => A (γ t) f x) 0

/-- **The Casimir operator** `Ω = H²/4 + (EF + FE)/2` of an action `A`, with the derived actions
of `E`, `F`, `H` taken along `upper`, `lower` and `expH`. -/
def casimir {X : Type*} (A : SL2R → (X → ℂ) → X → ℂ) (f : X → ℂ) (x : X) : ℂ :=
  derivAlong A expH (derivAlong A expH f) x / 4 +
    (derivAlong A upper (derivAlong A lower f) x + derivAlong A lower (derivAlong A upper f) x) / 2

/-! ## The principal series -/

section Principal

variable (ε : ℤ) (ν : ℂ)

lemma mult_of_pos {u : ℝ} (hu : 0 < u) :
    mult ε ν u = Complex.exp ((Real.log u : ℂ) * (I * ν - 1)) := by
  rw [mult, abs_of_pos hu, div_self hu.ne', Complex.ofReal_one, one_zpow, mul_one,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hu.ne'), Complex.ofReal_log hu.le]

/-- The multiplier `m(u) = |u|^{iν-1} sgn(u)^ε` has derivative `iν - 1` at `u = 1`. -/
lemma hasDerivAt_mult_one : HasDerivAt (mult ε ν) (I * ν - 1) 1 := by
  have h := ((Real.hasDerivAt_log one_ne_zero).ofReal_comp.mul_const (I * ν - 1)).cexp
  simp only [Real.log_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero, inv_one,
    Complex.ofReal_one, one_mul] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds one_pos] with u hu using mult_of_pos ε ν hu

/-- **The derived principal-series action along a curve** `γ` through `1`: if the denominator
and the Möbius map of `γ(t)` at `x` have derivatives `d` and `m` at `t = 0`, then
`d/dt|₀ (π(γ t) ψ)(x) = (iν - 1) d ψ(x) + m ψ'(x)`. -/
theorem hasDerivAt_act_curve (γ : ℝ → SL2R) {x d m : ℝ} {ψ : ℝ → ℂ}
    (hψ : DifferentiableAt ℝ ψ x) (hD0 : den (γ 0) x = 1) (hM0 : mob (γ 0) x = x)
    (hD : HasDerivAt (fun t => den (γ t) x) d 0) (hM : HasDerivAt (fun t => mob (γ t) x) m 0) :
    HasDerivAt (fun t => act ε ν (γ t) ψ x) ((I * ν - 1) * d * ψ x + m * deriv ψ x) 0 := by
  have h1 : HasDerivAt (fun t => mult ε ν (den (γ t) x)) (d • (I * ν - 1)) 0 :=
    (hasDerivAt_mult_one ε ν).scomp_of_eq 0 hD hD0.symm
  have h2 : HasDerivAt (fun t => ψ (mob (γ t) x)) (m • deriv ψ x) 0 :=
    hψ.hasDerivAt.scomp_of_eq 0 hM hM0.symm
  refine (h1.mul h2).congr_deriv ?_
  rw [hD0, hM0, mult_one, Complex.real_smul, Complex.real_smul]
  ring

lemma den_lower (t x : ℝ) : den (lower t) x = 1 := by simp [den, lower]
lemma mob_lower (t x : ℝ) : mob (lower t) x = x + t := by simp [mob, num, den, lower]
lemma den_upper (t x : ℝ) : den (upper t) x = t * x + 1 := by simp [den, upper]
lemma mob_upper (t x : ℝ) : mob (upper t) x = x / (t * x + 1) := by simp [mob, num, den, upper]
lemma den_expH (t x : ℝ) : den (expH t) x = (Real.exp t)⁻¹ := by simp [den, expH, diagSL]
lemma mob_expH (t x : ℝ) : mob (expH t) x = Real.exp t * x * Real.exp t := by
  simp [mob, num, den, expH, diagSL]

lemma hasDerivAt_den_lower (x : ℝ) : HasDerivAt (fun t => den (lower t) x) 0 0 := by
  simp only [den_lower]; exact hasDerivAt_const _ _

lemma hasDerivAt_mob_lower (x : ℝ) : HasDerivAt (fun t => mob (lower t) x) 1 0 := by
  simp only [mob_lower]; exact (hasDerivAt_id' (x := (0 : ℝ))).const_add x

lemma hasDerivAt_den_upper (x : ℝ) : HasDerivAt (fun t => den (upper t) x) x 0 := by
  simp only [den_upper]
  exact ((hasDerivAt_id' (x := (0 : ℝ))).mul_const x |>.add_const 1).congr_deriv (one_mul x)

lemma hasDerivAt_mob_upper (x : ℝ) : HasDerivAt (fun t => mob (upper t) x) (-x ^ 2) 0 := by
  simp only [mob_upper]
  exact ((hasDerivAt_const (0 : ℝ) x).div ((hasDerivAt_id' (x := (0 : ℝ))).mul_const x
    |>.add_const 1) (by norm_num)).congr_deriv (by ring)

lemma hasDerivAt_den_expH (x : ℝ) : HasDerivAt (fun t => den (expH t) x) (-1) 0 := by
  simp only [den_expH]
  exact ((Real.hasDerivAt_exp 0).inv (Real.exp_pos 0).ne').congr_deriv (by simp)

lemma hasDerivAt_mob_expH (x : ℝ) : HasDerivAt (fun t => mob (expH t) x) (2 * x) 0 := by
  simp only [mob_expH]
  exact (((Real.hasDerivAt_exp 0).mul_const x).mul (Real.hasDerivAt_exp 0)).congr_deriv
    (by simp only [Real.exp_zero, one_mul, mul_one]; ring)

/-- **`F` acts by `d/dx`** on the principal series. -/
theorem derivAlong_lower {ψ : ℝ → ℂ} {x : ℝ} (hψ : DifferentiableAt ℝ ψ x) :
    derivAlong (act ε ν) lower ψ x = deriv ψ x := by
  rw [derivAlong, (hasDerivAt_act_curve ε ν lower hψ (den_lower 0 x)
    (by rw [mob_lower, add_zero]) (hasDerivAt_den_lower x) (hasDerivAt_mob_lower x)).deriv]
  simp

/-- **`E` acts by `(iν - 1) x - x² d/dx`** on the principal series. -/
theorem derivAlong_upper {ψ : ℝ → ℂ} {x : ℝ} (hψ : DifferentiableAt ℝ ψ x) :
    derivAlong (act ε ν) upper ψ x = (I * ν - 1) * x * ψ x - x ^ 2 * deriv ψ x := by
  rw [derivAlong, (hasDerivAt_act_curve ε ν upper hψ (by rw [den_upper]; ring)
    (by rw [mob_upper]; simp) (hasDerivAt_den_upper x) (hasDerivAt_mob_upper x)).deriv]
  push_cast; ring

/-- **`H` acts by `(1 - iν) + 2x d/dx`** on the principal series. -/
theorem derivAlong_expH {ψ : ℝ → ℂ} {x : ℝ} (hψ : DifferentiableAt ℝ ψ x) :
    derivAlong (act ε ν) expH ψ x = (1 - I * ν) * ψ x + 2 * x * deriv ψ x := by
  rw [derivAlong, (hasDerivAt_act_curve ε ν expH hψ (by rw [den_expH]; simp)
    (by rw [mob_expH]; simp) (hasDerivAt_den_expH x) (hasDerivAt_mob_expH x)).deriv]
  push_cast; ring

variable {ε ν}

/-- `x ↦ c x ψ(x) - x² ψ'(x)` has the expected derivative. -/
lemma hasDerivAt_upperForm (c : ℂ) {ψ : ℝ → ℂ} {x : ℝ} (hψ : DifferentiableAt ℝ ψ x)
    (hψ' : DifferentiableAt ℝ (deriv ψ) x) :
    HasDerivAt (fun y : ℝ => c * y * ψ y - (y : ℂ) ^ 2 * deriv ψ y)
      (c * ψ x + c * x * deriv ψ x - (2 * x * deriv ψ x + (x : ℂ) ^ 2 * deriv (deriv ψ) x)) x := by
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id' (x := x)).ofReal_comp
  refine (((hx.const_mul c).mul hψ.hasDerivAt).sub ((hx.fun_pow 2).mul hψ'.hasDerivAt))
    |>.congr_deriv ?_
  push_cast; ring

/-- `x ↦ a ψ(x) + 2x ψ'(x)` has the expected derivative. -/
lemma hasDerivAt_hForm (a : ℂ) {ψ : ℝ → ℂ} {x : ℝ} (hψ : DifferentiableAt ℝ ψ x)
    (hψ' : DifferentiableAt ℝ (deriv ψ) x) :
    HasDerivAt (fun y : ℝ => a * ψ y + 2 * y * deriv ψ y)
      (a * deriv ψ x + (2 * deriv ψ x + 2 * x * deriv (deriv ψ) x)) x := by
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id' (x := x)).ofReal_comp
  refine ((hψ.hasDerivAt.const_mul a).add ((hx.const_mul 2).mul hψ'.hasDerivAt)).congr_deriv ?_
  ring

/-- The second-order derived actions of the principal series on a twice-differentiable `ψ`. -/
lemma derivAlong_principal_second {ψ : ℝ → ℂ} (hψ : Differentiable ℝ ψ)
    (hψ' : Differentiable ℝ (deriv ψ)) (x : ℝ) :
    derivAlong (act ε ν) upper (derivAlong (act ε ν) lower ψ) x =
        (I * ν - 1) * x * deriv ψ x - x ^ 2 * deriv (deriv ψ) x ∧
      derivAlong (act ε ν) lower (derivAlong (act ε ν) upper ψ) x =
        (I * ν - 1) * ψ x + (I * ν - 1) * x * deriv ψ x -
          (2 * x * deriv ψ x + (x : ℂ) ^ 2 * deriv (deriv ψ) x) ∧
      derivAlong (act ε ν) expH (derivAlong (act ε ν) expH ψ) x =
        (1 - I * ν) * ((1 - I * ν) * ψ x + 2 * x * deriv ψ x) +
          2 * x * ((1 - I * ν) * deriv ψ x + (2 * deriv ψ x + 2 * x * deriv (deriv ψ) x)) := by
  have eL : derivAlong (act ε ν) lower ψ = deriv ψ :=
    funext fun y => derivAlong_lower ε ν (hψ y)
  have eU : derivAlong (act ε ν) upper ψ =
      fun y : ℝ => (I * ν - 1) * y * ψ y - (y : ℂ) ^ 2 * deriv ψ y :=
    funext fun y => derivAlong_upper ε ν (hψ y)
  have eH : derivAlong (act ε ν) expH ψ = fun y : ℝ => (1 - I * ν) * ψ y + 2 * y * deriv ψ y :=
    funext fun y => derivAlong_expH ε ν (hψ y)
  have hU := hasDerivAt_upperForm (I * ν - 1) (hψ x) (hψ' x)
  have hH := hasDerivAt_hForm (1 - I * ν) (hψ x) (hψ' x)
  refine ⟨?_, ?_, ?_⟩
  · rw [eL, derivAlong_upper ε ν (hψ' x)]
  · rw [eU, derivAlong_lower ε ν hU.differentiableAt, hU.deriv]
  · rw [eH, derivAlong_expH ε ν hH.differentiableAt, hH.deriv]

/-- **The Lie bracket is respected**: `[E, F] = H` on twice-differentiable functions. -/
theorem commutator_principal {ψ : ℝ → ℂ} (hψ : Differentiable ℝ ψ)
    (hψ' : Differentiable ℝ (deriv ψ)) (x : ℝ) :
    derivAlong (act ε ν) upper (derivAlong (act ε ν) lower ψ) x -
        derivAlong (act ε ν) lower (derivAlong (act ε ν) upper ψ) x =
      derivAlong (act ε ν) expH ψ x := by
  obtain ⟨h1, h2, -⟩ := derivAlong_principal_second (ε := ε) (ν := ν) hψ hψ' x
  rw [h1, h2, derivAlong_expH ε ν (hψ x)]
  ring

/-- **The Casimir value of the principal series**: `Ω ψ = -(1 + ν²)/4 · ψ` for every
twice-differentiable `ψ`, for every complex `ν`. -/
theorem casimir_principal {ψ : ℝ → ℂ} (hψ : Differentiable ℝ ψ)
    (hψ' : Differentiable ℝ (deriv ψ)) (x : ℝ) :
    casimir (act ε ν) ψ x = -(1 + ν ^ 2) / 4 * ψ x := by
  obtain ⟨h1, h2, h3⟩ := derivAlong_principal_second (ε := ε) (ν := ν) hψ hψ' x
  rw [casimir, h1, h2, h3]
  linear_combination (ν ^ 2 / 4 * ψ x) * Complex.I_sq

/-- On the unitary principal series (`ν` real) the Casimir value `-(1 + ν²)/4` is at most
`-1/4`. -/
theorem casimir_principal_le (ν : ℝ) : (-(1 + (ν : ℂ) ^ 2) / 4).re ≤ -1 / 4 := by
  have : (-(1 + (ν : ℂ) ^ 2) / 4) = ((-(1 + ν ^ 2) / 4 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  nlinarith [sq_nonneg ν]

end Principal

/-! ## The holomorphic discrete series -/

section Discrete

variable (n : ℕ)

/-- The Möbius map `w ↦ (a w + c) / (b w + d)` of `gᵀ` on `ℂ`. -/
def mobC (g : SL2R) (w : ℂ) : ℂ := (g 0 0 * w + g 1 0) / jac g w

/-- The weight-`n` action on functions `ℂ → ℂ`:
`(D_n(g) F)(w) = (b w + d)⁻ⁿ F((a w + c) / (b w + d))`. On the upper half-plane it is the
action `discreteAction` on representatives (`actC_coe`). -/
def actC (g : SL2R) (F : ℂ → ℂ) (w : ℂ) : ℂ := jac g w ^ (-(n : ℤ)) * F (mobC g w)

/-- `actC` restricted to `ℍ` is the formula of `discreteAction` (`coeFn_discreteAction`). -/
lemma actC_coe (g : SL2R) (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    actC n g (fun w => f (UpperHalfPlane.ofComplex w)) z =
      jac g z ^ (-(n : ℤ)) * f (tsmul g z) := by
  rw [actC, mobC, ← coe_tsmul, UpperHalfPlane.ofComplex_apply]

/-- **The derived discrete-series action along a curve** `γ` through `1`. -/
theorem hasDerivAt_actC_curve (γ : ℝ → SL2R) {w d m : ℂ} {F : ℂ → ℂ}
    (hF : DifferentiableAt ℂ F w) (hD0 : jac (γ 0) w = 1) (hM0 : mobC (γ 0) w = w)
    (hD : HasDerivAt (fun t => jac (γ t) w) d 0) (hM : HasDerivAt (fun t => mobC (γ t) w) m 0) :
    HasDerivAt (fun t => actC n (γ t) F w) (-n * d * F w + m * deriv F w) 0 := by
  have h1 : HasDerivAt (fun t => jac (γ t) w ^ (-(n : ℤ)))
      (((-(n : ℤ) : ℤ) : ℂ) * jac (γ 0) w ^ (-(n : ℤ) - 1) * d) 0 :=
    (hasDerivAt_zpow (-(n : ℤ)) (jac (γ 0) w) (Or.inl (by rw [hD0]; exact one_ne_zero))).comp_of_eq
      0 hD rfl
  have h2 : HasDerivAt (fun t => F (mobC (γ t) w)) (deriv F w * m) 0 :=
    hF.hasDerivAt.comp_of_eq 0 hM hM0.symm
  refine (h1.mul h2).congr_deriv ?_
  rw [hD0, hM0, one_zpow, one_zpow]
  push_cast; ring

lemma jac_lower (t : ℝ) (w : ℂ) : jac (lower t) w = 1 := by simp [jac, lower]
lemma mobC_lower (t : ℝ) (w : ℂ) : mobC (lower t) w = w + t := by simp [mobC, jac, lower]
lemma jac_upper (t : ℝ) (w : ℂ) : jac (upper t) w = t * w + 1 := by simp [jac, upper]
lemma mobC_upper (t : ℝ) (w : ℂ) : mobC (upper t) w = w / (t * w + 1) := by
  simp [mobC, jac, upper]
lemma jac_expH (t : ℝ) (w : ℂ) : jac (expH t) w = ((Real.exp t)⁻¹ : ℝ) := by
  simp only [jac, expH, diagSL, coe_mk]; simp
lemma mobC_expH (t : ℝ) (w : ℂ) : mobC (expH t) w = ((Real.exp t * Real.exp t : ℝ) : ℂ) * w := by
  simp only [mobC, jac_expH]
  simp only [expH, diagSL, coe_mk]; simp
  field_simp

lemma hasDerivAt_jac_lower (w : ℂ) : HasDerivAt (fun t : ℝ => jac (lower t) w) 0 0 := by
  simp only [jac_lower]; exact hasDerivAt_const _ _

lemma hasDerivAt_mobC_lower (w : ℂ) : HasDerivAt (fun t : ℝ => mobC (lower t) w) 1 0 := by
  simp only [mobC_lower]
  exact ((hasDerivAt_id' (x := (0 : ℝ))).ofReal_comp.const_add w).congr_deriv (by simp)

lemma hasDerivAt_jac_upper (w : ℂ) : HasDerivAt (fun t : ℝ => jac (upper t) w) w 0 := by
  simp only [jac_upper]
  exact (((hasDerivAt_id' (x := (0 : ℝ))).ofReal_comp.mul_const w).add_const 1).congr_deriv
    (by simp)

lemma hasDerivAt_mobC_upper (w : ℂ) : HasDerivAt (fun t : ℝ => mobC (upper t) w) (-w ^ 2) 0 := by
  simp only [mobC_upper]
  exact ((hasDerivAt_const (0 : ℝ) w).div
    (((hasDerivAt_id' (x := (0 : ℝ))).ofReal_comp.mul_const w).add_const 1)
    (by simp)).congr_deriv (by simp; ring)

lemma hasDerivAt_jac_expH (w : ℂ) : HasDerivAt (fun t : ℝ => jac (expH t) w) (-1) 0 := by
  simp only [jac_expH]
  exact ((Real.hasDerivAt_exp 0).inv (Real.exp_pos 0).ne').ofReal_comp.congr_deriv (by simp)

lemma hasDerivAt_mobC_expH (w : ℂ) : HasDerivAt (fun t : ℝ => mobC (expH t) w) (2 * w) 0 := by
  simp only [mobC_expH]
  exact (((Real.hasDerivAt_exp 0).mul (Real.hasDerivAt_exp 0)).ofReal_comp.mul_const w).congr_deriv
    (by rw [Real.exp_zero]; push_cast; ring)

/-- **`F` acts by `d/dw`** on the discrete series. -/
theorem derivAlong_lower_D {F : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℂ F w) :
    derivAlong (actC n) lower F w = deriv F w := by
  rw [derivAlong, (hasDerivAt_actC_curve n lower hF (jac_lower 0 w)
    (by rw [mobC_lower]; simp) (hasDerivAt_jac_lower w) (hasDerivAt_mobC_lower w)).deriv]
  simp

/-- **`E` acts by `-n w - w² d/dw`** on the discrete series. -/
theorem derivAlong_upper_D {F : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℂ F w) :
    derivAlong (actC n) upper F w = -n * w * F w - w ^ 2 * deriv F w := by
  rw [derivAlong, (hasDerivAt_actC_curve n upper hF (by rw [jac_upper]; simp)
    (by rw [mobC_upper]; simp) (hasDerivAt_jac_upper w) (hasDerivAt_mobC_upper w)).deriv]
  ring

/-- **`H` acts by `n + 2w d/dw`** on the discrete series. -/
theorem derivAlong_expH_D {F : ℂ → ℂ} {w : ℂ} (hF : DifferentiableAt ℂ F w) :
    derivAlong (actC n) expH F w = n * F w + 2 * w * deriv F w := by
  rw [derivAlong, (hasDerivAt_actC_curve n expH hF (by rw [jac_expH]; simp)
    (by rw [mobC_expH]; simp) (hasDerivAt_jac_expH w) (hasDerivAt_mobC_expH w)).deriv]
  ring

/-- The upper half-plane as an open subset of `ℂ`. -/
abbrev upperSet : Set ℂ := {w : ℂ | 0 < w.im}

lemma isOpen_upperSet : IsOpen upperSet := isOpen_lt continuous_const Complex.continuous_im

variable {n}

/-- The second-order derived actions of the discrete series on a function holomorphic on the
upper half-plane. -/
lemma derivAlong_discrete_second {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperSet) {w : ℂ}
    (hw : w ∈ upperSet) :
    derivAlong (actC n) upper (derivAlong (actC n) lower F) w =
        -n * w * deriv F w - w ^ 2 * deriv (deriv F) w ∧
      derivAlong (actC n) lower (derivAlong (actC n) upper F) w =
        -n * F w - n * w * deriv F w - (2 * w * deriv F w + w ^ 2 * deriv (deriv F) w) ∧
      derivAlong (actC n) expH (derivAlong (actC n) expH F) w =
        n * (n * F w + 2 * w * deriv F w) +
          2 * w * (n * deriv F w + (2 * deriv F w + 2 * w * deriv (deriv F) w)) := by
  have hU : upperSet ∈ 𝓝 w := isOpen_upperSet.mem_nhds hw
  have hFd : ∀ v ∈ upperSet, DifferentiableAt ℂ F v := fun v hv =>
    hF.differentiableAt (isOpen_upperSet.mem_nhds hv)
  have hF' : DifferentiableOn ℂ (deriv F) upperSet := hF.deriv isOpen_upperSet
  have hF'w : DifferentiableAt ℂ (deriv F) w := hF'.differentiableAt hU
  have hFw := hFd w hw
  -- the first-order operators agree near `w` with explicit holomorphic functions
  have eL : derivAlong (actC n) lower F =ᶠ[𝓝 w] deriv F :=
    Filter.eventually_of_mem hU fun v hv => derivAlong_lower_D n (hFd v hv)
  have eU : derivAlong (actC n) upper F =ᶠ[𝓝 w]
      fun v => -n * v * F v - v ^ 2 * deriv F v :=
    Filter.eventually_of_mem hU fun v hv => derivAlong_upper_D n (hFd v hv)
  have eH : derivAlong (actC n) expH F =ᶠ[𝓝 w] fun v => n * F v + 2 * v * deriv F v :=
    Filter.eventually_of_mem hU fun v hv => derivAlong_expH_D n (hFd v hv)
  have hUf : HasDerivAt (fun v => -n * v * F v - v ^ 2 * deriv F v)
      (-n * F w - n * w * deriv F w - (2 * w * deriv F w + w ^ 2 * deriv (deriv F) w)) w := by
    refine ((((hasDerivAt_id' (x := w)).const_mul (-(n : ℂ))).mul hFw.hasDerivAt).sub
      (((hasDerivAt_id' (x := w)).fun_pow 2).mul hF'w.hasDerivAt)).congr_deriv ?_
    push_cast; ring
  have hHf : HasDerivAt (fun v => n * F v + 2 * v * deriv F v)
      (n * deriv F w + (2 * deriv F w + 2 * w * deriv (deriv F) w)) w := by
    refine ((hFw.hasDerivAt.const_mul (n : ℂ)).add
      (((hasDerivAt_id' (x := w)).const_mul 2).mul hF'w.hasDerivAt)).congr_deriv ?_
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hd := hF'w.congr_of_eventuallyEq eL
    rw [derivAlong_upper_D n hd, eL.eq_of_nhds, eL.deriv_eq]
  · have hd := hUf.differentiableAt.congr_of_eventuallyEq eU
    rw [derivAlong_lower_D n hd, eU.deriv_eq, hUf.deriv]
  · have hd := hHf.differentiableAt.congr_of_eventuallyEq eH
    rw [derivAlong_expH_D n hd, eH.eq_of_nhds, eH.deriv_eq, hHf.deriv]

/-- **The Lie bracket is respected**: `[E, F] = H` on holomorphic functions. -/
theorem commutator_discrete {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperSet) {w : ℂ}
    (hw : w ∈ upperSet) :
    derivAlong (actC n) upper (derivAlong (actC n) lower F) w -
        derivAlong (actC n) lower (derivAlong (actC n) upper F) w =
      derivAlong (actC n) expH F w := by
  obtain ⟨h1, h2, -⟩ := derivAlong_discrete_second (n := n) hF hw
  rw [h1, h2, derivAlong_expH_D n (hF.differentiableAt (isOpen_upperSet.mem_nhds hw))]
  ring

/-- **The Casimir value of the discrete series**: `Ω F = (n/2)(n/2 - 1) F` on the upper
half-plane for every `F` holomorphic there. -/
theorem casimir_discrete {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperSet) {w : ℂ}
    (hw : w ∈ upperSet) :
    casimir (actC n) F w = (n / 2) * (n / 2 - 1) * F w := by
  obtain ⟨h1, h2, h3⟩ := derivAlong_discrete_second (n := n) hF hw
  rw [casimir, h1, h2, h3]
  ring

/-- For `n ≥ 2` the Casimir value of `D_n⁺` is nonnegative, so it differs from every value
`-(1 + ν²)/4 ≤ -1/4` of the unitary principal series. -/
theorem casimir_discrete_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ ((n : ℝ) / 2) * ((n : ℝ) / 2 - 1) := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply mul_nonneg <;> linarith

/-- **Non-vacuity**: `(w + i)⁻ⁿ`, whose restriction to `ℍ` is the nonzero vector
`lowestVec n` of `A²_n` (`lowestClass_ne_zero`), has Casimir eigenvalue `(n/2)(n/2 - 1)`. -/
theorem casimir_lowestVec {w : ℂ} (hw : w ∈ upperSet) :
    casimir (actC n) (fun v => (v + I) ^ (-(n : ℤ))) w =
      (n / 2) * (n / 2 - 1) * (w + I) ^ (-(n : ℤ)) := by
  refine casimir_discrete (fun v hv => ?_) hw
  have h0 : v + I ≠ 0 := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
    have : 0 < v.im := hv
    linarith
  exact (DifferentiableAt.zpow (f := fun v : ℂ => v + I) (differentiableAt_id.add_const _)
    (Or.inl h0)).differentiableWithinAt

end Discrete

end Lightlike.Lorentz.SL2R
