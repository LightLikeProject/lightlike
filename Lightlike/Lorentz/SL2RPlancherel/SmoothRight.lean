module

public import Mathlib
public import Lightlike.Lorentz.SL2RPlancherel.PolarTorus

/-!
# Right derivatives of smooth functions on `SL(2,ℝ)` in `KAK` coordinates

A function `f : SL(2,ℝ) → ℂ` is *smooth* when it is the restriction of a `C^∞` function
`F : (Fin 2 → Fin 2 → ℝ) → ℂ` on the four entries.  The right derivative of `F` at `g` in the
direction of a matrix `X` is `dF F g X = DF_g (g X)`.  For `g = k_α a(ξ) k_θ` the three partial
derivatives of `P(α, ξ, θ) = F(k_α a(ξ) k_θ)` are
`∂θ P = dF F g J`, `∂ξ P = cos 2θ · dF F g H + sin 2θ · dF F g S`,
`∂α P = cosh ξ · ∂θ P − 2 sinh ξ (cos 2θ · dF F g S − sin 2θ · dF F g H)`
with `J = [[0,1],[-1,0]]`, `H = diag(1/2, -1/2)`, `S = [[0,1/2],[1/2,0]]`.  Layer 2c-i of the
Plancherel formula on `SL(2,ℝ)`, milestone HA3.
-/

@[expose] public section

open Real

noncomputable section

namespace Lightlike.Lorentz.SL2R

/-- The four entries of a matrix, as a point of the normed space `Fin 2 → Fin 2 → ℝ`. -/
abbrev Ent := Fin 2 → Fin 2 → ℝ

/-- A matrix as a point of `Ent`. -/
def ent (M : Matrix (Fin 2) (Fin 2) ℝ) : Ent := fun i j => M i j

/-- The right derivative of a function `F` on the entries at `g` in the direction `X`:
`dF F g X = DF_g (g X)`. -/
def dF (F : Ent → ℂ) (g : Matrix (Fin 2) (Fin 2) ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  fderiv ℝ F (ent g) (ent (g * X))

/-- The tangent matrix `J = [[0,1],[-1,0]]` of the rotations `k_t`. -/
def matJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The tangent matrix `H = diag(1/2, -1/2)` of `a(t)`. -/
def matH : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 2, 0; 0, -1 / 2]

/-- The tangent matrix `S = [[0,1/2],[1/2,0]]` of the symmetric boosts. -/
def matS : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 / 2; 1 / 2, 0]

/-- The chain rule along a matrix curve through `g`: if the matrix curve `c` has derivative `X` at
`0` and `c 0 = 1`, then `t ↦ F (g c(t))` has derivative `dF F g X` at `0`. -/
lemma hasDerivAt_comp_curve {F : Ent → ℂ} (hF : Differentiable ℝ F) (g : Matrix (Fin 2) (Fin 2) ℝ)
    {c : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hc : HasDerivAt (fun t => ent (g * c t)) (ent (g * X)) 0)
    (h0 : c 0 = 1) :
    HasDerivAt (fun t => F (ent (g * c t))) (dF F g X) 0 := by
  have h1 : HasFDerivAt F (fderiv ℝ F (ent (g * c 0))) _ :=
    (hF _).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) hc
  have h3 : HasDerivAt (fun t => F (ent (g * c t))) ((fderiv ℝ F (ent (g * c 0))) (ent (g * X))) 0 := h2
  rw [h0, mul_one] at h3
  exact h3

/-- The derivative of a matrix curve `t ↦ g * c t` from the entries of `c`. -/
lemma hasDerivAt_mul_curve (g : Matrix (Fin 2) (Fin 2) ℝ) {a b c d : ℝ → ℝ}
    {t : ℝ} {va vb vc vd : ℝ}
    (ha : HasDerivAt a va t) (hb : HasDerivAt b vb t)
    (hc : HasDerivAt c vc t) (hd : HasDerivAt d vd t) :
    HasDerivAt (fun s => ent (g * !![a s, b s; c s, d s]))
      (ent (g * !![va, vb; vc, vd])) t := by
  unfold ent
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | exact (ha.const_mul _).add (hc.const_mul _) |>.congr_deriv (by ring)
    | exact (hb.const_mul _).add (hd.const_mul _) |>.congr_deriv (by ring)

/-- A function with a derivative in the shifted variable has that derivative. -/
lemma hasDerivAt_of_shift {φ : ℝ → ℂ} {v : ℂ} {x : ℝ} (h : HasDerivAt (fun t => φ (x + t)) v 0) :
    HasDerivAt φ v x := by
  have h' : HasDerivAt (fun t => φ (x + t)) v (x - x) := by simpa using h
  have := h'.comp_sub_const x x
  simpa using this

/-- The function `P(α, ξ, θ) = F(k_α a(ξ) k_θ)` of the `KAK` coordinates. -/
def kakP (F : Ent → ℂ) (α ξ θ : ℝ) : ℂ :=
  F (ent ((rot α * aR ξ * rot θ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ))

/-- The matrix `g = k_α a(ξ) k_θ`. -/
def kakM (α ξ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := ((rot α * aR ξ * rot θ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ)

lemma coe_aR (ξ : ℝ) : ((aR ξ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.exp (ξ / 2), 0; 0, (Real.exp (ξ / 2))⁻¹] := rfl

/-- **`∂θ`**: the derivative in the right angle is the right derivative in the direction `J`. -/
theorem hasDerivAt_kakP_theta {F : Ent → ℂ} (hF : Differentiable ℝ F) (α ξ θ : ℝ) :
    HasDerivAt (fun θ' => kakP F α ξ θ') (dF F (kakM α ξ θ) matJ) θ := by
  apply hasDerivAt_of_shift
  have hc := hasDerivAt_mul_curve (kakM α ξ θ) (a := fun t => Real.cos t) (b := fun t => Real.sin t)
    (c := fun t => -Real.sin t) (d := fun t => Real.cos t) (t := 0)
    (Real.hasDerivAt_cos 0) (Real.hasDerivAt_sin 0) (Real.hasDerivAt_sin 0).neg
    (Real.hasDerivAt_cos 0)
  have hJ : (!![-Real.sin 0, Real.cos 0; -Real.cos 0, -Real.sin 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      matJ := by simp [matJ]
  rw [hJ] at hc
  have key := hasDerivAt_comp_curve hF (kakM α ξ θ) (c := fun t => !![Real.cos t, Real.sin t; -Real.sin t, Real.cos t]) hc (by ext i j; fin_cases i <;> fin_cases j <;> simp)
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [kakP, kakM, rot_add, ← mul_assoc, Matrix.SpecialLinearGroup.coe_mul, coe_rot]

/-- The right derivative is real-linear in the direction. -/
lemma dF_comb (F : Ent → ℂ) (g X Y : Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) :
    dF F g (a • X + b • Y) = (a : ℂ) * dF F g X + (b : ℂ) * dF F g Y := by
  have h : ent (g * (a • X + b • Y)) = a • ent (g * X) + b • ent (g * Y) := by
    ext i j
    simp [ent, Matrix.mul_add]
  unfold dF
  rw [h, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- Three-term real-linearity of the right derivative. -/
lemma dF_comb3 (F : Ent → ℂ) (g X Y Z : Matrix (Fin 2) (Fin 2) ℝ) (a b c : ℝ) :
    dF F g (a • X + b • Y + c • Z) =
      (a : ℂ) * dF F g X + (b : ℂ) * dF F g Y + (c : ℂ) * dF F g Z := by
  have h : ent (g * (a • X + b • Y + c • Z)) =
      a • ent (g * X) + b • ent (g * Y) + c • ent (g * Z) := by
    ext i j
    simp [ent, Matrix.mul_add]
  unfold dF
  rw [h, map_add, map_add, map_smul, map_smul, map_smul, Complex.real_smul, Complex.real_smul,
    Complex.real_smul]

/-- The conjugated boost `k_{-θ} a(t) k_θ` as an explicit matrix. -/
lemma coe_conj_aR (θ t : ℝ) :
    ((rot (-θ) * aR t * rot θ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.exp (t / 2) * Real.cos θ ^ 2 + Real.exp (-(t / 2)) * Real.sin θ ^ 2,
         (Real.exp (t / 2) - Real.exp (-(t / 2))) * Real.cos θ * Real.sin θ;
         (Real.exp (t / 2) - Real.exp (-(t / 2))) * Real.sin θ * Real.cos θ,
         Real.exp (t / 2) * Real.sin θ ^ 2 + Real.exp (-(t / 2)) * Real.cos θ ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_aR, Real.exp_neg] <;> ring

lemma aR_zero : aR 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aR, diagSL]

lemma aR_add (a b : ℝ) : aR (a + b) = aR a * aR b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aR, diagSL, Matrix.mul_apply, Fin.sum_univ_two, add_div, Real.exp_add]
  ring

lemma rot_mul_rot_neg (θ : ℝ) : rot θ * rot (-θ) = 1 := by
  rw [← rot_add]; simp

lemma kakM_add_xi (α ξ t θ : ℝ) : kakM α (ξ + t) θ =
    kakM α ξ θ * ((rot (-θ) * aR t * rot θ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold kakM
  rw [← Matrix.SpecialLinearGroup.coe_mul]
  congr 1
  rw [aR_add]
  calc rot α * (aR ξ * aR t) * rot θ
      = rot α * aR ξ * (rot θ * rot (-θ)) * aR t * rot θ := by rw [rot_mul_rot_neg]; simp [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/-- **`∂ξ`**: the derivative in `ξ` is `cos 2θ` times the right derivative in direction `H` plus
`sin 2θ` times that in direction `S`. -/
theorem hasDerivAt_kakP_xi {F : Ent → ℂ} (hF : Differentiable ℝ F) (α ξ θ : ℝ) :
    HasDerivAt (fun ξ' => kakP F α ξ' θ)
      ((Real.cos (2 * θ) : ℂ) * dF F (kakM α ξ θ) matH +
        (Real.sin (2 * θ) : ℂ) * dF F (kakM α ξ θ) matS) ξ := by
  apply hasDerivAt_of_shift
  have hp : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (1 / 2) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).div_const 2).exp
    simpa using this
  have hq : HasDerivAt (fun t : ℝ => Real.exp (-(t / 2))) (-(1 / 2)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).div_const 2).neg.exp
    simpa using this
  have hc := hasDerivAt_mul_curve (kakM α ξ θ)
    (a := fun t => Real.exp (t / 2) * Real.cos θ ^ 2 + Real.exp (-(t / 2)) * Real.sin θ ^ 2)
    (b := fun t => (Real.exp (t / 2) - Real.exp (-(t / 2))) * Real.cos θ * Real.sin θ)
    (c := fun t => (Real.exp (t / 2) - Real.exp (-(t / 2))) * Real.sin θ * Real.cos θ)
    (d := fun t => Real.exp (t / 2) * Real.sin θ ^ 2 + Real.exp (-(t / 2)) * Real.cos θ ^ 2)
    (t := 0) (va := 1 / 2 * Real.cos θ ^ 2 + -(1 / 2) * Real.sin θ ^ 2)
    (vb := (1 / 2 - -(1 / 2)) * Real.cos θ * Real.sin θ)
    (vc := (1 / 2 - -(1 / 2)) * Real.sin θ * Real.cos θ)
    (vd := 1 / 2 * Real.sin θ ^ 2 + -(1 / 2) * Real.cos θ ^ 2)
    ((hp.mul_const _).add (hq.mul_const _))
    (((hp.sub hq).mul_const _).mul_const _) (((hp.sub hq).mul_const _).mul_const _)
    ((hp.mul_const _).add (hq.mul_const _))
  have hX : (!![1 / 2 * Real.cos θ ^ 2 + -(1 / 2) * Real.sin θ ^ 2,
      (1 / 2 - -(1 / 2)) * Real.cos θ * Real.sin θ;
      (1 / 2 - -(1 / 2)) * Real.sin θ * Real.cos θ,
      1 / 2 * Real.sin θ ^ 2 + -(1 / 2) * Real.cos θ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.cos (2 * θ) • matH + Real.sin (2 * θ) • matS := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matH, matS, Real.cos_two_mul, Real.sin_two_mul] <;> nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hX] at hc
  have key := hasDerivAt_comp_curve hF (kakM α ξ θ)
    (c := fun t => ((rot (-θ) * aR t * rot θ : SL2R) : Matrix (Fin 2) (Fin 2) ℝ))
    (by simpa only [coe_conj_aR] using hc) (by
      have h1 : rot (-θ) * aR 0 * rot θ = 1 := by
        rw [aR_zero, mul_one, ← rot_add]; simp
      rw [h1]; rfl)
  rw [dF_comb] at key
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show F (ent (kakM α (ξ + t) θ)) = _
  rw [kakM_add_xi]

/-- The left-curve version of `hasDerivAt_mul_curve`. -/
lemma hasDerivAt_mul_curve_left (g : Matrix (Fin 2) (Fin 2) ℝ) {a b c d : ℝ → ℝ}
    {t : ℝ} {va vb vc vd : ℝ}
    (ha : HasDerivAt a va t) (hb : HasDerivAt b vb t)
    (hc : HasDerivAt c vc t) (hd : HasDerivAt d vd t) :
    HasDerivAt (fun s => ent (!![a s, b s; c s, d s] * g))
      (ent (!![va, vb; vc, vd] * g)) t := by
  unfold ent
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | exact (ha.mul_const _).add (hb.mul_const _) |>.congr_deriv (by ring)
    | exact (hc.mul_const _).add (hd.mul_const _) |>.congr_deriv (by ring)

/-- The conjugation identity `J g = g Y` for `g = k_α a(ξ) k_θ`. -/
lemma matJ_mul_kakM (α ξ θ : ℝ) : matJ * kakM α ξ θ = kakM α ξ θ *
    (Real.cosh ξ • matJ - (2 * Real.sinh ξ) • (Real.cos (2 * θ) • matS - Real.sin (2 * θ) • matH)) := by
  have hu := Real.exp_pos (ξ / 2)
  set u := Real.exp (ξ / 2) with hu_def
  have h1 : Real.exp ξ = u * u := by rw [hu_def, ← Real.exp_add]; ring_nf
  have h2 : Real.exp (-ξ) = (u * u)⁻¹ := by rw [Real.exp_neg, h1]
  have hch : Real.cosh ξ = (u * u + (u * u)⁻¹) / 2 := by rw [Real.cosh_eq, h1, h2]
  have hsh : Real.sinh ξ = (u * u - (u * u)⁻¹) / 2 := by rw [Real.sinh_eq, h1, h2]
  have hα := Real.sin_sq_add_cos_sq α
  have hθ := Real.sin_sq_add_cos_sq θ
  unfold kakM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matJ, matS, matH, Matrix.mul_apply, Fin.sum_univ_two, coe_aR, hch, hsh,
      Real.cos_two_mul, Real.sin_two_mul]
  all_goals field_simp
  · simp only [← hu_def]
    linear_combination (2 * Real.cos θ * Real.sin α * (u - 1) * (u + 1) * (u ^ 2 + 1)) * hθ
  · simp only [← hu_def]
    linear_combination (2 * Real.cos α * Real.cos θ * u ^ 2 * (u - 1) * (u + 1) * (u ^ 2 + 1)) * hθ
  · simp only [← hu_def]
    linear_combination (2 * Real.cos α * Real.cos θ * (u - 1) * (u + 1) * (u ^ 2 + 1)) * hθ
  · simp only [← hu_def]
    linear_combination (-2 * Real.cos θ * Real.sin α * u ^ 2 * (u - 1) * (u + 1) * (u ^ 2 + 1)) * hθ

/-- **`∂α`**. -/
theorem hasDerivAt_kakP_alpha {F : Ent → ℂ} (hF : Differentiable ℝ F) (α ξ θ : ℝ) :
    HasDerivAt (fun α' => kakP F α' ξ θ)
      ((Real.cosh ξ : ℂ) * dF F (kakM α ξ θ) matJ -
        (2 * Real.sinh ξ : ℝ) * ((Real.cos (2 * θ) : ℂ) * dF F (kakM α ξ θ) matS -
          (Real.sin (2 * θ) : ℂ) * dF F (kakM α ξ θ) matH)) α := by
  apply hasDerivAt_of_shift
  have hc := hasDerivAt_mul_curve_left (kakM α ξ θ) (a := fun t => Real.cos t) (b := fun t => Real.sin t)
    (c := fun t => -Real.sin t) (d := fun t => Real.cos t) (t := 0)
    (Real.hasDerivAt_cos 0) (Real.hasDerivAt_sin 0) (Real.hasDerivAt_sin 0).neg
    (Real.hasDerivAt_cos 0)
  have hJ : (!![-Real.sin 0, Real.cos 0; -Real.cos 0, -Real.sin 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      matJ := by simp [matJ]
  rw [hJ, matJ_mul_kakM] at hc
  have h1 : HasFDerivAt F (fderiv ℝ F (ent (!![Real.cos 0, Real.sin 0; -Real.sin 0, Real.cos 0] * kakM α ξ θ))) _ :=
    (hF _).hasFDerivAt
  have h2 := h1.comp_hasDerivAt (0 : ℝ) hc
  have hY : (Real.cosh ξ • matJ - (2 * Real.sinh ξ) • (Real.cos (2 * θ) • matS - Real.sin (2 * θ) • matH)) =
      Real.cosh ξ • matJ + (-(2 * Real.sinh ξ * Real.cos (2 * θ))) • matS +
        (2 * Real.sinh ξ * Real.sin (2 * θ)) • matH := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matJ, matS, matH] <;> ring
  have h3 : HasDerivAt (fun t => F (ent (!![Real.cos t, Real.sin t; -Real.sin t, Real.cos t] * kakM α ξ θ)))
      (dF F (kakM α ξ θ) (Real.cosh ξ • matJ - (2 * Real.sinh ξ) • (Real.cos (2 * θ) • matS - Real.sin (2 * θ) • matH))) 0 := by
    have h4 : HasDerivAt (fun t => F (ent (!![Real.cos t, Real.sin t; -Real.sin t, Real.cos t] * kakM α ξ θ)))
        ((fderiv ℝ F (ent (!![Real.cos 0, Real.sin 0; -Real.sin 0, Real.cos 0] * kakM α ξ θ)))
          (ent (kakM α ξ θ * (Real.cosh ξ • matJ - (2 * Real.sinh ξ) • (Real.cos (2 * θ) • matS - Real.sin (2 * θ) • matH))))) 0 := h2
    have hid : (!![Real.cos 0, Real.sin 0; -Real.sin 0, Real.cos 0] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hid, one_mul] at h4
    unfold dF
    exact h4
  rw [hY, dF_comb3] at h3
  refine (h3.congr_deriv (by push_cast; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show F (ent (kakM (α + t) ξ θ)) = F (ent (!![Real.cos t, Real.sin t; -Real.sin t, Real.cos t] * kakM α ξ θ))
  congr 2
  simp only [kakM, add_comm α t, rot_add, mul_assoc, Matrix.SpecialLinearGroup.coe_mul, coe_rot]

end Lightlike.Lorentz.SL2R
