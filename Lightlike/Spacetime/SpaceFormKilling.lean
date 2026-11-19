import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# The Killing algebra of the space form of curvature `k` in isotropic coordinates

On `ℝ³` the fields `Pₘ(x) = (1 - k|x|²/4) eₘ + (k/2) xₘ x` and `R_ab(x) = x_a e_b - x_b e_a` have the brackets
`[Pₘ, Pₙ] = -k Rₘₙ`, `[R_ab, Pₘ] = δₘᵦ P_a - δₘₐ P_b` and those of `so(3)` (Mathlib's convention
`[V, W] = DW(V) - DV(W)`), and are Killing for `δ/(1 + k|x|²/4)²`, the maximally symmetric 3-metric of curvature `k`
(Carroll, gr-qc/9712019, eqs. (8.2)-(8.7), pp. 218-219, in isotropic coordinates).
-/

open Set

noncomputable section

namespace Lightlike.SpaceForm

/-- `|x|²` on `ℝ³`. -/
def nsq (x : Fin 3 → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The curved translation `Pₘ(x) = (1 - k|x|²/4) eₘ + (k/2) xₘ x`. -/
def P (k : ℝ) (m : Fin 3) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (1 - k * nsq x / 4) • (Pi.single m 1 : Fin 3 → ℝ) + (k / 2 * x m) • x

/-- The rotation `R_ab(x) = x_a e_b - x_b e_a`. -/
def R (a b : Fin 3) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  x a • (Pi.single b 1 : Fin 3 → ℝ) - x b • (Pi.single a 1 : Fin 3 → ℝ)

/-- The derivative of `|x|²`. -/
noncomputable def dnsq (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ := ∑ i, (2 * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i

theorem hasFDerivAt_nsq (x : Fin 3 → ℝ) : HasFDerivAt nsq (dnsq x) x := by
  unfold nsq dnsq
  refine HasFDerivAt.fun_sum fun i _ => ?_
  have hi : HasFDerivAt (fun y : Fin 3 → ℝ => y i) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) x := hasFDerivAt_apply i x
  have := hi.mul hi
  convert this using 1
  · funext y; simp only [Pi.mul_apply]; ring
  · ext v; simp; ring

/-- The derivative of `Pₘ`: `u ↦ -(k/2)(x · u) eₘ + (k/2) uₘ x + (k/2) xₘ u`. -/
noncomputable def dP (k : ℝ) (m : Fin 3) (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (-(k / 4) • dnsq x).smulRight (Pi.single m 1 : Fin 3 → ℝ) +
    ((k / 2 * x m) • ContinuousLinearMap.id ℝ (Fin 3 → ℝ) + ((k / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) m).smulRight x)

theorem hasFDerivAt_P (k : ℝ) (m : Fin 3) (x : Fin 3 → ℝ) : HasFDerivAt (P k m) (dP k m x) x := by
  have h1 : HasFDerivAt (fun x => (1 - k * nsq x / 4) • (Pi.single m 1 : Fin 3 → ℝ))
      ((-(k / 4) • dnsq x).smulRight (Pi.single m 1 : Fin 3 → ℝ)) x := by
    have := ((hasFDerivAt_nsq x).const_mul (k / 4)).const_sub 1
    convert this.smul_const (Pi.single m 1 : Fin 3 → ℝ) using 1
    · funext y; congr 1; ring
    · ext v i; simp
  have h2 : HasFDerivAt (fun x : Fin 3 → ℝ => (k / 2 * x m) • x)
      ((k / 2 * x m) • ContinuousLinearMap.id ℝ (Fin 3 → ℝ) + ((k / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) m).smulRight x) x := by
    have hc : HasFDerivAt (fun x : Fin 3 → ℝ => k / 2 * x m) ((k / 2) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) m) x := by
      simpa using (hasFDerivAt_apply m x).const_mul (k / 2)
    exact hc.smul (hasFDerivAt_id x)
  exact h1.add h2

/-- The derivative of `R_ab` (a linear field). -/
noncomputable def dR (a b : Fin 3) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a).smulRight (Pi.single b 1 : Fin 3 → ℝ) -
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) b).smulRight (Pi.single a 1 : Fin 3 → ℝ)

theorem hasFDerivAt_R (a b : Fin 3) (x : Fin 3 → ℝ) : HasFDerivAt (R a b) (dR a b) x := by
  have : R a b = dR a b := by funext y; simp [R, dR]
  rw [this]; exact (dR a b).hasFDerivAt

theorem P_apply (k : ℝ) (m : Fin 3) (x : Fin 3 → ℝ) (i : Fin 3) :
    P k m x i = (1 - k * nsq x / 4) * (if i = m then 1 else 0) + k / 2 * x m * x i := by
  simp [P, Pi.single_apply]

theorem R_apply (a b : Fin 3) (x : Fin 3 → ℝ) (i : Fin 3) :
    R a b x i = x a * (if i = b then 1 else 0) - x b * (if i = a then 1 else 0) := by
  simp [R, Pi.single_apply]

theorem dP_apply (k : ℝ) (m : Fin 3) (x u : Fin 3 → ℝ) (i : Fin 3) :
    dP k m x u i = -(k / 4) * dnsq x u * (if i = m then 1 else 0) + k / 2 * x m * u i + k / 2 * u m * x i := by
  simp [dP, Pi.single_apply]; split_ifs <;> ring

theorem dR_apply (a b : Fin 3) (u : Fin 3 → ℝ) (i : Fin 3) :
    dR a b u i = u a * (if i = b then 1 else 0) - u b * (if i = a then 1 else 0) := by
  simp [dR, Pi.single_apply]

theorem dnsq_apply (x u : Fin 3 → ℝ) : dnsq x u = ∑ i, 2 * x i * u i := by
  simp [dnsq]

/-- `[Pₘ, Pₙ] = -k Rₘₙ`. -/
theorem lieBracket_P_P (k : ℝ) (m n : Fin 3) (x : Fin 3 → ℝ) :
    VectorField.lieBracket ℝ (P k m) (P k n) x = (-k) • R m n x := by
  rw [VectorField.lieBracket, (hasFDerivAt_P k n x).fderiv, (hasFDerivAt_P k m x).fderiv]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dP_apply, P_apply, R_apply, dnsq_apply, nsq,
    Fin.sum_univ_three]
  fin_cases m <;> fin_cases n <;> fin_cases i <;> simp <;> ring

/-- `[R_ab, Pₘ] = δₘᵦ P_a - δₘₐ P_b`. -/
theorem lieBracket_R_P (k : ℝ) (a b m : Fin 3) (x : Fin 3 → ℝ) :
    VectorField.lieBracket ℝ (R a b) (P k m) x =
      (if m = b then (1 : ℝ) else 0) • P k a x - (if m = a then (1 : ℝ) else 0) • P k b x := by
  rw [VectorField.lieBracket, (hasFDerivAt_P k m x).fderiv, (hasFDerivAt_R a b x).fderiv]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dP_apply, P_apply, R_apply, dR_apply, dnsq_apply, nsq,
    Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> fin_cases m <;> fin_cases i <;> simp [-mul_eq_zero] <;> ring1

/-- `[R_ab, R_cd] = -(δ_ad R_cb - δ_ac R_db - δ_bd R_ca + δ_bc R_da)`. -/
theorem lieBracket_R_R (a b c d : Fin 3) (x : Fin 3 → ℝ) :
    VectorField.lieBracket ℝ (R a b) (R c d) x =
      -((if a = d then (1 : ℝ) else 0) • R c b x - (if a = c then (1 : ℝ) else 0) • R d b x -
        (if b = d then (1 : ℝ) else 0) • R c a x + (if b = c then (1 : ℝ) else 0) • R d a x) := by
  rw [VectorField.lieBracket, (hasFDerivAt_R c d x).fderiv, (hasFDerivAt_R a b x).fderiv]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, R_apply, dR_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases i <;> simp

/-- The Euclidean dot product as a bilinear form. -/
def dotL : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i)

theorem dotL_apply (u w : Fin 3 → ℝ) : dotL u w = ∑ i, u i * w i := by simp [dotL]

/-- The conformal factor `1 + k|x|²/4`. -/
def ψ (k : ℝ) (x : Fin 3 → ℝ) : ℝ := 1 + k * nsq x / 4

/-- The space form of curvature `k` in isotropic coordinates, `δ/(1 + k|x|²/4)²`. -/
def metric (k : ℝ) (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ := (ψ k x ^ 2)⁻¹ • dotL

theorem metric_apply (k : ℝ) (x u w : Fin 3 → ℝ) : metric k x u w = (ψ k x ^ 2)⁻¹ * ∑ i, u i * w i := by
  simp [metric, dotL_apply]

set_option maxSynthPendingDepth 3 in
theorem hasFDerivAt_metric (k : ℝ) {x : Fin 3 → ℝ} (hx : ψ k x ≠ 0) :
    HasFDerivAt (metric k) ((((-(k / 2)) / ψ k x ^ 3) • dnsq x).smulRight dotL) x := by
  have hψ : HasFDerivAt (ψ k) ((k / 4) • dnsq x) x := by
    have := ((hasFDerivAt_nsq x).const_mul (k / 4)).const_add 1
    convert this using 1
    funext y; simp only [ψ]; ring
  have h2 := (hasDerivAt_inv (pow_ne_zero 2 hx)).comp_hasFDerivAt x (hψ.pow 2)
  have h3 := h2.smul_const dotL
  convert h3 using 1
  all_goals try (funext y; rfl)
  ext v
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  rw [show ((-(k / 2)) / ψ k x ^ 3) * dnsq x v = -((ψ k x ^ 2) ^ 2)⁻¹ * (↑2 * ψ k x ^ (2 - 1) * ((k / 4) * dnsq x v)) by
    field_simp; ring]
  simp

/-- `x · Pₘ(x) = xₘ (1 + k|x|²/4)`. -/
theorem dnsq_P (k : ℝ) (m : Fin 3) (x : Fin 3 → ℝ) : dnsq x (P k m x) = 2 * x m * ψ k x := by
  rw [dnsq_apply]; simp only [P_apply, ψ, nsq, Fin.sum_univ_three]
  fin_cases m <;> simp <;> ring

theorem dnsq_R (a b : Fin 3) (x : Fin 3 → ℝ) : dnsq x (R a b x) = 0 := by
  rw [dnsq_apply]; simp only [R_apply, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp <;> ring

/-- **The curved translations are Killing** for `δ/(1 + k|x|²/4)²`. -/
theorem killing_P (k : ℝ) (m : Fin 3) {x : Fin 3 → ℝ} (hx : ψ k x ≠ 0) (u w : Fin 3 → ℝ) :
    fderiv ℝ (metric k) x (P k m x) u w + metric k x (dP k m x u) w + metric k x u (dP k m x w) = 0 := by
  rw [(hasFDerivAt_metric k hx).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, dnsq_P,
    metric_apply]
  rw [dotL_apply]
  simp only [dP_apply, dnsq_apply, Fin.sum_univ_three]
  fin_cases m <;> simp <;> field_simp <;> ring

/-- **The rotations are Killing** for `δ/(1 + k|x|²/4)²`. -/
theorem killing_R (k : ℝ) (a b : Fin 3) {x : Fin 3 → ℝ} (hx : ψ k x ≠ 0) (u w : Fin 3 → ℝ) :
    fderiv ℝ (metric k) x (R a b x) u w + metric k x (dR a b u) w + metric k x u (dR a b w) = 0 := by
  rw [(hasFDerivAt_metric k hx).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul, dnsq_R,
    metric_apply, mul_zero, zero_mul, zero_add]
  rw [← mul_add]
  simp only [dR_apply, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp

/-! ## The Killing algebra as an indexed family -/

/-- The index set: the curved translations `Pₘ` (`inl m`) and the rotations `R_ab` (`inr (a, b)`, a redundant
spanning family of `so(3)`). -/
abbrev Idx := Fin 3 ⊕ (Fin 3 × Fin 3)

/-- The Killing fields of the space form of curvature `k`. -/
def X (k : ℝ) : Idx → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  | .inl m => P k m
  | .inr ab => R ab.1 ab.2

/-- The indicator `[e = e₀]`. -/
def ind (e e₀ : Idx) : ℝ := if e = e₀ then 1 else 0

/-- The structure constants of the Killing algebra of the space form of curvature `k`:
`[Pₘ, Pₙ] = -k Rₘₙ`, `[Pₘ, R_ab] = δₘₐ P_b - δₘᵦ P_a`, `[R_ab, Pₘ] = δₘᵦ P_a - δₘₐ P_b`, and
`[R_ab, R_cd] = -(δ_ad R_cb - δ_ac R_db - δ_bd R_ca + δ_bc R_da)`. -/
def S (k : ℝ) : Idx → Idx → Idx → ℝ
  | .inl m, .inl n, e => -k * ind e (.inr (m, n))
  | .inl m, .inr ab, e => (if m = ab.1 then ind e (.inl ab.2) else 0) - (if m = ab.2 then ind e (.inl ab.1) else 0)
  | .inr ab, .inl m, e => (if m = ab.2 then ind e (.inl ab.1) else 0) - (if m = ab.1 then ind e (.inl ab.2) else 0)
  | .inr ab, .inr cd, e =>
      -((if ab.1 = cd.2 then ind e (.inr (cd.1, ab.2)) else 0) - (if ab.1 = cd.1 then ind e (.inr (cd.2, ab.2)) else 0) -
        (if ab.2 = cd.2 then ind e (.inr (cd.1, ab.1)) else 0) + (if ab.2 = cd.1 then ind e (.inr (cd.2, ab.1)) else 0))

theorem sum_ind_smul (k : ℝ) (e₀ : Idx) (x : Fin 3 → ℝ) : ∑ e, ind e e₀ • X k e x = X k e₀ x := by
  rw [Finset.sum_eq_single e₀ (fun e _ he => by simp [ind, he]) (by simp)]
  simp [ind]

@[simp] theorem X_inl (k : ℝ) (m : Fin 3) : X k (.inl m) = P k m := rfl

@[simp] theorem X_inr (k : ℝ) (a b : Fin 3) : X k (.inr (a, b)) = R a b := rfl

theorem sum_ite_ind_smul (k : ℝ) (q : Prop) [Decidable q] (e₀ : Idx) (x : Fin 3 → ℝ) :
    ∑ e, (if q then ind e e₀ else 0) • X k e x = (if q then (1 : ℝ) else 0) • X k e₀ x := by
  split_ifs
  · simp only [sum_ind_smul, one_smul]
  · simp

/-- **The brackets of the Killing algebra close with the structure constants `S k`.** -/
theorem lieBracket_X (k : ℝ) (i j : Idx) (x : Fin 3 → ℝ) :
    VectorField.lieBracket ℝ (X k i) (X k j) x = ∑ e, S k i j e • X k e x := by
  rcases i with m | ⟨a, b⟩ <;> rcases j with n | ⟨c, d⟩
  · simp only [S, mul_smul, ← Finset.smul_sum, sum_ind_smul, X_inl, X_inr, lieBracket_P_P]
  · rw [VectorField.lieBracket_swap]
    simp only [S, sub_smul, Finset.sum_sub_distrib, sum_ite_ind_smul, X_inl, X_inr, lieBracket_R_P, neg_sub]
  · simp only [S, sub_smul, Finset.sum_sub_distrib, sum_ite_ind_smul, X_inl, X_inr, lieBracket_R_P]
  · simp only [S, neg_smul, Finset.sum_neg_distrib, sub_smul, add_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, sum_ite_ind_smul, X_inl, X_inr, lieBracket_R_R]

/-- The Gram matrix of the family at the origin: `δₘₙ` on the translations, `0` elsewhere. -/
def gram0 : Idx → Idx → ℝ
  | .inl m, .inl n => if m = n then 1 else 0
  | _, _ => 0

theorem X_zero (k : ℝ) (i : Idx) : X k i 0 = match i with | .inl m => Pi.single m 1 | .inr _ => 0 := by
  rcases i with m | ⟨a, b⟩ <;> simp [X, P, R, nsq]

theorem metric_zero_apply (k : ℝ) (u w : Fin 3 → ℝ) : metric k 0 u w = ∑ i, u i * w i := by
  simp [metric_apply, ψ, nsq]

end Lightlike.SpaceForm

end
