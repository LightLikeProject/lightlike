module

public import Lightlike.Lorentz.Spherical

/-!
# The limit formula for the orbital integrals of SL(2,ℂ) (milestone HA2)

For a function `F` on `2 × 2` complex matrices and `μ ∈ ℂ*`, the orbital integral over the upper
triangular matrices with diagonal `(μ, μ⁻¹)` is

    Φ_F(μ) = ∫_ℂ F([[μ, x], [0, μ⁻¹]]) d²x        (`orbInt`).

**Limit formula** (`limit_formula`). If `F` is `C²` with compact support and invariant under
conjugation by `SU(2)`, then the Laplacian of `s ↦ Φ_F(e^s)` at `s = 0` is `-8π F(1)`:

    ∂²_t Φ_F(e^t)|₀ + ∂²_t Φ_F(e^{it})|₀ = -8π F(1).

This is the formula of Gel'fand–Naimark and Harish-Chandra that recovers `F(1)` from the
orbital integrals. It is the step of the Plancherel formula where the Plancherel density
`n² + 4ρ²` comes from.

## Implementation notes

For complex groups the formula is elementary. With `n_r = [[1, r], [0, 1]]` (`nMat`), compare
the curve `β(t) = [[e^{tw}, r], [0, e^{-tw}]]` (`βc`) with the curve
`κ(t) = [[1 + wt, r], [-w²t²/r, 1 - wt]]` (`κc`), for `w = 1` and `w = i`.

- `κ` lies in the conjugation orbit of `n_{r + t²/r}`: it is `A n_{r + t²/r} A⁻¹` with
  `A = [[1, w̄t/r], [-wt/r, 1]]`, a positive multiple of an element of `SU(2)` (`orbit_curve`).
  So `F ∘ κ = F ∘ (t ↦ n_{r + t²/r})`.
- `β` and `κ` have the same value and velocity at `t = 0`. So the second derivatives of
  `F ∘ β` and `F ∘ κ` differ by `DF(n_r)(β''(0) - κ''(0))` (`second_deriv_orbit`).
- These differences cancel between `w = 1` and `w = i`. What is left is
  `r ((F ∘ β₁)''(0) + (F ∘ βᵢ)''(0)) = 4 ∂_r F(n_r)` (`second_deriv_sum`).

By `SU(2)`-invariance under diagonal matrices, `F([[μ, x], [0, μ⁻¹]])` depends on `x` only
through `|x|` (`triMat_norm`). In polar coordinates `Φ_F(μ) = 2π ∫₀^C r F([[μ, r], [0, μ⁻¹]]) dr`
for any `C` beyond the support (`orbInt_eq`). Differentiating twice under the integral
(`deriv_deriv_integral`), the identity above integrates to `8π ∫₀^C ∂_r F(n_r) dr = -8π F(1)`.

## Conventions

`F` is a function on the arrays `Fin 2 → Fin 2 → ℂ` (written `P2` here), the same set as
`Matrix (Fin 2) (Fin 2) ℂ`. The array type carries Mathlib's global sup norm, whose topology is
the product topology used for `SL(2,ℂ)`; on the matrix type the norm is only a local instance,
under which the spaces of continuous linear maps needed for second derivatives are not found by
instance search. Arrays are built with `mat2 a b c d = [[a, b], [c, d]]`; matrix products are
taken in `Matrix (Fin 2) (Fin 2) ℂ`, which is definitionally the same type.

## References

- I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR 11 (1947); M. A. Naimark, *Linear representations of the Lorentz group* (1964), ch. III.
- Harish-Chandra, *The Plancherel formula for complex semisimple Lie groups*, Trans. AMS 76
  (1954).
-/

@[expose] public section

open MeasureTheory Complex
open scoped Matrix ComplexConjugate

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-! ### Arrays -/

/-- The `2 × 2` array `[[a, b], [c, d]]`, as an element of `Fin 2 → Fin 2 → ℂ`. -/
def mat2 (a b c d : ℂ) : P2 := !![a, b; c, d]

@[simp] lemma mat2_apply_zero_zero (a b c d : ℂ) : mat2 a b c d 0 0 = a := rfl
@[simp] lemma mat2_apply_zero_one (a b c d : ℂ) : mat2 a b c d 0 1 = b := rfl
@[simp] lemma mat2_apply_one_zero (a b c d : ℂ) : mat2 a b c d 1 0 = c := rfl
@[simp] lemma mat2_apply_one_one (a b c d : ℂ) : mat2 a b c d 1 1 = d := rfl

/-- Arrays add entrywise. -/
lemma mat2_add (a b c d a' b' c' d' : ℂ) :
    mat2 a b c d + mat2 a' b' c' d' = mat2 (a + a') (b + b') (c + c') (d + d') := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Arrays subtract entrywise. -/
lemma mat2_sub (a b c d a' b' c' d' : ℂ) :
    mat2 a b c d - mat2 a' b' c' d' = mat2 (a - a') (b - b') (c - c') (d - d') := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Real multiples of arrays, entrywise. -/
lemma mat2_smul (s : ℝ) (a b c d : ℂ) :
    s • mat2 a b c d = mat2 (s * a) (s * b) (s * c) (s * d) := by
  funext i j; fin_cases i <;> fin_cases j <;> exact Complex.real_smul

/-- The zero array. -/
@[simp] lemma mat2_zero : mat2 0 0 0 0 = 0 := by
  funext i j; fin_cases i <;> fin_cases j <;> rfl

/-- An entry is bounded by the sup norm. -/
lemma norm_apply_le (X : P2) (i j : Fin 2) : ‖X i j‖ ≤ ‖X‖ :=
  (norm_le_pi_norm (X i) j).trans (norm_le_pi_norm X i)

/-- The unipotent matrix `n_q = [[1, q], [0, 1]]`. -/
def nMat (q : ℂ) : P2 := mat2 1 q 0 1

/-- The upper triangular matrix `[[μ, x], [0, μ⁻¹]]`. -/
noncomputable def triMat (μ x : ℂ) : P2 := mat2 μ x 0 μ⁻¹

/-- The matrix `e₁₂ = [[0, 1], [0, 0]]`, the direction of `r ↦ n_r`. -/
def eMat : P2 := mat2 0 1 0 0

/-! ### Invariance under `SU(2)` conjugation -/

/-- `F` is invariant under conjugation by `SU(2)`: `F(k X k⁻¹) = F(X)`. -/
def IsSU2ConjInvariant (F : P2 → ℂ) : Prop :=
  ∀ k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ, ∀ X : M2, F (k * X * star k) = F X

/-- An `SU(2)`-conjugation invariant function is invariant under conjugation by any `U` with
`U* U = c` and `det U = c` for a real `c > 0`, since `U / √c ∈ SU(2)`. -/
lemma IsSU2ConjInvariant.conj_scaled {F : P2 → ℂ} (hK : IsSU2ConjInvariant F) {U : M2} {c : ℝ}
    (hc : 0 < c) (hU : star U * U = (c : ℂ) • 1) (hd : U.det = c) (X : M2) :
    F (U * X * ((c : ℂ)⁻¹ • star U)) = F X := by
  set s : ℝ := (Real.sqrt c)⁻¹ with hs
  have hs2 : (s : ℂ) * s * c = 1 := by
    have : s * s * c = 1 := by
      rw [hs, ← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
    exact_mod_cast this
  have hk : (s : ℂ) • U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
    refine ⟨?_, ?_⟩
    · rw [star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_smul_comm, hU, smul_smul,
        hs2, one_smul]
    · rw [Matrix.det_smul, hd, Fintype.card_fin, ← hs2]; ring
  have h := hK _ hk X
  rw [star_smul, Complex.star_def, Complex.conj_ofReal] at h
  rw [← h]
  congr 1
  have : (c : ℂ)⁻¹ = s * s := by
    rw [eq_comm]; exact (eq_inv_of_mul_eq_one_left hs2)
  rw [this, mul_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm]

/-- **Diagonal reduction.** `F([[μ, x], [0, μ⁻¹]]) = F([[μ, |x|], [0, μ⁻¹]])`, by conjugation with
`diag(ζ, ζ̄)`, `ζ² = x/|x|`. -/
lemma triMat_norm {F : P2 → ℂ} (hK : IsSU2ConjInvariant F) (μ x : ℂ) :
    F (triMat μ x) = F (triMat μ (‖x‖ : ℂ)) := by
  set ζ : ℂ := cexp ((arg x / 2 : ℝ) * I) with hζ
  have hζ1 : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj', hζ, Complex.norm_exp_ofReal_mul_I]; simp
  have hζ1' : conj ζ * ζ = 1 := by rw [mul_comm]; exact hζ1
  have hζ2 : ζ * ζ * ‖x‖ = x := by
    rw [hζ, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, add_halves, mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I x
  set U : M2 := !![ζ, 0; 0, conj ζ] with hU
  have hstar : star U = !![conj ζ, 0; 0, ζ] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hU]
  have h1 : star U * U = ((1 : ℝ) : ℂ) • 1 := by
    rw [hstar, hU]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hζ1, hζ1']
  have h2 : U.det = ((1 : ℝ) : ℂ) := by
    rw [hU, Matrix.det_fin_two_of]; simp [hζ1]
  rw [← hK.conj_scaled one_pos h1 h2 (triMat μ (‖x‖ : ℂ))]
  congr 1
  rw [hstar, hU]
  unfold triMat mat2
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -μ * hζ1
  · linear_combination -hζ2
  · linear_combination -μ⁻¹ * hζ1'

/-! ### The curves -/

/-- The curve `β(t) = [[e^{tw}, r], [0, e^{-tw}]]`. -/
noncomputable def βc (w : ℂ) (r t : ℝ) : P2 := mat2 (cexp (t * w)) r 0 (cexp (-(t * w)))

/-- The velocity of `βc`. -/
noncomputable def βc' (w : ℂ) (t : ℝ) : P2 := mat2 (w * cexp (t * w)) 0 0 (-(w * cexp (-(t * w))))

/-- The acceleration of `βc`. -/
noncomputable def βc'' (w : ℂ) (t : ℝ) : P2 :=
  mat2 (w * (w * cexp (t * w))) 0 0 (w * (w * cexp (-(t * w))))

/-- The orbit curve `κ(t) = [[1 + wt, r], [-w²t²/r, 1 - wt]]`. -/
noncomputable def κc (w : ℂ) (r t : ℝ) : P2 := mat2 (1 + w * t) r (-(w ^ 2 * t ^ 2 / r)) (1 - w * t)

/-- The velocity of `κc`. -/
noncomputable def κc' (w : ℂ) (r t : ℝ) : P2 := mat2 w 0 (-(2 * w ^ 2 * t / r)) (-w)

/-- The acceleration of `κc`. -/
noncomputable def κc'' (w : ℂ) (r : ℝ) : P2 := mat2 0 0 (-(2 * w ^ 2 / r)) 0

/-- The curve `t ↦ n_{r + t²/r}`. -/
noncomputable def νc (r t : ℝ) : P2 := nMat (r + t ^ 2 / r)

/-- The velocity of `νc`. -/
noncomputable def νc' (r t : ℝ) : P2 := mat2 0 (2 * t / r) 0 0

/-- The acceleration of `νc`. -/
noncomputable def νc'' (r : ℝ) : P2 := mat2 0 (2 / r) 0 0

/-- **Orbit curve.** `κ(t) = A n_{r + t²/r} A⁻¹` with `A = [[1, w̄t/r], [-wt/r, 1]]`, a positive
multiple of an element of `SU(2)`; so `F(κ(t)) = F(n_{r + t²/r})` for `|w| = 1`. -/
lemma orbit_curve {F : P2 → ℂ} (hK : IsSU2ConjInvariant F) {w : ℂ} (hw : w * conj w = 1)
    {r : ℝ} (hr : r ≠ 0) (t : ℝ) : F (κc w r t) = F (νc r t) := by
  have hc : 0 < 1 + t ^ 2 / r ^ 2 := by positivity
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hw' : conj w * w = 1 := by rw [mul_comm]; exact hw
  set U : M2 := !![1, conj w * t / r; -(w * t / r), 1] with hU
  have hstar : star U = !![1, -(conj w * t / r); w * t / r, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hU]
  have h1 : star U * U = ((1 + t ^ 2 / r ^ 2 : ℝ) : ℂ) • 1 := by
    rw [hstar, hU]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> linear_combination (t:ℂ)^2 * hw'
  have h2 : U.det = ((1 + t ^ 2 / r ^ 2 : ℝ) : ℂ) := by
    rw [hU, Matrix.det_fin_two_of]; push_cast; field_simp; linear_combination (t:ℂ)^2 * hw'
  have hrt : (r : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < r ^ 2 + t ^ 2 := by positivity
    exact_mod_cast this.ne'
  rw [νc, ← hK.conj_scaled hc h1 h2 (nMat (r + t ^ 2 / r))]
  congr 1
  rw [hstar, hU]
  unfold κc nMat mat2
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first
    | ring1
    | linear_combination (-(t : ℂ) ^ 2) * hw

/-! ### Derivatives along curves -/

/-- The chain rule along a curve. -/
lemma hasDerivAt_comp_curve {F : P2 → ℂ} (hF : ContDiff ℝ 2 F) {c : ℝ → P2} {v : P2} {t : ℝ}
    (hc : HasDerivAt c v t) : HasDerivAt (fun t => F (c t)) (fderiv ℝ F (c t) v) t :=
  (hF.differentiable (by simp) (c t)).hasFDerivAt.comp_hasDerivAt t hc

/-- **Second derivative along a curve.** If `c` has velocity `c'` and acceleration `a` at `t`,
then `t ↦ DF(c t)(c' t)` has derivative `D²F(c t)(c' t, c' t) + DF(c t)(a)` at `t`. -/
lemma hasDerivAt_fderiv_curve {F : P2 → ℂ} (hF : ContDiff ℝ 2 F) {c c' : ℝ → P2} {a : P2}
    {t : ℝ} (hc : HasDerivAt c (c' t) t) (hc' : HasDerivAt c' a t) :
    HasDerivAt (fun t => fderiv ℝ F (c t) (c' t))
      (fderiv ℝ (fderiv ℝ F) (c t) (c' t) (c' t) + fderiv ℝ F (c t) a) t := by
  have h1 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (c t)) (c t) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) (c t)).hasFDerivAt
  exact (h1.comp_hasDerivAt t hc).clm_apply hc'

/-- Derivative of a `2 × 2` array-valued curve, entry by entry. -/
lemma hasDerivAt_mat2 {a b c d : ℝ → ℂ} {a' b' c' d' : ℂ} {t : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) (hc : HasDerivAt c c' t) (hd : HasDerivAt d d' t) :
    HasDerivAt (fun t => mat2 (a t) (b t) (c t) (d t)) (mat2 a' b' c' d') t := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa [mat2]

/-- Continuity of a `2 × 2` array-valued map, entry by entry. -/
lemma continuous_mat2 {X : Type*} [TopologicalSpace X] {a b c d : X → ℂ} (ha : Continuous a)
    (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous fun p => mat2 (a p) (b p) (c p) (d p) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa [mat2]

/-- The real line in `ℂ` has derivative `1`. -/
lemma hasDerivAt_ofReal' (t : ℝ) : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

/-- `d/dt e^{tw} = w e^{tw}`. -/
lemma hasDerivAt_cexp_mul (w : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => cexp (y * w)) (w * cexp (t * w)) t := by
  convert ((hasDerivAt_ofReal' t).mul_const w).cexp using 1; ring

/-- `d/dt e^{-tw} = -w e^{-tw}`. -/
lemma hasDerivAt_cexp_neg_mul (w : ℂ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => cexp (-(y * w))) (-(w * cexp (-(t * w)))) t := by
  have h : HasDerivAt (fun y : ℝ => -((y : ℂ) * w)) (-(1 * w)) t :=
    ((hasDerivAt_ofReal' t).mul_const w).neg
  convert h.cexp using 1; ring

/-- The velocity of `βc`. -/
lemma hasDerivAt_βc (w : ℂ) (r t : ℝ) : HasDerivAt (βc w r) (βc' w t) t :=
  hasDerivAt_mat2 (hasDerivAt_cexp_mul w t) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    (hasDerivAt_cexp_neg_mul w t)

/-- The acceleration of `βc`. -/
lemma hasDerivAt_βc' (w : ℂ) (t : ℝ) : HasDerivAt (βc' w) (βc'' w t) t := by
  refine hasDerivAt_mat2 ((hasDerivAt_cexp_mul w t).const_mul w) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _) (((hasDerivAt_cexp_neg_mul w t).const_mul w).neg.congr_deriv ?_)
  ring

/-- The velocity of `κc`. -/
lemma hasDerivAt_κc (w : ℂ) (r t : ℝ) : HasDerivAt (κc w r) (κc' w r t) t := by
  have ht := hasDerivAt_ofReal' t
  refine hasDerivAt_mat2 ((ht.const_mul w).const_add 1 |>.congr_deriv (by ring))
    (hasDerivAt_const _ _) (((ht.pow 2).const_mul (w ^ 2)).div_const (r : ℂ) |>.neg |>.congr_deriv
      (by push_cast; ring)) ((ht.const_mul w).const_sub 1 |>.congr_deriv (by ring))

/-- The acceleration of `κc`. -/
lemma hasDerivAt_κc' (w : ℂ) (r t : ℝ) : HasDerivAt (κc' w r) (κc'' w r) t := by
  have ht := hasDerivAt_ofReal' t
  refine hasDerivAt_mat2 (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    ((ht.const_mul (2 * w ^ 2)).div_const (r : ℂ) |>.neg |>.congr_deriv (by ring))
    (hasDerivAt_const _ _)

/-- The velocity of `νc`. -/
lemma hasDerivAt_νc (r t : ℝ) : HasDerivAt (νc r) (νc' r t) t := by
  have ht := hasDerivAt_ofReal' t
  refine hasDerivAt_mat2 (hasDerivAt_const _ _)
    (((ht.pow 2).div_const (r : ℂ)).const_add (r : ℂ) |>.congr_deriv (by push_cast; ring))
    (hasDerivAt_const _ _) (hasDerivAt_const _ _)

/-- The acceleration of `νc`. -/
lemma hasDerivAt_νc' (r t : ℝ) : HasDerivAt (νc' r) (νc'' r) t := by
  have ht := hasDerivAt_ofReal' t
  refine hasDerivAt_mat2 (hasDerivAt_const _ _)
    ((ht.const_mul 2).div_const (r : ℂ) |>.congr_deriv (by ring))
    (hasDerivAt_const _ _) (hasDerivAt_const _ _)

/-- `r ↦ n_r` has velocity `e₁₂`. -/
lemma hasDerivAt_nMat (y : ℝ) : HasDerivAt (fun y : ℝ => nMat y) eMat y :=
  hasDerivAt_mat2 (hasDerivAt_const _ _) (hasDerivAt_ofReal' y) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _)

/-! ### The pointwise identity -/

/-- `β(0) = n_r`. -/
lemma βc_zero (w : ℂ) (r : ℝ) : βc w r 0 = nMat r := by simp [βc, nMat]

/-- `κ(0) = n_r`. -/
lemma κc_zero (w : ℂ) (r : ℝ) : κc w r 0 = nMat r := by simp [κc, nMat]

/-- `ν(0) = n_r`. -/
lemma νc_zero (r : ℝ) : νc r 0 = nMat r := by simp [νc]

/-- `β'(0) = κ'(0) = diag(w, -w)`. -/
lemma βc'_zero (w : ℂ) (r : ℝ) : βc' w 0 = κc' w r 0 := by simp [βc', κc']

/-- `ν'(0) = 0`. -/
lemma νc'_zero (r : ℝ) : νc' r 0 = 0 := by simp [νc']

/-- **Comparison with the orbit curve.** The second derivative of `F` along `β` at `t = 0` is
`DF(n_r)(ν''(0) - κ''(0) + β''(0))`. -/
lemma second_deriv_orbit {F : P2 → ℂ} (hF : ContDiff ℝ 2 F) (hK : IsSU2ConjInvariant F) {w : ℂ}
    (hw : w * conj w = 1) {r : ℝ} (hr : r ≠ 0) :
    fderiv ℝ (fderiv ℝ F) (βc w r 0) (βc' w 0) (βc' w 0) + fderiv ℝ F (βc w r 0) (βc'' w 0) =
      fderiv ℝ F (nMat r) (νc'' r - κc'' w r + βc'' w 0) := by
  have heq : (fun t => fderiv ℝ F (κc w r t) (κc' w r t)) =
      fun t => fderiv ℝ F (νc r t) (νc' r t) := by
    have e : (fun t => F (κc w r t)) = fun t => F (νc r t) :=
      funext fun t => orbit_curve hK hw hr t
    funext t
    rw [← (hasDerivAt_comp_curve hF (hasDerivAt_κc w r t)).deriv,
      ← (hasDerivAt_comp_curve hF (hasDerivAt_νc r t)).deriv, e]
  have h1 := hasDerivAt_fderiv_curve hF (hasDerivAt_κc w r 0) (hasDerivAt_κc' w r 0)
  have h2 := hasDerivAt_fderiv_curve hF (hasDerivAt_νc r 0) (hasDerivAt_νc' r 0)
  rw [heq] at h1
  have h := h1.unique h2
  rw [κc_zero, νc_zero, νc'_zero, ← βc'_zero w r] at h
  simp only [map_zero, zero_add] at h
  rw [βc_zero, map_add, map_sub, ← h]
  ring

/-- **The pointwise identity.** `r ((F ∘ β₁)''(0) + (F ∘ βᵢ)''(0)) = 4 ∂_r F(n_r)`. -/
lemma second_deriv_sum {F : P2 → ℂ} (hF : ContDiff ℝ 2 F) (hK : IsSU2ConjInvariant F) {r : ℝ}
    (hr : r ≠ 0) :
    (r : ℂ) * (fderiv ℝ (fderiv ℝ F) (βc 1 r 0) (βc' 1 0) (βc' 1 0) +
        fderiv ℝ F (βc 1 r 0) (βc'' 1 0)) +
      (r : ℂ) * (fderiv ℝ (fderiv ℝ F) (βc I r 0) (βc' I 0) (βc' I 0) +
        fderiv ℝ F (βc I r 0) (βc'' I 0)) =
      4 * fderiv ℝ F (nMat r) eMat := by
  rw [second_deriv_orbit hF hK (by simp) hr, second_deriv_orbit hF hK (by simp) hr, ← mul_add,
    ← map_add]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hm : νc'' r - κc'' 1 r + βc'' 1 0 + (νc'' r - κc'' I r + βc'' I 0) = (4 / r : ℝ) • eMat := by
    simp only [νc'', κc'', βc'', eMat, mat2_add, mat2_sub, mat2_smul]
    congr 1 <;> simp <;> field_simp <;> ring
  rw [hm, map_smul, Complex.real_smul]
  push_cast
  field_simp

/-! ### Differentiation under the integral sign -/

/-- Differentiation under `∫₀^C` for a jointly continuous integrand with a jointly continuous
`t`-derivative. -/
lemma hasDerivAt_integral_param {G G' : ℝ → ℝ → ℂ} {C : ℝ} (t₀ : ℝ)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2) (hG' : Continuous fun p : ℝ × ℝ => G' p.1 p.2)
    (hd : ∀ t y, HasDerivAt (fun t => G t y) (G' t y) t) :
    HasDerivAt (fun t => ∫ y in (0 : ℝ)..C, G t y) (∫ y in (0 : ℝ)..C, G' t₀ y) t₀ := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall t₀ 1).prod (isCompact_uIcc (a := (0 : ℝ)) (b := C))
    ).exists_bound_of_continuousOn hG'.continuousOn
  have hsec : ∀ {H : ℝ → ℝ → ℂ}, (Continuous fun p : ℝ × ℝ => H p.1 p.2) → ∀ t,
      Continuous (H t) := fun hH t => hH.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => B)
    (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => (hsec hG t).aestronglyMeasurable)
    ((hsec hG t₀).intervalIntegrable _ _) (hsec hG' t₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y hy t ht => hB (t, y) ⟨Metric.ball_subset_closedBall ht,
      Set.uIoc_subset_uIcc hy⟩) intervalIntegrable_const
    (Filter.Eventually.of_forall fun y _ t _ => hd t y)).2

/-- Continuity of the second-derivative expression `D²F(a)(u, u) + DF(a)(v)`. -/
lemma continuous_second {F : P2 → ℂ} (hF : ContDiff ℝ 2 F) {X : Type*} [TopologicalSpace X]
    {a u v : X → P2} (ha : Continuous a) (hu : Continuous u) (hv : Continuous v) :
    Continuous fun p => fderiv ℝ (fderiv ℝ F) (a p) (u p) (u p) + fderiv ℝ F (a p) (v p) := by
  have hF1 : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  have hF2 : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by simp)
  exact (((hF2.comp ha).clm_apply hu).clm_apply hu).add ((hF1.comp ha).clm_apply hv)

/-- **Second derivative under the integral.** For a family of curves `c y` with jointly continuous
velocity `c'` and acceleration `c''`,
`∂²_t ∫₀^C y F(c y t) dy = ∫₀^C y (D²F(c)(c', c') + DF(c)(c'')) dy`. -/
lemma deriv_deriv_integral {F : P2 → ℂ} (hF : ContDiff ℝ 2 F) {c c' c'' : ℝ → ℝ → P2} {C : ℝ}
    (hc : Continuous fun p : ℝ × ℝ => c p.1 p.2) (hc' : Continuous fun p : ℝ × ℝ => c' p.1 p.2)
    (hc'' : Continuous fun p : ℝ × ℝ => c'' p.1 p.2)
    (hd : ∀ y t, HasDerivAt (c y) (c' y t) t) (hd' : ∀ y t, HasDerivAt (c' y) (c'' y t) t)
    (t₀ : ℝ) :
    deriv (deriv fun t => ∫ y in (0 : ℝ)..C, (y : ℂ) * F (c y t)) t₀ =
      ∫ y in (0 : ℝ)..C, (y : ℂ) * (fderiv ℝ (fderiv ℝ F) (c y t₀) (c' y t₀) (c' y t₀) +
        fderiv ℝ F (c y t₀) (c'' y t₀)) := by
  have hF1 : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  have hy : Continuous fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ) := continuous_ofReal.comp continuous_snd
  -- the integrands as functions of `(t, y)`, parameter first
  have hc_s : Continuous fun p : ℝ × ℝ => c p.2 p.1 := hc.comp continuous_swap
  have hc'_s : Continuous fun p : ℝ × ℝ => c' p.2 p.1 := hc'.comp continuous_swap
  have hc''_s : Continuous fun p : ℝ × ℝ => c'' p.2 p.1 := hc''.comp continuous_swap
  have h1 : ∀ t, HasDerivAt (fun t => ∫ y in (0 : ℝ)..C, (y : ℂ) * F (c y t))
      (∫ y in (0 : ℝ)..C, (y : ℂ) * fderiv ℝ F (c y t) (c' y t)) t := fun t =>
    hasDerivAt_integral_param (G := fun t y => (y : ℂ) * F (c y t))
      (G' := fun t y => (y : ℂ) * fderiv ℝ F (c y t) (c' y t)) t
      (hy.mul (hF.continuous.comp hc_s)) (hy.mul ((hF1.comp hc_s).clm_apply hc'_s))
      fun t y => (hasDerivAt_comp_curve hF (hd y t)).const_mul _
  rw [show (deriv fun t => ∫ y in (0 : ℝ)..C, (y : ℂ) * F (c y t)) =
      fun t => ∫ y in (0 : ℝ)..C, (y : ℂ) * fderiv ℝ F (c y t) (c' y t) from
    funext fun t => (h1 t).deriv]
  exact (hasDerivAt_integral_param (G := fun t y => (y : ℂ) * fderiv ℝ F (c y t) (c' y t))
    (G' := fun t y => (y : ℂ) * (fderiv ℝ (fderiv ℝ F) (c y t) (c' y t) (c' y t) +
      fderiv ℝ F (c y t) (c'' y t))) t₀
    (hy.mul ((hF1.comp hc_s).clm_apply hc'_s))
    (hy.mul (continuous_second hF hc_s hc'_s hc''_s))
    fun t y => (hasDerivAt_fderiv_curve hF (hd y t) (hd' y t)).const_mul _).deriv

/-! ### The orbital integral -/

/-- The orbital integral `Φ_F(μ) = ∫_ℂ F([[μ, x], [0, μ⁻¹]]) d²x` over the upper triangular
matrices with diagonal `(μ, μ⁻¹)`. -/
noncomputable def orbInt (F : P2 → ℂ) (μ : ℂ) : ℂ := ∫ x : ℂ, F (triMat μ x)

/-- A compactly supported function vanishes beyond some radius `C > 0`. -/
lemma exists_bound_support {F : P2 → ℂ} (hs : HasCompactSupport F) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : P2, C ≤ ‖X‖ → F X = 0 := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0 + 1, by positivity, fun X hX => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have h1 := hR h
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  linarith [le_max_left R 0]

/-- `F([[μ, y], [0, μ⁻¹]]) = 0` once `y ≥ C`. -/
lemma triMat_eq_zero {F : P2 → ℂ} {C : ℝ} (hCF : ∀ X : P2, C ≤ ‖X‖ → F X = 0) (μ : ℂ) {y : ℝ}
    (hy : C ≤ y) : F (triMat μ y) = 0 := by
  refine hCF _ (hy.trans ((le_abs_self y).trans ?_))
  simpa [triMat] using norm_apply_le (triMat μ y) 0 1

/-- **Polar form of the orbital integral.** `Φ_F(μ) = 2π ∫₀^C y F([[μ, y], [0, μ⁻¹]]) dy` for
any `C` beyond the support of `F`. -/
lemma orbInt_eq {F : P2 → ℂ} (hK : IsSU2ConjInvariant F) {C : ℝ} (hC : 0 ≤ C)
    (hCF : ∀ X : P2, C ≤ ‖X‖ → F X = 0) (μ : ℂ) :
    orbInt F μ = 2 * Real.pi * ∫ y in (0 : ℝ)..C, (y : ℂ) * F (triMat μ y) := by
  have h1 : orbInt F μ = ∫ x : ℂ, F (triMat μ (‖x‖ : ℂ)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => triMat_norm hK μ x)
  have h2 := integral_comp_norm_complex (fun y : ℝ => F (triMat μ y))
  beta_reduce at h2
  rw [h1, h2, intervalIntegral.integral_of_le hC,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self]
  rintro y ⟨hy, hy'⟩
  rw [triMat_eq_zero hCF μ ?_, mul_zero]
  simp only [Set.mem_Ioc, not_and, not_le] at hy'
  exact (hy' hy).le

/-- `[[e^{tw}, y], [0, e^{-tw}]]` is `βc`. -/
lemma triMat_cexp (w : ℂ) (y t : ℝ) : triMat (cexp (t * w)) y = βc w y t := by
  simp [triMat, βc, Complex.exp_neg]

/-! ### The limit formula -/

/-- **The limit formula** (Gel'fand–Naimark, Harish-Chandra). If `F` is `C²` with compact support
and invariant under conjugation by `SU(2)`, the Laplacian of `s ↦ Φ_F(e^s)` at `s = 0` is
`-8π F(1)`:

    ∂²_t Φ_F(e^t)|₀ + ∂²_t Φ_F(e^{it})|₀ = -8π F(1),

with `Φ_F(μ) = ∫_ℂ F([[μ, x], [0, μ⁻¹]]) d²x` (`orbInt`) and `1 = mat2 1 0 0 1`. -/
theorem limit_formula {F : P2 → ℂ} (hF : ContDiff ℝ 2 F) (hs : HasCompactSupport F)
    (hK : IsSU2ConjInvariant F) :
    deriv (deriv fun t : ℝ => orbInt F (cexp t)) 0 +
      deriv (deriv fun t : ℝ => orbInt F (cexp (t * I))) 0 =
      -(8 * Real.pi) * F (mat2 1 0 0 1) := by
  obtain ⟨C, hC, hCF⟩ := exists_bound_support hs
  have hβ : ∀ w : ℂ, Continuous fun p : ℝ × ℝ => βc w p.1 p.2 := fun w => by
    unfold βc; exact continuous_mat2 (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hβ' : ∀ w : ℂ, Continuous fun p : ℝ × ℝ => βc' w p.2 := fun w => by
    unfold βc'; exact continuous_mat2 (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hβ'' : ∀ w : ℂ, Continuous fun p : ℝ × ℝ => βc'' w p.2 := fun w => by
    unfold βc''; exact continuous_mat2 (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hD : ∀ w : ℂ, deriv (deriv fun t : ℝ => orbInt F (cexp (t * w))) 0 =
      2 * Real.pi * ∫ y in (0 : ℝ)..C, (y : ℂ) * (fderiv ℝ (fderiv ℝ F) (βc w y 0) (βc' w 0)
        (βc' w 0) + fderiv ℝ F (βc w y 0) (βc'' w 0)) := by
    intro w
    have hΦ : (fun t : ℝ => orbInt F (cexp (t * w))) =
        fun t => 2 * Real.pi * ∫ y in (0 : ℝ)..C, (y : ℂ) * F (βc w y t) := by
      funext t
      rw [orbInt_eq hK hC.le hCF]
      simp only [triMat_cexp]
    rw [hΦ]
    simp only [deriv_const_mul_field']
    congr 1
    exact deriv_deriv_integral hF (c := βc w) (c' := fun _ t => βc' w t)
      (c'' := fun _ t => βc'' w t) (hβ w) (hβ' w) (hβ'' w) (fun y t => hasDerivAt_βc w y t)
      (fun _ t => hasDerivAt_βc' w t) 0
  have hint : ∀ w : ℂ, IntervalIntegrable (fun y : ℝ => (y : ℂ) * (fderiv ℝ (fderiv ℝ F)
      (βc w y 0) (βc' w 0) (βc' w 0) + fderiv ℝ F (βc w y 0) (βc'' w 0))) volume 0 C := fun w =>
    (continuous_ofReal.mul (continuous_second hF
      ((hβ w).comp (continuous_id.prodMk continuous_const)) continuous_const
      continuous_const)).intervalIntegrable _ _
  have hn : Continuous fun y : ℝ => nMat y := by
    unfold nMat; exact continuous_mat2 (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hFTC : ∫ y in (0 : ℝ)..C, fderiv ℝ F (nMat y) eMat = F (nMat C) - F (nMat (0 : ℝ)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_comp_curve hF (hasDerivAt_nMat y))
      (((hF.continuous_fderiv (by simp)).comp hn).clm_apply continuous_const
        |>.intervalIntegrable _ _)
  have hC0 : F (nMat C) = 0 :=
    hCF _ ((le_abs_self C).trans (by simpa [nMat] using norm_apply_le (nMat C) 0 1))
  have h1 : (fun t : ℝ => orbInt F (cexp t)) = fun t : ℝ => orbInt F (cexp (t * 1)) := by simp
  rw [h1, hD 1, hD I, ← mul_add, ← intervalIntegral.integral_add (hint 1) (hint I),
    intervalIntegral.integral_congr_ae (g := fun y : ℝ => 4 * fderiv ℝ F (nMat y) eMat) ?_,
    intervalIntegral.integral_const_mul, hFTC, hC0]
  · simp only [nMat, ofReal_zero]; ring
  · refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Set.uIoc_of_le hC.le] at hy
    exact second_deriv_sum hF hK hy.1.ne'

end Lightlike.Lorentz
