import Lightlike.Regge.D4.ReggeEquations

/-!
# The gradient of the 4D Regge action

`hasDerivAt_reggeAction4_grad` (`Lightlike/Regge/D4/ReggeEquations.lean`) differentiates the 4D
Regge action along every line `ℓ + τ v` in the space of edge lengths. For a finite vertex set this
file proves the stronger statement that the action is (Fréchet) differentiable on the
finite-dimensional space `Finset V → ℝ` of length assignments, with derivative
`v ↦ Σ_e v_e ∂S/∂ℓ_e`.

## Main results

* `differentiableAt_dihedral4`: the dihedral angle of a non-degenerate labelled 4-simplex is a
  differentiable function of the lengths.
* `differentiableAt_reggeAction4`: the Regge action is differentiable at non-degenerate lengths.
* `hasFDerivAt_reggeAction4` (**Regge's equations, gradient form**): its derivative is
  `reggeGradient4 K ℓ`, the linear functional `v ↦ Σ_e v_e ∂S/∂ℓ_e`.
-/

open Real Finset

namespace Lightlike.Regge4

open Lightlike.FourD (Complex4)
open Lightlike.FourD.Complex4 (mem_faces)
open Lightlike.Regge (triH)

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Squared lengths are differentiable functions of the length assignment. -/
@[fun_prop] theorem differentiable_sq (a b : V) :
    Differentiable ℝ fun m : Finset V → ℝ => sq m a b := by
  by_cases h : a = b
  · subst h
    simp only [sq_self]
    fun_prop
  · simp only [sq_of_ne _ h]
    fun_prop

/-- **The dihedral angle is differentiable in the lengths** at a non-degenerate labelled 4-simplex
(the two tetrahedra at the triangle with positive volume, the triangle with positive area, the
4-simplex with positive 4-volume). -/
theorem differentiableAt_dihedral4 {ℓ : Finset V → ℝ} {p q r s u : V}
    (hs : 0 < gram3 ℓ p q r s) (hu : 0 < gram3 ℓ p q r u) (h2 : 0 < gram2 ℓ p q r)
    (h4 : 0 < gram4 ℓ p q r s u) :
    DifferentiableAt ℝ (fun m => dihedral4 m p q r s u) ℓ := by
  have hM : DifferentiableAt ℝ (fun m : Finset V → ℝ => mixed m p q r s u) ℓ := by
    unfold mixed det3 ip
    fun_prop
  have hP : DifferentiableAt ℝ (fun m : Finset V → ℝ => gram3 m p q r s * gram3 m p q r u) ℓ := by
    unfold gram3 det3 ip
    fun_prop
  have hP0 : 0 < gram3 ℓ p q r s * gram3 ℓ p q r u := mul_pos hs hu
  have hS := hP.sqrt hP0.ne'
  have hsP : √(gram3 ℓ p q r s * gram3 ℓ p q r u) ≠ 0 := (Real.sqrt_pos.mpr hP0).ne'
  have hC : DifferentiableAt ℝ (fun m => mixed m p q r s u /
      √(gram3 m p q r s * gram3 m p q r u)) ℓ := by
    fun_prop (disch := assumption)
  have hdj := desnanot_jacobi ℓ p q r s u
  have hgap : 0 < gram2 ℓ p q r * gram4 ℓ p q r s u := mul_pos h2 h4
  have hsq : (mixed ℓ p q r s u / √(gram3 ℓ p q r s * gram3 ℓ p q r u)) ^ 2 < 1 := by
    rw [div_pow, Real.sq_sqrt hP0.le, div_lt_one hP0]
    linarith
  have hbd := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hsq)
  exact (Real.differentiableAt_arccos.mpr ⟨hbd.1.ne', hbd.2.ne⟩).comp ℓ hC

omit [DecidableEq V] in
/-- Areas are differentiable in the lengths at a triangle of positive area. -/
theorem differentiableAt_area4 {ℓ : Finset V → ℝ} {t : Finset V} (h : 0 < triH ℓ t) :
    DifferentiableAt ℝ (fun m => area4 m t) ℓ := by
  have hH : DifferentiableAt ℝ (fun m : Finset V → ℝ => triH m t) ℓ := by
    unfold triH
    fun_prop
  have hS := hH.sqrt h.ne'
  unfold area4
  fun_prop

/-- One 4-simplex's area-weighted angle sum is differentiable in the lengths. -/
theorem differentiableAt_simpSum4 {K : Complex4 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg4 K ℓ)
    {σ : Finset V} (hσ : σ ∈ K.simps) :
    DifferentiableAt ℝ (fun m => ∑ t ∈ σ.powersetCard 3, area4 m t * dihedralAt4 m σ t) ℓ := by
  refine DifferentiableAt.fun_sum fun t ht => ?_
  obtain ⟨hts, ht3⟩ := mem_powersetCard.mp ht
  refine (differentiableAt_area4 (hK.tri t (mem_faces.mpr ⟨σ, hσ, hts, ht3⟩))).mul ?_
  obtain ⟨a, b, c, x, y, hab, hac, hax, hay, hbc, hbx, hby, hcx, hcy, hxy, rfl, rfl⟩ :=
    exists_label4 (K.card_eq σ hσ) ht3 hts
  have hfun : (fun m => dihedralAt4 m {a, b, c, x, y} {a, b, c}) =
      fun m => dihedral4 m a b c x y :=
    funext fun m => dihedralAt4_eq m hab hac hax hay hbc hbx hby hcx hcy hxy
  have hnd := hK.nondeg4 hab hac hax hay hbc hbx hby hcx hcy hxy hσ
  rw [hfun]
  exact differentiableAt_dihedral4 hnd.f_u hnd.f_s hnd.t₁ hnd.g4

/-- **The 4D Regge action is differentiable** at non-degenerate edge lengths, as a function on the
finite-dimensional space of length assignments. -/
theorem differentiableAt_reggeAction4 {K : Complex4 V} {ℓ : Finset V → ℝ}
    (hK : LengthsNondeg4 K ℓ) : DifferentiableAt ℝ (reggeAction4 K) ℓ := by
  have : reggeAction4 K = fun m => ∑ t ∈ intTris4 K, 2 * π * area4 m t +
      ∑ t ∈ bdryTris4 K, π * area4 m t -
      ∑ σ ∈ K.simps, ∑ t ∈ σ.powersetCard 3, area4 m t * dihedralAt4 m σ t :=
    funext (reggeAction4_eq_sum_simps K)
  rw [this]
  exact ((DifferentiableAt.fun_sum fun t ht =>
      (differentiableAt_area4 (hK.tri t (mem_filter.mp ht).1)).const_mul (2 * π)).add
    (DifferentiableAt.fun_sum fun t ht =>
      (differentiableAt_area4 (hK.tri t (mem_filter.mp ht).1)).const_mul π)).sub
    (DifferentiableAt.fun_sum fun σ hσ => differentiableAt_simpSum4 hK hσ)

/-- The gradient of the 4D Regge action at the lengths `ℓ`: the linear functional
`v ↦ Σ_e v_e ∂S/∂ℓ_e` on length variations. -/
noncomputable def reggeGradient4 (K : Complex4 V) (ℓ : Finset V → ℝ) :
    (Finset V → ℝ) →L[ℝ] ℝ :=
  ∑ e ∈ K.edges, reggePartial4 K ℓ e • ContinuousLinearMap.proj e

omit [Fintype V] in
/-- The gradient applied to a variation `v`. -/
theorem reggeGradient4_apply [Fintype V] (K : Complex4 V) (ℓ v : Finset V → ℝ) :
    reggeGradient4 K ℓ v = ∑ e ∈ K.edges, v e * reggePartial4 K ℓ e := by
  simp [reggeGradient4, mul_comm]

/-- **Regge's equations, gradient form.** At non-degenerate edge lengths the 4D Regge action is
differentiable on the space of length assignments, and its derivative is `reggeGradient4`:
`∂S/∂ℓ_e = Σ_{t ∋ e} (∂A_t/∂ℓ_e) (δ_t or ψ_t)`. -/
theorem hasFDerivAt_reggeAction4 {K : Complex4 V} {ℓ : Finset V → ℝ} (hK : LengthsNondeg4 K ℓ) :
    HasFDerivAt (reggeAction4 K) (reggeGradient4 K ℓ) ℓ := by
  have hd := (differentiableAt_reggeAction4 hK).hasFDerivAt
  convert hd using 1
  ext v
  have hline : HasDerivAt (fun τ : ℝ => ℓ + τ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ℓ
  have h1 := hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have h2 := hasDerivAt_reggeAction4_grad hK v
  have hfun : (reggeAction4 K ∘ fun τ : ℝ => ℓ + τ • v) =
      fun τ => reggeAction4 K (lineL ℓ v τ) := by
    funext τ
    simp only [Function.comp]
    congr 1
  rw [hfun] at h1
  rw [reggeGradient4_apply, h2.unique h1]

end Lightlike.Regge4
