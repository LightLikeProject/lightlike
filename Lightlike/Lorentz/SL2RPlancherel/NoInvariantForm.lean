import Mathlib
import Lightlike.Lorentz.SL2RCasimir

/-!
# No positive invariant form outside the complementary series (HA3 trust check)

The principal-series model `act ε ν` of `SL(2,ℝ)` (`|cx+d|^{iν-1}`) is unitary on `L²(ℝ)` for real
`ν`. For `ν = iτ`, `τ` real, the multiplier is `|t|^{-τ-1}`; writing `s = (1+τ)/2` the model is the
usual family `|cx+d|^{-2s}`, and the complementary series is the part `|τ| < 1`, `s ∈ (0,1)`, on which
an invariant positive form exists (parameter `σ = |τ|/2 ∈ (0, 1/2)`).

This file shows that **for `|τ| > 1` there is no positive definite Hermitian form on any space of
smooth functions stable under the derived action of `E, F, H` for which `E, F, H` are skew**.
The argument is the sign of the Casimir on a `K`-fixed vector. For `W = E - F`,
`Ω = H²/4 + (E+F)²/4 - W²/4`, so on a vector with `W v = 0` we get
`B(v, Ω v) = -B(Hv,Hv)/4 - B(Ev,Ev) ≤ 0` for a form `B` for which `H, E, F` are skew and
`B ≥ 0`. The function `(1+x²)^{-(τ+1)/2}` is `K`-fixed (`E v = F v`) with `Ω v = (τ²-1)/4 · v`,
which is `> 0` iff `|τ| > 1`.

## Main results

* `re_form_casimir_le`: the abstract sign statement.
* `no_invariant_form`: for `|τ| > 1` no positive definite form invariant under the derived action
  exists on a space of functions containing `(1+x²)^{-(τ+1)/2}`.

Infinitesimal invariance (skewness of `E, F, H`) is what a unitary form gives on smooth vectors;
group invariance is not assumed since `act g f` is singular at the pole of `g`.
-/

open Complex

noncomputable section

namespace Lightlike.Lorentz.SL2RPlancherel

section Abstract

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- **Sign of the Casimir on a `K`-fixed vector.** If `E, F, H` are skew for a positive
semidefinite sesquilinear form `B` and `E v = F v`, then `Re B(v, Ω v) ≤ 0`, where
`Ω = H²/4 + (EF+FE)/2`. -/
theorem re_form_casimir_le (B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) (E F H : V →ₗ[ℂ] V)
    (hE : ∀ u w, B (E u) w + B u (E w) = 0) (hF : ∀ u w, B (F u) w + B u (F w) = 0)
    (hH : ∀ u w, B (H u) w + B u (H w) = 0) (hpos : ∀ u, 0 ≤ (B u u).re) (v : V)
    (hEF : E v = F v) :
    (B v ((1 / 4 : ℂ) • H (H v) + (1 / 2 : ℂ) • (E (F v) + F (E v)))).re ≤ 0 := by
  have h1 : B v (H (H v)) = - B (H v) (H v) := by
    have := hH v (H v)
    linear_combination this
  have h2 : B v (E (F v)) = - B (E v) (E v) := by
    have := hE v (F v)
    have e : B (E v) (F v) = B (E v) (E v) := by rw [← hEF]
    linear_combination this - e
  have h3 : B v (F (E v)) = - B (E v) (E v) := by
    have := hF v (E v)
    have e : B (F v) (E v) = B (E v) (E v) := by rw [← hEF]
    linear_combination this - e
  have h4 : B v ((1 / 4 : ℂ) • H (H v) + (1 / 2 : ℂ) • (E (F v) + F (E v))) =
      -(1 / 4 : ℂ) * B (H v) (H v) - B (E v) (E v) := by
    rw [map_add, map_smul, map_smul, map_add, h1, h2, h3]
    simp only [smul_eq_mul]
    ring
  rw [h4]
  have a := hpos (H v)
  have b := hpos (E v)
  simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im] at *
  norm_num at *
  linarith

/-- **Positivity transfers to the Casimir eigenvalue.** If moreover `Ω v = λ v` with real
`λ > 0` and `v ≠ 0`, then `B` is not positive definite. -/
theorem not_posDef_of_casimir_pos (B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ) (E F H : V →ₗ[ℂ] V)
    (hE : ∀ u w, B (E u) w + B u (E w) = 0) (hF : ∀ u w, B (F u) w + B u (F w) = 0)
    (hH : ∀ u w, B (H u) w + B u (H w) = 0) (v : V) (hv : v ≠ 0) (hEF : E v = F v)
    (c : ℝ) (hc : 0 < c)
    (hΩ : (1 / 4 : ℂ) • H (H v) + (1 / 2 : ℂ) • (E (F v) + F (E v)) = (c : ℂ) • v) :
    ¬ ∀ u, u ≠ 0 → 0 < (B u u).re := by
  intro hpos
  have hnn : ∀ u, 0 ≤ (B u u).re := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · exact (hpos u hu).le
  have h := re_form_casimir_le B E F H hE hF hH hnn v hEF
  rw [hΩ, map_smul] at h
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at h
  have := hpos v hv
  nlinarith

end Abstract

section Concrete

open Lightlike.Lorentz.SL2R

/-- The `K`-fixed function `(1+x²)^{-(τ+1)/2}` of the model `|t|^{-τ-1}`. -/
def sphericalVec (τ : ℝ) (x : ℝ) : ℂ := (((1 + x ^ 2) ^ (-(τ + 1) / 2) : ℝ) : ℂ)

lemma hasDerivAt_sphericalVec (τ x : ℝ) :
    HasDerivAt (sphericalVec τ)
      (((2 * x * (-(τ + 1) / 2) * (1 + x ^ 2) ^ (-(τ + 1) / 2 - 1) : ℝ)) : ℂ) x := by
  have h : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have h2 := (h.rpow_const (p := -(τ + 1) / 2) (Or.inl (by positivity))).ofReal_comp
  exact h2

lemma deriv_sphericalVec (τ x : ℝ) : deriv (sphericalVec τ) x =
      (((2 * x * (-(τ + 1) / 2) * (1 + x ^ 2) ^ (-(τ + 1) / 2 - 1) : ℝ)) : ℂ) :=
  (hasDerivAt_sphericalVec τ x).deriv

/-- `E v = F v`: the function `(1+x²)^{-(τ+1)/2}` is fixed by `E - F`, the generator of `K`. -/
lemma upper_sub_lower_sphericalVec (ε : ℤ) (τ x : ℝ) :
    derivAlong (act ε (I * τ)) upper (sphericalVec τ) x =
      derivAlong (act ε (I * τ)) lower (sphericalVec τ) x := by
  have hd : DifferentiableAt ℝ (sphericalVec τ) x := (hasDerivAt_sphericalVec τ x).differentiableAt
  rw [derivAlong_upper ε _ hd, derivAlong_lower ε _ hd, deriv_sphericalVec]
  have hp : (1 + x ^ 2 : ℝ) ^ (-(τ + 1) / 2) =
      (1 + x ^ 2) ^ (-(τ + 1) / 2 - 1) * (1 + x ^ 2) := by
    rw [Real.rpow_sub_one (by positivity)]
    field_simp
  simp only [sphericalVec]
  rw [hp]
  push_cast
  have : (I : ℂ) * (I * τ) = -τ := by
    linear_combination (τ : ℂ) * Complex.I_sq
  rw [this]
  ring

/-- **No positive invariant form for `|τ| > 1`** (infinitesimal: `E, F, H` on smooth vectors, not group-level).
Let `S` be a space of twice-differentiable
functions on `ℝ` with linear maps `E, F, H` acting as the derived principal-series action of
`SL(2,ℝ)` for `ν = iτ` (the model `|cx+d|^{-τ-1}`), and containing `(1+x²)^{-(τ+1)/2}`. If
`|τ| > 1`, no sesquilinear form on `S` for which `E, F, H` are skew is positive definite. For
`|τ| < 1` (the complementary series, `σ = |τ|/2 ∈ (0, 1/2)`) the Casimir eigenvalue `(τ²-1)/4` is
`≤ 0` and there is no obstruction. -/
theorem no_invariant_form (ε : ℤ) (τ : ℝ) (hτ : 1 < |τ|)
    (S : Submodule ℂ (ℝ → ℂ)) (hS : ∀ f ∈ S, Differentiable ℝ f ∧ Differentiable ℝ (deriv f))
    (E F H : S →ₗ[ℂ] S)
    (hE : ∀ f : S, (E f : ℝ → ℂ) = derivAlong (act ε (I * τ)) upper f)
    (hF : ∀ f : S, (F f : ℝ → ℂ) = derivAlong (act ε (I * τ)) lower f)
    (hH : ∀ f : S, (H f : ℝ → ℂ) = derivAlong (act ε (I * τ)) expH f)
    (v : S) (hv : (v : ℝ → ℂ) = sphericalVec τ)
    (B : S →ₛₗ[starRingEnd ℂ] S →ₗ[ℂ] ℂ)
    (hBE : ∀ u w, B (E u) w + B u (E w) = 0) (hBF : ∀ u w, B (F u) w + B u (F w) = 0)
    (hBH : ∀ u w, B (H u) w + B u (H w) = 0) :
    ¬ ∀ u, u ≠ 0 → 0 < (B u u).re := by
  have hτ2 : 1 < τ ^ 2 := by
    have := sq_abs τ
    nlinarith [abs_nonneg τ]
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := congrFun hv 0
    rw [h] at h1
    simp [sphericalVec] at h1
  have hEF : E v = F v := by
    refine Subtype.ext (funext fun x => ?_)
    rw [hE, hF, hv]
    exact upper_sub_lower_sphericalVec ε τ x
  refine not_posDef_of_casimir_pos B E F H hBE hBF hBH v hv0 hEF ((τ ^ 2 - 1) / 4)
    (by linarith) ?_
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨h1, h2⟩ := hS v v.2
  have hc := casimir_principal (ε := ε) (ν := I * (τ : ℂ)) h1 h2 x
  have hcas : casimir (act ε (I * (τ : ℂ))) (v : ℝ → ℂ) x =
      (((τ ^ 2 - 1) / 4 : ℝ) : ℂ) * (v : ℝ → ℂ) x := by
    rw [hc]
    push_cast
    linear_combination (-(τ : ℂ) ^ 2 / 4 * (v : ℝ → ℂ) x) * Complex.I_sq
  have e1 : ((((1 / 4 : ℂ) • H (H v) + (1 / 2 : ℂ) • (E (F v) + F (E v)) : S)) : ℝ → ℂ) x =
      casimir (act ε (I * (τ : ℂ))) (v : ℝ → ℂ) x := by
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hH (H v), hH v, hE (F v), hF v, hF (E v), hE v, casimir]
    ring
  rw [e1, hcas]
  simp

/-! ### The hypotheses are satisfiable: smooth functions with the derived operators -/

open scoped ContDiff

/-- The space of smooth functions `ℝ → ℂ`. -/
def smoothFns : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f}
  add_mem' := fun {_ _} (ha : ContDiff ℝ ∞ _) (hb : ContDiff ℝ ∞ _) => ha.add hb
  zero_mem' := (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => (0 : ℂ))
  smul_mem' := fun _ _ (hf : ContDiff ℝ ∞ _) => contDiff_const.smul hf

lemma contDiff_ofReal_id : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff

lemma mem_smoothFns {f : ℝ → ℂ} : f ∈ smoothFns ↔ ContDiff ℝ ∞ f := Iff.rfl

/-- The first-order operator `f ↦ a f + b f'` on smooth functions, for smooth coefficients. -/
def smoothOp (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    smoothFns →ₗ[ℂ] smoothFns where
  toFun f := ⟨fun x => a x * (f : ℝ → ℂ) x + b x * deriv (f : ℝ → ℂ) x,
    (ha.mul f.2).add (hb.mul (contDiff_infty_iff_deriv.1 f.2).2)⟩
  map_add' f g := by
    refine Subtype.ext (funext fun x => ?_)
    have hf := (contDiff_infty_iff_deriv.1 f.2).1 x
    have hg := (contDiff_infty_iff_deriv.1 g.2).1 x
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [deriv_add hf hg]
    ring
  map_smul' c f := by
    refine Subtype.ext (funext fun x => ?_)
    have hf := (contDiff_infty_iff_deriv.1 f.2).1 x
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [deriv_const_smul c hf]
    simp only [smul_eq_mul]
    ring

lemma smoothOp_apply (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (f : smoothFns)
    (x : ℝ) : (smoothOp a b ha hb f : ℝ → ℂ) x = a x * (f : ℝ → ℂ) x + b x * deriv (f : ℝ → ℂ) x :=
  rfl

/-- The derived action `E` on smooth functions: `(iν-1) x f - x² f'`, `ν = iτ`. -/
def opE (τ : ℝ) : smoothFns →ₗ[ℂ] smoothFns :=
  smoothOp (fun x => (I * (I * τ) - 1) * x) (fun x => -(x : ℂ) ^ 2)
    (contDiff_const.mul contDiff_ofReal_id) ((contDiff_ofReal_id.pow 2).neg)

/-- The derived action `F = d/dx` on smooth functions. -/
def opF : smoothFns →ₗ[ℂ] smoothFns :=
  smoothOp (fun _ => 0) (fun _ => 1) contDiff_const contDiff_const

/-- The derived action `H`: `(1 - iν) f + 2x f'`, `ν = iτ`. -/
def opH (τ : ℝ) : smoothFns →ₗ[ℂ] smoothFns :=
  smoothOp (fun _ => 1 - I * (I * τ)) (fun x => 2 * (x : ℂ)) contDiff_const
    (contDiff_const.mul contDiff_ofReal_id)

lemma opE_eq (ε : ℤ) (τ : ℝ) (f : smoothFns) :
    (opE τ f : ℝ → ℂ) = derivAlong (act ε (I * τ)) upper f := by
  funext x
  have hd := ((contDiff_infty_iff_deriv.1 f.2).1) x
  rw [derivAlong_upper ε _ hd, opE, smoothOp_apply]
  ring

lemma opF_eq (ε : ℤ) (τ : ℝ) (f : smoothFns) :
    (opF f : ℝ → ℂ) = derivAlong (act ε (I * τ)) lower f := by
  funext x
  have hd := ((contDiff_infty_iff_deriv.1 f.2).1) x
  rw [derivAlong_lower ε _ hd, opF, smoothOp_apply]
  ring

lemma opH_eq (ε : ℤ) (τ : ℝ) (f : smoothFns) :
    (opH τ f : ℝ → ℂ) = derivAlong (act ε (I * τ)) expH f := by
  funext x
  have hd := ((contDiff_infty_iff_deriv.1 f.2).1) x
  rw [derivAlong_expH ε _ hd, opH, smoothOp_apply]

lemma contDiff_sphericalVec (τ : ℝ) : ContDiff ℝ ∞ (sphericalVec τ) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ => (1 + x ^ 2) ^ (-(τ + 1) / 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).rpow_const_of_ne (fun x => by positivity)
  exact Complex.ofRealCLM.contDiff.comp h

/-- **No positive invariant form for `|τ| > 1`, on smooth functions** (infinitesimal: `E, F, H` on smooth vectors, not
group-level). The case of
`no_invariant_form` for the space of all smooth functions with the derived operators
`opE, opF, opH` (which exist, so the hypotheses are satisfiable): no positive definite form
for which they are skew. -/
theorem no_invariant_form_smooth (τ : ℝ) (hτ : 1 < |τ|)
    (B : smoothFns →ₛₗ[starRingEnd ℂ] smoothFns →ₗ[ℂ] ℂ)
    (hBE : ∀ u w, B (opE τ u) w + B u (opE τ w) = 0) (hBF : ∀ u w, B (opF u) w + B u (opF w) = 0)
    (hBH : ∀ u w, B (opH τ u) w + B u (opH τ w) = 0) :
    ¬ ∀ u, u ≠ 0 → 0 < (B u u).re :=
  no_invariant_form 0 τ hτ smoothFns
    (fun f hf => by
      have := contDiff_infty_iff_deriv.1 hf
      exact ⟨this.1, ((contDiff_infty_iff_deriv.1 this.2).1)⟩)
    (opE τ) opF (opH τ) (opE_eq 0 τ) (opF_eq 0 τ) (opH_eq 0 τ)
    ⟨sphericalVec τ, contDiff_sphericalVec τ⟩ rfl B hBE hBF hBH

end Concrete

end Lightlike.Lorentz.SL2RPlancherel
