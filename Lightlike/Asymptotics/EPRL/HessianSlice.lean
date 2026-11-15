import Lightlike.Oscillatory.PhaseReduction

/-!
# The Hessian through second derivatives along lines and curves

Two general facts used to compare the Hessian of an amplitude in two charts:

* `iteratedDeriv_two_line`: for a smooth `φ : ℝⁿ → ℂ`, the second derivative at `0` of
  `t ↦ φ(t u)` is the quadratic form `uᵀ (hessMat φ 0) u`;
* `iteratedDeriv_two_comp_eq`: for smooth `Φ` on a normed space and two smooth curves with the same
  value, velocity and acceleration at `0`, the second derivatives of `Φ ∘ c` agree.

A symmetric complex matrix whose quadratic form vanishes on all real vectors is zero
(`eq_zero_of_isSymm_of_qform`).
-/

open Matrix Complex Lightlike.Oscillatory
open scoped ContDiff

namespace Lightlike.Asymptotics.EPRL

/-- The second derivative of `Φ ∘ c` at `0`: `D²Φ(c₀)(c', c') + DΦ(c₀)(c'')`. -/
theorem deriv_deriv_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℂ} (hΦ : ContDiff ℝ ∞ Φ) {c : ℝ → E} (hc : ContDiff ℝ ∞ c) :
    deriv (deriv (Φ ∘ c)) 0 = fderiv ℝ (fderiv ℝ Φ) (c 0) (deriv c 0) (deriv c 0) +
      fderiv ℝ Φ (c 0) (deriv (deriv c) 0) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΦ' : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hc' : Differentiable ℝ (deriv c) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hc).2).1
  have h1 : deriv (Φ ∘ c) = fun t => fderiv ℝ Φ (c t) (deriv c t) := funext fun t =>
    fderiv_comp_deriv t (hΦd _) (hcd t)
  rw [h1]
  have hA : HasDerivAt (fun t => fderiv ℝ Φ (c t))
      (fderiv ℝ (fderiv ℝ Φ) (c 0) (deriv c 0)) 0 :=
    (hΦ' (c 0)).hasFDerivAt.comp_hasDerivAt 0 (hcd 0).hasDerivAt
  have hB : HasDerivAt (deriv c) (deriv (deriv c) 0) 0 := (hc' 0).hasDerivAt
  exact (hA.clm_apply hB).deriv

/-- The second derivative at `0` of `t ↦ φ(t u)` is the quadratic form of the Hessian. -/
theorem iteratedDeriv_two_line {n : ℕ} {φ : (Fin n → ℝ) → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (u : Fin n → ℝ) :
    iteratedDeriv 2 (fun t : ℝ => φ (t • u)) 0 =
      ∑ i, ∑ j, (u i : ℂ) * u j * hessMat φ 0 i j := by
  classical
  have hc : ContDiff ℝ ∞ (fun t : ℝ => t • u) := contDiff_id.smul contDiff_const
  have hd : deriv (fun t : ℝ => t • u) = fun _ => u := funext fun t => by
    simpa using ((hasDerivAt_id t).smul_const u).deriv
  have hdd : deriv (deriv fun t : ℝ => t • u) 0 = 0 := by rw [hd]; simp
  have h := deriv_deriv_comp hφ hc
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  change deriv (deriv (φ ∘ fun t : ℝ => t • u)) 0 = _
  rw [h, hdd, hd]
  simp only [map_zero, add_zero, zero_smul]
  have hu : u = ∑ i, u i • (Pi.single i 1 : Fin n → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hessMat_eq hφ, Complex.real_smul, Complex.real_smul]
  ring

/-- **Second derivatives of compositions** depend only on the 2-jet of the curve. -/
theorem iteratedDeriv_two_comp_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℂ} (hΦ : ContDiff ℝ ∞ Φ) {c₁ c₂ : ℝ → E} (h₁ : ContDiff ℝ ∞ c₁)
    (h₂ : ContDiff ℝ ∞ c₂) (h0 : c₁ 0 = c₂ 0) (h1 : deriv c₁ 0 = deriv c₂ 0)
    (h2 : deriv (deriv c₁) 0 = deriv (deriv c₂) 0) :
    iteratedDeriv 2 (Φ ∘ c₁) 0 = iteratedDeriv 2 (Φ ∘ c₂) 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]
  rw [deriv_deriv_comp hΦ h₁, deriv_deriv_comp hΦ h₂, h0, h1, h2]

/-- A symmetric matrix over `ℂ` whose quadratic form vanishes on all real vectors is zero. -/
theorem eq_zero_of_isSymm_of_qform {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.IsSymm)
    (h : ∀ u : Fin n → ℝ, ∑ i, ∑ j, (u i : ℂ) * u j * B i j = 0) : B = 0 := by
  classical
  set b : (Fin n → ℝ) → (Fin n → ℝ) → ℂ := fun u v => ∑ i, ∑ j, (u i : ℂ) * v j * B i j with hb
  have key : ∀ u v, ∑ i, ∑ j, ((u + v) i : ℂ) * (u + v) j * B i j =
      b u u + b v v + b u v + b v u := fun u v => by
    simp only [hb, Pi.add_apply, Complex.ofReal_add, add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hbij : ∀ i j, b (Pi.single i 1) (Pi.single j 1) = B i j := fun i j => by
    simp only [hb, Pi.single_apply, apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one,
      Complex.ofReal_zero, ite_mul, mul_ite, one_mul, zero_mul, mul_zero, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hbu : ∀ u, b u u = 0 := fun u => h u
  ext i j
  by_cases hij : i = j
  · subst hij
    have := hbu (Pi.single i 1)
    rw [hbij] at this
    simpa using this
  · have h1 := h (Pi.single i 1 + Pi.single j 1)
    rw [key, hbu, hbu, hbij, hbij, hB.apply i j] at h1
    have h2 : (2 : ℂ) * B i j = 0 := by linear_combination h1
    simpa using h2

end Lightlike.Asymptotics.EPRL
