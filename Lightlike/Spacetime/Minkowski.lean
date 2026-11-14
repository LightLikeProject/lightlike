module

public import Lightlike.Spacetime.Lorentzian

/-!
# Minkowski space and proper time

Minkowski space of dimension `n` is the manifold `ℝⁿ = Fin n → ℝ` (modelled on itself, one global
chart) with the constant metric `η = diag(-1, 1, …, 1)`.

Main results
* `minkowskiForm_isLorentzian` : `η` is a Lorentzian form (the standard basis is a Lorentz frame).
* `minkowskiMetric` : `η` as a smooth `LorentzianMetric` on the manifold `ℝⁿ`.
* `properTime_inertial` : proper time along an inertial worldline `t ↦ x + t v`.
* `properTime_reparam` : proper time is invariant under orientation-preserving `C¹`
  reparametrisations.
* `reverse_cauchySchwarz`, `twin_paradox` : for future-directed timelike vectors,
  `τ(u) + τ(v) ≤ τ(u + v)` - the straight worldline maximises proper time (the kinematic core of
  the twin paradox).

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), ch. 1 (special relativity and flat spacetime); R. M. Wald, *General Relativity* (University of Chicago Press, 1984), ch. 1.
-/

@[expose] public section

open Bundle Manifold Matrix Set
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

/-- The Minkowski bilinear form `η(v, w) = Σᵢ ηᵢᵢ vⁱ wⁱ` on `ℝⁿ`, as a continuous bilinear map. -/
def minkowskiForm (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, etaDiag i •
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

@[simp] lemma minkowskiForm_apply {n : ℕ} (v w : Fin n → ℝ) :
    minkowskiForm n v w = ∑ i, etaDiag i * v i * w i := by
  simp [minkowskiForm, _root_.sum_apply, mul_assoc]

/-- `η(eᵢ, eⱼ) = ηᵢⱼ` on the standard basis vectors. -/
lemma minkowskiForm_single {n : ℕ} (i j : Fin n) :
    minkowskiForm n (Pi.single i 1) (Pi.single j 1) = eta n i j := by
  simp only [minkowskiForm_apply, eta_apply]
  by_cases h : i = j
  · subst h; simp [Pi.single_apply]
  · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simp [Ne.symm h]
    · simp [Pi.single_apply, hk]

/-- The standard basis of `ℝⁿ` is a Lorentz frame for `η`. -/
theorem minkowskiForm_isLorentzian (n : ℕ) : IsLorentzianForm n (minkowskiForm n) :=
  ⟨Pi.basisFun ℝ (Fin n), fun i j => by simpa using minkowskiForm_single i j⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Minkowski space** as a smooth Lorentzian manifold: the manifold `ℝⁿ` with the constant
metric `η` on every tangent space. Smoothness is proved exactly as Mathlib proves smoothness of the
constant Riemannian metric on an inner product space (`riemannianMetricVectorSpace`). -/
def minkowskiMetric (n : ℕ) : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) (Fin n → ℝ) n where
  g _ := minkowskiForm n
  lorentzian _ := minkowskiForm_isLorentzian n
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := minkowskiForm n)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

/-! ## Proper time -/

variable {n : ℕ}

/-- The squared Minkowski length `η(v, v)` (negative for timelike `v`). -/
def mSq (v : Fin n → ℝ) : ℝ := minkowskiForm n v v

/-- The proper time elapsed along a straight segment with displacement `v`: `√(-η(v,v))`. -/
def tau (v : Fin n → ℝ) : ℝ := √(-mSq v)

/-- **Proper time** along a curve `γ : ℝ → ℝⁿ` between parameters `a` and `b`:
`τ[γ] = ∫ₐᵇ √(-η(γ'(t), γ'(t))) dt`. (Meaningful for timelike curves; for other curves the
integrand is `0` wherever `γ'` is not timelike, by the convention `√x = 0` for `x ≤ 0`.) -/
def properTime (γ : ℝ → Fin n → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, tau (deriv γ t)

lemma mSq_smul (c : ℝ) (v : Fin n → ℝ) : mSq (c • v) = c ^ 2 * mSq v := by
  simp only [mSq, map_smul, _root_.smul_apply, smul_eq_mul]; ring

lemma tau_smul {c : ℝ} (hc : 0 ≤ c) (v : Fin n → ℝ) : tau (c • v) = c * tau v := by
  rw [tau, mSq_smul, show -(c ^ 2 * mSq v) = c ^ 2 * -mSq v by ring, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq hc, tau]

/-- Proper time along the inertial worldline `t ↦ x + t • v` is `(b - a) · √(-η(v,v))`. -/
theorem properTime_inertial (x v : Fin n → ℝ) (a b : ℝ) :
    properTime (fun t => x + t • v) a b = (b - a) * tau v := by
  have hd : ∀ t, deriv (fun t : ℝ => x + t • v) t = v := fun t => by
    simpa using (((hasDerivAt_id t).smul_const v).const_add x).deriv
  simp [properTime, hd]

lemma continuous_tau : Continuous (tau : (Fin n → ℝ) → ℝ) := by
  unfold tau mSq; fun_prop

/-- **Reparametrisation invariance of proper time.** If `φ` is `C¹` and non-decreasing
(`φ' ≥ 0`) and `γ` is `C¹`, then `τ[γ ∘ φ] on [a,b] = τ[γ] on [φ a, φ b]`. -/
theorem properTime_reparam (γ : ℝ → Fin n → ℝ) (φ : ℝ → ℝ) (hγ : ContDiff ℝ 1 γ)
    (hφ : ContDiff ℝ 1 φ) (hmono : ∀ t, 0 ≤ deriv φ t) (a b : ℝ) :
    properTime (γ ∘ φ) a b = properTime γ (φ a) (φ b) := by
  have hγd : Differentiable ℝ γ := hγ.differentiable one_ne_zero
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hchain : ∀ t, deriv (γ ∘ φ) t = deriv φ t • deriv γ (φ t) := fun t => by
    exact deriv.scomp t (hγd _) (hφd _)
  unfold properTime
  simp_rw [hchain, tau_smul (hmono _)]
  have hcont : Continuous fun t => tau (deriv γ t) :=
    continuous_tau.comp (hγ.continuous_deriv le_rfl)
  rw [← intervalIntegral.integral_comp_mul_deriv (f := φ) (f' := deriv φ)
    (g := fun t => tau (deriv γ t)) (fun t _ => (hφd t).hasDerivAt)
    (hφ.continuous_deriv le_rfl).continuousOn hcont]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp [mul_comm]

/-! ## The reverse triangle inequality (twin paradox) -/

variable {d : ℕ}

/-- A vector in `ℝ^{d+1}` is **future-directed timelike** if `η(v,v) < 0` and `v⁰ > 0`. -/
def IsFutureTimelike (v : Fin (d + 1) → ℝ) : Prop := mSq v < 0 ∧ 0 < v 0

/-- Squared spatial length `Σᵢ (vⁱ)²`, `i = 1 … d`. -/
def spatialSq (v : Fin (d + 1) → ℝ) : ℝ := ∑ i : Fin d, v i.succ ^ 2

lemma mSq_eq (v : Fin (d + 1) → ℝ) : mSq v = -(v 0) ^ 2 + spatialSq v := by
  simp [mSq, spatialSq, Fin.sum_univ_succ, etaDiag, Fin.succ_ne_zero, sq]

lemma minkowskiForm_eq (u v : Fin (d + 1) → ℝ) :
    minkowskiForm (d + 1) u v = -(u 0 * v 0) + ∑ i : Fin d, u i.succ * v i.succ := by
  simp [Fin.sum_univ_succ, etaDiag, Fin.succ_ne_zero]

/-- **Reverse Cauchy–Schwarz inequality** in Minkowski space: for future-directed timelike
`u, v`, `-η(u,v) ≥ τ(u) τ(v)`. (In Euclidean space the inequality goes the other way.) -/
theorem reverse_cauchySchwarz {u v : Fin (d + 1) → ℝ} (hu : IsFutureTimelike u)
    (hv : IsFutureTimelike v) : tau u * tau v ≤ -minkowskiForm (d + 1) u v := by
  obtain ⟨hu1, hu0⟩ := hu
  obtain ⟨hv1, hv0⟩ := hv
  rw [mSq_eq] at hu1 hv1
  set a := spatialSq u
  set b := spatialSq v
  set s := ∑ i : Fin d, u i.succ * v i.succ with hs
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- Euclidean Cauchy–Schwarz on the spatial parts
  have hcs : s ^ 2 ≤ a * b := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  set α := √a
  set β := √b
  have hα : α ^ 2 = a := Real.sq_sqrt ha
  have hβ : β ^ 2 = b := Real.sq_sqrt hb
  have hα0 : 0 ≤ α := Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := Real.sqrt_nonneg _
  have hsαβ : s ≤ α * β := by
    have : |s| ≤ α * β := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul ha]
      exact Real.sqrt_le_sqrt hcs
    exact (le_abs_self s).trans this
  have hαu : α < u 0 := by nlinarith
  have hβv : β < v 0 := by nlinarith
  rw [minkowskiForm_eq, ← hs]
  have hC : 0 ≤ u 0 * v 0 - s := by nlinarith [mul_le_mul hαu.le hβv.le hβ0 hu0.le]
  have key : (u 0 ^ 2 - a) * (v 0 ^ 2 - b) ≤ (u 0 * v 0 - s) ^ 2 := by
    nlinarith [sq_nonneg (u 0 * β - v 0 * α), mul_le_mul hαu.le hβv.le hβ0 hu0.le]
  have htu : tau u = √(u 0 ^ 2 - a) := by rw [tau, mSq_eq]; ring_nf; rfl
  have htv : tau v = √(v 0 ^ 2 - b) := by rw [tau, mSq_eq]; ring_nf; rfl
  rw [htu, htv, ← Real.sqrt_mul (by nlinarith), show -(-(u 0 * v 0) + s) = u 0 * v 0 - s by ring]
  calc √((u 0 ^ 2 - a) * (v 0 ^ 2 - b)) ≤ √((u 0 * v 0 - s) ^ 2) := Real.sqrt_le_sqrt key
    _ = u 0 * v 0 - s := Real.sqrt_sq hC

/-- **Twin paradox (reverse triangle inequality).** For future-directed timelike displacements
`u` and `v`, the proper time along the broken worldline `0 → u → u + v` is at most the proper time
along the straight worldline `0 → u + v`: `τ(u) + τ(v) ≤ τ(u + v)`. -/
theorem twin_paradox {u v : Fin (d + 1) → ℝ} (hu : IsFutureTimelike u)
    (hv : IsFutureTimelike v) : tau u + tau v ≤ tau (u + v) := by
  have hrc := reverse_cauchySchwarz hu hv
  have hA : 0 ≤ -mSq u := by linarith [hu.1]
  have hB : 0 ≤ -mSq v := by linarith [hv.1]
  have hsum : -mSq (u + v) = -mSq u + 2 * -minkowskiForm (d + 1) u v + -mSq v := by
    simp only [mSq, map_add, _root_.add_apply]
    rw [(minkowskiForm_isLorentzian (d + 1)).symm v u]; ring
  have h1 : (tau u + tau v) ^ 2 ≤ -mSq (u + v) := by
    rw [hsum]
    have := Real.sq_sqrt hA; have := Real.sq_sqrt hB
    simp only [tau] at hrc ⊢
    nlinarith
  calc tau u + tau v = √((tau u + tau v) ^ 2) :=
        (Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    _ ≤ tau (u + v) := Real.sqrt_le_sqrt h1

end Lightlike
