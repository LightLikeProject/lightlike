import Mathlib

/-!
# The variation of the volume density (GE15, stage S1, first part)

`hasDerivAt_det_add_smul` is Jacobi's formula `d/dt det (G + t H) = det G · tr (G⁻¹ H)` at `t = 0` for an invertible `G`; `hasDerivAt_sqrt_abs_det_add_smul`
is `d/dt √|det (G + t H)| = ½ √|det G| tr (G⁻¹ H)`, the variation `δ√|g| = ½ √|g| gᵘᵛ δg_{uv}` of the volume density. Neither is in Mathlib.

`hasDerivAt_inv_add_smul` is the derivative of the matrix inverse along a line, `d/dt (G + t H)⁻¹ = -G⁻¹ H G⁻¹` (entrywise).

**Limits.** Stage S1 of the first variation of the Einstein-Hilbert action: the variation of the Christoffel symbols, the Palatini identity
and the integral statement are not in this file.
-/

open Matrix Polynomial

namespace Lightlike

variable {n : ℕ}

/-- The derivative of `det (1 + t A)` at `t = 0` is `tr A`. -/
theorem hasDerivAt_det_one_add_smul (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • A).det) A.trace 0 := by
  set Q : ℝ[X] := (det (1 + (X : ℝ[X]) • A.map C)).divX.divX with hQ
  have h : (fun t : ℝ => (1 + t • A).det) = fun t => 1 + A.trace * t + Q.eval t * t ^ 2 := by
    funext t
    exact Matrix.det_one_add_smul t A
  rw [h]
  have h1 : HasDerivAt (fun t : ℝ => 1 + A.trace * t) A.trace 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul A.trace).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => Q.eval t * t ^ 2) 0 0 := by
    have := (Q.hasDerivAt (0 : ℝ)).mul ((hasDerivAt_pow 2 (0 : ℝ)))
    convert this using 1
    simp
  have := h1.add h2
  convert this using 1
  simp

/-- **Jacobi's formula** along a line: `d/dt det (G + t H) = det G · tr (G⁻¹ H)` at `t = 0`. -/
theorem hasDerivAt_det_add_smul (G H : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G.det) :
    HasDerivAt (fun t : ℝ => (G + t • H).det) (G.det * (G⁻¹ * H).trace) 0 := by
  have e : ∀ t : ℝ, (G + t • H).det = G.det * (1 + t • (G⁻¹ * H)).det := by
    intro t
    have : G + t • H = G * (1 + t • (G⁻¹ * H)) := by
      rw [mul_add, mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
    rw [this, Matrix.det_mul]
  simp_rw [e]
  exact (hasDerivAt_det_one_add_smul (G⁻¹ * H)).const_mul G.det

/-- **The variation of the volume density**: `d/dt √|det (G + t H)| = ½ √|det G| tr (G⁻¹ H)` at `t = 0`. -/
theorem hasDerivAt_sqrt_abs_det_add_smul (G H : Matrix (Fin n) (Fin n) ℝ) (hG : G.det ≠ 0) :
    HasDerivAt (fun t : ℝ => √|(G + t • H).det|) ((1 / 2) * √|G.det| * (G⁻¹ * H).trace) 0 := by
  have hd := hasDerivAt_det_add_smul G H (IsUnit.mk0 _ hG)
  set s : ℝ := (SignType.sign G.det : ℝ) with hs
  have hs2 : s * G.det = |G.det| := by
    rcases lt_or_gt_of_ne hG with h | h
    · simp [hs, abs_of_neg h, sign_neg h]
    · simp [hs, abs_of_pos h, sign_pos h]
  have hpos : 0 < |G.det| := abs_pos.2 hG
  have hs1 : s * s = 1 := by
    rcases lt_or_gt_of_ne hG with h | h
    · simp [hs, sign_neg h]
    · simp [hs, sign_pos h]
  have hev : (fun t : ℝ => √|(G + t • H).det|) =ᶠ[nhds 0] fun t => √(s * (G + t • H).det) := by
    have hc : ContinuousAt (fun t : ℝ => (G + t • H).det) 0 := hd.continuousAt
    have : ∀ᶠ t in nhds (0 : ℝ), s * (G + t • H).det > 0 := by
      have := hc.tendsto.const_mul s
      refine this.eventually (lt_mem_nhds ?_)
      simpa [hs2] using hpos
    filter_upwards [this] with t ht
    congr 1
    have : |(G + t • H).det| = s * (G + t • H).det := by
      rcases lt_or_gt_of_ne hG with h | h
      · have hsn : s = -1 := by simp [hs, sign_neg h]
        rw [hsn] at ht ⊢
        rw [abs_of_neg (by linarith)]; ring
      · have hsn : s = 1 := by simp [hs, sign_pos h]
        rw [hsn] at ht ⊢
        rw [abs_of_pos (by linarith)]; ring
    exact this
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (fun t : ℝ => s * (G + t • H).det) (s * (G.det * (G⁻¹ * H).trace)) 0 := hd.const_mul s
  have h2 := h1.sqrt (by simpa [hs2] using hpos.ne')
  convert h2 using 1
  simp only [zero_smul, add_zero, hs2]
  have : s * (G.det * (G⁻¹ * H).trace) = |G.det| * (G⁻¹ * H).trace := by rw [← mul_assoc, hs2]
  rw [this]
  have hsq : √|G.det| * √|G.det| = |G.det| := Real.mul_self_sqrt hpos.le
  have hq : 0 < √|G.det| := Real.sqrt_pos.2 hpos
  field_simp
  rw [Real.sq_sqrt hpos.le]
  ring


theorem differentiable_det_of {f : ℝ → Matrix (Fin n) (Fin n) ℝ} (hf : ∀ i j, Differentiable ℝ (fun t => f t i j)) :
    Differentiable ℝ (fun t => (f t).det) := by
  simp only [Matrix.det_apply]
  refine Differentiable.fun_sum fun σ _ => ?_
  exact (Differentiable.fun_finset_prod fun i _ => hf _ _).const_smul _

theorem differentiable_adjugate_of {f : ℝ → Matrix (Fin n) (Fin n) ℝ} (hf : ∀ i j, Differentiable ℝ (fun t => f t i j))
    (i j : Fin n) : Differentiable ℝ (fun t => (f t).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine differentiable_det_of fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    exact differentiable_const _
  · simp only [Matrix.updateRow_ne h]
    exact hf a b

/-- The inverse of a differentiable matrix family is differentiable where the determinant is nonzero. -/
theorem differentiableAt_inv_of {f : ℝ → Matrix (Fin n) (Fin n) ℝ} (hf : ∀ i j, Differentiable ℝ (fun t => f t i j))
    {t : ℝ} (ht : (f t).det ≠ 0) (i j : Fin n) : DifferentiableAt ℝ (fun t => (f t)⁻¹ i j) t := by
  have hd : DifferentiableAt ℝ (fun t => (f t).det) t := (differentiable_det_of hf) t
  have ha : DifferentiableAt ℝ (fun t => (f t).adjugate i j) t := (differentiable_adjugate_of hf i j) t
  have : (fun t => (f t)⁻¹ i j) = fun t => ((f t).det)⁻¹ * (f t).adjugate i j := by
    funext s
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [this]
  exact (hd.inv ht).mul ha

/-- **The derivative of the matrix inverse along a line**: `d/dt (G + t H)⁻¹ = - G⁻¹ H G⁻¹` at `t = 0`, entrywise. -/
theorem hasDerivAt_inv_add_smul (G H : Matrix (Fin n) (Fin n) ℝ) (hG : G.det ≠ 0) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => ((G + t • H)⁻¹) i j) (-(G⁻¹ * H * G⁻¹) i j) 0 := by
  set f : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => G + t • H with hf
  have hfe : ∀ i j, Differentiable ℝ (fun t => f t i j) := by
    intro i j
    simp only [hf, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have h0 : (f 0).det ≠ 0 := by simpa [hf] using hG
  have hdiff : ∀ i j, DifferentiableAt ℝ (fun t => (f t)⁻¹ i j) 0 := fun i j => differentiableAt_inv_of hfe h0 i j
  set D : Matrix (Fin n) (Fin n) ℝ := fun i j => deriv (fun t => (f t)⁻¹ i j) 0 with hD
  -- differentiate `f t * (f t)⁻¹ = 1`
  have hprod : ∀ i j, HasDerivAt (fun t => (f t * (f t)⁻¹) i j) ((H * (f 0)⁻¹ + f 0 * D) i j) 0 := by
    intro i j
    simp only [Matrix.mul_apply]
    have : ∀ k, HasDerivAt (fun t => f t i k * (f t)⁻¹ k j) (H i k * (f 0)⁻¹ k j + f 0 i k * D k j) 0 := by
      intro k
      have h1 : HasDerivAt (fun t => f t i k) (H i k) 0 := by
        simp only [hf, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (H i k)).const_add (G i k)
      exact h1.mul (hdiff k j).hasDerivAt
    simpa [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib] using HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => this k)
  have hone : ∀ t, (f t).det ≠ 0 → f t * (f t)⁻¹ = 1 := fun t ht => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ht)
  have hev : ∀ i j, (fun t => (f t * (f t)⁻¹) i j) =ᶠ[nhds 0] fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j
    have hc : ContinuousAt (fun t => (f t).det) 0 := ((differentiable_det_of hfe) 0).continuousAt
    filter_upwards [hc.eventually_ne h0] with t ht
    rw [hone t ht]
  have hzero : H * (f 0)⁻¹ + f 0 * D = 0 := by
    ext i j
    have := (hprod i j).unique ((hasDerivAt_const (0 : ℝ) ((1 : Matrix (Fin n) (Fin n) ℝ) i j)).congr_of_eventuallyEq (hev i j))
    simpa using this
  have hf0 : f 0 = G := by simp [hf]
  rw [hf0] at hzero
  have hDeq : D = -(G⁻¹ * H * G⁻¹) := by
    have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
    have h1 : G * D = -(H * G⁻¹) := by
      have := hzero; rw [add_eq_zero_iff_eq_neg'] at this ; simpa using this
    calc D = G⁻¹ * (G * D) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = -(G⁻¹ * H * G⁻¹) := by rw [h1, Matrix.mul_neg, Matrix.mul_assoc]
  have := (hdiff i j).hasDerivAt
  rw [show deriv (fun t => (f t)⁻¹ i j) 0 = D i j from rfl, hDeq] at this
  simpa [hf] using this


end Lightlike
