import Lightlike.Spacetime.VariationDet
import Lightlike.Spacetime.Curvature

/-!
# The derivatives of the inverse metric and of the volume density (GE15, stage S2)

For a symmetric metric `g` on `ℝⁿ`, differentiable at `x` with `det g x ≠ 0`:

* `pd_inv_eq`: `∂_ρ gˢᵛ = -Γˢ_{ρα} gᵃᵛ - Γᵛ_{ρα} gˢᵃ`;
* `pd_sqrt_abs_det`: `∂_ρ √|det g| = √|det g| Γ^κ_{κρ}`;
* `hasDerivAt_det_path`, `hasDerivAt_sqrt_abs`: Jacobi's formula along a path and the derivative of `√|f|`.

**Limits.** Coordinate statements on `ℝⁿ`, for the coordinate Christoffel symbols of `Curvature.lean`; stage S2 of the first variation
of the Einstein-Hilbert action.
-/

open Matrix

noncomputable section

namespace Lightlike

variable {n : ℕ}

/-- **The derivative of the inverse metric**: `∂_ρ gˢᵛ = -Γˢ_{ρα} gᵃᵛ - Γᵛ_{ρα} gˢᵃ` for a symmetric metric. -/
theorem pd_inv_eq (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hsym : ∀ y a b, g y a b = g y b a) (hd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x)
    (hx : (g x).det ≠ 0) (ρ σ ν : Fin n) :
    pd ρ (fun y => (g y)⁻¹ σ ν) x =
      -∑ α, (christoffel g σ ρ α x * (g x)⁻¹ α ν + christoffel g ν ρ α x * (g x)⁻¹ σ α) := by
  have h1 := fderiv_inv_entry hd hx (Pi.single ρ (1 : ℝ) : Fin n → ℝ) σ ν
  unfold pd
  rw [h1]
  set G : Matrix (Fin n) (Fin n) ℝ := (g x)⁻¹ with hG
  have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
    have : (g x)ᵀ = g x := by ext i j; exact hsym x j i
    rw [Matrix.transpose_nonsing_inv, this]
  have hGs : ∀ a b, G a b = G b a := by
    intro a b
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hT a) b).symm
  set Dg : Fin n → Fin n → Fin n → ℝ := fun a b c => pd c (fun y => g y a b) x with hDg
  have hDs : ∀ a b c, Dg a b c = Dg b a c := by
    intro a b c
    simp only [hDg]
    have : (fun y => g y a b) = fun y => g y b a := by funext y; exact hsym y a b
    rw [this]
  have hΓ : ∀ s a, christoffel g s ρ a x =
      (1 / 2) * ∑ l, G s l * (Dg l a ρ + Dg l ρ a - Dg ρ a l) := fun s a => rfl
  have hH : ∀ a b, fderiv ℝ (fun y => g y a b) x (Pi.single ρ (1 : ℝ) : Fin n → ℝ) = Dg a b ρ := fun a b => rfl
  simp only [hH, Matrix.mul_apply, Matrix.of_apply, hΓ]
  congr 1
  rw [Finset.sum_add_distrib]
  have hR2 : ∑ x, (1 / 2 * ∑ l, G ν l * (Dg l x ρ + Dg l ρ x - Dg ρ x l)) * G σ x =
      ∑ x, ∑ l, 1 / 2 * G σ l * G x ν * (Dg x l ρ + Dg x ρ l - Dg ρ l x) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hGs ν x]; ring
  have hR1 : ∑ x, (1 / 2 * ∑ l, G σ l * (Dg l x ρ + Dg l ρ x - Dg ρ x l)) * G x ν =
      ∑ x, ∑ l, 1 / 2 * G σ l * G x ν * (Dg l x ρ + Dg l ρ x - Dg ρ x l) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hL : ∑ j, (∑ j_1, G σ j_1 * Dg j_1 j ρ) * G j ν = ∑ x, ∑ l, G σ l * G x ν * Dg l x ρ := by
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hR1, hR2, hL, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hDs x l ρ, hDs l ρ x, hDs x ρ l]
  ring


/-- **Jacobi's formula along a path**: `d/ds det M(s) = det M(0) tr (M(0)⁻¹ M'(0))`. -/
theorem hasDerivAt_det_path (M : ℝ → Matrix (Fin n) (Fin n) ℝ) (M' : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) 0) (hG : (M 0).det ≠ 0) :
    HasDerivAt (fun s => (M s).det) ((M 0).det * ((M 0)⁻¹ * M').trace) 0 := by
  set Φ : (Fin n → Fin n → ℝ) → ℝ := fun A => Matrix.det A with hΦ
  have hdiffΦ : DifferentiableAt ℝ Φ (M 0) :=
    differentiableAt_det_of (f := fun A : Fin n → Fin n → ℝ => (A : Matrix (Fin n) (Fin n) ℝ)) (fun i j =>
      (differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_id : DifferentiableAt ℝ (id : (Fin n → Fin n → ℝ) → _) (M 0)) i) j))
  have hcurve : HasDerivAt (fun s => (M s : Fin n → Fin n → ℝ)) (M' : Fin n → Fin n → ℝ) 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => h i j
  have h1 := hdiffΦ.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcurve
  -- the same for the affine curve
  have hline : HasDerivAt (fun s : ℝ => ((M 0 + s • M' : Matrix (Fin n) (Fin n) ℝ) : Fin n → Fin n → ℝ)) (M' : Fin n → Fin n → ℝ) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (M' i j)).const_add (M 0 i j)
  have hline0 : (M 0 + (0 : ℝ) • M' : Matrix (Fin n) (Fin n) ℝ) = M 0 := by simp
  have h2 := hdiffΦ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by show M 0 = M 0 + (0 : ℝ) • M'; exact hline0.symm)
  have hJ := hasDerivAt_det_add_smul (M 0) M' (isUnit_iff_ne_zero.2 hG)
  have e2 : (fderiv ℝ Φ (M 0)) (M' : Fin n → Fin n → ℝ) = (M 0).det * ((M 0)⁻¹ * M').trace := h2.unique hJ
  rw [e2] at h1
  exact h1


/-- The derivative of `√|f|` where `f ≠ 0`: `d/ds √|f s| = (d / f 0) √|f 0| / 2`. -/
theorem hasDerivAt_sqrt_abs {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (h0 : f 0 ≠ 0) :
    HasDerivAt (fun s => √|f s|) (d / f 0 * √|f 0| / 2) 0 := by
  set s : ℝ := (SignType.sign (f 0) : ℝ) with hs
  have hs2 : s * f 0 = |f 0| := by
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [hs, abs_of_neg h, sign_neg h]
    · simp [hs, abs_of_pos h, sign_pos h]
  have hpos : 0 < |f 0| := abs_pos.2 h0
  have hev : (fun t => √|f t|) =ᶠ[nhds 0] fun t => √(s * f t) := by
    have hc : ContinuousAt f 0 := hf.continuousAt
    have : ∀ᶠ t in nhds (0 : ℝ), s * f t > 0 := by
      have := hc.tendsto.const_mul s
      refine this.eventually (lt_mem_nhds ?_)
      simpa [hs2] using hpos
    filter_upwards [this] with t ht
    congr 1
    rcases lt_or_gt_of_ne h0 with h | h
    · have hsn : s = -1 := by simp [hs, sign_neg h]
      rw [hsn] at ht ⊢
      rw [abs_of_neg (by linarith)]; ring
    · have hsn : s = 1 := by simp [hs, sign_pos h]
      rw [hsn] at ht ⊢
      rw [abs_of_pos (by linarith)]; ring
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have h1 : HasDerivAt (fun t : ℝ => s * f t) (s * d) 0 := hf.const_mul s
  have h2 := h1.sqrt (by rw [hs2]; exact hpos.ne')
  convert h2 using 1
  rw [hs2]
  have hsq : √|f 0| * √|f 0| = |f 0| := Real.mul_self_sqrt hpos.le
  have hq : 0 < √|f 0| := Real.sqrt_pos.2 hpos
  have hss : s * s = 1 := by
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [hs, sign_neg h]
    · simp [hs, sign_pos h]
  field_simp
  rw [Real.sq_sqrt hpos.le, ← hs2]
  ring


/-- **The derivative of the volume density**: `∂_ρ √|det g| = √|det g| Γ^κ_{κρ}` for a symmetric metric. -/
theorem pd_sqrt_abs_det (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hsym : ∀ y a b, g y a b = g y b a) (hd : ∀ a b, DifferentiableAt ℝ (fun y => g y a b) x)
    (hx : (g x).det ≠ 0) (ρ : Fin n) :
    pd ρ (fun y => √|(g y).det|) x = √|(g x).det| * ∑ κ, christoffel g κ κ ρ x := by
  set e : Fin n → ℝ := Pi.single ρ (1 : ℝ) with he
  have hline : HasDerivAt (fun s : ℝ => x + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hlx : (fun s : ℝ => x + s • e) 0 = x := by simp
  have hent : ∀ a b, HasDerivAt (fun s : ℝ => g (x + s • e) a b) (pd ρ (fun y => g y a b) x) 0 := by
    intro a b
    have := (hd a b).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline hlx.symm
    exact this
  have hM0 : g (x + (0 : ℝ) • e) = g x := by simp
  have hdet := hasDerivAt_det_path (fun s => g (x + s • e)) (Matrix.of fun a b => pd ρ (fun y => g y a b) x)
    (fun a b => hent a b) (by simpa [hM0] using hx)
  have hsq := hasDerivAt_sqrt_abs hdet (by simpa [hM0] using hx)
  -- the function is differentiable at `x`
  have hdiffdet : DifferentiableAt ℝ (fun y => (g y).det) x := differentiableAt_det_of hd
  have hdiffψ : DifferentiableAt ℝ (fun y => √|(g y).det|) x := (hdiffdet.abs hx).sqrt (abs_ne_zero.2 hx)
  have hψ := hdiffψ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline hlx.symm
  have hsq' : HasDerivAt ((fun y => √|(g y).det|) ∘ fun s : ℝ => x + s • e)
      ((g x).det * ((g x)⁻¹ * Matrix.of fun a b => pd ρ (fun y => g y a b) x).trace / (g x).det * √|(g x).det| / 2) 0 := by
    simp only [hM0] at hsq
    exact hsq
  have hu := hψ.unique hsq'
  have hdet0 := hx
  set G : Matrix (Fin n) (Fin n) ℝ := (g x)⁻¹ with hG
  have hT : ((g x)⁻¹)ᵀ = (g x)⁻¹ := by
    have : (g x)ᵀ = g x := by ext i j; exact hsym x j i
    rw [Matrix.transpose_nonsing_inv, this]
  have hGs : ∀ a b, G a b = G b a := by
    intro a b
    simpa [Matrix.transpose_apply] using (congrFun (congrFun hT a) b).symm
  set Dg : Fin n → Fin n → Fin n → ℝ := fun a b c => pd c (fun y => g y a b) x with hDg
  have hDs : ∀ a b c, Dg a b c = Dg b a c := by
    intro a b c
    simp only [hDg]
    have : (fun y => g y a b) = fun y => g y b a := by funext y; exact hsym y a b
    rw [this]
  have htr : ((g x)⁻¹ * Matrix.of fun a b => pd ρ (fun y => g y a b) x).trace = ∑ κ, ∑ l, G κ l * Dg l κ ρ := by
    simp [Matrix.trace, Matrix.mul_apply, hG, hDg]
  have hchr : ∑ κ, christoffel g κ κ ρ x =
      (1 / 2) * ∑ κ, ∑ l, G κ l * (Dg l κ ρ + Dg l ρ κ - Dg ρ κ l) := by
    simp only [christoffel, Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun l _ => ?_
    have h' := hDs ρ κ l
    simp only [hG, hDg] at h' ⊢
    rw [h']
    ring
  have hcancel : ∑ κ, ∑ l, G κ l * (Dg l ρ κ - Dg ρ κ l) = 0 := by
    have : ∑ κ, ∑ l, G κ l * (Dg l ρ κ - Dg ρ κ l) =
        (∑ κ, ∑ l, G κ l * Dg l ρ κ) - ∑ κ, ∑ l, G κ l * Dg ρ κ l := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [this, sub_eq_zero]
    rw [Finset.sum_comm (f := fun κ l => G κ l * Dg ρ κ l)]
    refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hGs l κ, hDs l ρ κ]
  have hsplit : ∑ κ, ∑ l, G κ l * (Dg l κ ρ + Dg l ρ κ - Dg ρ κ l) =
      (∑ κ, ∑ l, G κ l * Dg l κ ρ) + ∑ κ, ∑ l, G κ l * (Dg l ρ κ - Dg ρ κ l) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun l _ => by ring
  have hmain : (fderiv ℝ (fun y => √|(g y).det|) x) e =
      √|(g x).det| * ∑ κ, christoffel g κ κ ρ x := by
    rw [hu, htr, hchr, hsplit, hcancel]
    field_simp
    ring
  exact hmain

end Lightlike
