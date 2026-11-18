import Mathlib
import Lightlike.Canonical.HamiltonianHH
import Lightlike.Canonical.MatrixInverseAt

/-!
# The derivatives of the first-order density along the three directions

`Psi` and `Theta` are linear in the 1-jet apart from the quadratic `√h L`. The derivatives along `(0, W)` and along
`(P, 0)` are computed explicitly: `fderiv Psi z (0, W) = −√det · Lbil`, `fderiv Theta z (0, W) = √det · wJ(W)`, and the
derivative along the metric direction involves `∂ h⁻¹ = −h⁻¹ P h⁻¹`.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma gamJ_add_smul (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 W : H1arr d) (t : ℝ) (i j k : Fin d) :
    gamJ Hi (H1 + t • W) i j k = gamJ Hi H1 i j k + t * gamJ Hi W i j k := by
  unfold gamJ
  have h : ∑ l, Hi i l * ((H1 + t • W) j l k + (H1 + t • W) k l j - (H1 + t • W) l j k) =
      (∑ l, Hi i l * (H1 j l k + H1 k l j - H1 l j k)) + t * ∑ l, Hi i l * (W j l k + W k l j - W l j k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]; ring

/-- The polarization of the Einstein Lagrangian in the 1-jet: `d/dt L (H1 + t W)` at `t = 0`. -/
def Lbil (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 W : H1arr d) : ℝ :=
  ∑ σ, ∑ ν, Hi σ ν * ∑ ρ, ∑ l, (gamJ Hi H1 ρ l σ * gamJ Hi W l ρ ν + gamJ Hi W ρ l σ * gamJ Hi H1 l ρ ν -
    gamJ Hi H1 ρ σ ν * gamJ Hi W l ρ l - gamJ Hi W ρ σ ν * gamJ Hi H1 l ρ l)

lemma LgJ_add_smul (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 W : H1arr d) (t : ℝ) :
    LgJ Hi (H1 + t • W) = LgJ Hi H1 + t * Lbil Hi H1 W + t ^ 2 * LgJ Hi W := by
  unfold LgJ Lbil
  simp only [gamJ_add_smul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ν _ => ?_
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun l _ => ?_
  ring

lemma hasDerivAt_LgJ_H1 (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 W : H1arr d) :
    HasDerivAt (fun t : ℝ => LgJ Hi (H1 + t • W)) (Lbil Hi H1 W) 0 := by
  have e : (fun t : ℝ => LgJ Hi (H1 + t • W)) =
      fun t => LgJ Hi H1 + t * Lbil Hi H1 W + t ^ 2 * LgJ Hi W := funext (LgJ_add_smul Hi H1 W)
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => t * Lbil Hi H1 W) (Lbil Hi H1 W) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (Lbil Hi H1 W)
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * LgJ Hi W) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const (LgJ Hi W)
  have := ((h1.const_add (LgJ Hi H1)).add h2)
  exact HasDerivAt.congr_deriv this (by simp)

lemma wJ_add_smul (Hi : Matrix (Fin d) (Fin d) ℝ) (H1 W : H1arr d) (t : ℝ) (ρ : Fin d) :
    wJ Hi (H1 + t • W) ρ = wJ Hi H1 ρ + t * wJ Hi W ρ := by
  unfold wJ
  have p1 : ∑ σ, ∑ ν, Hi σ ν * gamJ Hi (H1 + t • W) ρ σ ν =
      ∑ σ, ∑ ν, Hi σ ν * gamJ Hi H1 ρ σ ν + t * ∑ σ, ∑ ν, Hi σ ν * gamJ Hi W ρ σ ν := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [gamJ_add_smul]; ring
  have p2 : ∑ σ, Hi ρ σ * ∑ l, gamJ Hi (H1 + t • W) l σ l =
      ∑ σ, Hi ρ σ * ∑ l, gamJ Hi H1 l σ l + t * ∑ σ, Hi ρ σ * ∑ l, gamJ Hi W l σ l := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [gamJ_add_smul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [p1, p2]; ring

lemma fderiv_eq_of_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → ℝ) (z V : E)
    (hd : DifferentiableAt ℝ Φ z) {c : ℝ} (h : HasDerivAt (fun t : ℝ => Φ (z + t • V)) c 0) :
    fderiv ℝ Φ z V = c := by
  have hline : HasDerivAt (fun s : ℝ => z + s • V) V 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add z
    exact HasDerivAt.congr_deriv this (by simp)
  have h2 : HasFDerivAt Φ (fderiv ℝ Φ z) (z + (0 : ℝ) • V) := by simpa using hd.hasFDerivAt
  exact (h2.comp_hasDerivAt (0 : ℝ) hline).unique h

lemma Arr_add_zero (t : ℝ) (w : Arr d) :
    w + t • (((fun _ _ => 0, fun _ _ => 0)) : Arr d) = w := by
  ext1 <;> funext a b <;> simp

/-- The direction that changes only the 1-jet. -/
def dirW (W : H1arr d) : Arr d × H1arr d := (((fun _ _ => 0, fun _ _ => 0) : Arr d), W)

lemma fderiv_Psi_H1 (c : ℝ) {z : Arr d × H1arr d} (hdet : 0 < (Matrix.of z.1.1).det) (W : H1arr d) :
    fderiv ℝ (Psi c) z (dirW W) =
      -(Real.sqrt (Matrix.of z.1.1).det * Lbil (Matrix.of z.1.1)⁻¹ z.2 W) := by
  refine fderiv_eq_of_line _ _ _ ((contDiffAt_Psi c hdet).differentiableAt (by simp)) ?_
  have e : (fun t : ℝ => Psi c (z + t • dirW W)) = fun t =>
      Kfun c z.1 - Real.sqrt (Matrix.of z.1.1).det * LgJ (Matrix.of z.1.1)⁻¹ (z.2 + t • W) := by
    funext t
    have h1 : (z + t • dirW W).1 = z.1 := by
      show z.1 + t • (((fun _ _ => 0, fun _ _ => 0)) : Arr d) = z.1
      exact Arr_add_zero t z.1
    have h2 : (z + t • dirW W).2 = z.2 + t • W := rfl
    simp only [Psi, h1, h2]
  rw [e]
  have := (hasDerivAt_LgJ_H1 (Matrix.of z.1.1)⁻¹ z.2 W).const_mul (Real.sqrt (Matrix.of z.1.1).det)
  have h2 := (hasDerivAt_const (0 : ℝ) (Kfun c z.1)).sub this
  exact HasDerivAt.congr_deriv h2 (by ring)

lemma fderiv_Theta_H1 (ρ : Fin d) {z : Arr d × H1arr d} (hdet : 0 < (Matrix.of z.1.1).det) (W : H1arr d) :
    fderiv ℝ (Theta ρ) z (dirW W) = Real.sqrt (Matrix.of z.1.1).det * wJ (Matrix.of z.1.1)⁻¹ W ρ := by
  refine fderiv_eq_of_line _ _ _ ((contDiffAt_Theta ρ hdet).differentiableAt (by simp)) ?_
  have e : (fun t : ℝ => Theta ρ (z + t • dirW W)) = fun t =>
      Real.sqrt (Matrix.of z.1.1).det * (wJ (Matrix.of z.1.1)⁻¹ z.2 ρ + t * wJ (Matrix.of z.1.1)⁻¹ W ρ) := by
    funext t
    have h1 : (z + t • dirW W).1 = z.1 := by
      show z.1 + t • (((fun _ _ => 0, fun _ _ => 0)) : Arr d) = z.1
      exact Arr_add_zero t z.1
    have h2 : (z + t • dirW W).2 = z.2 + t • W := rfl
    simp only [Theta, h1, h2, wJ_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => wJ (Matrix.of z.1.1)⁻¹ z.2 ρ + t * wJ (Matrix.of z.1.1)⁻¹ W ρ)
      (wJ (Matrix.of z.1.1)⁻¹ W ρ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (wJ (Matrix.of z.1.1)⁻¹ W ρ)).const_add
      (wJ (Matrix.of z.1.1)⁻¹ z.2 ρ)
  exact h1.const_mul _

/-- The derivative of `w^ρ` along a change of the inverse metric `D` (product rule). -/
def wDer (Hi D : Matrix (Fin d) (Fin d) ℝ) (H1 : H1arr d) (ρ : Fin d) : ℝ :=
  (∑ σ, ∑ ν, (D σ ν * gamJ Hi H1 ρ σ ν + Hi σ ν * gamJ D H1 ρ σ ν)) -
    ∑ σ, (D ρ σ * ∑ l, gamJ Hi H1 l σ l + Hi ρ σ * ∑ l, gamJ D H1 l σ l)

lemma hasDerivAt_gamJ_Hi {Hm : ℝ → Matrix (Fin d) (Fin d) ℝ} {D : Matrix (Fin d) (Fin d) ℝ}
    (hD : ∀ a b, HasDerivAt (fun t => Hm t a b) (D a b) 0) (H1 : H1arr d) (i j k : Fin d) :
    HasDerivAt (fun t => gamJ (Hm t) H1 i j k) (gamJ D H1 i j k) 0 := by
  unfold gamJ
  exact (HasDerivAt.fun_sum fun l _ => (hD i l).mul_const (H1 j l k + H1 k l j - H1 l j k)).const_mul _

lemma hasDerivAt_wJ_Hi {Hm : ℝ → Matrix (Fin d) (Fin d) ℝ} {D : Matrix (Fin d) (Fin d) ℝ}
    (hD : ∀ a b, HasDerivAt (fun t => Hm t a b) (D a b) 0) (H1 : H1arr d) (ρ : Fin d) :
    HasDerivAt (fun t => wJ (Hm t) H1 ρ) (wDer (Hm 0) D H1 ρ) 0 := by
  unfold wJ wDer
  refine HasDerivAt.sub ?_ ?_
  · refine HasDerivAt.fun_sum fun σ _ => HasDerivAt.fun_sum fun ν _ => ?_
    exact (hD σ ν).mul (hasDerivAt_gamJ_Hi hD H1 ρ σ ν)
  · refine HasDerivAt.fun_sum fun σ _ => ?_
    exact (hD ρ σ).mul (HasDerivAt.fun_sum fun l _ => hasDerivAt_gamJ_Hi hD H1 l σ l)

lemma hasDerivAt_inv_path (H P : Matrix (Fin d) (Fin d) ℝ) (hdet : H.det ≠ 0) (a b : Fin d) :
    HasDerivAt (fun t : ℝ => (H + t • P)⁻¹ a b) (-(H⁻¹ * P * H⁻¹) a b) 0 := by
  have hM : ∀ i j, Differentiable ℝ (fun t : ℝ => (H + t • P) i j) := fun i j => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; fun_prop
  have h0 : ((fun t : ℝ => H + t • P) 0).det ≠ 0 := by simpa using hdet
  have hd := Gauge.differentiableAt_inv_entry (fun t : ℝ => H + t • P) (fun i j => (hM i j) 0) h0 a b
  have := Gauge.fderiv_inv_entry_at (fun t : ℝ => H + t • P) hM (0 : ℝ) (1 : ℝ) h0 a b
  have h2 := hd.hasDerivAt
  have hMd : ∀ c b, fderiv ℝ (fun y : ℝ => (H + y • P) c b) 0 1 = P c b := by
    intro c b
    rw [fderiv_apply_one_eq_deriv]
    have : HasDerivAt (fun y : ℝ => (H + y • P) c b) (P c b) 0 := by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (P c b)).const_add (H c b)
    exact this.deriv
  have e : deriv (fun t : ℝ => (H + t • P)⁻¹ a b) 0 = -(H⁻¹ * P * H⁻¹) a b := by
    rw [← fderiv_apply_one_eq_deriv, this]
    simp only [hMd, zero_smul, add_zero]
    simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [e] at h2
  exact h2

/-- The direction that changes only the metric, by the matrix `P`. -/
def dirA (P : Matrix (Fin d) (Fin d) ℝ) : Arr d × H1arr d :=
  (((fun a b => P a b, fun _ _ => 0) : Arr d), fun _ _ _ => 0)

lemma fderiv_Theta_metric (ρ : Fin d) {z : Arr d × H1arr d} (hdet : 0 < (Matrix.of z.1.1).det)
    (P : Matrix (Fin d) (Fin d) ℝ) :
    fderiv ℝ (Theta ρ) z (dirA P) =
      (Matrix.of z.1.1).det * ((Matrix.of z.1.1)⁻¹ * P).trace / (2 * Real.sqrt (Matrix.of z.1.1).det) *
          wJ (Matrix.of z.1.1)⁻¹ z.2 ρ +
        Real.sqrt (Matrix.of z.1.1).det * wDer (Matrix.of z.1.1)⁻¹ (-((Matrix.of z.1.1)⁻¹ * P *
          (Matrix.of z.1.1)⁻¹)) z.2 ρ := by
  set H : Matrix (Fin d) (Fin d) ℝ := Matrix.of z.1.1 with hH
  refine fderiv_eq_of_line _ _ _ ((contDiffAt_Theta ρ hdet).differentiableAt (by simp)) ?_
  have e1 : ∀ t : ℝ, Matrix.of (z + t • dirA P).1.1 = H + t • P := by
    intro t; ext a b; simp [dirA, hH]
  have e2 : ∀ t : ℝ, (z + t • dirA P).2 = z.2 := by
    intro t; funext a b c; simp [dirA]
  have e : (fun t : ℝ => Theta ρ (z + t • dirA P)) = fun t =>
      Real.sqrt (H + t • P).det * wJ (H + t • P)⁻¹ z.2 ρ := by
    funext t; simp only [Theta, e1, e2]
  rw [e]
  have hs := hasDerivAt_sqrt_det H P hdet
  have hw := hasDerivAt_wJ_Hi (Hm := fun t : ℝ => (H + t • P)⁻¹) (D := -(H⁻¹ * P * H⁻¹))
    (fun a b => by simpa using hasDerivAt_inv_path H P hdet.ne' a b) z.2 ρ
  have := hs.mul hw
  refine HasDerivAt.congr_deriv this ?_
  simp [hH]

end Lightlike.Canonical

end
