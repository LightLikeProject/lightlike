import Lightlike.Asymptotics.EPRL.Critical
import Lightlike.Asymptotics.EPRL.DihedralNormals

/-!
# The critical values of the Regge state

At the critical point `U⁺_a = Q_4† Q_a` every propagator of the Regge state is
`e^{+ i Θ_e / 2}`, so that the integrand `Π_e P_e^{n_e}` has the value `e^{+ i S}` with
`S = Σ_e (n_e/2) Θ_e` the Regge action (`prop_critPlus`, `cohAmp_critPlus`).
-/

open Matrix Complex Finset

namespace Lightlike.Asymptotics.EPRL

variable (σ : Simplex4)

/-- The matrix `Q_a = quatMat N_a` is unitary: `Q Q† = 1`. -/
lemma quatMat_mul_conjTranspose (a : Fin 5) :
    quatMat (outNormal σ a) * (quatMat (outNormal σ a))ᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff.mp (normalSU2 σ a).2.1)

/-- The matrix `m_e` of the lift of the unit bivector is unitary: `m† m = 1`. -/
lemma liftSU2_conjTranspose_mul (e : Fin 10) :
    (liftSU2 (unitBivector σ e))ᴴ * liftSU2 (unitBivector σ e) = 1 := by
  have h := Lightlike.Spin4.toMat_mem_SU2 ⟨_, Lightlike.Spin4.mem_unitary_of_normSq
    (normSq_liftQuat_bivector σ e)⟩
  rw [toMat_liftQuat] at h
  exact Matrix.mem_unitaryGroup_iff'.mp h.1

/-- Cancellation helper for the chain of unitary factors. -/
lemma chain_cancel {A B C m D ε : Matrix (Fin 2) (Fin 2) ℂ} (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1)
    (hC : C * Cᴴ = 1) (hm : mᴴ * m = 1) :
    ((Aᴴ * m * D * ε)ᴴ * (Cᴴ * A)ᴴ * (Cᴴ * B) * (Bᴴ * m * ε)) = εᴴ * Dᴴ * ε := by
  have h1 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, A * (Aᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, B * (Bᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  have h3 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, C * (Cᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hC, Matrix.one_mul]
  have h4 : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, mᴴ * (m * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hm, Matrix.one_mul]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h1, h3, h2, h4]

/-- **The propagator at `X = critPlus`** is the phase `e^{+ i Θ_e / 2}`. -/
theorem prop_critPlus (e : Fin 10) :
    prop (reggeState σ) (critPlus σ) e = cexp (I * (reggeAngle σ e : ℂ) / 2) := by
  have h := chain_cancel (ε := epsMat) (D := phaseMat (reggeAngle σ e))
    (quatMat_mul_conjTranspose σ (edgeSrc e)) (quatMat_mul_conjTranspose σ (edgeTgt e))
    (quatMat_mul_conjTranspose σ 4) (liftSU2_conjTranspose_mul σ e)
  unfold prop
  simp only [reggeState, critPlus, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h]
  simp [phaseMat, epsMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.of_apply]
  rw [← Complex.exp_conj]
  have h2 : (starRingEnd ℂ) 2 = 2 := by simpa using Complex.conj_ofReal 2
  simp [map_div₀, Complex.conj_ofReal, h2, neg_div]

/-- **The edge rotation as matrices**: `Q_a Q_b† = m_e d(2 Θ_e) m_e†`. -/
lemma quatMat_mul_conjTranspose_eq (e : Fin 10) :
    quatMat (outNormal σ (edgeSrc e)) * (quatMat (outNormal σ (edgeTgt e)))ᴴ =
      liftSU2 (unitBivector σ e) * phaseMat (2 * reggeAngle σ e) *
        (liftSU2 (unitBivector σ e))ᴴ := by
  have h := congrArg Lightlike.Spin4.toMat (normal_mul_star_normal σ e)
  simpa only [map_mul, Lightlike.Spin4.toMat_star, toMat_normalQuat, toMat_liftQuat,
    toMat_phaseQuat] using h

/-- Conjugating by a unitary: `m† (m D m†) (m X) = D X` when `m† m = 1`. -/
lemma conj_cancel {m D X : Matrix (Fin 2) (Fin 2) ℂ} (hm : mᴴ * m = 1) :
    mᴴ * ((m * D * mᴴ) * (m * X)) = D * X := by
  have : mᴴ * ((m * D * mᴴ) * (m * X)) = (mᴴ * m) * D * ((mᴴ * m) * X) := by
    simp only [Matrix.mul_assoc]
  rw [this, hm]; simp

/-- **The propagator at `X = critMinus`** is the phase `e^{- i Θ_e / 2}`. -/
theorem prop_critMinus (e : Fin 10) :
    prop (reggeState σ) critMinus e = cexp (-(I * (reggeAngle σ e : ℂ) / 2)) := by
  have hm := liftSU2_conjTranspose_mul σ e
  have h : prop (reggeState σ) critMinus e =
      (epsMatᴴ * ((phaseMat (reggeAngle σ e))ᴴ * (phaseMat (2 * reggeAngle σ e) * epsMat))) 0 0 := by
    unfold prop
    simp only [reggeState, critMinus, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.conjTranspose_one, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    rw [← conj_cancel (X := epsMat) (D := phaseMat (2 * reggeAngle σ e)) hm,
      ← quatMat_mul_conjTranspose_eq]
    simp only [Matrix.mul_assoc]
  rw [h]
  simp [phaseMat, epsMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Matrix.of_apply]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have h2 : (starRingEnd ℂ) 2 = 2 := by simpa using Complex.conj_ofReal 2
  congr 1
  simp [map_div₀, Complex.conj_ofReal, h2, neg_div]
  ring

/-- **The critical value at `critMinus`**: `F_n = e^{- i S}`. -/
theorem cohAmp_critMinus (n : Fin 10 → ℕ) :
    cohAmp n (reggeState σ) critMinus = cexp (-(I * (reggeAction σ n : ℂ))) := by
  unfold cohAmp reggeAction
  simp only [prop_critMinus, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun e _ => by ring

/-- **The critical value at `critPlus`**: `F_n = e^{+ i S}` with `S = Σ_e (n_e/2) Θ_e` the Regge
action. -/
theorem cohAmp_critPlus (n : Fin 10 → ℕ) :
    cohAmp n (reggeState σ) (critPlus σ) = cexp (I * (reggeAction σ n : ℂ)) := by
  unfold cohAmp reggeAction
  simp only [prop_critPlus, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => by ring

end Lightlike.Asymptotics.EPRL
