import Mathlib
import Lightlike.Canonical.HamiltonianLink
import Lightlike.Canonical.HamiltonianHH

/-!
# The coefficient `W^b` of the bracket of two Hamiltonian constraints

`Ψ_b − Θ_a^b − Θ_d^b = −2 ∇_σ π^{bσ}`, the covariant divergence of the momentum.
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- **The coefficient of the bracket**: `Ψ_b − Θ_a^b − Θ_d^b = −2 (∇_σ π^{bσ})`. -/
theorem W_eq (hd : 2 ≤ d) {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π)
    (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y) {x : Fin d → ℝ} (hpos : 0 < (h x).det) (b : Fin d) :
    fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Vb h π x b) -
        fderiv ℝ (Theta b) (Zthree h π x) (Va h π x) - fderiv ℝ (Theta b) (Zthree h π x) (Vd h π x) =
      -2 * momentumDivergence h π b x := by
  have hdetz : 0 < (Matrix.of (Zthree h π x).1.1).det := hpos
  have e1 : Vb h π x b = dirW (fun a i j => if a = b then Pm h π x i j else 0) := rfl
  have e2 : Va h π x = dirA (Pm h π x) := rfl
  have e3 : Vd h π x = dirW (fun a i j => Lightlike.pd a (fun y => Pm h π y i j) x) := rfl
  rw [e1, e2, e3, fderiv_Psi_H1 _ hdetz, fderiv_Theta_metric b hdetz, fderiv_Theta_H1 b hdetz]
  have hz1 : Matrix.of (Zthree h π x).1.1 = h x := rfl
  have hz2 : (Zthree h π x).2 = jet1 h x := rfl
  rw [hz1, hz2, Lbil_delta, wDer_sandwich]
  set c : ℝ := 2 / ((d : ℝ) - 1) with hc
  set s : ℝ := Real.sqrt (h x).det with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
  have hdetU : IsUnit (h x).det := hpos.ne'.isUnit
  set Hi : Matrix (Fin d) (Fin d) ℝ := (h x)⁻¹ with hHi
  have hhH : h x * Hi = 1 := Matrix.mul_nonsing_inv _ hdetU
  have hHh : Hi * h x = 1 := Matrix.nonsing_inv_mul _ hdetU
  have hHs : Hiᵀ = Hi := by rw [hHi, Matrix.transpose_nonsing_inv, hs x]
  have hHsym : ∀ i j, Hi i j = Hi j i := fun i j => by
    have := congrFun (congrFun hHs j) i
    simpa [Matrix.transpose_apply] using this
  have hH1 : ∀ k i j, jet1 h x k i j = jet1 h x k j i := fun k i j => by
    unfold jet1
    have : (fun y => h y i j) = fun y => h y j i := funext fun y => by
      have := congrFun (congrFun (hs y) j) i
      simpa [Matrix.transpose_apply] using this
    rw [this]
  set G : Fin d → Fin d → Fin d → ℝ := gamJ Hi (jet1 h x) with hG
  have hGs : ∀ i j k, G i j k = G i k j := fun i j k => by
    rw [hG]; unfold gamJ
    congr 1
    exact Finset.sum_congr rfl fun l _ => by rw [hH1 j l k, hH1 k l j, hH1 l j k, hH1 l k j]; ring_nf
  have hPs : ∀ i j, Pm h π x i j = Pm h π x j i := Pm_symm h π hs hps x
  have st := stage1 Hi (Pm h π x) G hHsym hPs hGs b
  have hdPs : ∀ a i j, Lightlike.pd a (fun y => Pm h π y i j) x = Lightlike.pd a (fun y => Pm h π y j i) x :=
    fun a i j => by
      have : (fun y => Pm h π y i j) = fun y => Pm h π y j i := funext fun y => Pm_symm h π hs hps y i j
      rw [this]
  rw [wJ_eq_Tnc Hi _ hHsym hdPs b]
  have hcd : c * ((d : ℝ) - 1) = 2 := by
    have : (d : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [hc]; field_simp
  have hdiv := Tnc_Ymat Hi (h x) (Dpi h π x) c hHs hHh hhH (hs x) hcd b
  have hsum := sum_Dpi h π x (fun a b => by
      have := congrFun (congrFun (hps x) b) a
      simpa [Matrix.transpose_apply] using this) hGs b
  have hfun : (fun a i j => Lightlike.pd a (fun y => Pm h π y i j) x - corr (Pm h π x) G a i j) =
      fun a i j => s⁻¹ * Ymat (h x) (Dpi h π x) c a i j := by
    funext a i j
    have := congrFun (congrFun (dP_sub_corr hh hπ hs hps hpos a) i) j
    rw [corr_eq_mat] 
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
    exact this
  have hT := Tnc_sub Hi (fun a i j => Lightlike.pd a (fun y => Pm h π y i j) x) (corr (Pm h π x) G) b
  rw [hfun, Tnc_smul Hi (fun a i j => Ymat (h x) (Dpi h π x) c a i j) s⁻¹ b, hdiv, hsum] at hT
  have hdet : (h x).det = s * s := (Real.mul_self_sqrt hpos.le).symm
  have hw : wJ Hi (jet1 h x) b = (∑ σ, ∑ ν, Hi σ ν * G b σ ν) - ∑ σ, Hi b σ * ∑ l, G l σ l := rfl
  have hq : (h x).det * (Hi * Pm h π x).trace / (2 * s) = s * (1 / 2 * (Hi * Pm h π x).trace) := by
    rw [hdet]; field_simp
  have hinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs0.ne'
  rw [hq, hw]
  linear_combination s * st + s * hT - (2 * momentumDivergence h π b x) * hinv


end Lightlike.Canonical

end
