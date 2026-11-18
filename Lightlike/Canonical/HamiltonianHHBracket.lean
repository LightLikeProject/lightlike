import Mathlib
import Lightlike.Canonical.HamiltonianWEq
import Lightlike.Canonical.MomentumADM

/-!
# The bracket of two Hamiltonian constraints

`{H[N], H[M]} = D[Y]` with `Y^i = h^{ij}(N ∂_j M − M ∂_j N)`: the differentiation of `H[N]` along `M · P` in first-order
form (`dirDeriv_hamiltonianConstraint_first`), the antisymmetrization (`B_algebra`), the coefficient
`W^b = −2 ∇_σ π^{bσ}` (`W_eq`), and the ADM form of the momentum constraint (`momentumConstraint_eq_adm_of_smooth`).
-/

open Matrix MeasureTheory

open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- Entries of a product of matrix fields with smooth entries are smooth. -/
lemma contDiff_matmul {F G : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (hF : ∀ i j, ContDiff ℝ ∞ (fun y => F y i j)) (hG : ∀ i j, ContDiff ℝ ∞ (fun y => G y i j)) (i j : Fin d) :
    ContDiff ℝ ∞ (fun y => (F y * G y) i j) := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hF i k).mul (hG k j)

/-- The unit `π`-gradient of the Hamiltonian constraint is smooth. -/
lemma smooth_Pm {h π : TensorField d} (hh : SmoothTensor h) (hπ : SmoothTensor π)
    (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y) (hpos : ∀ y, 0 < (h y).det) :
    SmoothTensor (hamiltonianPiGradient (fun _ => (1 : ℝ)) h π) := by
  intro i j
  have e : (fun y => hamiltonianPiGradient (fun _ => (1 : ℝ)) h π y i j) = fun y =>
      (Real.sqrt (h y).det)⁻¹ * (2 * (h y * π y * h y) i j -
        (2 / ((d : ℝ) - 1)) * (h y * π y).trace * h y i j) := by
    funext y
    have := Pm_eq_Xfield h π hs hps y
    show Pm h π y i j = _
    rw [this]
    simp [Xfield, Matrix.sub_apply]
  rw [e]
  have h1 : ∀ i j, ContDiff ℝ ∞ (fun y => (h y * π y) i j) := contDiff_matmul hh hπ
  have h2 : ∀ i j, ContDiff ℝ ∞ (fun y => (h y * π y * h y) i j) := contDiff_matmul h1 hh
  have h3 : ContDiff ℝ ∞ (fun y => (h y * π y).trace) := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact ContDiff.sum fun k _ => h1 k k
  refine ((contDiff_sqrt_det hh hpos).inv fun y => (Real.sqrt_pos.mpr (hpos y)).ne').mul ?_
  exact (contDiff_const.mul (h2 i j)).sub ((contDiff_const.mul h3).mul (hh i j))

/-- The mixed coefficient `Θ_b^{ρ b}` is symmetric. -/
lemma Thetab_symm {h π : TensorField d} (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y) {x : Fin d → ℝ}
    (hpos : 0 < (h x).det) (ρ b : Fin d) :
    fderiv ℝ (Theta ρ) (Zthree h π x) (Vb h π x b) = fderiv ℝ (Theta b) (Zthree h π x) (Vb h π x ρ) := by
  have hdetz : 0 < (Matrix.of (Zthree h π x).1.1).det := hpos
  have e1 : ∀ c, Vb h π x c = dirW (fun a i j => if a = c then Pm h π x i j else 0) := fun c => rfl
  rw [e1, e1, fderiv_Theta_H1 ρ hdetz, fderiv_Theta_H1 b hdetz]
  have hz1 : Matrix.of (Zthree h π x).1.1 = h x := rfl
  have hz2 : (Zthree h π x).2 = jet1 h x := rfl
  rw [hz1]
  have hdetU : IsUnit (h x).det := hpos.ne'.isUnit
  have hHs : ((h x)⁻¹)ᵀ = (h x)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hs x]
  have hHsym : ∀ i j, (h x)⁻¹ i j = (h x)⁻¹ j i := fun i j => by
    have := congrFun (congrFun hHs j) i
    simpa [Matrix.transpose_apply] using this
  have hPs : ∀ i j, Pm h π x i j = Pm h π x j i := Pm_symm h π hs hps x
  rw [wJ_delta hHsym hPs b ρ, wJ_delta hHsym hPs ρ b]
  congr 2
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun ν _ => by rw [hPs ν l]; ring
  · rw [hHsym ρ b]

/-- `δH[M]/δπ = M · P` entrywise. -/
lemma hpg_apply (M : (Fin d → ℝ) → ℝ) (h π : TensorField d) (y : Fin d → ℝ) (i j : Fin d) :
    hamiltonianPiGradient M h π y i j = M y * hamiltonianPiGradient (fun _ => (1 : ℝ)) h π y i j := by
  rw [hamiltonianPiGradient_smul]; simp

/-- **The variation of `H[N]` along `δH[M]/δπ`.** -/
lemma dirDeriv_H_along {N M : (Fin d → ℝ) → ℝ} (hN : ContDiff ℝ ∞ N) (hNc : HasCompactSupport N)
    (hM : ContDiff ℝ ∞ M) (hMc : HasCompactSupport M) {h π : TensorField d} (hh : SmoothTensor h)
    (hπ : SmoothTensor π) (hs : ∀ y, (h y)ᵀ = h y) (hps : ∀ y, (π y)ᵀ = π y)
    (hpos : ∀ y, (h y).PosDef) :
    Integrable (fun x => fderiv ℝ (Phi1 (1 / ((d : ℝ) - 1))) (Z1 N h π x)
        (V1 (hamiltonianPiGradient M h π) x)) volume ∧
      dirDeriv (hamiltonianConstraint N) h π (hamiltonianPiGradient M h π) 0 =
        ∫ x, fderiv ℝ (Phi1 (1 / ((d : ℝ) - 1))) (Z1 N h π x) (V1 (hamiltonianPiGradient M h π) x) := by
  have hdp : ∀ y, 0 < (h y).det := fun y => (hpos y).det_pos
  have hP := smooth_Pm hh hπ hs hps hdp
  refine dirDeriv_hamiltonianConstraint_first hN hNc hh hπ (fun y a b => ?_) hpos
    (fun i j => ?_) (fun i j => ?_) (fun y a b => ?_)
  · have := congrFun (congrFun (hs y) b) a
    simpa [Matrix.transpose_apply] using this
  · have e : (fun y => hamiltonianPiGradient M h π y i j) = fun y =>
        M y * hamiltonianPiGradient (fun _ => (1 : ℝ)) h π y i j := funext fun y => hpg_apply M h π y i j
    rw [e]; exact hM.mul (hP i j)
  · have e : (fun y => hamiltonianPiGradient M h π y i j) = fun y =>
        M y * hamiltonianPiGradient (fun _ => (1 : ℝ)) h π y i j := funext fun y => hpg_apply M h π y i j
    rw [e]
    exact hMc.mul_right
  · rw [hpg_apply M h π y a b, hpg_apply M h π y b a]
    have := Pm_symm h π hs hps y a b
    exact congrArg (M y * ·) this

/-- **`{H[N], H[M]} = D[Y]`** with `Y^i = h^{ij}(N ∂_j M − M ∂_j N)`, for smooth data. -/
theorem bracket_hamiltonian_hamiltonian_of_smooth (hd : 2 ≤ d) {N M : (Fin d → ℝ) → ℝ}
    (hN : ContDiff ℝ ∞ N) (hNc : HasCompactSupport N) (hM : ContDiff ℝ ∞ M) (hMc : HasCompactSupport M)
    {h π : TensorField d} (hh : SmoothTensor h) (hpos : ∀ x, (h x).PosDef) (hπ : SmoothTensor π)
    (hπs : ∀ x, (π x)ᵀ = π x) :
    admBracket (hamiltonianConstraint N) (hamiltonianConstraint M) (hamiltonianPiGradient N)
        (hamiltonianPiGradient M) h π =
      momentumConstraint
        (fun x i => ∑ j, (h x)⁻¹ i j * (N x * Lightlike.pd j M x - M x * Lightlike.pd j N x)) h π := by
  have hdp : ∀ y, 0 < (h y).det := fun y => (hpos y).det_pos
  have hsymh : ∀ y a b, h y a b = h y b a := fun y a b => by
    have := (hpos y).1.apply a b
    simpa using this.symm
  have hs : ∀ y, (h y)ᵀ = h y := fun y => Matrix.ext fun a b => (hsymh y b a)
  obtain ⟨hIN, hdN⟩ := dirDeriv_H_along hN hNc hM hMc hh hπ hs hπs hpos
  obtain ⟨hIM, hdM⟩ := dirDeriv_H_along hM hMc hN hNc hh hπ hs hπs hpos
  have hP := smooth_Pm hh hπ hs hπs hdp
  -- the shift
  set Z : (Fin d → ℝ) → Fin d → ℝ := fun x j => N x * Lightlike.pd j M x - M x * Lightlike.pd j N x with hZ
  set Y : VectorField d := fun x i => ∑ j, (h x)⁻¹ i j * Z x j with hY
  have hZs : ∀ j, ContDiff ℝ ∞ (fun y => Z y j) := fun j =>
    (hN.mul (smooth_pd hM j)).sub (hM.mul (smooth_pd hN j))
  have hZc : ∀ j, HasCompactSupport (fun y => Z y j) := fun j => by
    refine HasCompactSupport.sub ?_ ?_
    · exact hNc.mul_right
    · exact hMc.mul_right
  have hYs : SmoothVec Y := fun i =>
    ContDiff.sum fun j _ => (contDiff_inv_comp hh (fun y => (hdp y).ne') i j).mul (hZs j)
  have hYc : ∀ i, HasCompactSupport (fun y => Y y i) := fun i =>
    hcs_sum _ _ fun j _ => (hZc j).mul_left
  unfold admBracket
  rw [hdN, hdM, ← integral_sub hIN hIM]
  rw [show (momentumConstraint Y h π) = _ from momentumConstraint_eq_adm_of_smooth hYs hYc hh hpos hπ hπs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx := hdp x
  have hsplit1 := first_deriv_split (N := N) hM hP hx
  have hsplit2 := first_deriv_split (N := M) hN hP hx
  have hB := B_algebra (N x) (M x) (fun ρ => Lightlike.pd ρ N x) (fun ρ => Lightlike.pd ρ M x)
    (fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Va h π x))
    (fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Vd h π x))
    (fun b => fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Vb h π x b))
    (fun b => fderiv ℝ (Theta b) (Zthree h π x) (Va h π x))
    (fun b => fderiv ℝ (Theta b) (Zthree h π x) (Vd h π x))
    (fun ρ b => fderiv ℝ (Theta ρ) (Zthree h π x) (Vb h π x b))
    (fun ρ b => Thetab_symm hs hπs hx ρ b)
  have hW : ∀ b, fderiv ℝ (Psi (1 / ((d : ℝ) - 1))) (Zthree h π x) (Vb h π x b) -
      fderiv ℝ (Theta b) (Zthree h π x) (Va h π x) - fderiv ℝ (Theta b) (Zthree h π x) (Vd h π x) =
      -2 * momentumDivergence h π b x := fun b => W_eq hd hh hπ hs hπs hx b
  have hlow : ∀ i, ∑ k, h x i k * Y x k = Z x i := by
    intro i
    have hdetU : IsUnit (h x).det := (hdp x).ne'.isUnit
    have hhH : h x * (h x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetU
    simp only [hY, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ k, h x i k * ((h x)⁻¹ k j * Z x j) = (if i = j then 1 else 0) * Z x j := fun j => by
      have := congrFun (congrFun hhH i) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [← this, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    simp
  simp only [hlow]
  rw [hsplit1, hsplit2, hB]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hW b]
  simp only [hZ]
  ring

end Lightlike.Canonical

end
