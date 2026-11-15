import Lightlike.Asymptotics.EPRL.HaarGraph
import Lightlike.Asymptotics.EPRL.HessianChart
import Lightlike.Asymptotics.EPRL.HaarChart
import Lightlike.Asymptotics.EPRL.Localise4

/-!
# The gnomonic chart of SU(2) as a matrix

The Haar-measure chart `gammaSU` of `HaarGraph` (a quaternion `(1, q) / √(1 + |q|²)`) has the
matrix `gmat q = (1 + |q|²)^(-1/2) (1 + N(q))` used for the Hessian comparison
(`HessianChart`).
-/

open Matrix

namespace Lightlike.Asymptotics.EPRL

/-- The matrix of `gammaSU q` is the gnomonic matrix `gmat q`. -/
theorem coe_gammaSU (q : Fin 3 → ℝ) :
    ((gammaSU q : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = gmat q := by
  have hg : grad q = (1 + ∑ k, q k ^ 2) ^ (-(1/2 : ℝ)) := by
    unfold grad gsq
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul (by positivity)]
    simp [Fin.sum_univ_three, add_assoc]
  unfold gammaSU sphereToSU2 gmat
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Lightlike.Spin4.toMat_apply, Lightlike.Spin4.quatMat, gamma, gammaH, Nmat, hg]

/-- The gauge-fixed point `(p_a γ(q_a))_a, 1` is the gnomonic chart `qchart` around `(p, 1)`. -/
theorem snoc_gamma_eq_qchart (p : Fin 4 → SU2) (q : Fin 12 → ℝ) :
    (fun a : Fin 5 => ((Fin.snoc (fun a : Fin 4 => p a * gammaSU (reshape.symm q a)) (1 : SU2) :
        Fin 5 → SU2) a : Matrix (Fin 2) (Fin 2) ℂ)) =
      qchart (fun a : Fin 5 => ((Fin.snoc p (1 : SU2) : Fin 5 → SU2) a : Matrix (Fin 2) (Fin 2) ℂ))
        q := by
  funext a
  refine Fin.lastCases ?_ (fun b => ?_) a
  · simp only [Fin.snoc_last, qchart]
    simp
  · have hb : ((Fin.castSucc b : Fin 5) : ℕ) < 4 := by simp
    have hbb : (⟨(Fin.castSucc b : ℕ), hb⟩ : Fin 4) = b := by ext; simp
    have hblk : blk q b = reshape.symm q b := rfl
    simp only [qchart, hb, dite_true, hbb, hblk, Fin.snoc_castSucc, Submonoid.coe_mul, coe_gammaSU]

end Lightlike.Asymptotics.EPRL
