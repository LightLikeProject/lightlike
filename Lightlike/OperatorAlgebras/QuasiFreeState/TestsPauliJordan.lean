import Lightlike.OperatorAlgebras.QuasiFreeState.PauliJordan

/-!
# Tests for the Pauli-Jordan purity theorem

The 2-chain: with a causal matrix of two points `x ≺ y` the Pauli-Jordan matrix is `D = a [[0, -1], [1, 0]]` for a
coefficient `a ≥ 0` (the normalisation depends on the dimension and is not fixed here), and `|iD| = H = a·1`. Then
`PJData D H` holds (`chainData`), so the Sorkin-Johnston state of the 2-chain is pure (`isPureState_chain`). Wrong input: a
symmetric matrix is not a Pauli-Jordan matrix (`not_pjData_symmetric`), and an odd number of points has a kernel
(a 1-point chain, `D = 0`, `H = 0`), where the state is the trivial pure state on `ℝ` with the central
Weyl unitaries equal to `1` (`isPureState_onePoint`).
-/

namespace Lightlike.OperatorAlgebras.QuasiFreeState

open Matrix

/-- The Pauli-Jordan matrix of the 2-chain, with coefficient `a`. -/
def chainD (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -a; a, 0]

/-- Its absolute value `|iD| = a·1`. -/
def chainH (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, 0; 0, a]

/-- The hypotheses of the purity theorem hold for the 2-chain. -/
theorem chainData (a : ℝ) (ha : 0 ≤ a) : PJData (chainD a) (chainH a) where
  anti := by ext i j; fin_cases i <;> fin_cases j <;> simp [chainD]
  psd := by
    have : chainH a = a • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [chainH]
    rw [this]
    exact Matrix.PosSemidef.one.smul ha
  sq := by ext i j; fin_cases i <;> fin_cases j <;> simp [chainD, chainH, Matrix.mul_apply, Fin.sum_univ_two]
  comm := by ext i j; fin_cases i <;> fin_cases j <;> simp [chainD, chainH, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The Sorkin-Johnston state of the 2-chain is pure.** -/
theorem isPureState_chain (a : ℝ) (ha : 0 ≤ a) :
    haveI : Fact (qfKerM (pjOmega (chainD a)) (pjEta (chainH a))).PosSemidef :=
      qfFact _ _ (pj_omega_antisymm (chainData a ha)) (pj_isCovariance (chainData a ha))
    IsPureState (qfState (pjOmega (chainD a)) (pjEta (chainH a)) (pj_omega_antisymm (chainData a ha))) :=
  isPureState_pauliJordan (chainData a ha)

/-- **Wrong input**: a nonzero symmetric matrix is not a Pauli-Jordan matrix. -/
theorem not_pjData_symmetric (H : Matrix (Fin 2) (Fin 2) ℝ) : ¬ PJData !![0, 1; 1, 0] H := by
  intro h
  have := congrFun (congrFun h.anti 0) 1
  simp at this
  norm_num at this

/-- **One point** (`D = 0`, `H = 0`; the kernel is everything): the data hold and the state is pure. -/
theorem onePointData : PJData (0 : Matrix (Fin 1) (Fin 1) ℝ) 0 where
  anti := by simp
  psd := Matrix.PosSemidef.zero
  sq := by simp
  comm := by simp

/-- The state of the one-point chain is pure. -/
theorem isPureState_onePoint :
    haveI : Fact (qfKerM (pjOmega (0 : Matrix (Fin 1) (Fin 1) ℝ)) (pjEta 0)).PosSemidef :=
      qfFact _ _ (pj_omega_antisymm onePointData) (pj_isCovariance onePointData)
    IsPureState (qfState (pjOmega (0 : Matrix (Fin 1) (Fin 1) ℝ)) (pjEta 0) (pj_omega_antisymm onePointData)) :=
  isPureState_pauliJordan onePointData

end Lightlike.OperatorAlgebras.QuasiFreeState
