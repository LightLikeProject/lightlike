import Lightlike.OperatorAlgebras.SecondQuantFinite
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Tests for `dΓ` on finitely many modes

One fermionic mode on `Λ(ℂ) = Λ⁰(ℂ) ⊕ Λ¹(ℂ) = ℂ Ω ⊕ ℂ e`, in the basis `Ω`, `e`: `a = |Ω⟩⟨e|`, `a* = |e⟩⟨Ω|`.

* `isModeAlgebra_oneMode`: the CAR hold, so this is a mode algebra with `ε = -1`;
* `dGamma_oneMode`: `dΓ(h) = 0 ⊕ h`, which is `dΓ₀(h) ⊕ dΓ₁(h)` for `dΓₙ(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1` (Dereziński,
  Section 5.2, p. 19), and `dΓ(1)` is the number operator;
* `not_isModeAlgebra_oneMode_boson`: the same operators do not satisfy the CCR (wrong input).
-/

namespace Lightlike.OperatorAlgebras.SecondQuantFinite

/-- The annihilator `a = |Ω⟩⟨e|` of one fermionic mode. -/
def annOne : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The creator `a* = |e⟩⟨Ω|` of one fermionic mode. -/
def creOne : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- **One fermionic mode is a mode algebra with `ε = -1`.** -/
theorem isModeAlgebra_oneMode :
    IsModeAlgebra (R := Matrix (Fin 2) (Fin 2) ℂ) (ι := Unit) (-1) (fun _ => annOne) (fun _ => creOne) :=
  isModeAlgebra_car
    (fun _ _ => by
      ext i j; fin_cases i <;> fin_cases j <;> simp [annOne, creOne, Matrix.mul_apply, Fin.sum_univ_two])
    (fun _ _ => by
      ext i j; fin_cases i <;> fin_cases j <;> simp [annOne, Matrix.mul_apply, Fin.sum_univ_two])
    (fun _ _ => by
      ext i j; fin_cases i <;> fin_cases j <;> simp [creOne, Matrix.mul_apply, Fin.sum_univ_two])

/-- **`dΓ(h) = 0 ⊕ h` on `Λ⁰(ℂ) ⊕ Λ¹(ℂ)`.** -/
theorem dGamma_oneMode (h : Matrix Unit Unit ℂ) :
    dGamma (fun _ => annOne) (fun _ => creOne) h = !![0, 0; 0, h () ()] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dGamma, annOne, creOne, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Wrong input**: one fermionic mode does not satisfy `a a* = 1 + a* a`, so it is not a mode algebra with
`ε = 1`. -/
theorem not_isModeAlgebra_oneMode_boson :
    ¬ IsModeAlgebra (R := Matrix (Fin 2) (Fin 2) ℂ) (ι := Unit) 1 (fun _ => annOne) (fun _ => creOne) := by
  intro hm
  have h := congrFun (congrFun (hm.ann_cre () ()) 1) 1
  simp [annOne, creOne, Matrix.mul_apply, Fin.sum_univ_two] at h
  norm_num at h

end Lightlike.OperatorAlgebras.SecondQuantFinite
