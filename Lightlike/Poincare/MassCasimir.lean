module

public import Lightlike.Poincare.InducedMassive

/-!
# The mass Casimir on the induced massive representations

The translations of the induced representation act on a wave function at `P` by the phase `e^{i⟨P, X⟩}`, so the
momentum of the state at `P` is `P` itself, and its Minkowski square is `⟨P, P⟩ = det P` (`mink_self`). On the mass
shell this is `m²` (`mink_self_massShell`): the quadratic Casimir `P² = m²`. For the spin representation
`Lightlike.SU2.spinRep 1` of spin `1/2` the wave functions take values in `ℂ²`: two states per momentum
(`card_spinHalf_fibre`), the check of T-HA6.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2, first remark (page 11 of v2): the Hilbert space of the irreducible representation is
  an eigenspace of the quadratic Casimir with eigenvalue `± m²` (their signature `(−,+,+,+)`).
-/

@[expose] public section

noncomputable section

open Matrix Lightlike.Lorentz

namespace Lightlike.Poincare

/-- The Minkowski square of a Hermitian momentum is its determinant. -/
lemma mink_self (P : Matrix (Fin 2) (Fin 2) ℂ) : mink P P = P.det := by
  have h : P + P = (2 : ℂ) • P := by rw [two_smul]
  rw [mink, h, Matrix.det_smul]
  simp only [Fintype.card_fin]
  ring

/-- **`P² = m²` on the mass shell.** -/
theorem mink_self_massShell {m : ℝ} (P : MassShell m) : mink P.1 P.1 = ((m ^ 2 : ℝ) : ℂ) := by
  rw [mink_self, P.2.2]

/-- **Two states per momentum for spin `1/2`**: the fibre of the induced representation of `spinRep 1`. -/
theorem card_spinHalf_fibre : Fintype.card (Fin (1 + 1)) = 2 := rfl

/-- The induced spin-`1/2` action is defined (non-vacuity). -/
example {m : ℝ} (hm : 0 < m) (A : SL2C) (ψ : MassShell m → Fin (1 + 1) → ℂ) :
    inducedAct hm (Lightlike.SU2.spinRep 1) (A * A⁻¹) ψ = ψ := by
  rw [mul_inv_cancel, inducedAct_one]

end Lightlike.Poincare
