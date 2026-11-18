import Lightlike.OperatorAlgebras.FockExists

/-!
# Trust checks for the existence of the Fock representation

The representation built in `FockExists.lean` is not the trivial one: for `f ≠ 0` the Weyl unitary `W f` is not
the identity, because the vacuum expectation `⟪Ω, W f Ω⟫ = exp (-‖f‖² / 4)` is then strictly less than
`1 = ⟪Ω, Ω⟫`. So the Weyl relations are represented by genuinely nontrivial unitaries, and the kernel
`fockGram` has the sign convention of the Weyl relation (otherwise `fockW` would not satisfy it, `fockW_weyl`).
-/

open scoped InnerProductSpace

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- **Non-triviality**: for `f ≠ 0`, `W f` of the constructed Fock representation is not the identity. -/
theorem fockRepOf_W_ne_one {f : h} (hf : f ≠ 0) :
    (fockRepOf h).W f ≠ LinearIsometryEquiv.refl ℂ (FockSpace h) := by
  intro heq
  have h1 : ⟪(fockRepOf h).Ω, (fockRepOf h).W f (fockRepOf h).Ω⟫_ℂ =
      Complex.exp (-(‖f‖ ^ 2 / 4 : ℝ)) := (fockRepOf h).vacuum_expectation f
  rw [heq] at h1
  simp only [LinearIsometryEquiv.coe_refl, id_eq] at h1
  have h2 : ⟪(fockRepOf h).Ω, (fockRepOf h).Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, (fockRepOf h).norm_Ω]; simp
  rw [h2, ← Complex.ofReal_neg, ← Complex.ofReal_exp] at h1
  have h3 : Real.exp (-(‖f‖ ^ 2 / 4)) = 1 := by exact_mod_cast h1.symm
  have h4 : -(‖f‖ ^ 2 / 4) = 0 := Real.exp_eq_one_iff _ |>.1 h3
  have h5 : ‖f‖ = 0 := by nlinarith [norm_nonneg f]
  exact hf (norm_eq_zero.1 h5)

end Lightlike.OperatorAlgebras
