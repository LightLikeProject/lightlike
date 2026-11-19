import Lightlike.OperatorAlgebras.FockIrreducible

/-!
# Trust checks for the irreducibility of the Fock representation

The hypotheses of `fockRep_cyclic` are satisfied by the constructed Fock representation `fockRepOf`, and the
conclusion is nontrivial: the kernel vector `k_f` of any `f` is cyclic, and a nonzero scalar multiple of the
vacuum is too.
-/

universe u

namespace Lightlike.OperatorAlgebras

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- **Non-vacuity**: every kernel vector `k_f` of the constructed Fock representation is cyclic (`k_f ≠ 0`, since
`⟪k_f, k_f⟫ = 1`). -/
theorem kf_cyclic (f : h) :
    (Submodule.span ℂ (Set.range fun g => (fockRepOf h).W g (kf f))).topologicalClosure = ⊤ := by
  refine fockRep_cyclic (fockRepOf h) ?_
  intro h0
  have h1 := inner_kf f f
  rw [fockGram_self, h0, inner_zero_left] at h1
  exact zero_ne_one h1

end Lightlike.OperatorAlgebras
