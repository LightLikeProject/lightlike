import Lightlike.Gauge.DiracStage
import Lightlike.Gauge.DiracRegular

/-!
# The Dirac stage as the next regular tuple

Wiring of `DiracStage` to `DiracRegular`: on a set `U` where the block `B` of the bracket matrix is invertible and its
rank is constant (Schur complement zero), the points of the stage set `zeroSet Φ` where a multiplier exists are exactly
the zero set of the stage extended by the secondary constraints `χ`, `appendStage Φ χ`. Together with
`exists_stable_of_regular` this gives termination of the stage chain, locally, under the added hypothesis that the
extended tuples are regular, with the secondary constraints given explicitly (smooth where `B`, `D`, `h` are, by
`differentiableAt_chi`) rather than assumed to exist.

Local statement: on `U` only; a global choice can fail. The statement was not compared with Henneaux and Teitelboim 1992,
Chapter One, "Constrained Hamiltonian Systems".
-/

namespace Lightlike.Gauge

open Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : Type*} [Fintype m]
  [DecidableEq m] {b : ℕ}

/-- **The stage as the next tuple**: on `U`, `stageSet` of the zero set of `Φ` is the zero set of `Φ` extended by the
secondary constraints `χ`. -/
theorem stageSet_inter_eq {a : ℕ} (Cm : E → Matrix (m ⊕ Fin b) (m ⊕ Fin b) ℝ) (h : E → (m ⊕ Fin b) → ℝ)
    (Φ : Fin a → E → ℝ) (U : Set E)
    (hU : ∀ x ∈ U, IsUnit (Cm x).toBlocks₁₁.det ∧
      (Cm x).toBlocks₂₂ = (Cm x).toBlocks₂₁ * (Cm x).toBlocks₁₁⁻¹ * (Cm x).toBlocks₁₂) :
    stageSet Cm h (zeroSet Φ) ∩ U = zeroSet (appendStage Φ fun j x => chi Cm h x j) ∩ U := by
  ext x
  simp only [Set.mem_inter_iff, stageSet, Set.mem_setOf_eq, zeroSet_appendStage]
  constructor
  · rintro ⟨⟨hx, hu⟩, hxU⟩
    refine ⟨⟨hx, fun j => ?_⟩, hxU⟩
    have := (exists_multiplier_iff_chi Cm h (hU x hxU).1 (hU x hxU).2).mp hu
    exact congrFun this j
  · rintro ⟨⟨hx, hχ⟩, hxU⟩
    refine ⟨⟨hx, ?_⟩, hxU⟩
    exact (exists_multiplier_iff_chi Cm h (hU x hxU).1 (hU x hxU).2).mpr (funext hχ)

end Lightlike.Gauge
