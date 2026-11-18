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
  [DecidableEq m] {b : ℕ} {l : Type*} [Fintype l] [DecidableEq l]

/-- **The stage as the next tuple**: on `U`, `stageSet` of the zero set of `Φ` is the zero set of `Φ` extended by the
secondary constraints `χ`. -/
theorem stageSet_inter_eq {a : ℕ} (Cm : E → Matrix (m ⊕ Fin b) (m ⊕ l) ℝ) (h : E → (m ⊕ Fin b) → ℝ)
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

/-- **The chain of regular stages and the final consistency**: let the stages `Φ k` (extending one another, regular,
with nonempty zero sets) be related to the consistency conditions by `hstage` (on a set `U k` of constant rank, the
points of `zeroSet (Φ k)` with a multiplier are those of `zeroSet (Φ (k + 1))`, as `stageSet_inter_eq` gives when
`Φ (k + 1)` extends `Φ k` by the secondary constraints). Then from some stage `N` on the zero set no longer changes,
and every point of it that lies in `U N` has a multiplier: the evolution is consistent there. -/
theorem final_consistent (n : ℕ → ℕ) (Φ : ∀ k, Fin (n k) → E → ℝ) (hmono : ∀ k, n k ≤ n (k + 1))
    (hext : ∀ k i, Φ (k + 1) (Fin.castLE (hmono k) i) = Φ k i) (hreg : ∀ k, IsRegularStage (Φ k))
    (hne : ∀ k, (zeroSet (Φ k)).Nonempty) (Cm : ℕ → E → Matrix (m ⊕ Fin b) (m ⊕ l) ℝ)
    (h : ℕ → E → (m ⊕ Fin b) → ℝ) (U : ℕ → Set E)
    (hstage : ∀ k, stageSet (Cm k) (h k) (zeroSet (Φ k)) ∩ U k = zeroSet (Φ (k + 1)) ∩ U k) :
    ∃ N, (∀ k, N ≤ k → zeroSet (Φ k) = zeroSet (Φ N)) ∧
      ∀ x ∈ zeroSet (Φ N) ∩ U N, ∃ u, Cm N x *ᵥ u + h N x = 0 := by
  obtain ⟨N, hN⟩ := exists_stable_of_regular n Φ hmono hext hreg hne
  refine ⟨N, hN, fun x hx => ?_⟩
  have h1 : x ∈ zeroSet (Φ (N + 1)) ∩ U N := by rw [hN (N + 1) (by omega)]; exact hx
  rw [← hstage N] at h1
  exact h1.1.2

end Lightlike.Gauge
