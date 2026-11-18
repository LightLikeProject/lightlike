import Lightlike.Gauge.DiracWire
import Lightlike.Gauge.DiracRegular

/-!
# The Dirac algorithm producing its own stages from primary data

`DiracWire.final_consistent` takes the stage tuples `Φ k` and the relation `hstage` between them and the consistency
conditions as hypotheses. Here the stages are *defined* from the primary data: primary constraints `φ : Fin M → E → ℝ`,
a Hamiltonian `H`, a bracket `br` (Physlib's Poisson bracket for the phase space `X × X`, see `Lightlike.Gauge.DiracPoisson`), and
at every stage a **selection** `Sel S` (the choice of an invertible block of the consistency matrix, local data). The
consistency system of a stage `S` (Wipf's lectures, arXiv:hep-th/9312078, Section 3.3, eq. (3.24)) is
`{S_i, H} + ∑_a {S_i, φ_a} u_a = 0` for the multipliers `u_a`, `a < M`, and all the constraints `S_i` of the stages up to this one; the next stage
appends the secondary constraints `χ = h₂ - D B⁻¹ h₁` computed from the selected block (`DiracStage.chi`).

* `Stage`, `Sel`, `Stage.consCm`, `Stage.consH`, `Stage.next`: one step.
* `stages`: the sequence of stages from a rule `sel` choosing a selection for every stage.
* `final_consistent_of_data`: with the regularity of the stages and the constant-rank hypotheses on the sets `U k`, no
  hypothesis relating the stages to the consistency conditions is needed.

Local: the selections and the sets `U k` where the chosen block is invertible and the rank constant are hypotheses.
-/

namespace Lightlike.Gauge

open Matrix

variable {E : Type*}

/-- A stage: a finite tuple of constraint functions on `E`. -/
structure Stage (E : Type*) where
  n : ℕ
  Φ : Fin n → E → ℝ

/-- A selection for a stage `S` and `M` primary constraints: row and column splittings into an invertible-block part and
the rest. -/
structure Sel (S : Stage E) (M : ℕ) where
  r : ℕ
  p : ℕ
  l : ℕ
  eR : Fin S.n ≃ Fin r ⊕ Fin p
  eC : Fin M ≃ Fin r ⊕ Fin l

variable {M : ℕ}

/-- The consistency matrix of a stage, rows in the selected splitting: `{S_i, φ_a}`. -/
noncomputable def Stage.consCm (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (S : Stage E) (σ : Sel S M)
    (x : E) : Matrix (Fin σ.r ⊕ Fin σ.p) (Fin σ.r ⊕ Fin σ.l) ℝ :=
  Matrix.of fun i j => br (S.Φ (σ.eR.symm i)) (φ (σ.eC.symm j)) x

/-- The vector `h_i = {S_i, H}` in the selected row splitting. -/
noncomputable def Stage.consH (br : (E → ℝ) → (E → ℝ) → E → ℝ) (H : E → ℝ) (S : Stage E) (σ : Sel S M)
    (x : E) : Fin σ.r ⊕ Fin σ.p → ℝ :=
  fun i => br (S.Φ (σ.eR.symm i)) H x

/-- The secondary constraints of the stage, `χ_j = h₂ - D B⁻¹ h₁`, as functions on `E`. -/
noncomputable def Stage.chiFun (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S : Stage E)
    (σ : Sel S M) : Fin σ.p → E → ℝ :=
  fun j x => chi (S.consCm br φ σ) (S.consH br H σ) x j

/-- **One step**: the stage extended by its secondary constraints. -/
noncomputable def Stage.next (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S : Stage E)
    (σ : Sel S M) : Stage E :=
  ⟨S.n + σ.p, appendStage S.Φ (S.chiFun br φ H σ)⟩

/-- **The stages from primary data**: `S₀` the primary constraints, and a rule `sel` choosing a selection at every stage. -/
noncomputable def stages (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (sel : ∀ S : Stage E, Sel S M) (S₀ : Stage E) : ℕ → Stage E
  | 0 => S₀
  | k + 1 => (stages br φ H sel S₀ k).next br φ H (sel (stages br φ H sel S₀ k))

/-- The multiplier system in the selected splitting is the multiplier system `{S_i, H} + ∑_a {S_i, φ_a} u_a = 0`. -/
theorem Stage.consistency_translate (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ) (S : Stage E)
    (σ : Sel S M) (x : E) (u' : Fin σ.r ⊕ Fin σ.l → ℝ)
    (h : S.consCm br φ σ x *ᵥ u' + S.consH br H σ x = 0) :
    ∃ u : Fin M → ℝ, ∀ i : Fin S.n, br (S.Φ i) H x + ∑ a, br (S.Φ i) (φ a) x * u a = 0 := by
  refine ⟨u' ∘ σ.eC, fun i => ?_⟩
  have := congrFun h (σ.eR i)
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Stage.consCm, Stage.consH, Matrix.of_apply,
    Equiv.symm_apply_apply, Pi.zero_apply] at this
  rw [← Equiv.sum_comp σ.eC] at this
  simpa [add_comm] using this

section Final

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The stage `k + 1` is the stage `k` extended by its secondary constraints (by definition). -/
theorem stages_succ_n (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (sel : ∀ S : Stage E, Sel S M) (S₀ : Stage E) (k : ℕ) :
    (stages br φ H sel S₀ (k + 1)).n = (stages br φ H sel S₀ k).n + (sel (stages br φ H sel S₀ k)).p := rfl

/-- **The Dirac algorithm from primary data, locally under constant rank**: the stages are generated from `φ`, `H`, `br` and
the selection rule; assume every stage is regular with nonempty zero set, and on the sets `U k` the selected block is
invertible with vanishing Schur complement. Then from some stage `N` on the zero sets stop changing, and every point of
`zeroSet (stage N) ∩ U N` has a multiplier `u` solving all the consistency conditions
`{S_i, H} + ∑_a {S_i, φ_a} u_a = 0`: no hypothesis relating the stages to the consistency conditions is needed. -/
theorem final_consistent_of_data (br : (E → ℝ) → (E → ℝ) → E → ℝ) (φ : Fin M → E → ℝ) (H : E → ℝ)
    (sel : ∀ S : Stage E, Sel S M) (S₀ : Stage E)
    (hreg : ∀ k, IsRegularStage (stages br φ H sel S₀ k).Φ)
    (hne : ∀ k, (zeroSet (stages br φ H sel S₀ k).Φ).Nonempty) (U : ℕ → Set E)
    (hU : ∀ k, ∀ x ∈ U k,
      IsUnit ((stages br φ H sel S₀ k).consCm br φ (sel (stages br φ H sel S₀ k)) x).toBlocks₁₁.det ∧
      ((stages br φ H sel S₀ k).consCm br φ (sel (stages br φ H sel S₀ k)) x).toBlocks₂₂ =
        ((stages br φ H sel S₀ k).consCm br φ (sel (stages br φ H sel S₀ k)) x).toBlocks₂₁ *
          ((stages br φ H sel S₀ k).consCm br φ (sel (stages br φ H sel S₀ k)) x).toBlocks₁₁⁻¹ *
          ((stages br φ H sel S₀ k).consCm br φ (sel (stages br φ H sel S₀ k)) x).toBlocks₁₂) :
    ∃ N, (∀ k, N ≤ k → zeroSet (stages br φ H sel S₀ k).Φ = zeroSet (stages br φ H sel S₀ N).Φ) ∧
      ∀ x ∈ zeroSet (stages br φ H sel S₀ N).Φ ∩ U N, ∃ u : Fin M → ℝ, ∀ i : Fin (stages br φ H sel S₀ N).n,
        br ((stages br φ H sel S₀ N).Φ i) H x + ∑ a, br ((stages br φ H sel S₀ N).Φ i) (φ a) x * u a = 0 := by
  set st := stages br φ H sel S₀ with hst
  have hmono : ∀ k, (st k).n ≤ (st (k + 1)).n := fun k => Nat.le_add_right _ _
  have hext : ∀ k i, (st (k + 1)).Φ (Fin.castLE (hmono k) i) = (st k).Φ i := fun k i =>
    appendStage_castLE (st k).Φ ((st k).chiFun br φ H (sel (st k))) i
  obtain ⟨N, hN⟩ := exists_stable_of_regular (fun k => (st k).n) (fun k => (st k).Φ) hmono hext hreg hne
  refine ⟨N, hN, fun x hx => ?_⟩
  have hwire := stageSet_inter_eq ((st N).consCm br φ (sel (st N))) ((st N).consH br H (sel (st N)))
    (st N).Φ (U N) (hU N)
  have hx1 : x ∈ zeroSet (st (N + 1)).Φ ∩ U N := by rw [hN (N + 1) (by omega)]; exact hx
  have hx2 : x ∈ zeroSet (appendStage (st N).Φ ((st N).chiFun br φ H (sel (st N)))) ∩ U N := hx1
  rw [← hwire] at hx2
  obtain ⟨u', hu'⟩ := hx2.1.2
  exact (st N).consistency_translate br φ H (sel (st N)) x u' hu'

end Final

end Lightlike.Gauge
