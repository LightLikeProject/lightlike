import Lightlike.Poincare.PauliLubanskiL2
import Lightlike.OperatorAlgebras.Spectral.Stone.Basic

/-!
# The Pauli–Lubanski operator from the Stone generators

For an invariant measure `μ` on the mass shell, finite on compacts, the one-parameter subgroups `γ_{νρ}` of the
Lorentz generators act on `L²(μ; ℂ^{n+1})` by the one-parameter unitary groups `t ↦ U(γ_{νρ}(t))`
(`isOneParameterUnitaryGroup_lorGroupL2`). Every chart test function `ψ` lies in the domain of their Stone generator
`A_{νρ}` (`(1/i) d/dt` at `0`), and `A_{νρ} ψ = (1/i) M_{νρ} ψ` with the pointwise generator `M_{νρ}`
(`generator_lorGroupL2`). Hence the Pauli–Lubanski operator built from the Stone generators,
`W^μ ψ = ½ ε^{μνρσ} A_{νρ} (p_σ ψ)`, is the class of `Q ↦ (1/i) plMat(Q) ψ(Q)` (`pauliLubanski_stone`): it acts by
multiplication by a matrix function with Minkowski square `−m² s(s+1)` (`pauliLubanski_sq_generators`).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §1.2 (page 4 of v2: `W^μ = ½ ε^{μνρσ} M_{νρ} P_σ`), §5.2, equation (54) (page 39 of v2).
-/

open MeasureTheory Filter Topology Matrix Lightlike.Lorentz Lightlike.SU2 Lightlike.OperatorAlgebras.Spectral.Stone

namespace Lightlike.Poincare

noncomputable section

variable {m : ℝ} {μ : Measure (MassShell m)}

/-- The one-parameter unitary group of the Lorentz generator `M_{νρ}` on `L²`. -/
def lorGroupL2 (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (ν ρ : Fin 4) :
    ℝ → (Lp (Spinor n) 2 μ ≃ₗᵢ[ℂ] Lp (Spinor n) 2 μ) :=
  fun t => inducedL2E hm n hμ (lorCurve ν ρ t)

/-- **The Lorentz generators give one-parameter unitary groups on `L²`.** -/
theorem isOneParameterUnitaryGroup_lorGroupL2 (hm : 0 < m) (n : ℕ)
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (ν ρ : Fin 4) :
    IsOneParameterUnitaryGroup (lorGroupL2 hm n hμ ν ρ) where
  map_zero ψ := by
    simp only [lorGroupL2, inducedL2E_apply, lorCurve_zero, inducedL2_one]
  map_add s t ψ := by
    simp only [lorGroupL2, inducedL2E_apply, lorCurve_add, inducedL2_mul]

/-- **The Stone generator on chart test functions**: `ψ` lies in the domain of the Stone generator `A_{νρ}` of
`t ↦ U(γ_{νρ}(t))`, and `A_{νρ} ψ = (1/i) M_{νρ} ψ`. -/
theorem generator_lorGroupL2 (hm : 0 < m) {n : ℕ} [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (F : ChartTest n) (ν ρ : Fin 4) :
    ∃ h : F.toL2 hm μ ∈ (generator (lorGroupL2 hm n hμ ν ρ)).domain,
      generator (lorGroupL2 hm n hμ ν ρ) ⟨F.toL2 hm μ, h⟩ = Complex.I⁻¹ • F.genL2 hm μ (lorGen ν ρ) := by
  rw [exists_generator_eq_iff]
  have h := (F.tendsto_diffQuot_L2 hm hμ ν ρ).const_smul Complex.I⁻¹
  refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [generatorQuotient, lorGroupL2, inducedL2E_apply, mul_inv, mul_smul]

/-- The sum of `L²` classes of a finite family is the class of the sum. -/
lemma toLp_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → MassShell m → Spinor n}
    (hf : ∀ i, MemLp (f i) 2 μ) :
    ∑ i ∈ s, (hf i).toLp (f i) = (memLp_finsetSum' s fun i _ => hf i).toLp (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    apply Lp.ext
    filter_upwards [(memLp_finsetSum' (∅ : Finset ι) fun i _ => hf i).coeFn_toLp,
      Lp.coeFn_zero (E := Spinor n) (p := 2) (μ := μ)] with x h1 h2
    rw [h1, h2]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by rw [Finset.sum_insert ha])

/-- The class of a finite sum is a.e. the sum of the classes. -/
lemma coeFn_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Lp (Spinor n) 2 μ) :
    ⇑(∑ i ∈ s, g i) =ᵐ[μ] ∑ i ∈ s, ⇑(g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero (E := Spinor n) (p := 2) (μ := μ)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.rfl.add ih)

lemma toSp_smul (n : ℕ) (c : ℂ) (v : Fin (n + 1) → ℂ) : toSp n (c • v) = c • toSp n v := by
  simp only [toSp_apply, WithLp.toLp_smul]

namespace ChartTest

variable {n : ℕ} (F : ChartTest n)

lemma plMat_eq_sum (hm : 0 < m) (μ' : Fin 4) (Q : MassShell m) :
    toSp n (plMat hm n Q μ' *ᵥ F.ψ m Q) =
      ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ' ν ρ σ : ℝ) : ℂ) • toSp n ((F.mulP hm σ).genFun hm (lorGen ν ρ) Q) := by
  rw [← F.sum_genFun_mulP hm μ' Q]
  simp only [map_sum, toSp_smul]

lemma memLp_plMat (hm : 0 < m) [IsFiniteMeasureOnCompacts μ] (μ' : Fin 4) :
    MemLp (fun Q => toSp n (plMat hm n Q μ' *ᵥ F.ψ m Q)) 2 μ := by
  have e : (fun Q => toSp n (plMat hm n Q μ' *ᵥ F.ψ m Q)) = ∑ ν, ∑ ρ, ∑ σ,
      fun Q => ((1 / 2 * levi μ' ν ρ σ : ℝ) : ℂ) • toSp n ((F.mulP hm σ).genFun hm (lorGen ν ρ) Q) := by
    funext Q
    simp only [Finset.sum_apply]
    exact F.plMat_eq_sum hm μ' Q
  rw [e]
  refine memLp_finsetSum' _ fun ν _ => memLp_finsetSum' _ fun ρ _ => memLp_finsetSum' _ fun σ _ => ?_
  exact ((memLp_toSp (μ := μ) ((F.mulP hm σ).continuous_genFun hm (lorGen ν ρ))
    ((F.mulP hm σ).hasCompactSupport_genFun hm (lorGen ν ρ))).const_smul (((1 / 2 * levi μ' ν ρ σ : ℝ) : ℂ)))

/-- **The Pauli–Lubanski operator from the Stone generators**: for a chart test function `ψ`,
`½ ε^{μνρσ} A_{νρ} (p_σ ψ) = (1/i) plMat ψ` in `L²(μ)`, where `A_{νρ}` is the Stone generator of
`t ↦ U(γ_{νρ}(t))` (`generator_lorGroupL2`) and `plMat(Q) = dSpin(L(Q)⁻¹ X^μ_Q L(Q))`. -/
theorem pauliLubanski_stone (hm : 0 < m) [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (μ' : Fin 4) :
    ∑ ν, ∑ ρ, ∑ σ, ((1 / 2 * levi μ' ν ρ σ : ℝ) : ℂ) •
        generator (lorGroupL2 hm n hμ ν ρ)
          ⟨(F.mulP hm σ).toL2 hm μ, (generator_lorGroupL2 hm hμ (F.mulP hm σ) ν ρ).fst⟩ =
      Complex.I⁻¹ • (F.memLp_plMat hm (μ := μ) μ').toLp _ := by
  have hg : ∀ ν ρ σ, generator (lorGroupL2 hm n hμ ν ρ)
      ⟨(F.mulP hm σ).toL2 hm μ, (generator_lorGroupL2 hm hμ (F.mulP hm σ) ν ρ).fst⟩ =
        Complex.I⁻¹ • (F.mulP hm σ).genL2 hm μ (lorGen ν ρ) :=
    fun ν ρ σ => (generator_lorGroupL2 hm hμ (F.mulP hm σ) ν ρ).snd
  simp only [hg, smul_comm _ Complex.I⁻¹, ← Finset.smul_sum]
  congr 1
  apply Lp.ext
  set X : Fin 4 → Fin 4 → Fin 4 → Lp (Spinor n) 2 μ := fun ν ρ σ =>
    ((1 / 2 * levi μ' ν ρ σ : ℝ) : ℂ) • (F.mulP hm σ).genL2 hm μ (lorGen ν ρ)
  have hA : ∀ᵐ Q ∂μ, ∀ ν ρ σ, X ν ρ σ Q =
      ((1 / 2 * levi μ' ν ρ σ : ℝ) : ℂ) • toSp n ((F.mulP hm σ).genFun hm (lorGen ν ρ) Q) := by
    simp only [ae_all_iff]
    intro ν ρ σ
    have h4 : ⇑((F.mulP hm σ).genL2 hm μ (lorGen ν ρ)) =ᵐ[μ]
        fun Q => toSp n ((F.mulP hm σ).genFun hm (lorGen ν ρ) Q) :=
      (memLp_toSp (μ := μ) ((F.mulP hm σ).continuous_genFun hm (lorGen ν ρ))
        ((F.mulP hm σ).hasCompactSupport_genFun hm (lorGen ν ρ))).coeFn_toLp
    filter_upwards [Lp.coeFn_smul (((1 / 2 * levi μ' ν ρ σ : ℝ) : ℂ))
      ((F.mulP hm σ).genL2 hm μ (lorGen ν ρ)), h4] with Q e1 e2
    simp only [X]
    rw [e1, Pi.smul_apply, e2]
  have hB : ∀ᵐ Q ∂μ, ∀ ν ρ, (∑ σ, X ν ρ σ) Q = ∑ σ, X ν ρ σ Q := by
    simp only [ae_all_iff]
    intro ν ρ
    filter_upwards [coeFn_finsetSum Finset.univ (X ν ρ)] with Q h
    rw [h, Finset.sum_apply]
  have hC : ∀ᵐ Q ∂μ, ∀ ν, (∑ ρ, ∑ σ, X ν ρ σ) Q = ∑ ρ, (∑ σ, X ν ρ σ) Q := by
    simp only [ae_all_iff]
    intro ν
    filter_upwards [coeFn_finsetSum Finset.univ (fun ρ => ∑ σ, X ν ρ σ)] with Q h
    rw [h, Finset.sum_apply]
  have hD : (⇑(∑ ν, ∑ ρ, ∑ σ, X ν ρ σ)) =ᵐ[μ] fun Q => ∑ ν, (∑ ρ, ∑ σ, X ν ρ σ) Q := by
    filter_upwards [coeFn_finsetSum Finset.univ (fun ν => ∑ ρ, ∑ σ, X ν ρ σ)] with Q h
    rw [h, Finset.sum_apply]
  filter_upwards [hA, hB, hC, hD, (F.memLp_plMat hm (μ := μ) μ').coeFn_toLp] with Q hA hB hC hD hE
  rw [hD, hE, F.plMat_eq_sum hm μ' Q]
  simp only [hC, hB, hA]

end ChartTest

end

end Lightlike.Poincare
