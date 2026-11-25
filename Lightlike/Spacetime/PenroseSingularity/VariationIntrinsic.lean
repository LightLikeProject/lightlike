import Lightlike.Spacetime.PenroseSingularity.ExpIntrinsic
import Lightlike.Spacetime.PenroseSingularity.ExpTheta
import Lightlike.Spacetime.PenroseSingularity.VariationJets

/-!
# The intrinsic exponential variation and its chart expression (G1-012, step D4)

For a curve `γ` and tangent fields `W, Z` along it, `varT g γ W Z (s, t) = expT ⟨γ t, s W t + s² Z t⟩`. In the chart
at `p₀` it is `varA Θ (ψ ∘ γ) Wc Zc`, where `Wc`, `Zc` are the components of the fields in the trivialization at `p₀`.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M] (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The intrinsic variation `expT ⟨γ t, s W t + s² Z t⟩`. -/
def varT (γ : ℝ → M) (W Z : ∀ t, TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t)) (p : ℝ × ℝ) : M :=
  expT g (⟨γ p.2, p.1 • W p.2 + p.1 ^ 2 • Z p.2⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)

/-- The components of a tangent vector in the trivialization at `p₀`. -/
def comp (p₀ : M) {x : M} (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) : Fin n → ℝ :=
  (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀ (⟨x, v⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)).2

/-- `zetaMap` of the chart coordinates and components of a tangent vector is the vector. -/
theorem zetaMap_comp (p₀ : M) {x : M} (hx : x ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    zetaMap p₀ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ x, comp p₀ v) =
      (⟨x, v⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) := by
  have hs : x ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).source := by
    have := hx
    simpa [Causal.tTriv, TangentBundle.trivializationAt_baseSet] using this
  unfold zetaMap
  rw [(extChartAt 𝓘(ℝ, Fin n → ℝ) p₀).left_inv hs]
  have h1 := (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).symm_apply_apply_mk hx v
  have h2 : (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀ (⟨x, v⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) = (x, comp p₀ v) :=
    Prod.ext ((Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).coe_fst (by simpa using hx)) rfl
  rw [h2] at h1
  show (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).toOpenPartialHomeomorph.symm (x, comp p₀ v) = ⟨x, v⟩
  rw [← (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).mk_symm hx]
  exact congrArg (fun w => (⟨x, w⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) h1

/-- The components of a tangent vector are linear in the vector. -/
theorem comp_eq_linearMapAt (p₀ : M) {x : M} (hx : x ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    comp p₀ v = (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).linearMapAt ℝ x v := by
  rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx]
  rfl

/-- The components of `s v + s² u`. -/
theorem comp_add_smul (p₀ : M) {x : M} (hx : x ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet)
    (v u : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (s : ℝ) :
    comp p₀ (s • v + s ^ 2 • u) = s • comp p₀ v + s ^ 2 • comp p₀ u := by
  rw [comp_eq_linearMapAt p₀ hx, comp_eq_linearMapAt p₀ hx, comp_eq_linearMapAt p₀ hx]
  simp

/-- **The chart expression of the intrinsic variation.** In the chart at `p₀`, with `td` the exponential data
there, `ψ (varT g γ W Z (s, t)) = varA td.Θ (ψ ∘ γ) (comp p₀ ∘ W) (comp p₀ ∘ Z) (s, t)` whenever the point lies in
the domain of `td.Θ`. -/
theorem chart_varT (p₀ : M) (td : ThetaData g p₀) (γ : ℝ → M) (W Z : ∀ t, TangentSpace 𝓘(ℝ, Fin n → ℝ) (γ t))
    {p : ℝ × ℝ} (hx : γ p.2 ∈ (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M p₀).baseSet)
    (hD : (extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ p.2),
      p.1 • comp p₀ (W p.2) + p.1 ^ 2 • comp p₀ (Z p.2)) ∈ td.D) :
    extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (varT g γ W Z p) =
      varA td.Θ (fun t => extChartAt 𝓘(ℝ, Fin n → ℝ) p₀ (γ t)) (fun t => comp p₀ (W t))
        (fun t => comp p₀ (Z t)) p := by
  unfold varA varT
  rw [← comp_add_smul p₀ hx] at hD ⊢
  rw [td.exp_eq _ hD, zetaMap_comp p₀ hx]

end Lightlike.Penrose
