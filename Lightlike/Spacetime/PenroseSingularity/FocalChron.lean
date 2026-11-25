import Lightlike.Spacetime.PenroseSingularity.FamilyTheta
import Lightlike.Spacetime.PenroseSingularity.PenroseFocal

/-!
# Focal points and the chronological future (G1-012, step D4 as a named hypothesis)

`FocalImpliesChron T S` is the second-variation fact for a spacelike submanifold `S` of codimension two: along
a future null geodesic of a smooth family of null normal geodesics starting on `S`, a focal point strictly
before the endpoint puts the endpoint in `I⁺(S)`.
-/

open Set Filter Topology Manifold
open scoped ContDiff Manifold Matrix

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]

/-- **A focal point before the endpoint puts the endpoint in the chronological future of `S`.** For every
flow family `F (σ, t) = Γ (zS σ) t` of future null geodesics starting on `S` along null normals, whose initial
points are parametrised by an immersion of an `(n - 2)`-dimensional parameter space (`Q (σ, 0)` positive
definite), if the Gram matrix `Q (σ, t₀)` of the `σ`-derivatives is degenerate for some `0 < t₀ < L`, then
`Γ (zS σ) L ∈ I⁺(S)`. -/
def FocalImpliesChron (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) (T : Causal.TimeOrientation g)
    (S : Set M) : Prop :=
  ∀ (Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M)
    (zS : (Fin (n - 2) → ℝ) → TangentBundle 𝓘(ℝ, Fin n → ℝ) M)
    (Nz : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (J : Set ℝ) (Sg : Set (Fin (n - 2) → ℝ)),
    FlowFamily g Γ zS Nz J Sg →
    (∀ σ ∈ Sg, (zS σ).proj ∈ S) →
    (∀ σ ∈ Sg, g.g (zS σ).proj (zS σ).snd (zS σ).snd = 0 ∧ g.g (zS σ).proj (zS σ).snd (T.X (zS σ).proj) < 0) →
    (∀ σ ∈ Sg, ∀ j : Fin (n - 2), g.g (Γ (zS σ) 0) (phase (n := n) (Γ (zS σ)) 0).snd
      (mfderiv 𝓘(ℝ, Fin (n - 2) → ℝ) 𝓘(ℝ, Fin n → ℝ) (fun σ' => Γ (zS σ') 0) σ (Pi.single j 1)) = 0) →
    ∀ σ ∈ Sg, (Qg g Γ zS σ 0).PosDef →
    ∀ {L t₀ : ℝ}, 0 < t₀ → t₀ < L → L ∈ J → ¬ (Qg g Γ zS σ t₀).PosDef →
      Γ (zS σ) L ∈ Causal.chronFutureSet T S

/-- **The null energy condition in charts**: for every chart and every null tangent vector in its domain, the
Ricci curvature of the coordinate metric of the chart is non-negative on the chart components of the vector. -/
def ChartNEC (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n) : Prop :=
  ∀ (x₀ : M) (z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M),
    z.proj ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀).source → g.g z.proj z.snd z.snd = 0 →
      0 ≤ ∑ a, ∑ b, Lightlike.ricci (g.coordMetric x₀) a b (extChartAt 𝓘(ℝ, Fin n → ℝ) x₀ z.proj) *
        (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ z).2 a * (Causal.tTriv 𝓘(ℝ, Fin n → ℝ) M x₀ z).2 b

end Lightlike.Penrose
