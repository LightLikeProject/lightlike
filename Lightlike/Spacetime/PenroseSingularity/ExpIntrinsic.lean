import Lightlike.Spacetime.PenroseSingularity.ExpGerm

/-!
# The exponential map on the tangent bundle (G1-012, step D4)

`expT g z` is the value at `1` of the geodesic curve whose phase at `0` is the tangent vector `z`, and `z.proj`
outside the domain of the exponential map. It does not depend on a chart, and `expT_eq_of` identifies it with the
time-one value of any geodesic curve with that initial phase.
-/

open Bundle Manifold Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike.Penrose

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] (g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n)

/-- The tangent vectors on which the exponential map is defined: those with a geodesic curve on an open interval
containing `0` and `1` whose phase at `0` is the vector. -/
def ExpDomainT : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M) :=
  {z | ∃ (a b : ℝ) (γ : ℝ → M), a < 0 ∧ 1 < b ∧ IsGeodesicCurveOn g γ (Ioo a b) ∧ phase (n := n) γ 0 = z}

/-- The exponential map on the tangent bundle. -/
def expT (z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) : M := by
  classical
  exact if h : z ∈ ExpDomainT g then (Classical.choose (Classical.choose_spec (Classical.choose_spec h))) 1
    else z.proj

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- **`expT` is the time-one value of any geodesic curve with the given initial phase.** -/
theorem expT_eq_of {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} {a b : ℝ} {γ : ℝ → M} (ha : a < 0) (hb : 1 < b)
    (hγ : IsGeodesicCurveOn g γ (Ioo a b)) (h0 : phase (n := n) γ 0 = z) : expT g z = γ 1 := by
  have hz : z ∈ ExpDomainT g := ⟨a, b, γ, ha, hb, hγ, h0⟩
  unfold expT
  rw [dite_eq_left_of_eq_true (eq_true hz)]
  obtain ⟨ha₀, hb₀, hγ₀, h00⟩ := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hz))
  set a₀ := Classical.choose hz
  set b₀ := Classical.choose (Classical.choose_spec hz)
  set γ₀ := Classical.choose (Classical.choose_spec (Classical.choose_spec hz))
  have hsub : Ioo (max a a₀) (min b b₀) ⊆ Ioo a b := Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hsub₀ : Ioo (max a a₀) (min b b₀) ⊆ Ioo a₀ b₀ := Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have h0mem : (0 : ℝ) ∈ Ioo (max a a₀) (min b b₀) := ⟨max_lt ha ha₀, lt_min (by linarith) (by linarith)⟩
  have h1mem : (1 : ℝ) ∈ Ioo (max a a₀) (min b b₀) := ⟨max_lt (by linarith) (by linarith), lt_min hb hb₀⟩
  exact eqOn_of_phase_eq' g isOpen_Ioo isPreconnected_Ioo (hγ₀.mono hsub₀) (hγ.mono hsub) h0mem
    (by rw [h00, h0]) h1mem

/-- **The time-one value of a flow germ is `expT`.** -/
theorem expT_eq_flow {N : Set (TangentBundle 𝓘(ℝ, Fin n → ℝ) M)} {ε : ℝ}
    {Γ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M → ℝ → M} (hε : 0 < ε)
    (hgeo : ∀ z ∈ N, IsGeodesicCurveOn g (Γ z) (Ioo (-ε) (1 + ε)) ∧ phase (n := n) (Γ z) 0 = z)
    {z : TangentBundle 𝓘(ℝ, Fin n → ℝ) M} (hz : z ∈ N) : expT g z = Γ z 1 :=
  expT_eq_of g (by linarith) (by linarith) (hgeo z hz).1 (hgeo z hz).2

/-- **`expT` of a zero vector is its base point.** -/
theorem expT_zero (p : M) : expT g (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M) = p := by
  have h := expT_eq_of g (z := (⟨p, 0⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) (a := -1) (b := 2)
    (γ := fun _ => p) (by norm_num) (by norm_num) (isGeodesicCurveOn_const g p _) (phase_const p 0)
  exact h

end Lightlike.Penrose
