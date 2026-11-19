import Lightlike.GR.KruskalKretschmann

/-!
# Ingoing radial null geodesics reach the singularity at finite affine parameter

Gap row G1-020. Source read: S. M. Carroll, *Lecture Notes on General Relativity*, arXiv:gr-qc/9712019, chapter 7,
printed page 171: a point where a curvature scalar goes to infinity is regarded as a singularity, and "we should
also check that the point is not 'infinitely far away'; that is, that it can be reached by travelling a finite
distance along a curve".

* `IsCoordGeodesic`: a curve in a chart with velocity `v` and acceleration `a` satisfying the geodesic equation
  `a^i + Γ^i_{jk} v^j v^k = 0`.
* In ingoing Eddington–Finkelstein coordinates `(v, r, θ, φ)` the curve `λ ↦ (v₀, r₀ - λ, θ₀, φ₀)` is a geodesic
  (`ef_ingoing_isCoordGeodesic`) with null velocity (`ef_ingoing_null`): `-r` is an affine parameter of the
  ingoing radial null rays.
* It stays in the chart for `λ < r₀` and the Kretschmann scalar along it tends to infinity as `λ → r₀`
  (`tendsto_kretschmann_ef_ingoing`): the singularity `r = 0` is reached at the finite affine parameter `r₀`.
  So the extension is geodesically incomplete, and by `not_tendsto_of_isometric_chart` this geodesic cannot be
  continued in any extension.
-/

open Matrix Real Set Filter Topology

noncomputable section

namespace Lightlike

/-- **A geodesic in a chart** on the parameter set `s`: a curve `γ` with velocity `v` and acceleration `a` such
that `a^i + Σ_{jk} Γ^i_{jk}(γ) v^j v^k = 0`. -/
def IsCoordGeodesic {n : ℕ} (g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (γ : ℝ → Fin n → ℝ)
    (s : Set ℝ) : Prop :=
  ∃ v a : ℝ → Fin n → ℝ, (∀ t ∈ s, HasDerivAt γ (v t) t) ∧ (∀ t ∈ s, HasDerivAt v (a t) t) ∧
    ∀ t ∈ s, ∀ i, a t i + ∑ j, ∑ k, christoffel g i j k (γ t) * v t j * v t k = 0

variable (M : ℝ)

/-- The Christoffel symbols `Γ^i_{rr}` of the Eddington–Finkelstein metric vanish. -/
lemma christoffel_ef_rr (i : Fin 4) (y : Fin 4 → ℝ) : christoffel (efMetric M) i 1 1 y = 0 := by
  have h : ∀ l : Fin 4, (fun z : Fin 4 → ℝ => efMetric M z l 1) = fun _ => if l = 0 then (1 : ℝ) else 0 := by
    intro l
    funext z
    fin_cases l <;> simp [efMetric]
  simp only [christoffel, h, pd_const]
  simp

/-- The ingoing radial null ray `λ ↦ (v₀, r₀ - λ, θ₀, φ₀)`. -/
def efIngoing (v₀ r₀ θ₀ φ₀ : ℝ) (t : ℝ) : Fin 4 → ℝ := ![v₀, r₀ - t, θ₀, φ₀]

/-- **The ingoing radial null rays are geodesics, affinely parametrized by `-r`.** -/
theorem ef_ingoing_isCoordGeodesic (v₀ r₀ θ₀ φ₀ : ℝ) :
    IsCoordGeodesic (efMetric M) (efIngoing v₀ r₀ θ₀ φ₀) univ := by
  refine ⟨fun _ => ![0, -1, 0, 0], fun _ => 0, fun t _ => ?_, fun t _ => hasDerivAt_const t _,
    fun t _ i => ?_⟩
  · rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_const t v₀
    · exact (hasDerivAt_id' t).const_sub r₀
    · exact hasDerivAt_const t θ₀
    · exact hasDerivAt_const t φ₀
  · simp [Fin.sum_univ_four, christoffel_ef_rr]

/-- The velocity of an ingoing radial ray is null. -/
theorem ef_ingoing_null (y : Fin 4 → ℝ) :
    (![0, -1, 0, 0] : Fin 4 → ℝ) ⬝ᵥ efMetric M y *ᵥ ![0, -1, 0, 0] = 0 := by
  simp [efMetric, dotProduct, mulVec, Fin.sum_univ_four]

lemma efIngoing_mem {v₀ r₀ θ₀ φ₀ t : ℝ} (ht : t < r₀) (hθ : 0 < θ₀) (hθ' : θ₀ < π) :
    efIngoing v₀ r₀ θ₀ φ₀ t ∈ efU :=
  ⟨by show 0 < r₀ - t; linarith, hθ, hθ'⟩

/-- **The curvature blows up at the finite affine parameter `r₀`** along an ingoing radial null geodesic. -/
theorem tendsto_kretschmann_ef_ingoing (hM : 0 < M) (v₀ r₀ : ℝ) {θ₀ : ℝ} (hθ : 0 < θ₀) (hθ' : θ₀ < π)
    (φ₀ : ℝ) :
    Tendsto (fun t => kretschmann (efMetric M) (efIngoing v₀ r₀ θ₀ φ₀ t)) (𝓝[<] r₀) atTop := by
  rw [tendsto_atTop]
  intro B
  set ε : ℝ := min 1 (48 * M ^ 2 / (|B| + 1)) with hε
  have hB1 : 0 < |B| + 1 := by positivity
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ 48 * M ^ 2 / (|B| + 1) := min_le_right _ _
  filter_upwards [Ioo_mem_nhdsLT (show r₀ - ε < r₀ by linarith)] with t ht
  have hρ : 0 < r₀ - t := by linarith [ht.2]
  have hρε : r₀ - t < ε := by linarith [ht.1]
  rw [kretschmann_ef M hM (efIngoing_mem ht.2 hθ hθ')]
  show B ≤ 48 * M ^ 2 / (r₀ - t) ^ 6
  have h6 : (r₀ - t) ^ 6 ≤ r₀ - t := by
    have hle : r₀ - t ≤ 1 := by linarith
    calc (r₀ - t) ^ 6 = (r₀ - t) * (r₀ - t) ^ 5 := by ring
      _ ≤ (r₀ - t) * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hρ.le hle) hρ.le
      _ = r₀ - t := mul_one _
  have h8 : ε * (|B| + 1) ≤ 48 * M ^ 2 := by rwa [le_div_iff₀ hB1] at hε2
  have h7 : (r₀ - t) ^ 6 * (|B| + 1) ≤ 48 * M ^ 2 := by nlinarith [pow_pos hρ 6]
  have h9 : |B| + 1 ≤ 48 * M ^ 2 / (r₀ - t) ^ 6 := by
    rw [le_div_iff₀ (pow_pos hρ 6)]
    linarith
  linarith [le_abs_self B]

end Lightlike
