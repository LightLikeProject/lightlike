import Lightlike.Spacetime.CausalLadder.ChartLine
import Lightlike.Spacetime.Causal.Ladder
import Lightlike.Spacetime.Causal.BasicRelations

/-!
# Open sets in the causal past

In a manifold without boundary, every neighbourhood of a point `y` contains a nonempty open set of
points whose causal future contains `y`: a ball in the chart, at distance one time-step below `y`
(`exists_open_subset_causalPast`). This is the local input for the strict monotonicity of the
volume of the causal past, `x ↦ μ(J⁻(x))`, in Hawking's time function.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A nonempty open set in the causal past, inside any neighbourhood.** In a manifold without
boundary, for every neighbourhood `U` of `y` there is a nonempty open `O ⊆ U` with `y ∈ J⁺(a)` for
every `a ∈ O`. -/
theorem exists_open_subset_causalPast [BoundarylessManifold I M] (y : M) {U : Set M}
    (hU : U ∈ 𝓝 y) :
    ∃ O : Set M, IsOpen O ∧ O.Nonempty ∧ O ⊆ U ∧ ∀ a ∈ O, y ∈ causalFuture T a := by
  obtain ⟨V, r₀, ε, -, hr₀, hε, hbt, hline⟩ := exists_line_scale T y
  set φ := extChartAt I y with hφ
  have hysrc : y ∈ φ.source := mem_extChartAt_source y
  have hpre : φ.symm ⁻¹' U ∈ 𝓝 (φ y) := by
    have hcont : ContinuousAt φ.symm (φ y) := continuousAt_extChartAt_symm y
    exact hcont.preimage_mem_nhds (by rwa [φ.left_inv hysrc])
  obtain ⟨r₁, hr₁, hball1⟩ := Metric.mem_nhds_iff.1 hpre
  set ρ : ℝ := min r₁ r₀ with hρ
  have hρpos : 0 < ρ := lt_min hr₁ hr₀
  have hρ1 : ρ ≤ r₁ := min_le_left _ _
  have hρ0 : ρ ≤ r₀ := min_le_right _ _
  set s : ℝ := ρ / (8 * (‖V‖ + 1)) with hs
  have hspos : 0 < s := by positivity
  have hsV : ‖s • V‖ < ρ / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, hs]
    have : ‖V‖ < ‖V‖ + 1 := by linarith
    calc ρ / (8 * (‖V‖ + 1)) * ‖V‖ ≤ ρ / (8 * (‖V‖ + 1)) * (‖V‖ + 1) :=
          mul_le_mul_of_nonneg_left this.le (by positivity)
      _ = ρ / 8 := by field_simp
      _ < ρ / 4 := by linarith
  set c₀ : E := φ y - s • V with hc₀
  set δ : ℝ := min (ρ / 4) (s * ε) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hc₀ball : c₀ ∈ Metric.ball (φ y) r₀ := by
    rw [Metric.mem_ball, dist_eq_norm, hc₀, sub_sub_cancel_left, norm_neg]
    linarith
  refine ⟨{q | q ∈ φ.source ∧ ‖φ q - c₀‖ < δ}, ?_, ⟨φ.symm c₀, ?_⟩, ?_, ?_⟩
  · have : ContinuousOn (fun q => ‖φ q - c₀‖) φ.source :=
      ((continuousOn_extChartAt y).sub continuousOn_const).norm
    exact this.isOpen_inter_preimage (isOpen_extChartAt_source y) (isOpen_Iio (a := δ))
  · refine ⟨φ.map_target (hbt hc₀ball), ?_⟩
    rw [φ.right_inv (hbt hc₀ball)]; simpa using hδpos
  · rintro q ⟨hq, hqδ⟩
    have h1 : ‖φ q - φ y‖ < ρ := by
      have : ‖φ q - φ y‖ ≤ ‖φ q - c₀‖ + ‖c₀ - φ y‖ := by
        have := norm_add_le (φ q - c₀) (c₀ - φ y)
        simpa using this
      have h2 : ‖c₀ - φ y‖ = ‖s • V‖ := by rw [hc₀, sub_sub_cancel_left, norm_neg]
      have h3 : δ ≤ ρ / 4 := min_le_left _ _
      linarith
    have := hball1 (show φ q ∈ Metric.ball (φ y) r₁ by rw [Metric.mem_ball, dist_eq_norm]; linarith)
    simpa [Set.mem_preimage, φ.left_inv hq] using this
  · rintro q ⟨hq, hqδ⟩
    have h1 : ‖φ q - φ y‖ < ρ := by
      have : ‖φ q - φ y‖ ≤ ‖φ q - c₀‖ + ‖c₀ - φ y‖ := by
        have := norm_add_le (φ q - c₀) (c₀ - φ y)
        simpa using this
      have h2 : ‖c₀ - φ y‖ = ‖s • V‖ := by rw [hc₀, sub_sub_cancel_left, norm_neg]
      have h3 : δ ≤ ρ / 4 := min_le_left _ _
      linarith
    have hqball : φ q ∈ Metric.ball (φ y) r₀ := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith
    have hyball : φ y ∈ Metric.ball (φ y) r₀ := Metric.mem_ball_self hr₀
    have hsε : δ ≤ s * ε := min_le_right _ _
    have hnorm : ‖φ y - φ q - s • V‖ < s * ε := by
      have : φ y - φ q - s • V = -(φ q - c₀) := by rw [hc₀]; abel
      rw [this, norm_neg]; linarith
    have := hline s hspos (by linarith [hsV, hρ0]) (φ q) hqball (φ y) hyball hnorm
    rwa [φ.left_inv hq, φ.left_inv hysrc] at this

/-- **The causal past is monotone along the causal future.** `y ∈ J⁺(x)` gives `J⁻(x) ⊆ J⁻(y)`. -/
theorem causalPast_subset_of_mem_causalFuture {x y : M} (hxy : y ∈ causalFuture T x) :
    causalPast T x ⊆ causalPast T y := fun a ha => causal_trans T ha hxy

/-- **Strict monotonicity of the volume of the causal past.** Let `μ` be a finite Borel measure
that is positive on nonempty open sets, on a manifold without boundary, causal with closed causal
pasts. If `y ∈ J⁺(x)` and `y ≠ x` then `μ(J⁻(x)) < μ(J⁻(y))`. -/
theorem measure_causalPast_lt [BoundarylessManifold I M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) [IsFiniteMeasure μ] (hμ : ∀ O : Set M, IsOpen O → O.Nonempty → 0 < μ O)
    (hcausal : IsCausal T) (hclosed : ∀ x : M, IsClosed (causalPast T x)) {x y : M}
    (hxy : y ∈ causalFuture T x) (hne : y ≠ x) : μ (causalPast T x) < μ (causalPast T y) := by
  have hy : y ∉ causalPast T x := fun hyx => hne (hcausal x y hxy hyx).symm
  obtain ⟨O, hO, hOne, hOU, hOy⟩ := exists_open_subset_causalPast T y
    ((hclosed x).isOpen_compl.mem_nhds hy)
  have hsub : causalPast T x ∪ O ⊆ causalPast T y :=
    union_subset (causalPast_subset_of_mem_causalFuture T hxy) fun a ha => hOy a ha
  have hdisj : Disjoint (causalPast T x) O := Set.disjoint_left.2 fun a ha haO => hOU haO ha
  calc μ (causalPast T x) < μ (causalPast T x) + μ O :=
        ENNReal.lt_add_right (measure_ne_top μ _) (hμ O hO hOne).ne'
    _ = μ (causalPast T x ∪ O) := (measure_union hdisj hO.measurableSet).symm
    _ ≤ μ (causalPast T y) := measure_mono hsub

end Lightlike.Causal
