import Lightlike.Spacetime.CausalLadder.NullBoundary
import Lightlike.Spacetime.CausalLadder.LocalLift
import Lightlike.Spacetime.CausalLadder.NearFuture
import Lightlike.Spacetime.Causal.OpenPast
import Lightlike.Spacetime.CausalLadder.ChartLine
import Lightlike.Spacetime.VolumeMeasure
import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.Ladder

/-!
# The frontier of a past set is null for the volume measure

On a manifold modelled on `ℝⁿ` with a Lorentzian metric and a time orientation, the frontier of a
past set (`a ∈ A` and `a ∈ J⁺(b)` give `b ∈ A`, as `J⁻(x)` is) has volume zero. In a chart box
(`exists_line_scale`) the image of the set has the cone property of `NullBoundary.lean`, so its
frontier is Lebesgue-null; the volume of a set in a chart is the integral of the density over its
image (`volumeMeasure_chart`), and countably many boxes cover the manifold.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open MeasureTheory Set Manifold TopologicalSpace Filter Topology Bundle Metric
open scoped ContDiff ENNReal

noncomputable section

namespace Lightlike.Causal

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] [SecondCountableTopology M] [T2Space M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M] [MeasurableSpace M] [BorelSpace M]
  {g : LorentzianMetric 𝓘(ℝ, Fin n → ℝ) M n} (T : TimeOrientation g)

/-- **The frontier of a past set has volume zero.** -/
theorem volumeMeasure_frontier_pastSet_eq_zero
    {A : Set M} (hA : ∀ a ∈ A, ∀ b : M, a ∈ causalFuture T b → b ∈ A) :
    volumeMeasure g (frontier A) = 0 := by
  classical
  have hdata : ∀ q : M, ∃ (V : Fin n → ℝ) (r₀ ε : ℝ), V ≠ 0 ∧ 0 < r₀ ∧ 0 < ε ∧
      Metric.ball (extChartAt 𝓘(ℝ, Fin n → ℝ) q q) r₀ ⊆ (extChartAt 𝓘(ℝ, Fin n → ℝ) q).target ∧
      ∀ s : ℝ, 0 < s → ‖s • V‖ < r₀ / 2 →
        ∀ a ∈ Metric.ball (extChartAt 𝓘(ℝ, Fin n → ℝ) q q) r₀,
          ∀ b ∈ Metric.ball (extChartAt 𝓘(ℝ, Fin n → ℝ) q q) r₀, ‖b - a - s • V‖ < s * ε →
            (extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm b ∈
              causalFuture T ((extChartAt 𝓘(ℝ, Fin n → ℝ) q).symm a) :=
    fun q => exists_line_scale T q
  choose V r₀ ε hV hr₀ hε hbt hline using hdata
  set box : M → Set M := fun q => {m | m ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) q).source ∧
    ‖extChartAt 𝓘(ℝ, Fin n → ℝ) q m - extChartAt 𝓘(ℝ, Fin n → ℝ) q q‖ < r₀ q} with hbox
  have hbox_open : ∀ q, IsOpen (box q) := fun q => by
    have : ContinuousOn (fun m => ‖extChartAt 𝓘(ℝ, Fin n → ℝ) q m - extChartAt 𝓘(ℝ, Fin n → ℝ) q q‖)
        (extChartAt 𝓘(ℝ, Fin n → ℝ) q).source :=
      ((continuousOn_extChartAt q).sub continuousOn_const).norm
    exact this.isOpen_inter_preimage (isOpen_extChartAt_source q) (isOpen_Iio (a := r₀ q))
  have hqbox : ∀ q, q ∈ box q := fun q => ⟨mem_extChartAt_source q, by simpa using hr₀ q⟩
  obtain ⟨t, htc, hcov⟩ := countable_cover_nhds (f := box) fun q => (hbox_open q).mem_nhds (hqbox q)
  have hbox_null : ∀ q, volumeMeasure g (frontier A ∩ box q) = 0 := by
    intro q
    set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) q with hφ
    set ε' : ℝ := min (ε q) (‖V q‖ / 2) with hε'
    have hVpos : 0 < ‖V q‖ := norm_pos_iff.2 (hV q)
    have hε'pos : 0 < ε' := lt_min (hε q) (by positivity)
    have hε'V : ε' < ‖V q‖ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    set s₀ : ℝ := r₀ q / (2 * (‖V q‖ + 1)) with hs₀
    have hs₀pos : 0 < s₀ := by have := hr₀ q; positivity
    set Ω : Set (Fin n → ℝ) := Metric.ball (φ q) (r₀ q) with hΩ
    set Aq : Set (Fin n → ℝ) := φ '' (A ∩ box q) with hAq
    have hbox_src : ∀ m ∈ box q, m ∈ φ.source := fun m hm => hm.1
    have hP : ∀ a ∈ Aq, a ∈ Ω → ∀ b ∈ Ω, a - b ∈ openCone (V q) ε' s₀ → b ∈ Aq := by
      rintro a ⟨m, ⟨hmA, hmbox⟩, rfl⟩ haΩ b hbΩ ⟨s, hs0, hs1, hsn⟩
      have hsV : ‖s • V q‖ < r₀ q / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
        calc s * ‖V q‖ < s₀ * ‖V q‖ := mul_lt_mul_of_pos_right hs1 hVpos
          _ < r₀ q / 2 := by
            rw [hs₀, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hr₀ q]
      have hnorm : ‖φ m - b - s • V q‖ < s * ε q :=
        lt_of_lt_of_le hsn (mul_le_mul_of_nonneg_left (min_le_left _ _) hs0.le)
      have hcau := hline q s hs0 hsV b hbΩ (φ m) haΩ hnorm
      rw [φ.left_inv hmbox.1] at hcau
      have hbA := hA m hmA (φ.symm b) hcau
      have hbt' := hbt q hbΩ
      refine ⟨φ.symm b, ⟨hbA, ⟨φ.map_target hbt', ?_⟩⟩, φ.right_inv hbt'⟩
      rw [φ.right_inv hbt']
      rw [hΩ, Metric.mem_ball, dist_eq_norm] at hbΩ
      exact hbΩ
    have hfr : φ '' (frontier A ∩ box q) ⊆ frontier Aq ∩ Ω := by
      rintro _ ⟨m, ⟨hmF, hmbox⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · -- in the closure
        have hmcl : m ∈ closure (A ∩ box q) := by
          have := (hbox_open q).inter_closure ⟨hmbox, frontier_subset_closure hmF⟩
          rwa [inter_comm] at this
        exact ((continuousOn_extChartAt q).continuousWithinAt hmbox.1 |>.mono (fun x hx => hx.2.1)).mem_closure_image hmcl
      · -- not in the interior
        intro hint
        obtain ⟨N, hN, hNopen, hmN⟩ := mem_interior.1 hint
        have hW : IsOpen ((φ ⁻¹' N) ∩ box q) := by
          have : ContinuousOn φ (box q) := (continuousOn_extChartAt q).mono fun x hx => hx.1
          exact this.isOpen_inter_preimage (hbox_open q) hNopen |> fun h => by simpa [inter_comm] using h
        have hmW : m ∈ (φ ⁻¹' N) ∩ box q := ⟨hmN, hmbox⟩
        have hWA : (φ ⁻¹' N) ∩ box q ⊆ A := by
          rintro w ⟨hwN, hwbox⟩
          obtain ⟨a, ⟨haA, habox⟩, hφa⟩ := hN hwN
          have : a = w := φ.injOn habox.1 hwbox.1 hφa
          rwa [this] at haA
        exact hmF.2 (mem_interior.2 ⟨_, hWA, hW, hmW⟩)
      · rw [hΩ, Metric.mem_ball, dist_eq_norm]; exact hmbox.2
    have hnull : volume (frontier Aq ∩ Ω) = 0 :=
      volume_frontier_inter_eq_zero (hV q) hε'pos hε'V hs₀pos Metric.isOpen_ball hP
    have hBmeas : MeasurableSet (frontier A ∩ box q) :=
      isClosed_frontier.measurableSet.inter (hbox_open q).measurableSet
    rw [volumeMeasure_chart g q hBmeas (fun m hm => hm.2.1)]
    exact setLIntegral_measure_zero _ _ (measure_mono_null hfr hnull)
  have hsub : frontier A ⊆ ⋃ q ∈ t, (frontier A ∩ box q) := by
    intro m hm
    have : m ∈ ⋃ q ∈ t, box q := by rw [hcov]; trivial
    simp only [mem_iUnion] at this ⊢
    obtain ⟨q, hq, hmq⟩ := this
    exact ⟨q, hq, hm, hmq⟩
  refine measure_mono_null hsub ?_
  exact (measure_biUnion_null_iff htc).2 fun q _ => hbox_null q

/-- The causal past is a past set: `a ∈ J⁻(x)` and `a ∈ J⁺(b)` give `b ∈ J⁻(x)`. -/
theorem causalPast_isPastSet (x : M) :
    ∀ a ∈ causalPast T x, ∀ b : M, a ∈ causalFuture T b → b ∈ causalPast T x :=
  fun _ ha _ hb => causal_trans T hb ha

/-- **The null horismos, from the push-up property.** Suppose that every point of the interior of
`J⁻(x)` has `x` in the interior of its causal future (a consequence of the push-up lemmas
`I⁺ ∘ J⁺ ⊆ I⁺` and `J⁺ ∘ I⁺ ⊆ I⁺`). Then the set of points of `J⁻(x)`
whose causal future is not a neighbourhood of `x` has volume zero: it lies in the frontier of `J⁻(x)`,
the frontier of a past set. -/
theorem volumeMeasure_causalPast_diff_eq_zero (x : M)
    (hpush : ∀ a : M, a ∈ interior (causalPast T x) → causalFuture T a ∈ 𝓝 x) :
    volumeMeasure g (causalPast T x \ {a | causalFuture T a ∈ 𝓝 x}) = 0 := by
  refine measure_mono_null (t := frontier (causalPast T x)) ?_
    (volumeMeasure_frontier_pastSet_eq_zero T (causalPast_isPastSet T x))
  rintro a ⟨ha, hna⟩
  refine ⟨subset_closure ha, ?_⟩
  intro hint
  exact hna (hpush a hint)

/-- **The push-up property for the interior of `J⁻(x)`.** If `a` is in the interior of `J⁻(x)`, then `x`
is in the interior of `J⁺(a)`: a point `b ∈ I⁺(a)` of the neighbourhood lies in `J⁻(x)`, so `x ∈ J⁺(b)`, hence
`x ∈ I⁺(a)` (first push-up, from the openness of the chronological futures), an open subset of `J⁺(a)`. -/
theorem mem_nhds_causalFuture_of_mem_interior (x : M) {a : M} (ha : a ∈ interior (causalPast T x)) :
    causalFuture T a ∈ 𝓝 x := by
  obtain ⟨b, hbW, hbI⟩ := exists_mem_chronFuture_near T a (mem_interior_iff_mem_nhds.1 ha)
  have hbx : x ∈ causalFuture T b := hbW
  have hx : x ∈ chronFuture T a :=
    chronFuture_causalFuture_trans_of_isOpen T (isOpen_chronFuture_of_reach T) hbI hbx
  exact mem_of_superset ((isOpen_chronFuture_of_reach T a).mem_nhds hx) (chron_subset_causal T a)

/-- **The null horismos, without hypothesis on the push-up**: the set of
points of `J⁻(x)` whose causal future is not a neighbourhood of `x` has volume zero. -/
theorem volumeMeasure_horismos_eq_zero (x : M) :
    volumeMeasure g (causalPast T x \ {a | causalFuture T a ∈ 𝓝 x}) = 0 :=
  volumeMeasure_causalPast_diff_eq_zero T x (fun _ ha => mem_nhds_causalFuture_of_mem_interior T x ha)

end Lightlike.Causal
