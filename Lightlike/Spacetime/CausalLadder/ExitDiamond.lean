import Lightlike.Spacetime.CausalLadder.ConeCurve
import Lightlike.Spacetime.CausalLadder.CurveContinuity
import Lightlike.Spacetime.CausalLadder.FirstExit
import Lightlike.Spacetime.Causal.BasicRelations
import Lightlike.Spacetime.Causal.CurveOps

/-!
# Diamonds and exits for causal curves

In a chart box `O ⊆ K ⊆ W`, with the chart cone estimate (`ℓ`, `C`), the set
`{q ∈ O | a q + s q / C < δ, -a q + s q / C < δ}` (with `a q = ℓ (φ q) - ℓ (φ x)` and
`s q = ‖φ q - φ x‖`) is causally convex with respect to curves that stay in `O`. For two causal
curves `y ⇝ w ⇝ z` with `y`, `z` in the diamond, either `w` is in the diamond, or a curve leaves `O`:
there are points `m`, `q ∈ K` with `q ∉ O`, causal curves `y ⇝ m ⇝ q` inside `K`, and `z ∈ J⁺(q)`.

Supporting lemma for the causal ladder; no catalogue entry.
-/

open Bundle Manifold Set Filter Topology MeasureTheory
open scoped Manifold ContDiff

namespace Lightlike.Causal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- `a ⇝ b` by a future causal curve with all values in `K`. -/
def ReachIn (K : Set M) (a b : M) : Prop :=
  ∃ (γ : ℝ → M) (s t : ℝ), s ≤ t ∧ IsFutureCausalCurve T γ (Icc s t) ∧ (∀ u ∈ Icc s t, γ u ∈ K) ∧
    γ s = a ∧ γ t = b

/-- A sub-arc of a causal curve: `γ t ∈ J⁺ (γ s)` for `s ≤ t` in the domain. -/
theorem causalFuture_of_subarc {γ : ℝ → M} {a b s t : ℝ} (hγ : IsFutureCausalCurve T γ (Icc a b))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) : γ t ∈ causalFuture T (γ s) := by
  rcases hst.eq_or_lt with rfl | hlt
  · exact self_mem_causalFuture T _
  · exact ⟨γ, s, t, hlt.le, IsCurveWith.mono hγ hs.1 ht.2 hlt, rfl, rfl⟩

/-- A sub-arc of a causal curve that stays in `K` is a `ReachIn` step. -/
theorem reachIn_of_subarc {γ : ℝ → M} {a b s t : ℝ} {K : Set M}
    (hγ : IsFutureCausalCurve T γ (Icc a b)) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (hK : ∀ u ∈ Icc s t, γ u ∈ K) : ReachIn T K (γ s) (γ t) := by
  rcases hst.eq_or_lt with rfl | hlt
  · exact ⟨fun _ => γ s, 0, 0, le_rfl, isCurveWith_const _ _ 0, fun u hu => by
      simpa [(mem_Icc.1 hu).1.antisymm (mem_Icc.1 hu).2] using hK s ⟨le_rfl, le_rfl⟩, rfl, rfl⟩
  · exact ⟨γ, s, t, hlt.le, IsCurveWith.mono hγ hs.1 ht.2 hlt, hK, rfl, rfl⟩

/-- **Exit or diamond.** See the module docstring. -/
theorem exit_or_diamond (p : M) {W : Set M} {ℓ : E →L[ℝ] ℝ} {C : ℝ} (hC : 0 < C)
    (hest : ∀ (γ : ℝ → M) (a b : ℝ), IsFutureCausalCurve T γ (Icc a b) → (∀ t ∈ Icc a b, γ t ∈ W) →
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
          ℓ (extChartAt I p (γ s)) ≤ ℓ (extChartAt I p (γ t)) ∧
          ‖extChartAt I p (γ t) - extChartAt I p (γ s)‖ ≤
            C * (ℓ (extChartAt I p (γ t)) - ℓ (extChartAt I p (γ s))))
    {O K : Set M} (hO : IsOpen O) (hOK : O ⊆ K) (hKW : K ⊆ W) (hclK : closure O ⊆ K) (x : M)
    {δ : ℝ} {Vd : Set M}
    (hVd : Vd = {q | q ∈ O ∧ ℓ (extChartAt I p q) - ℓ (extChartAt I p x) +
        ‖extChartAt I p q - extChartAt I p x‖ / C < δ ∧
      -(ℓ (extChartAt I p q) - ℓ (extChartAt I p x)) +
        ‖extChartAt I p q - extChartAt I p x‖ / C < δ})
    {y z w : M} (hy : y ∈ Vd) (hz : z ∈ Vd) (hyw : w ∈ causalFuture T y)
    (hwz : z ∈ causalFuture T w) :
    w ∈ Vd ∨ ∃ m q : M, ReachIn T K y m ∧ ReachIn T K m q ∧ q ∈ K ∧ q ∉ O ∧
      z ∈ causalFuture T q := by
  obtain ⟨γ₁, a₁, b₁, hab₁, hγ₁, e₁, e₂⟩ := hyw
  obtain ⟨γ₂, a₂, b₂, hab₂, hγ₂, e₃, e₄⟩ := hwz
  rw [hVd] at hy hz
  have hyO : y ∈ O := hy.1
  have hzO : z ∈ O := hz.1
  -- the first curve
  by_cases h1 : ∀ t ∈ Icc a₁ b₁, γ₁ t ∈ O
  · by_cases h2 : ∀ t ∈ Icc a₂ b₂, γ₂ t ∈ O
    · -- both curves stay in `O`: `w` is in the diamond
      left
      rw [hVd]
      have hwO : w ∈ O := by rw [← e₂]; exact h1 b₁ ⟨hab₁, le_rfl⟩
      have c1 := hest γ₁ a₁ b₁ hγ₁ (fun t ht => hKW (hOK (h1 t ht))) a₁ ⟨le_rfl, hab₁⟩ b₁
        ⟨hab₁, le_rfl⟩ hab₁
      have c2 := hest γ₂ a₂ b₂ hγ₂ (fun t ht => hKW (hOK (h2 t ht))) a₂ ⟨le_rfl, hab₂⟩ b₂
        ⟨hab₂, le_rfl⟩ hab₂
      rw [e₁, e₂] at c1
      rw [e₃, e₄] at c2
      obtain ⟨hy1, hy2⟩ := hy.2
      obtain ⟨hz1, hz2⟩ := hz.2
      set φ := extChartAt I p
      have t1 : ‖φ w - φ x‖ ≤ ‖φ y - φ x‖ + ‖φ w - φ y‖ := by
        have := norm_add_le (φ y - φ x) (φ w - φ y)
        simpa using this
      have t2 : ‖φ w - φ x‖ ≤ ‖φ z - φ x‖ + ‖φ z - φ w‖ := by
        have := norm_add_le (φ z - φ x) (φ w - φ z)
        rw [norm_sub_rev (φ w) (φ z)] at this
        simpa using this
      refine ⟨hwO, ?_, ?_⟩
      · have hA : ‖φ w - φ x‖ / C ≤ ‖φ z - φ x‖ / C + (ℓ (φ z) - ℓ (φ w)) := by
          rw [div_le_iff₀ hC, add_mul, div_mul_cancel₀ _ hC.ne']
          linarith [t2, c2.2, mul_comm C (ℓ (φ z) - ℓ (φ w))]
        linarith [hA, hz1]
      · have hA : ‖φ w - φ x‖ / C ≤ ‖φ y - φ x‖ / C + (ℓ (φ w) - ℓ (φ y)) := by
          rw [div_le_iff₀ hC, add_mul, div_mul_cancel₀ _ hC.ne']
          linarith [t1, c1.2, mul_comm C (ℓ (φ w) - ℓ (φ y))]
        linarith [hA, hy2]
    · -- the second curve leaves `O`
      right
      push Not at h2
      obtain ⟨t₀, ht₀, hnot⟩ := h2
      obtain ⟨t₂, ht₂, hout, hbefore, hcl⟩ := exists_first_exit
        hγ₂.lipschitz.continuousOn hO (by rw [e₃, ← e₂]; exact h1 b₁ ⟨hab₁, le_rfl⟩) ⟨t₀, ht₀, hnot⟩
      have ht₂' : t₂ ∈ Icc a₂ b₂ := ⟨ht₂.1.le, ht₂.2⟩
      refine ⟨w, γ₂ t₂, ?_, ?_, hclK hcl, hout, ?_⟩
      · have := reachIn_of_subarc T hγ₁ (s := a₁) (t := b₁) (K := K) ⟨le_rfl, hab₁⟩
          ⟨hab₁, le_rfl⟩ hab₁ (fun u hu => hOK (h1 u hu))
        rwa [e₁, e₂] at this
      · have := reachIn_of_subarc T hγ₂ (s := a₂) (t := t₂) (K := K) ⟨le_rfl, hab₂⟩ ht₂'
          ht₂.1.le (fun u hu => by
            rcases hu.2.eq_or_lt with h | h
            · rw [h]; exact hclK hcl
            · exact hOK (hbefore u ⟨hu.1, h⟩))
        rwa [e₃] at this
      · have := causalFuture_of_subarc T hγ₂ ht₂' ⟨hab₂, le_rfl⟩ ht₂.2
        rwa [e₄] at this
  · -- the first curve leaves `O`
    right
    push Not at h1
    obtain ⟨t₀, ht₀, hnot⟩ := h1
    obtain ⟨t₁, ht₁, hout, hbefore, hcl⟩ := exists_first_exit hγ₁.lipschitz.continuousOn hO
      (by rw [e₁]; exact hyO) ⟨t₀, ht₀, hnot⟩
    have ht₁' : t₁ ∈ Icc a₁ b₁ := ⟨ht₁.1.le, ht₁.2⟩
    refine ⟨y, γ₁ t₁, ?_, ?_, hclK hcl, hout, ?_⟩
    · exact ⟨fun _ => y, 0, 0, le_rfl, isCurveWith_const _ _ 0, fun u _ => hOK hyO, rfl, rfl⟩
    · have := reachIn_of_subarc T hγ₁ (s := a₁) (t := t₁) (K := K) ⟨le_rfl, hab₁⟩ ht₁'
        ht₁.1.le (fun u hu => by
          rcases hu.2.eq_or_lt with h | h
          · rw [h]; exact hclK hcl
          · exact hOK (hbefore u ⟨hu.1, h⟩))
      rwa [e₁] at this
    · have h3 := causalFuture_of_subarc T hγ₁ ht₁' ⟨hab₁, le_rfl⟩ ht₁.2
      rw [e₂] at h3
      exact causal_trans T h3 ⟨γ₂, a₂, b₂, hab₂, hγ₂, e₃, e₄⟩

end Lightlike.Causal
