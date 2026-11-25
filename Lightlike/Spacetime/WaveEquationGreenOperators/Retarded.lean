import Mathlib
import Lightlike.Spacetime.WaveEquationGreenOperators.Model

/-!
# The retarded Green operator of the `1+1` wave operator: calculus lemmas

Convolution with the quadrant indicator commutes with directional derivatives, and the inverse
of `∂_u`, `∂_v` on compactly supported smooth functions is the primitive from `-∞`.
-/

open Function MeasureTheory Set Filter Topology
open scoped ContDiff Convolution

namespace Lightlike.Rows.G1_059

theorem dirDeriv_retardedFun {f : ℝ × ℝ → ℝ} (hf : f ∈ testFns) (w : ℝ × ℝ) (x : ℝ × ℝ) :
    fderiv ℝ (retardedFun f) x w = retardedFun (fun p => fderiv ℝ f p w) x := by
  have h := hf.2.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) (hf.1.of_le (by simp))
    quadrant_locInt x
  rw [retardedFun, h.fderiv]
  have hex := (hf.2.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℝ).precompL (ℝ × ℝ))
    (hf.1.continuous_fderiv (by simp)) quadrant_locInt x
  rw [convolution_def, retardedFun, convolution_def, ContinuousLinearMap.integral_apply hex]
  rfl

theorem dirDeriv_mem_testFns {f : ℝ × ℝ → ℝ} (hf : f ∈ testFns) (w : ℝ × ℝ) :
    (fun p => fderiv ℝ f p w) ∈ testFns :=
  ⟨contDiff_dirDeriv hf.1 w, hf.2.fderiv_apply ℝ w⟩

/-- Fundamental theorem of calculus in the `v` direction for a test function. -/
theorem integral_Iic_snd {g : ℝ × ℝ → ℝ} (hg : g ∈ testFns) (a v : ℝ) :
    ∫ b in Iic v, fderiv ℝ g (a, b) (0, 1) = g (a, v) := by
  have hφ : ContDiff ℝ 1 (fun s => g (a, s)) :=
    (hg.1.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)
  have hcs : HasCompactSupport (fun s => g (a, s)) :=
    HasCompactSupport.intro (hg.2.isCompact.image continuous_snd)
      (fun s hs => image_eq_zero_of_notMem_tsupport (fun h => hs ⟨_, h, rfl⟩))
  have hd : ∀ s, fderiv ℝ g (a, s) (0, 1) = deriv (fun s => g (a, s)) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => (a, s)) ((0, 1) : ℝ × ℝ) s :=
      (hasDerivAt_const s a).prodMk (hasDerivAt_id s)
    have h2 := ((hg.1.differentiable (by simp)) (a, s)).hasFDerivAt.comp_hasDerivAt s h1
    exact h2.deriv.symm
  simp_rw [hd]
  exact hcs.integral_Iic_deriv_eq hφ v

/-- Fundamental theorem of calculus in the `u` direction for a test function. -/
theorem integral_Iic_fst {g : ℝ × ℝ → ℝ} (hg : g ∈ testFns) (u b : ℝ) :
    ∫ a in Iic u, fderiv ℝ g (a, b) (1, 0) = g (u, b) := by
  have hφ : ContDiff ℝ 1 (fun s => g (s, b)) :=
    (hg.1.of_le (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have hcs : HasCompactSupport (fun s => g (s, b)) :=
    HasCompactSupport.intro (hg.2.isCompact.image continuous_fst)
      (fun s hs => image_eq_zero_of_notMem_tsupport (fun h => hs ⟨_, h, rfl⟩))
  have hd : ∀ s, fderiv ℝ g (s, b) (1, 0) = deriv (fun s => g (s, b)) s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => (s, b)) ((1, 0) : ℝ × ℝ) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s b)
    have h2 := ((hg.1.differentiable (by simp)) (s, b)).hasFDerivAt.comp_hasDerivAt s h1
    exact h2.deriv.symm
  simp_rw [hd]
  exact hcs.integral_Iic_deriv_eq hφ u

/-- The retarded convolution is the iterated integral over the past quadrant:
`(f ⋆ Q)(u, v) = ∫_{a ≤ u} ∫_{b ≤ v} f(a, b)`. -/
theorem retardedFun_eq {h : ℝ × ℝ → ℝ} (hh : h ∈ testFns) (u v : ℝ) :
    retardedFun h (u, v) = ∫ a in Iic u, ∫ b in Iic v, h (a, b) := by
  have hint : Integrable h (volume : Measure (ℝ × ℝ)) :=
    (hh.1.continuous).integrable_of_hasCompactSupport hh.2
  have hkey : (fun t : ℝ × ℝ => (ContinuousLinearMap.mul ℝ ℝ) (h t) (quadrant ((u, v) - t))) =
      (Iic u ×ˢ Iic v).indicator h := by
    funext t
    by_cases ht : t ∈ Iic u ×ˢ Iic v
    · have : 0 ≤ (u, v).1 - t.1 ∧ 0 ≤ (u, v).2 - t.2 := by
        simp only [mem_prod, mem_Iic] at ht
        exact ⟨sub_nonneg.2 ht.1, sub_nonneg.2 ht.2⟩
      rw [Set.indicator_of_mem ht, quadrant, Set.indicator_of_mem (show (u, v) - t ∈
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from this)]
      simp
    · have : ¬ (0 ≤ (u, v).1 - t.1 ∧ 0 ≤ (u, v).2 - t.2) := by
        simp only [mem_prod, mem_Iic, not_and_or, not_le] at ht
        simp only [not_and_or, not_le, sub_neg]
        rcases ht with h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
      rw [Set.indicator_of_notMem ht, quadrant, Set.indicator_of_notMem (show (u, v) - t ∉
        {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} from this)]
      simp
  rw [retardedFun, convolution_def, hkey, integral_indicator (measurableSet_Iic.prod measurableSet_Iic),
    Measure.volume_eq_prod, setIntegral_prod _ hint.integrableOn]

/-- **Left inverse**: `G⁺ (P f) = f` for a test function `f`, with `P = ∂_v ∂_u`. -/
theorem retardedFun_wave {f : ℝ × ℝ → ℝ} (hf : f ∈ testFns) :
    retardedFun (fun p => fderiv ℝ (fun q => fderiv ℝ f q (1, 0)) p (0, 1)) = f := by
  have hg := dirDeriv_mem_testFns hf (1, 0)
  funext ⟨u, v⟩
  rw [retardedFun_eq (dirDeriv_mem_testFns hg (0, 1))]
  simp_rw [integral_Iic_snd hg]
  exact integral_Iic_fst hf u v

/-- The causal future in null coordinates: `J⁺ S = {p | ∃ s ∈ S, s.u ≤ p.u ∧ s.v ≤ p.v}`. -/
def causalFuture (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := {p | ∃ s ∈ S, s.1 ≤ p.1 ∧ s.2 ≤ p.2}

/-- The retarded Green operator `f ↦ f ⋆ Q` as a linear map from test functions to smooth
functions. -/
noncomputable def retarded : testFns →ₗ[ℝ] smoothFns where
  toFun f := ⟨retardedFun f, retardedFun_smooth f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact ((f.2.2.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) f.2.1.continuous
      quadrant_locInt).add_distrib
      (g.2.2.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) g.2.1.continuous
      quadrant_locInt))
  map_smul' c f := by
    apply Subtype.ext
    exact smul_convolution

/-- `P (G⁺ f) = f`. -/
theorem wave_retarded (f : testFns) : wave (retarded f) = ⟨f, testFns_le f.2⟩ := by
  apply Subtype.ext
  funext x
  have h1 : (fun q => fderiv ℝ (retardedFun f) q (1, 0)) =
      retardedFun (fun p => fderiv ℝ (f : ℝ × ℝ → ℝ) p (1, 0)) :=
    funext fun q => dirDeriv_retardedFun f.2 _ q
  show fderiv ℝ (fun q => fderiv ℝ (retardedFun f) q (1, 0)) x (0, 1) = (f : ℝ × ℝ → ℝ) x
  rw [h1, dirDeriv_retardedFun (dirDeriv_mem_testFns f.2 _), retardedFun_wave f.2]

/-- `G⁺ (P g) = g` for test functions. -/
theorem retarded_wave (g f : testFns) (h : wave ⟨g, testFns_le g.2⟩ = ⟨f, testFns_le f.2⟩) :
    (retarded f : ℝ × ℝ → ℝ) = g := by
  have h' : (fun p => fderiv ℝ (fun q => fderiv ℝ (g : ℝ × ℝ → ℝ) q (1, 0)) p (0, 1)) = f :=
    congrArg Subtype.val h
  show retardedFun f = g
  rw [← h']
  exact retardedFun_wave g.2

/-- Support rule for `G⁺`: `supp (G⁺ f) ⊆ J⁺ (supp f)`. -/
theorem support_retarded (f : testFns) :
    support ((retarded f : smoothFns) : ℝ × ℝ → ℝ) ⊆ causalFuture (support (f : ℝ × ℝ → ℝ)) := by
  intro p hp
  have h := support_convolution_subset (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) hp
  obtain ⟨s, hs, q, hq, rfl⟩ := h
  have hq' : q ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := support_indicator_subset hq
  exact ⟨s, hs, by simpa using hq'.1, by simpa using hq'.2⟩

/-- **The retarded Green operator of the `1+1` wave operator exists**: `G⁺ = f ↦ f ⋆ Q` is a
Green operator for `P = ∂_v ∂_u` with the support rule `J⁺` (cf. bgp-2007, §3.4). -/
theorem isGreenOperator_retarded :
    IsGreenOperator smoothFns testFns testFns_le wave causalFuture retarded where
  right_inv := wave_retarded
  left_inv := retarded_wave
  support_subset := support_retarded

end Lightlike.Rows.G1_059
