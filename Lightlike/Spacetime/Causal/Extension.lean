import Lightlike.Spacetime.Causal.IntegralRays
import Lightlike.Spacetime.Causal.CauchyDomain

/-!
# Extension of a timelike curve to an inextendible one

A future-directed timelike curve `γ` on `[a, b]` of a Hausdorff, second countable manifold without
boundary with a time orientation extends to a future-directed timelike curve without endpoints
that agrees with `γ` on `[a, b]`: follow the integral curves of a smooth future-directed timelike
vector field (`exists_smooth_field`) forwards from `γ b` and backwards from `γ a`; these have no
endpoints (`curveMax_not_hasFutureEndpoint`), and the three pieces are glued
(`IsFutureTimelikeCurve.glue`).

## References

* R. M. Wald, *General Relativity*, University of Chicago Press (1984), Section 8.1.
* S. W. Hawking and G. F. R. Ellis, *The Large Scale Structure of Space-Time*, Cambridge University
  Press (1973), Chapter 6.

The comparison of the statements with these sources at a location is pending.
-/

open Bundle Manifold Set MeasureTheory Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Lightlike

namespace Causal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [SecondCountableTopology M]
  {n : ℕ} {g : LorentzianMetric I M n} (T : TimeOrientation g)

/-- **A timelike curve extends to an inextendible timelike curve.** -/
theorem exists_inextendible_of_timelike {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (h : IsFutureTimelikeCurve T γ (Icc a b)) :
    ∃ (G : ℝ → M) (s : Set ℝ), IsInextendibleFutureTimelike T G s ∧ a ∈ s ∧ b ∈ s ∧
      G a = γ a ∧ G b = γ b := by
  have hfd : FiniteDimensional ℝ E := by
    obtain ⟨e, -⟩ := g.lorentzian (γ a)
    exact Module.Finite.of_basis e
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨X', hXs, hX⟩ := exists_smooth_field T
  have hY : CMDiff 1 (fun x ↦ (⟨x, X' x⟩ : TangentBundle I M)) := hXs.of_le (by norm_num)
  have hYT : ∀ x, T.IsFutureTimelike (X' x) := fun x => hX x
  have hY0 : ∀ x, X' x ≠ 0 := fun x h0 => by
    have := (hYT x).1
    rw [h0] at this
    simp at this
  have hYc := hY.continuous
  obtain ⟨L, DL, hLo, hLc, haL, hLa, hLint, hLnp⟩ := exists_ray_past hY hY0 (γ a) a
  obtain ⟨R, DR, hRo, hRc, hbR, hRb, hRint, hRnf⟩ := exists_ray_future hY hY0 (γ b) b
  have hLT : IsFutureTimelikeCurve T L DL :=
    isFutureTimelikeCurve_of_integralCurve T hYc hYT hLo hLc hLint
  have hRT : IsFutureTimelikeCurve T R DR :=
    isFutureTimelikeCurve_of_integralCurve T hYc hYT hRo hRc hRint
  classical
  set G : ℝ → M := fun t => if t ≤ a then L t else if t ≤ b then γ t else R t with hG
  have hGL : ∀ t, t ≤ a → G t = L t := fun t ht => by simp [hG, ht]
  have hGM : ∀ t, a ≤ t → t ≤ b → G t = γ t := fun t h1 h2 => by
    rcases h1.eq_or_lt with rfl | h1'
    · rw [hGL _ le_rfl, hLa]
    · simp [hG, not_le.2 h1', h2]
  have hGR : ∀ t, b ≤ t → G t = R t := fun t ht => by
    rcases ht.eq_or_lt with rfl | ht'
    · rw [hGM _ hab.le le_rfl, hRb]
    · simp [hG, not_le.2 (hab.trans ht'), not_le.2 ht']
  set S : Set ℝ := {t | (t ≤ a → t ∈ DL) ∧ (b ≤ t → t ∈ DR)} with hS
  have haS : a ∈ S := ⟨fun _ => haL, fun h => absurd h (not_le.2 hab)⟩
  have hbS : b ∈ S := ⟨fun h => absurd h (not_le.2 hab), fun _ => hbR⟩
  have hSo : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro t ⟨h1, h2⟩
    by_cases hta : t ≤ a
    · have htD := h1 hta
      refine mem_of_superset (inter_mem (hLo.mem_nhds htD) (Iio_mem_nhds (hta.trans_lt hab)))
        fun r ⟨hrD, hrb⟩ => ⟨fun _ => hrD, fun hbr => absurd hrb (not_lt.2 hbr)⟩
    · by_cases htb : b ≤ t
      · have htD := h2 htb
        refine mem_of_superset (inter_mem (hRo.mem_nhds htD) (Ioi_mem_nhds (hab.trans_le htb)))
          fun r ⟨hrD, hra⟩ => ⟨fun hra' => absurd hra (not_lt.2 hra'), fun _ => hrD⟩
      · refine mem_of_superset (Ioo_mem_nhds (not_le.1 hta) (not_le.1 htb))
          fun r ⟨hra, hrb⟩ => ⟨fun h => absurd hra (not_lt.2 h), fun h => absurd hrb (not_lt.2 h)⟩
  have hSc : S.OrdConnected := by
    refine ⟨fun u hu v hv r hr => ?_⟩
    by_cases hra : r ≤ a
    · exact ⟨fun _ => hLc.out (hu.1 (hr.1.trans hra)) haL ⟨hr.1, hra⟩,
        fun hbr => absurd (hab.trans_le hbr) (not_lt.2 hra)⟩
    · by_cases hrb : b ≤ r
      · exact ⟨fun h => absurd h hra, fun _ => hRc.out hbR (hv.2 (hrb.trans hr.2)) ⟨hrb, hr.2⟩⟩
      · exact ⟨fun h => absurd h hra, fun h => absurd h hrb⟩
  have hLp : ∀ u v, u < v → v ≤ a → Icc u v ⊆ S → IsFutureTimelikeCurve T L (Icc u v) :=
    fun u v huv hva hsub => hLT.restrict T (fun t ht => (hsub ht).1 (ht.2.trans hva)) huv
  have hRp : ∀ u v, u < v → b ≤ u → Icc u v ⊆ S → IsFutureTimelikeCurve T R (Icc u v) :=
    fun u v huv hbu hsub => hRT.restrict T (fun t ht => (hsub ht).2 (hbu.trans ht.1)) huv
  have hMp : ∀ u v, u < v → a ≤ u → v ≤ b → IsFutureTimelikeCurve T γ (Icc u v) :=
    fun u v huv hau hvb => h.restrict T (Icc_subset_Icc hau hvb) huv
  have hIcc : ∀ u v, u < v → Icc u v ⊆ S → IsFutureTimelikeCurve T G (Icc u v) := by
    intro u v huv hsub
    by_cases hbu : b ≤ u
    · exact (hRp u v huv hbu hsub).congr_Icc T fun t ht => hGR t (hbu.trans ht.1)
    · push Not at hbu
      by_cases hau : a ≤ u
      · by_cases hvb : v ≤ b
        · exact (hMp u v huv hau hvb).congr_Icc T fun t ht => hGM t (hau.trans ht.1) (ht.2.trans hvb)
        · push Not at hvb
          have h1 : IsFutureTimelikeCurve T γ (Icc u b) := hMp u b hbu hau le_rfl
          have h2 : IsFutureTimelikeCurve T R (Icc b v) := hRp b v hvb le_rfl
            (fun t ht => hsub ⟨hbu.le.trans ht.1, ht.2⟩)
          have h3 := IsFutureTimelikeCurve.glue T h1 h2 hbu hvb (hRb.symm)
          refine h3.congr_Icc T fun t ht => ?_
          by_cases htb : t ≤ b
          · simp only [htb, ite_true]; exact hGM t (hau.trans ht.1) htb
          · simp only [htb, ite_false]; exact hGR t (not_le.1 htb).le
      · push Not at hau
        by_cases hva : v ≤ a
        · exact (hLp u v huv hva hsub).congr_Icc T fun t ht => hGL t (ht.2.trans hva)
        · push Not at hva
          have hL1 : IsFutureTimelikeCurve T L (Icc u a) := hLp u a hau le_rfl
            (fun t ht => hsub ⟨ht.1, ht.2.trans hva.le⟩)
          by_cases hvb : v ≤ b
          · have hM1 : IsFutureTimelikeCurve T γ (Icc a v) := hMp a v hva le_rfl hvb
            have h3 := IsFutureTimelikeCurve.glue T hL1 hM1 hau hva hLa
            refine h3.congr_Icc T fun t ht => ?_
            by_cases hta : t ≤ a
            · simp only [hta, ite_true]; exact hGL t hta
            · simp only [hta, ite_false]; exact hGM t (not_le.1 hta).le (ht.2.trans hvb)
          · push Not at hvb
            have hM1 : IsFutureTimelikeCurve T γ (Icc a b) := h
            have h3 := IsFutureTimelikeCurve.glue T hL1 hM1 hau hab hLa
            have hR1 : IsFutureTimelikeCurve T R (Icc b v) := hRp b v hvb le_rfl
              (fun t ht => hsub ⟨hau.le.trans (hab.le.trans ht.1), ht.2⟩)
            have h4 := IsFutureTimelikeCurve.glue T h3 hR1 (hau.trans hab) hvb (by
              have : ¬ b ≤ a := not_le.2 hab
              simp [this, hRb])
            refine h4.congr_Icc T fun t ht => ?_
            by_cases htb : t ≤ b
            · simp only [htb, ite_true]
              by_cases hta : t ≤ a
              · simp only [hta, ite_true]; exact hGL t hta
              · simp only [hta, ite_false]; exact hGM t (not_le.1 hta).le htb
            · simp only [htb, ite_false]; exact hGR t (not_le.1 htb).le
  have hITC : IsFutureTimelikeCurve T G S := isFutureTimelikeCurve_of_Icc T hSo hSc hIcc
  refine ⟨G, S, ⟨hITC, ⟨a, haS⟩, ?_, ?_⟩, haS, hbS, ?_, ?_⟩
  · intro p hp
    refine hRnf p fun U hU => ?_
    obtain ⟨c0, hc0, hc⟩ := hp U hU
    have hmem : max c0 b ∈ DR := by
      rcases le_total c0 b with h1 | h1
      · rwa [max_eq_right h1]
      · rw [max_eq_left h1]; exact hc0.2 h1
    refine ⟨max c0 b, ⟨hmem, mem_Ici.2 (le_max_right _ _)⟩, fun t ht hct => ?_⟩
    have htS : t ∈ S := ⟨fun h => absurd (hab.trans_le ((le_max_right _ _).trans hct)) (not_lt.2 h),
      fun _ => ht.1⟩
    have := hc t htS ((le_max_left _ _).trans hct)
    rwa [hGR t ((le_max_right _ _).trans hct)] at this
  · intro p hp
    refine hLnp p fun U hU => ?_
    obtain ⟨c0, hc0, hc⟩ := hp U hU
    have hmem : min c0 a ∈ DL := by
      rcases le_total c0 a with h1 | h1
      · rw [min_eq_left h1]; exact hc0.1 h1
      · rwa [min_eq_right h1]
    refine ⟨min c0 a, ⟨hmem, mem_Iic.2 (min_le_right _ _)⟩, fun t ht hct => ?_⟩
    have htS : t ∈ S := ⟨fun _ => ht.1, fun h => absurd (hab.trans_le h) (not_lt.2 ht.2)⟩
    have := hc t htS (hct.trans (min_le_left _ _))
    rwa [hGL t ht.2] at this
  · rw [hGL a le_rfl, hLa]
  · rw [hGM b hab.le le_rfl]

/-- **A Cauchy surface is achronal** (on a Hausdorff, second countable manifold without boundary):
a timelike curve from `x` to `y` in the set extends to an inextendible timelike curve, which would
meet the set twice. The hypotheses (no boundary, second countable) match the source (Hawking–Ellis:
a connected paracompact Hausdorff manifold without boundary is second countable); approved by the
maintainers, 18 November 2026. (Hawking–Ellis, Chapter 6; the comparison with the book at its
location is pending.) -/
theorem IsCauchySurface.isAchronal_of_boundaryless {S : Set M} (h : IsCauchySurface T S) :
    IsAchronal T S := by
  rintro x hx y hy ⟨γ, a, b, hab, hγ, e1, e2⟩
  obtain ⟨G, s, hG, has, hbs, hGa, hGb⟩ := exists_inextendible_of_timelike T hab hγ
  obtain ⟨t, -, ht⟩ := h G s hG
  have h1 := ht a ⟨has, by rw [hGa, e1]; exact hx⟩
  have h2 := ht b ⟨hbs, by rw [hGb, e2]; exact hy⟩
  exact hab.ne (h1.trans h2.symm)

end Causal

end Lightlike
