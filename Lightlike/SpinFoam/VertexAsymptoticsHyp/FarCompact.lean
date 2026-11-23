import Lightlike.Asymptotics.Lorentzian.VertexFixChart
import Lightlike.Asymptotics.Lorentzian.Suppression
import Lightlike.Asymptotics.Lorentzian.VertexLocal

/-!
# The compact part of the far remainder of the Lorentzian vertex (T-SF10-P5)

For smooth cutoffs `χ`, `ψ` with compact supports in the chart domain `U`, both equal to `1` near
each point of the finite critical set `K`, the integral `∫ (ψ - χ) A e^{λ S}` of the Lorentzian
vertex in the fixed charts is `O(λ^{-N})` for every `N`. The amplitude `(ψ - χ) A` is smooth with
compact support, `Re S ≤ 0` there (`re_lorAction_le_zero`), and no critical point of `S` lies in its
support, so `expPhase_suppressed` applies. Source: BDFHP, Sec. 6.4 (`bdfhp-2010`); the statement is
the one of `Tasks/SF/T_SF10_P5.lean`.
-/

open Filter MeasureTheory Lightlike.Oscillatory Lightlike.Asymptotics.EPRL Matrix
open _root_.Asymptotics
open scoped ContDiff

namespace Lightlike.Asymptotics.Lorentzian

set_option linter.unusedVariables false in
/-- **The compact part of the far remainder is `O(λ^{-N})` for every `N`** (hypothesis `hK` is
`CriticalSetIs` with the cutoff `1`: every critical point of `tsupport A` with `Re S = 0` lies in `K`).
Same statement as `Tasks/SF/T_SF10_P5.lean`; the proof applies `expPhase_suppressed` to the smooth
compactly supported amplitude `(ψ - χ) A`, which vanishes near `K`. -/
theorem lorVertex_farRemainder_compact_proof
    {j p : Fin 10 → ℝ} {γ : ℝ} (hj : ∀ k, 0 < j k)
    (hp : ∀ k, p k = γ * j k) {g : BdryData}
    (hξ : ∀ k, ‖firstCol (g k 0)‖ = 1) (hξ' : ∀ k, ‖firstCol (g k 1)‖ = 1)
    (e : (Fin 44 → ℝ) ≃ᵐ ((Fin 4 → Fin 3 → ℂ) × (Fin 10 → ℂ))) (he : MeasurePreserving e volume volume)
    (hl : IsLinearMap ℝ e) {U : Set (Fin 44 → ℝ)} (hU : IsOpen U) (hUc : U ⊆ fixDomain e)
    (hP : ∀ x ∈ U, ∀ k,
      inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((fixVertexChart e x).2 k)) ∈ Complex.slitPlane)
    (hA : ContDiffOn ℝ ∞ (chartAmplitude e) U) (K : Finset (Fin 44 → ℝ))
    (hK : CriticalSetIs j p g e (fun _ => 1) K)
    (χ ψ : (Fin 44 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hχ1 : ∀ x ∈ K, χ =ᶠ[nhds x] fun _ => 1) (hψ1 : ∀ x ∈ K, ψ =ᶠ[nhds x] fun _ => 1) (N : ℕ) :
    (fun lam : ℕ => ∫ x, (((ψ x - χ x : ℝ) : ℂ) * chartAmplitude e x) *
        Complex.exp ((lam : ℝ) * lorChartAction j p g (fixVertexChart e) x)) =O[atTop]
      fun lam : ℕ => ((lam : ℝ) ^ (-(N : ℝ))) := by
  set A := chartAmplitude e with hAdef
  set S := lorChartAction j p g (fixVertexChart e) with hSdef
  set d : (Fin 44 → ℝ) → ℝ := fun x => ψ x - χ x with hd
  set a : (Fin 44 → ℝ) → ℂ := fun x => ((d x : ℝ) : ℂ) * A x with haDef
  have hdU : tsupport d ⊆ U := by
    have h : tsupport d ⊆ tsupport ψ ∪ tsupport χ := tsupport_sub ψ χ
    exact h.trans (Set.union_subset hψU hχU)
  have hsU : tsupport a ⊆ U :=
    (tsupport_mul_subset_left (f := fun x => ((d x : ℝ) : ℂ)) (g := A)).trans
      ((tsupport_comp_subset (by simp) (g := fun r : ℝ => (r : ℂ)) (f := d)).trans hdU)
  have hdsm : ContDiff ℝ ∞ d := hψ.sub hχ
  have ha : ContDiff ℝ ∞ a := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (Complex.ofRealCLM.contDiff.comp hdsm).contDiffAt.mul (hA.contDiffAt (hU.mem_nhds hx))
    · have hz : ∀ᶠ y in nhds x, d y = 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hdU h))
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hz] with y hy
      simp [haDef, hy]
  have hc : HasCompactSupport a := by
    refine (hψc.sub hχc).mono ?_
    intro x hx
    by_contra hdx
    exact hx (by simp [haDef, show d x = 0 from Function.notMem_support.mp hdx])
  have h0 : (0 : ℂ) ∉ Complex.slitPlane := by simp [Complex.slitPlane]
  have hne : ∀ x ∈ tsupport a, ∀ k,
      inner ℂ (spinAct ((fixVertexChart e x).1 (edgeSrc k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
          ((fixVertexChart e x).2 k)) (firstCol (g k 0)) *
        inner ℂ (jMap (firstCol (g k 1)))
          (spinAct ((fixVertexChart e x).1 (edgeTgt k) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
            ((fixVertexChart e x).2 k)) ≠ 0 :=
    fun x hx k h => h0 (h ▸ hP x (hsU hx) k)
  have hRe : ∀ x ∈ tsupport a, (S x).re ≤ 0 := fun x hx =>
    re_lorAction_le_zero (fun k => (hj k).le)
      (fun k h => (left_ne_zero_of_mul (hne x hx k)) (by rw [h]; simp))
      (fun k h => (right_ne_zero_of_mul (hne x hx k)) (by rw [h]; simp))
      hξ hξ' (fun k => left_ne_zero_of_mul (hne x hx k))
      (fun k => right_ne_zero_of_mul (hne x hx k))
  have hnc : ∀ x ∈ tsupport a, (S x).re < 0 ∨ fderiv ℝ S x ≠ 0 := by
    intro x hx
    by_contra hcon
    simp only [not_or, not_lt, not_not] at hcon
    have h1 : tsupport a ⊆ tsupport A :=
      tsupport_mul_subset_right (f := fun x => ((d x : ℝ) : ℂ)) (g := A)
    have hxA : x ∈ tsupport (fun x => (((fun _ : Fin 44 → ℝ => (1 : ℝ)) x : ℝ) : ℂ) * chartAmplitude e x) := by
      simpa using h1 hx
    have hxK : x ∈ K := (hK.1 x hxA).1 ⟨le_antisymm (hRe x hx) hcon.1, hcon.2⟩
    have hzA : a =ᶠ[nhds x] 0 := by
      filter_upwards [hψ1 x hxK, hχ1 x hxK] with y h1 h2
      simp [haDef, hd, h1, h2]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzA) hx
  obtain ⟨S', hS', W, hW, hKW, hSW⟩ := exists_smooth_extension hU
    (lorChartAction_fixVertexChart_contDiffOn e hl j p g hU hUc hP) hc hsU
  have hfd : ∀ x ∈ W, fderiv ℝ S' x = fderiv ℝ S x := fun x hx =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hW.mem_nhds hx) hSW)
  obtain ⟨C, hC⟩ := expPhase_suppressed (S := S') (a := a) hS' ha hc
    (fun x hx => by rw [hSW x (hKW hx)]; exact hRe x hx)
    (fun x hx => by rw [hSW x (hKW hx), hfd x (hKW hx)]; exact hnc x hx) N
  have hint' : ∀ τ : ℝ, (fun x => a x * Complex.exp (τ * S' x)) =
      fun x => a x * Complex.exp (τ * S x) := by
    intro τ; funext x
    by_cases hx : x ∈ tsupport a
    · rw [hSW x (hKW hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with lam hlam
  have hl1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have h := hC (lam : ℝ) hl1
  rw [hint' (lam : ℝ)] at h
  have hpos : (0 : ℝ) ≤ (lam : ℝ) := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos _), Real.rpow_neg hpos, Real.rpow_natCast]
  exact h

end Lightlike.Asymptotics.Lorentzian
