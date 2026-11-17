import Lightlike.Regge.Conv3.HingeLength

/-!
# The hinge term of the Regge action

For a hinge of the Kuhn grid of mesh `ε` with midpoint `v` in a compact `K ⊆ U` and edge class `k`, the product of
the geodesic length `ℓ` of the hinge and its deficit angle `2π - Σ dihedral angles` of the true star is
`-ε³ √(g(v)(w_k, w_k)) c₂(v) + O(ε⁴)`, uniformly in `v` (`hinge_term`). It combines the length of the hinge
(`hinge_length`) with the uniform angle expansion (`hinge_expansion_true`); the second-order coefficient `c₂`
is bounded on `K` because it depends continuously on the base point (`continuousOn_angC2`,
`continuousOn_clsAngC2`).

## Main results

* `hinge_term`: the `O(ε⁴)` expansion of the hinge term.
* `continuousOn_angC2`, `continuousOn_clsAngC2`: continuity of the second-order coefficients.

**Limits.** One edge class at a time, constants not explicit, local in `ε`.
-/

open Real Matrix Lightlike Filter Topology Metric Set
namespace Lightlike.Regge.Conv3
open Lightlike.Geodesic

variable {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ} {U : Set (Fin 3 → ℝ)}

/-- The second-order coefficient of the angle of an incidence depends continuously on the base point. -/
theorem continuousOn_angC2 (hg : IsRiemMetric g U) (σ h : Fin 6) :
    ContinuousOn (fun v => angC2 g v σ h) U := by
  intro v hv
  refine ContinuousAt.continuousWithinAt ?_
  have hn : U ∈ 𝓝 v := hg.coord.isOpen.mem_nhds hv
  have hV := valid_incQ (hg.posDef v hv) σ h
  have hq : ContinuousAt (fun v => incQ g v σ h) v := (continuousOn_incQ hg.coord σ h).continuousAt hn
  have hc : ContinuousAt (fun v => incC g v σ h) v := (continuousOn_incC hg.coord σ h).continuousAt hn
  have hr : ContinuousAt (fun v => incR g v σ h) v := (continuousOn_incR hg.coord σ h).continuousAt hn
  have hDh : ContinuousAt (fun v => Dh (incQ g v σ h, incR g v σ h)) v :=
    ContinuousAt.comp (g := Dh) (f := fun v => (incQ g v σ h, incR g v σ h)) (x := v)
      ((contDiffAt_Dh (p := (incQ g v σ h, incR g v σ h)) hV).continuousAt) (hq.prodMk hr)
  have h2 : ContinuousAt (fderiv ℝ (fderiv ℝ Dsq)) (incQ g v σ h) :=
    (((contDiffAt_Dsq hV).fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).continuousAt
  have h3 : ContinuousAt (fun v => fderiv ℝ (fderiv ℝ Dsq) (incQ g v σ h)) v :=
    ContinuousAt.comp (g := fderiv ℝ (fderiv ℝ Dsq)) (f := fun v => incQ g v σ h) (x := v) h2 hq
  have h4 : ContinuousAt (fun v => fderiv ℝ (fderiv ℝ Dsq) (incQ g v σ h) (incC g v σ h)
      (incC g v σ h)) v := (h3.clm_apply hc).clm_apply hc
  exact hDh.add (continuousAt_const.mul h4)

/-- The second-order coefficient of the class angle sum is continuous in the base point. -/
theorem continuousOn_clsAngC2 (hg : IsRiemMetric g U) (w : Fin 3 → ℝ) :
    ContinuousOn (fun v => clsSum w (angC2 g v)) U := by
  classical
  unfold clsSum
  refine continuousOn_finsetSum _ fun σ _ => continuousOn_finsetSum _ fun h _ => ?_
  by_cases hc : InClass w σ h
  · simp only [hc, ite_true]; exact continuousOn_angC2 hg σ h
  · simp only [hc, ite_false]; exact continuousOn_const

/-- The directions of the seven edge classes are nonzero vectors of sup norm at most `1`. -/
theorem dirs_ne_zero (k : Fin 7) : dirs k ≠ 0 := by
  intro e
  fin_cases k <;> simp [dirs, funext_iff, Fin.forall_fin_succ] at e

/-- The directions of the seven edge classes have sup norm at most `1`. -/
theorem dirs_norm_le (k : Fin 7) : ‖dirs k‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases k <;> fin_cases i <;> simp [dirs]

/-- **The hinge term.** For a Riemannian metric `g` on `U`, a compact `K ⊆ U` and an edge class `k`,
the product of the geodesic length `ℓ` of the hinge and its deficit angle `2π - Σ angles` of the true star
is `-ε³ √(g(v)(w_k, w_k)) c₂(v)` up to `M ε⁴`, uniformly in the hinge midpoint `v ∈ K`. -/
theorem hinge_term (hg : IsRiemMetric g U) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ U) (k : Fin 7) :
    ∃ M r : ℝ, 0 < r ∧ ∀ v ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ r →
      |Geodesic.dist g U (v - (ε / 2) • dirs k) (v + (ε / 2) • dirs k) *
          (2 * π - clsSum (dirs k) (fun σ h => Dsq (trueLen g U v ε σ h)))
        + ε ^ 3 * √(edgeQ g v (dirs k)) * clsSum (dirs k) (angC2 g v)| ≤ M * ε ^ 4 := by
  classical
  by_cases hne : K.Nonempty
  swap
  · exact ⟨0, 1, one_pos, fun v hv => absurd ⟨v, hv⟩ hne⟩
  obtain ⟨C, r1, hr1, hL⟩ := hinge_length hg hK hKU (dirs_ne_zero k) (dirs_norm_le k)
  obtain ⟨M, r2, hr2, hA⟩ := hinge_expansion_true hg hK hKU k
  have hSc : ContinuousOn (fun v => √(edgeQ g v (dirs k))) K :=
    (Real.continuous_sqrt.comp_continuousOn ((continuousOn_edgeQ hg.coord (dirs k)).mono hKU))
  have hTc : ContinuousOn (fun v => |clsSum (dirs k) (angC2 g v)|) K :=
    ((continuousOn_clsAngC2 hg (dirs k)).mono hKU).abs
  obtain ⟨v1, hv1, hS⟩ := hK.exists_isMaxOn hne hSc
  obtain ⟨v2, hv2, hT⟩ := hK.exists_isMaxOn hne hTc
  set S : ℝ := √(edgeQ g v1 (dirs k)) with hSd
  set T : ℝ := |clsSum (dirs k) (angC2 g v2)| with hTd
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hT0 : 0 ≤ T := abs_nonneg _
  refine ⟨S * M + |C| * T + |C| * |M|, min (min r1 r2) 1, lt_min (lt_min hr1 hr2) one_pos,
    fun v hv ε hε hεr => ?_⟩
  have hεr1 : ε ≤ r1 := hεr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεr2 : ε ≤ r2 := hεr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := hεr.trans (min_le_right _ _)
  set ℓ : ℝ := Geodesic.dist g U (v - (ε / 2) • dirs k) (v + (ε / 2) • dirs k) with hℓ
  set s : ℝ := √(edgeQ g v (dirs k)) with hs
  set c : ℝ := clsSum (dirs k) (angC2 g v) with hc
  set A : ℝ := clsSum (dirs k) (fun σ h => Dsq (trueLen g U v ε σ h)) with hAd
  set e : ℝ := ℓ - ε * s with he
  set R : ℝ := A - 2 * π - ε ^ 2 * c with hR
  have he_b : |e| ≤ C * ε ^ 3 := hL v hv ε hε hεr1
  have hR_b : |R| ≤ M * ε ^ 3 := hA v hv ε hε hεr2
  have hs_b : s ≤ S := hS hv
  have hc_b : |c| ≤ T := hT hv
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have eq : ℓ * (2 * π - A) + ε ^ 3 * s * c = -(ε * s * R) - e * ε ^ 2 * c - e * R := by
    rw [he, hR]; ring
  rw [eq]
  have hε3 : ε ^ 3 ≤ ε := by nlinarith [mul_pos hε hε]
  have b1 : |ε * s * R| ≤ ε * S * (M * ε ^ 3) := by
    rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_nonneg hs0]
    have := mul_le_mul hs_b hR_b (abs_nonneg R) hS0
    nlinarith [mul_nonneg hε.le (abs_nonneg R)]
  have b2 : |e * ε ^ 2 * c| ≤ |C| * ε ^ 3 * (ε ^ 2 * T) := by
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hε 2)]
    have h1 : |e| ≤ |C| * ε ^ 3 := he_b.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have := mul_le_mul h1 hc_b (abs_nonneg c) (by positivity)
    nlinarith [pow_pos hε 2]
  have b3 : |e * R| ≤ |C| * ε ^ 3 * (|M| * ε ^ 3) := by
    rw [abs_mul]
    have h1 : |e| ≤ |C| * ε ^ 3 := he_b.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have h2 : |R| ≤ |M| * ε ^ 3 := hR_b.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))
    exact mul_le_mul h1 h2 (abs_nonneg R) (by positivity)
  calc |-(ε * s * R) - e * ε ^ 2 * c - e * R|
      ≤ |ε * s * R| + |e * ε ^ 2 * c| + |e * R| := by
        refine (abs_sub _ _).trans ?_
        refine add_le_add ((abs_sub _ _).trans ?_) le_rfl
        rw [abs_neg]
  _ ≤ ε * S * (M * ε ^ 3) + |C| * ε ^ 3 * (ε ^ 2 * T) + |C| * ε ^ 3 * (|M| * ε ^ 3) :=
        add_le_add (add_le_add b1 b2) b3
  _ ≤ (S * M + |C| * T + |C| * |M|) * ε ^ 4 := by
        have e1 : ε ^ 5 ≤ ε ^ 4 := by nlinarith [pow_pos hε 4]
        have e2 : ε ^ 6 ≤ ε ^ 4 := by nlinarith [pow_pos hε 4, pow_pos hε 5]
        nlinarith [mul_nonneg (abs_nonneg C) hT0, mul_nonneg (abs_nonneg C) (abs_nonneg M),
          pow_pos hε 4, mul_nonneg hS0 (abs_nonneg M)]

end Lightlike.Regge.Conv3
