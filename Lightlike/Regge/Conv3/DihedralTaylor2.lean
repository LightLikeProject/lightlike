import Lightlike.Regge.Conv3.DihedralTaylor
import Lightlike.Regge.Linear.Taylor1DOn

/-!
# A uniform third-order Taylor bound for the dihedral angle in the squared lengths

The first-order bound `dihSq_taylor` is not enough to capture the second-order term of a deficit
angle: a perturbation of the squared lengths that is itself of first order in the mesh size
contributes through the Hessian. Here the expansion is carried one order further, with remainder
`M ‖δ‖³`, uniformly on compact sets of admissible squared lengths.

## Main results

* `taylor3_uniform`: for a `C³` function on an open set of a proper normed space `E` (for instance `Fin 6 → ℝ`) and a compact subset,
  `|F (L + δ) - F L - F'(L) δ - ½ F''(L)(δ, δ)| ≤ M ‖δ‖³`, uniformly.
* `contDiffAt_Dsq_all`: the dihedral angle `Dsq` is smooth, of every order `n`, at every admissible tuple.
* `contDiffAt_Dsq`: the special case `C³`.
* `fderiv_Dsq`: its derivative is the first variation `Dh`.
* `dihSq_taylor3`: the bound for `Dsq` on compact sets of admissible tuples.
-/

open Real Set Metric Lightlike.Regge.Linear

namespace Lightlike.Regge.Conv3

/-- **A uniform third-order Taylor bound.** For `F` of class `C³` on an open set `V` of
a proper normed space `E` (for instance `Fin 6 → ℝ`) and a compact `K ⊆ V`, there are `M` and `r > 0` such that for `L ∈ K`, `‖δ‖ ≤ r`,
`|F (L + δ) - F L - F'(L) δ - ½ F''(L)(δ, δ)| ≤ M ‖δ‖³`. -/
theorem taylor3_uniform {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : E → ℝ} {V : Set E} (hV : IsOpen V)
    (hF : ContDiffOn ℝ 3 F V) {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ M r : ℝ, 0 < r ∧ ∀ L ∈ K, ∀ δ : E, ‖δ‖ ≤ r →
      |F (L + δ) - F L - fderiv ℝ F L δ - (1 / 2) * fderiv ℝ (fderiv ℝ F) L δ δ| ≤ M * ‖δ‖ ^ 3 := by
  obtain ⟨ρ, hρ, hρV⟩ := hK.exists_cthickening_subset_open hV hKV
  have hK' : IsCompact (cthickening ρ K) := hK.cthickening
  have h1 : ContDiffOn ℝ 2 (fderiv ℝ F) V := hF.fderiv_of_isOpen hV (by norm_num)
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ (fderiv ℝ F)) V := h1.fderiv_of_isOpen hV (by norm_num)
  have h3 : ContinuousOn (fun x => ‖iteratedFDeriv ℝ 3 F x‖) V := by
    have := hF.continuousOn_iteratedFDerivWithin (m := 3) le_rfl hV.uniqueDiffOn
    exact (this.congr (iteratedFDerivWithin_of_isOpen 3 hV).symm).norm
  obtain ⟨B, hB⟩ := hK'.bddAbove_image (h3.mono hρV)
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  refine ⟨B', ρ, hρ, fun L hL δ hδ => ?_⟩
  have hball : ∀ t ∈ Icc (0 : ℝ) 1, L + t • δ ∈ closedBall L ρ := fun t ht => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, norm_nonneg δ]
  have hbc : closedBall L ρ ⊆ cthickening ρ K := closedBall_subset_cthickening hL ρ
  have hinV : ∀ t ∈ Icc (0 : ℝ) 1, L + t • δ ∈ V := fun t ht => hρV (hbc (hball t ht))
  have lin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => L + t • δ) δ t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const δ).const_add L
  have dF : ∀ x ∈ V, HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    ((hF.differentiableOn (by norm_num)) x hx |>.differentiableAt (hV.mem_nhds hx)).hasFDerivAt
  have dF1 : ∀ x ∈ V, HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x := fun x hx =>
    ((h1.differentiableOn (by norm_num)) x hx |>.differentiableAt (hV.mem_nhds hx)).hasFDerivAt
  have G1 : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => F (L + t • δ)) (fderiv ℝ F (L + t • δ) δ) t := fun t ht =>
    (dF _ (hinV t ht)).comp_hasDerivAt t (lin t)
  have G2 : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => fderiv ℝ F (L + t • δ) δ)
        (fderiv ℝ (fderiv ℝ F) (L + t • δ) δ δ) t := fun t ht => by
    have a := (dF1 _ (hinV t ht)).comp_hasDerivAt t (lin t)
    have b := a.clm_apply (hasDerivAt_const t δ)
    simpa using b
  have dP : ∀ x ∈ V, HasFDerivAt (iteratedFDeriv ℝ 2 F) (fderiv ℝ (iteratedFDeriv ℝ 2 F) x) x := by
    intro x hx
    have := hF.differentiableOn_iteratedFDerivWithin (m := 2) (by norm_num) hV.uniqueDiffOn
    exact (((this.congr (iteratedFDerivWithin_of_isOpen 2 hV).symm) x hx).differentiableAt
      (hV.mem_nhds hx)).hasFDerivAt
  have G3 : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ 2 F (L + t • δ) ![δ, δ])
        (fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ) δ ![δ, δ]) t := fun t ht => by
    have a := (dP _ (hinV t ht)).comp_hasDerivAt t (lin t)
    have b := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![δ, δ]).hasFDerivAt
      ).comp_hasDerivAt t a
    exact b
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1,
      |fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ) δ ![δ, δ]| ≤ (B' * ‖δ‖ ^ 3) * t ^ 0 := by
    intro t ht
    have hn : ‖fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ)‖ ≤ B' := by
      rw [norm_fderiv_iteratedFDeriv]
      exact (hB ⟨_, hbc (hball t ht), rfl⟩).trans (le_max_left _ _)
    have e1 := ContinuousLinearMap.le_opNorm (fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ)) δ
    have e2 := ContinuousMultilinearMap.le_opNorm
      (fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ) δ) ![δ, δ]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at e2
    rw [Real.norm_eq_abs] at *
    calc _ ≤ ‖fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ) δ‖ * (‖δ‖ * ‖δ‖) := by
          rw [← Real.norm_eq_abs]; exact e2
      _ ≤ (‖fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ)‖ * ‖δ‖) * (‖δ‖ * ‖δ‖) := by gcongr
      _ ≤ (B' * ‖δ‖) * (‖δ‖ * ‖δ‖) := by gcongr
      _ = _ := by ring
  have G2' : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ 2 F (L + t • δ) ![δ, δ])
        (fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ) δ ![δ, δ]) t := G3
  have hQ : ∀ x, iteratedFDeriv ℝ 2 F x ![δ, δ] = fderiv ℝ (fderiv ℝ F) x δ δ := fun x => by
    simp [iteratedFDeriv_two_apply]
  have hL3 : ∀ t ∈ Icc (0 : ℝ) 1,
      |fderiv ℝ (fderiv ℝ F) (L + t • δ) δ δ - fderiv ℝ (fderiv ℝ F) (L + (0 : ℝ) • δ) δ δ| ≤
        (B' * ‖δ‖ ^ 3) * t := fun t ht => by
    have := abs_le_of_deriv_le_on (F := fun t : ℝ => iteratedFDeriv ℝ 2 F (L + t • δ) ![δ, δ] -
        iteratedFDeriv ℝ 2 F (L + (0 : ℝ) • δ) ![δ, δ])
      (F' := fun t => fderiv ℝ (iteratedFDeriv ℝ 2 F) (L + t • δ) δ ![δ, δ]) (c := B' * ‖δ‖ ^ 3)
      (m := 0) (fun t ht => (G3 t ht).sub_const _) (by simp) hbd t ht
    simpa [hQ] using this
  have := taylor2_line_on G1 G2 hL3
  have h6 : 0 ≤ B' * ‖δ‖ ^ 3 := by positivity
  simp only [one_smul, zero_smul, add_zero] at this
  have h7 := abs_le.mp this
  rw [abs_le]
  constructor <;> linarith [h7.1, h7.2]

/-- **The dihedral angle `Dsq` is smooth** (of every order `n`) at every admissible tuple. -/
theorem contDiffAt_Dsq_all (n : ℕ∞) {L : Fin 6 → ℝ} (hL : Valid L) : ContDiffAt ℝ n Dsq L := by
  obtain ⟨ha, h1, h2, h3⟩ := hL
  have hc1 : cosSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) ≠ 1 := fun h => by
    rw [h] at h3; norm_num at h3
  have hc2 : cosSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) ≠ -1 := fun h => by
    rw [h] at h3; norm_num at h3
  have ha' := ha.ne'
  have hpp : 0 < Pp (L 0) (L 1) (L 2) * Pp (L 0) (L 3) (L 4) := mul_pos h1 h2
  have hs : √(Pp (L 0) (L 1) (L 2) * Pp (L 0) (L 3) (L 4)) ≠ 0 := (sqrt_pos.mpr hpp).ne'
  have hc : ContDiffAt ℝ n (fun L : Fin 6 → ℝ => cosSq (L 0) (L 1) (L 2) (L 3) (L 4) (L 5)) L := by
    unfold cosSq Nn
    unfold Pp at hs hpp h1 h2 ⊢
    fun_prop (disch := first | assumption | positivity | skip)
  exact (Real.contDiffAt_arccos hc2 hc1).comp L hc

/-- The dihedral angle `Dsq` is `C³` at every admissible tuple. -/
theorem contDiffAt_Dsq {L : Fin 6 → ℝ} (hL : Valid L) : ContDiffAt ℝ 3 Dsq L :=
  contDiffAt_Dsq_all 3 hL

/-- The derivative of `Dsq` is the first variation `Dh`. -/
theorem fderiv_Dsq {L : Fin 6 → ℝ} (δ : Fin 6 → ℝ) (hL : Valid L) :
    fderiv ℝ Dsq L δ = Dh (L, δ) := by
  have hd : DifferentiableAt ℝ Dsq L := (contDiffAt_Dsq hL).differentiableAt (by norm_num)
  have hd' : HasFDerivAt Dsq (fderiv ℝ Dsq L) (L + (0 : ℝ) • δ) := by
    simpa using hd.hasFDerivAt
  have h := hd'.comp_hasDerivAt (0 : ℝ) (f := fun ε : ℝ => L + ε • δ)
    (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add L)
  have h2 := hasDerivAt_Dsq δ hL
  have h' : HasDerivAt (fun ε : ℝ => Dsq (L + ε • δ)) (fderiv ℝ Dsq L δ) 0 := h
  exact h'.unique h2

/-- **Uniform third-order bound for the dihedral angle.** On a compact set `K` of admissible
squared-length tuples there are `M` and `r > 0` such that
`|Dsq (L + δ) - Dsq L - Dh (L, δ) - ½ D²Dsq(L)(δ, δ)| ≤ M ‖δ‖³` for `L ∈ K`, `‖δ‖ ≤ r`. -/
theorem dihSq_taylor3 {K : Set (Fin 6 → ℝ)} (hK : IsCompact K) (hKV : ∀ L ∈ K, Valid L) :
    ∃ M r : ℝ, 0 < r ∧ ∀ L ∈ K, ∀ δ : Fin 6 → ℝ, ‖δ‖ ≤ r →
      |Dsq (L + δ) - Dsq L - Dh (L, δ) - (1 / 2) * fderiv ℝ (fderiv ℝ Dsq) L δ δ| ≤
        M * ‖δ‖ ^ 3 := by
  have hF : ContDiffOn ℝ 3 Dsq {L | Valid L} := fun L hL =>
    (contDiffAt_Dsq hL).contDiffWithinAt
  obtain ⟨M, r, hr, h⟩ := taylor3_uniform isOpen_valid hF hK (fun L hL => hKV L hL)
  refine ⟨M, r, hr, fun L hL δ hδ => ?_⟩
  have := h L hL δ hδ
  rwa [fderiv_Dsq δ (hKV L hL)] at this

end Lightlike.Regge.Conv3
