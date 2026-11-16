import Lightlike.Regge.Linear3.PeriodicDivergences

/-!
# The `η²` coefficient of the integrated curvature density of `1 + η h` on the 3-torus

For a smooth symmetric `ℤ³`-periodic matrix field `h` on `ℝ³`, the `η²` coefficient of the cube integral of the
scalar-curvature density `(R/2) √det` of the metric `1 + η h` is `½ ∫ fpDens (∂h)`, the Fierz–Pauli density, with an
`O(|η|³)` remainder (`eh_eta_sq_coeff`). The proof applies the uniform second-order expansion `feta_expansion_dom`
pointwise to the jet of `h`, identifies the density with `Feta` of the jet (`Feta_eq`), and integrates, using the vanishing
integral of `F₁` and `∫ F₂ = ∫ fpDens` of `PeriodicDivergences`.

## Main results

* `eh_eta_sq_coeff`: `|∫ (R/2) √det (1 + η h) - (η²/2) ∫ fpDens (∂h)| ≤ C |η|³` for small `η`.
* `F1_jet`, `F2_jet`, `continuous_F1_jet`, `continuous_F2_jet`: the coefficients along a field.

**Limits.** Dimension 3; the unit cube and periodic `C^∞` symmetric fields only; the remainder constant is not
explicit. This is the expansion of the integrated density of `1 + η h` in `η`; it is not a statement about the Regge action,
about interpolated or geodesic edge lengths, or about a limit of triangulations. Two parts of the 3D linearization
(RC3) are still open: the envelope step relating the geodesic edge lengths to the interpolated ones, and the 3D
wrong-model control. Trust check: `eh_eta_sq_coeff_zero` (the zero field satisfies the hypotheses); the value of the
coefficient for a non-zero field is only checked numerically (`scripts/regge/regge3d_linearized_check.py`).
-/

open Real Finset MeasureTheory
open scoped ContDiff
namespace Lightlike.Regge.Linear3
open Lightlike.Regge Lightlike.Regge.Conv3

section EH3b

variable {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}

/-- The measure of the unit cube is one. -/
theorem volume_unitCube' : volume unitCube = 1 := by
  have hbox : unitCube = Set.Icc (0 : Fin 3 → ℝ) 1 := by
    unfold unitCube; rw [Set.pi_univ_Icc]; rfl
  rw [hbox]
  simp [Real.volume_Icc_pi]

/-- The measure of the unit cube is one. -/
theorem volume_unitCube : volume.real unitCube = 1 := by
  have hbox : unitCube = Set.Icc (0 : Fin 3 → ℝ) 1 := by
    unfold unitCube; rw [Set.pi_univ_Icc]; rfl
  rw [hbox]
  simp [Measure.real, Real.volume_Icc_pi]

/-- The first coefficient along the jet of a field is half the divergence of `S1field`. -/
theorem F1_jet (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (y : Fin 3 → ℝ) :
    F1 (jetOf hf y) = 1 / 2 * ∑ i, fderiv ℝ (S1field hf i) y (Pi.single i 1) := by
  rw [F1_eq _ (jet_symm hsm hsymm y).2.2.1]
  show _ = 1 / 2 * ∑ i, pd1 (S1field hf i) y i
  rw [div_S1field hsm]
  have hs : ∀ i j, dd2 hf y j i i j = dd2 hf y i j i j := fun i j => pd2_symm (hsm i j) y j i
  simp only [jetOf, hs]

/-- The second coefficient along the jet of a field is the Fierz–Pauli density plus the divergence of `Tprime`. -/
theorem F2_jet (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (y : Fin 3 → ℝ) :
    F2 (jetOf hf y) = fpDens (dh1 hf y) + ∑ m, fderiv ℝ (Tprime hf m) y (Pi.single m 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := jet_symm hsm hsymm y
  rw [F2_eq _ h1 h2 h3 h4]
  show fpDens (dh1 hf y) + divTp (Hm hf y) (dh1 hf y) (dd2 hf y) = _ + ∑ m, pd1 (Tprime hf m) y m
  rw [div_Tprime hsm]
  congr 2
  funext a b i j
  exact pd2_symm (hsm i j) y a b

/-- The jet of a `C³` field is continuous in the point. -/
theorem continuous_jetOf (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) : Continuous (jetOf hf) := by
  unfold jetOf
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · exact continuous_pi fun i => continuous_pi fun j => (hsm i j).continuous
  · exact continuous_pi fun k => continuous_pi fun i => continuous_pi fun j =>
      (contDiff_pd1 (n := 0) ((hsm i j).of_le (by norm_num)) k).continuous
  · exact continuous_pi fun k => continuous_pi fun l => continuous_pi fun i => continuous_pi fun j =>
      pd2_continuous (hsm i j) k l

/-- The first coefficient along a field is continuous in the point. -/
theorem continuous_F1_jet (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i) :
    Continuous fun y => F1 (jetOf hf y) := by
  simp_rw [F1_jet hsm hsymm]
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
  exact ((contDiff_S1field hsm i).continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The second coefficient along a field is continuous in the point. -/
theorem continuous_F2_jet (hsm : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i) :
    Continuous fun y => F2 (jetOf hf y) := by
  simp_rw [F2_jet hsm hsymm]
  have c2 : ∀ k i j, Continuous fun y => dh1 hf y k i j := fun k i j =>
    (contDiff_pd1 (n := 0) ((hsm i j).of_le (by norm_num)) k).continuous
  refine Continuous.add ?_ (continuous_finsetSum _ fun m _ => ?_)
  · simp only [fpDens]
    fun_prop
  · exact ((contDiff_Tprime hsm m).continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- If the jet of `h` at `y` is in the domain with `η`, then `1 + η h (y)` has non-zero determinant. -/
theorem gEta_posJ {η : ℝ} {y : Fin 3 → ℝ} (h : (η, jetOf hf y) ∈ posJ) : (gEta hf η y).det ≠ 0 := by
  have : gJ (η, jetOf hf y) = gEta hf η y := (gEta_eq hf η y).symm
  rw [← this]
  exact ne_of_gt h

open Classical in
/-- **The `η²` coefficient of the integrated curvature density.** For a smooth symmetric periodic field `h`, the cube
integral of `(R/2) √det` of `1 + η h` differs from `(η²/2)` times the cube integral of the Fierz–Pauli density of `∂h`
by at most `C |η|³` for small `η`. -/
theorem eh_eta_sq_coeff (hsm : ∀ i j, ContDiff ℝ ∞ (fun y => hf y i j))
    (hsymm : ∀ y i j, hf y i j = hf y j i)
    (hper : ∀ (p : Fin 3 → ℝ) (e : Fin 3 → ℤ), hf (p + fun i => (e i : ℝ)) = hf p) :
    ∃ C η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, |η| ≤ η₀ →
      |(∫ y in unitCube, scalarCurvature (gEta hf η) y / 2 * √((gEta hf η y).det)) -
        η ^ 2 / 2 * ∫ y in unitCube, fpDens (dh1 hf y)| ≤ C * |η| ^ 3 := by
  have hsm3 : ∀ i j, ContDiff ℝ 3 (fun y => hf y i j) := fun i j => (hsm i j).of_le (by simp)
  have hKc : IsCompact unitCube := isCompact_univ_pi fun _ => isCompact_Icc
  have hKj : IsCompact (jetOf hf '' unitCube) := hKc.image (continuous_jetOf hsm3)
  obtain ⟨M, r, hr, h⟩ := feta_expansion_dom hKj
  refine ⟨M, r, hr, fun η hη => ?_⟩
  have hmeas : MeasurableSet unitCube := hKc.isClosed.measurableSet
  -- pointwise: the density is `Feta` of the jet
  have hpt : ∀ y ∈ unitCube, scalarCurvature (gEta hf η) y / 2 * √((gEta hf η y).det) = Feta (η, jetOf hf y) := by
    intro y hy
    have hmem := (h (jetOf hf y) ⟨y, hy, rfl⟩ η hη).1
    rw [Feta_eq hsm hsymm η (gEta_posJ hmem)]
    congr 1
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    funext a b i j
    exact (pd1_pd1 ((hsm3 i j).of_le (by norm_num)) y b a).trans (pd2_symm (hsm3 i j) y b a)
  rw [setIntegral_congr_fun hmeas hpt]
  have hcont : ContinuousOn (fun y => Feta (η, jetOf hf y)) unitCube := by
    refine (contDiffOn_Feta.continuousOn).comp ((continuous_const.prodMk (continuous_jetOf hsm3)).continuousOn)
      fun y hy => (h (jetOf hf y) ⟨y, hy, rfl⟩ η hη).1
  have iF : IntegrableOn (fun y => Feta (η, jetOf hf y)) unitCube := hcont.integrableOn_compact hKc
  have i1 : IntegrableOn (fun y => F1 (jetOf hf y)) unitCube :=
    (continuous_F1_jet hsm3 hsymm).continuousOn.integrableOn_compact hKc
  have i2 : IntegrableOn (fun y => F2 (jetOf hf y)) unitCube :=
    (continuous_F2_jet hsm3 hsymm).continuousOn.integrableOn_compact hKc
  have hz1 := integral_F1_zero hsm3 hsymm hper
  have hz2 := integral_F2_eq hsm3 hsymm hper
  have iA : IntegrableOn (fun y => Feta (η, jetOf hf y) - η * F1 (jetOf hf y)) unitCube := iF.sub (i1.const_mul η)
  have iB : IntegrableOn (fun y => η ^ 2 / 2 * F2 (jetOf hf y)) unitCube := i2.const_mul _
  have iC : IntegrableOn (fun y => η * F1 (jetOf hf y)) unitCube := i1.const_mul _
  have e1 : ∫ y in unitCube, (Feta (η, jetOf hf y) - η * F1 (jetOf hf y) - η ^ 2 / 2 * F2 (jetOf hf y)) =
      (∫ y in unitCube, (Feta (η, jetOf hf y) - η * F1 (jetOf hf y))) - ∫ y in unitCube, η ^ 2 / 2 * F2 (jetOf hf y) :=
    integral_sub iA iB
  have e2 : ∫ y in unitCube, (Feta (η, jetOf hf y) - η * F1 (jetOf hf y)) =
      (∫ y in unitCube, Feta (η, jetOf hf y)) - ∫ y in unitCube, η * F1 (jetOf hf y) := integral_sub iF iC
  have hsplit : (∫ y in unitCube, Feta (η, jetOf hf y)) - η ^ 2 / 2 * ∫ y in unitCube, fpDens (dh1 hf y) =
      ∫ y in unitCube, (Feta (η, jetOf hf y) - η * F1 (jetOf hf y) - η ^ 2 / 2 * F2 (jetOf hf y)) := by
    rw [e1, e2, integral_const_mul, integral_const_mul, hz1, hz2]
    ring
  rw [hsplit]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := unitCube) (C := M * |η| ^ 3)
    (f := fun y => Feta (η, jetOf hf y) - η * F1 (jetOf hf y) - η ^ 2 / 2 * F2 (jetOf hf y))
    (by rw [volume_unitCube'] ; exact ENNReal.one_lt_top) (fun y hy => by
      simpa [Real.norm_eq_abs] using (h (jetOf hf y) ⟨y, hy, rfl⟩ η hη).2)
  simpa [Real.norm_eq_abs, volume_unitCube] using this

/-- Trust check: the zero field satisfies the hypotheses of `eh_eta_sq_coeff`. -/
theorem eh_eta_sq_coeff_zero :
    ∃ C η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, |η| ≤ η₀ →
      |(∫ y in unitCube, scalarCurvature (gEta (fun _ => (0 : Matrix (Fin 3) (Fin 3) ℝ)) η) y / 2 *
          √((gEta (fun _ => (0 : Matrix (Fin 3) (Fin 3) ℝ)) η y).det)) -
        η ^ 2 / 2 * ∫ y in unitCube, fpDens (dh1 (fun _ => (0 : Matrix (Fin 3) (Fin 3) ℝ)) y)| ≤ C * |η| ^ 3 :=
  eh_eta_sq_coeff (hf := fun _ => (0 : Matrix (Fin 3) (Fin 3) ℝ)) (fun _ _ => contDiff_const)
    (fun _ _ _ => rfl) (fun _ _ => rfl)

end EH3b

end Lightlike.Regge.Linear3
