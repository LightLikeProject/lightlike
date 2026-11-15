import Lightlike.Asymptotics.EPRL.ChartIntegral

/-!
# The inverse gnomonic chart of SU(2)

`tailM` reads the gnomonic coordinates `q = (Im M₀₀, Re M₀₁, Im M₀₁) / Re M₀₀` off a matrix. It
inverts `gammaSU` (`tailM_gammaSU`), and `gammaSU (tailM M) = M` for `M` in the open hemisphere
(`gammaSU_tailM`); `tailM` is continuous there.
-/

open Matrix MeasureTheory Set Quaternion Metric

namespace Lightlike.Asymptotics.EPRL

open Lightlike Lightlike.Spin4

/-- Gnomonic coordinates of a `2 × 2` matrix with `Re M₀₀ ≠ 0`. -/
noncomputable def tailM (M : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![(M 0 0).im / (M 0 0).re, (M 0 1).re / (M 0 0).re, (M 0 1).im / (M 0 0).re]

lemma tailM_gmat (w : Fin 3 → ℝ) : tailM (gmat w) = w := by
  have hg : (1 + ∑ k, w k ^ 2) ^ (-(1/2 : ℝ)) > 0 := by
    have : 0 ≤ ∑ k, w k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
    positivity
  set s := (1 + ∑ k, w k ^ 2) ^ (-(1/2 : ℝ)) with hs
  funext i
  fin_cases i <;> simp [tailM, gmat, Nmat] <;> field_simp

lemma tailM_gammaSU (w : Fin 3 → ℝ) : tailM (gammaSU w : Matrix (Fin 2) (Fin 2) ℂ) = w := by
  rw [coe_gammaSU, tailM_gmat]

lemma tailM_eq_tailH (x : sphere (0 : ℍ[ℝ]) 1) :
    tailM (sphereToSU2 x : Matrix (Fin 2) (Fin 2) ℂ) = tailH (x : ℍ[ℝ]) := by
  funext i
  fin_cases i <;> simp [tailM, tailH, sphereToSU2, toMat_apply, quatMat]

/-- On the open hemisphere, `gammaSU` inverts `tailM`. -/
lemma gammaSU_tailM {M : SU2} (hM : M ∈ hemiSU) :
    gammaSU (tailM (M : Matrix (Fin 2) (Fin 2) ℂ)) = M := by
  obtain ⟨x, rfl⟩ := sphereToSU2_bijective.2 M
  have hre : 0 < (x : ℍ[ℝ]).re := by
    have := hM
    simpa [hemiSU, re_sphereToSU2] using this
  rw [tailM_eq_tailH]
  unfold gammaSU
  congr 1
  exact Subtype.ext (gammaH_tailH (normSq_of_mem_sphere x) hre)

/-- The gnomonic chart of SU(2) is injective. -/
lemma gammaSU_injective : Function.Injective gammaSU := fun a b h => by
  have := congrArg (fun M : SU2 => tailM (M : Matrix (Fin 2) (Fin 2) ℂ)) h
  simpa [tailM_gammaSU] using this

lemma continuousOn_tailM :
    ContinuousOn (fun M : SU2 => tailM (M : Matrix (Fin 2) (Fin 2) ℂ)) hemiSU := by
  have hc : ∀ i j : Fin 2, Continuous fun M : SU2 => ((M : Matrix (Fin 2) (Fin 2) ℂ) i j) :=
    fun i j => (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  refine continuousOn_pi.mpr fun i => ?_
  have hne : ∀ M ∈ hemiSU, ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re ≠ 0 :=
    fun M hM => ne_of_gt (show 0 < ((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re from hM)
  have h00 := Complex.continuous_re.comp (hc 0 0)
  fin_cases i
  · exact ((Complex.continuous_im.comp (hc 0 0)).continuousOn).div h00.continuousOn hne
  · exact ((Complex.continuous_re.comp (hc 0 1)).continuousOn).div h00.continuousOn hne
  · exact ((Complex.continuous_im.comp (hc 0 1)).continuousOn).div h00.continuousOn hne

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

/-! ## The product chart of `SU(2)^4` around a point -/

/-- The gnomonic chart of SU(2) is continuous. -/
lemma continuous_gammaSU : Continuous gammaSU := by
  refine continuous_induced_rng.2 ?_
  have : (fun q => ((gammaSU q : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) = gmat := funext coe_gammaSU
  have h : Continuous fun q => ((gammaSU q : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [this]; exact contDiff_gmat.continuous
  exact h

lemma continuous_reshape : Continuous reshape :=
  continuous_pi fun i => show Continuous fun Y : Fin 4 → Fin 3 → ℝ =>
      Y (fpf.symm i).1 (fpf.symm i).2 from
    (continuous_apply _).comp (continuous_apply _)

lemma continuous_reshape_symm : Continuous reshape.symm :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_apply _

lemma one_mem_hemiSU : (1 : SU2) ∈ hemiSU := by
  show 0 < (((1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re
  simp

/-- The chart `ℝ¹² → SU(2)^4`, `q ↦ (p_a γ(q_a))_a`, around `p`. -/
noncomputable def chartMap (p : Fin 4 → SU2) (q : Fin 12 → ℝ) : Fin 4 → SU2 :=
  fun a => p a * gammaSU (reshape.symm q a)

/-- The domain of the chart around `p`: every `p_a⁻¹ Y_a` lies in the open hemisphere. -/
def hemiY (p : Fin 4 → SU2) : Set (Fin 4 → SU2) := {Y | ∀ a, (p a)⁻¹ * Y a ∈ hemiSU}

/-- The inverse chart: the gnomonic coordinates of `p_a⁻¹ Y_a`. -/
noncomputable def tailY (p Y : Fin 4 → SU2) : Fin 12 → ℝ :=
  reshape fun a => tailM (((p a)⁻¹ * Y a : SU2) : Matrix (Fin 2) (Fin 2) ℂ)

lemma continuous_chartMap (p : Fin 4 → SU2) : Continuous (chartMap p) :=
  continuous_pi fun a => continuous_const.mul
    (continuous_gammaSU.comp ((continuous_apply a).comp continuous_reshape_symm))

lemma chartMap_mem_hemiY (p : Fin 4 → SU2) (q : Fin 12 → ℝ) : chartMap p q ∈ hemiY p := fun a => by
  simpa [chartMap] using gammaSU_mem_hemi (reshape.symm q a)

lemma tailY_chartMap (p : Fin 4 → SU2) (q : Fin 12 → ℝ) : tailY p (chartMap p q) = q := by
  unfold tailY
  have : (fun a => tailM ((((p a)⁻¹ * chartMap p q a : SU2)) : Matrix (Fin 2) (Fin 2) ℂ)) =
      reshape.symm q := by
    funext a
    simp [chartMap, tailM_gammaSU]
  rw [this]; exact reshape.apply_symm_apply q

lemma chartMap_tailY {p Y : Fin 4 → SU2} (hY : Y ∈ hemiY p) : chartMap p (tailY p Y) = Y := by
  funext a
  unfold chartMap tailY
  rw [reshape.symm_apply_apply, gammaSU_tailM (hY a)]
  simp

lemma chartMap_zero (p : Fin 4 → SU2) : chartMap p 0 = p := by
  funext a
  have : reshape.symm (0 : Fin 12 → ℝ) a = 0 := rfl
  have h0 : gammaSU 0 = 1 := by
    apply Subtype.ext
    rw [coe_gammaSU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gmat, Nmat]
  simp [chartMap, this, h0]

lemma isOpen_hemiY (p : Fin 4 → SU2) : IsOpen (hemiY p) := by
  have : hemiY p = ⋂ a, (fun Y : Fin 4 → SU2 => (p a)⁻¹ * Y a) ⁻¹' hemiSU := by
    ext Y; simp [hemiY]
  rw [this]
  refine isOpen_iInter_of_finite fun a => ?_
  refine IsOpen.preimage (continuous_const.mul (continuous_apply a)) ?_
  exact isOpen_lt continuous_const
    (Complex.continuous_re.comp ((continuous_apply 0).comp ((continuous_apply 0).comp
      continuous_subtype_val)))

lemma continuousOn_tailY (p : Fin 4 → SU2) : ContinuousOn (tailY p) (hemiY p) := by
  refine continuous_reshape.comp_continuousOn ?_
  refine continuousOn_pi.mpr fun a => ?_
  exact continuousOn_tailM.comp (continuous_const.mul (continuous_apply a)).continuousOn
    (fun Y (hY : Y ∈ hemiY p) => hY a)

end Lightlike.Asymptotics.EPRL
