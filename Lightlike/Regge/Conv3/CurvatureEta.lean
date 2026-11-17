import Lightlike.Regge.Conv3.JetCurvature

/-!
# The scalar curvature of `1 + η h` as a smooth function of `η` and the jet of `h`

For a smooth symmetric matrix field `h` on `ℝ³` and a real `η`, the scalar curvature of the metric `g_η = 1 + η h` at a
point `m` where `det g_η (m) ≠ 0` is an explicit function of the jet `(η, h(m), ∂h(m), ∂∂h(m))`
(`scalar_gEta`, from `scalarCurvature_jet`), and `(R/2) √det g_η` is a smooth function `Feta` of that jet on the set where
`det (1 + η h) > 0` (`contDiffOn_Feta`). This is the first step towards the `η²` coefficient of the integrated curvature density
as a jet identity: the next steps expand `Feta` to second order in `η` uniformly on compact sets of jets.

## Main results

* `curvJ`, `chrJ`, `dChrJ`: the curvature expression in an inverse matrix and the derivatives of the metric.
* `scalar_curvJ`: `scalarCurvature g m = curvJ (g m)⁻¹ (∂g m) (∂∂g m)` for a coordinate metric.
* `scalar_gEta`, `Feta_eq`: the curvature density of `1 + η h` is `Feta` of the jet.
* `contDiffOn_Feta`: `Feta` is `C^∞` where the determinant is positive.

**Limits.** Dimension 3; `h` smooth (`C^∞`, as `IsCoordMetric` requires) and symmetric; nothing yet about the expansion in
`η`, about integrals, or about periodic fields.
-/

open Matrix Finset Real
open scoped ContDiff
namespace Lightlike.Regge.Conv3

/-- The Christoffel symbols `Γ^i_{jk}` from an inverse matrix `Gi` and the first derivatives `dg a i j = ∂_a g_ij`. -/
noncomputable def chrJ (Gi : Matrix (Fin 3) (Fin 3) ℝ) (dg : Fin 3 → Fin 3 → Fin 3 → ℝ) (i j k : Fin 3) : ℝ :=
  (1 / 2) * ∑ l, Gi i l * (dg j l k + dg k l j - dg l j k)

/-- `dChr` of `JetCurvature`, written in an inverse matrix `Gi`, the first derivatives `dg a i j = ∂_a g_ij` and the
second derivatives `ddg a b i j = ∂_a ∂_b g_ij`. -/
noncomputable def dChrJ (Gi : Matrix (Fin 3) (Fin 3) ℝ) (dg : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (ddg : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (μ ρ ν σ : Fin 3) : ℝ :=
  (1 / 2) * ∑ l,
      ((-∑ i, ∑ r, Gi ρ i * dg μ i r * Gi r l) * (dg ν l σ + dg σ l ν - dg l ν σ)
        + Gi ρ l * (ddg μ ν l σ + ddg μ σ l ν - ddg μ l ν σ))

/-- The scalar curvature as a function of the inverse metric and the first and second derivatives of the metric. -/
noncomputable def curvJ (Gi : Matrix (Fin 3) (Fin 3) ℝ) (dg : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (ddg : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ σ, ∑ ν, Gi σ ν * ∑ ρ, (dChrJ Gi dg ddg ρ ρ ν σ - dChrJ Gi dg ddg ν ρ ρ σ +
    ∑ l, (chrJ Gi dg ρ ρ l * chrJ Gi dg l ν σ - chrJ Gi dg ρ ν l * chrJ Gi dg l ρ σ))

/-- **The scalar curvature at a point is `curvJ` of the jet of the metric.** -/
theorem scalar_curvJ {U : Set (Fin 3 → ℝ)} {g : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hg : Lightlike.IsCoordMetric g U) {m : Fin 3 → ℝ} (hm : m ∈ U) :
    scalarCurvature g m = curvJ (g m)⁻¹ (fun a i j => pd a (fun y => g y i j) m)
      (fun a b i j => pd a (fun y => pd b (fun z => g z i j) y) m) := by
  rw [scalarCurvature_jet hg hm]
  rfl

section eta

variable {hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ}

/-- The matrix field `1 + η h`. -/
noncomputable def gEta (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (η : ℝ) (y : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := 1 + η • hf y

theorem pd_gEta (hsm : ∀ i j, ContDiff ℝ ∞ (fun y => hf y i j)) (η : ℝ) (a i j : Fin 3) (y : Fin 3 → ℝ) :
    pd a (fun z => gEta hf η z i j) y = η * pd a (fun z => hf z i j) y := by
  have h1 : (fun z => gEta hf η z i j) = fun z => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + η * hf z i j := by
    funext z; simp [gEta]
  have hd : DifferentiableAt ℝ (fun z => hf z i j) y := ((hsm i j).differentiable (by simp)) y
  rw [h1]
  unfold pd
  rw [fderiv_const_add, fderiv_const_mul hd]
  simp

theorem pd_pd_gEta (hsm : ∀ i j, ContDiff ℝ ∞ (fun y => hf y i j)) (η : ℝ) (a b i j : Fin 3) (y : Fin 3 → ℝ) :
    pd a (fun z => pd b (fun w => gEta hf η w i j) z) y = η * pd a (fun z => pd b (fun w => hf w i j) z) y := by
  have h1 : (fun z => pd b (fun w => gEta hf η w i j) z) = fun z => η * pd b (fun w => hf w i j) z := by
    funext z; exact pd_gEta hsm η b i j z
  have hd : DifferentiableAt ℝ (fun z => pd b (fun w => hf w i j) z) y := by
    have : ContDiff ℝ ∞ (fun z => pd b (fun w => hf w i j) z) := by
      unfold pd
      exact ((hsm i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (this.differentiable (by simp)) y
  rw [h1]
  exact pd_const_mul a η hd

/-- **The scalar curvature of `1 + η h` at a point is `curvJ` of the jet `(η h, η ∂h, η ∂∂h)`.** -/
theorem scalar_gEta (hsm : ∀ i j, ContDiff ℝ ∞ (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (η : ℝ) {m : Fin 3 → ℝ} (hm : (gEta hf η m).det ≠ 0) :
    scalarCurvature (gEta hf η) m = curvJ (gEta hf η m)⁻¹
      (fun a i j => η * pd a (fun y => hf y i j) m)
      (fun a b i j => η * pd a (fun y => pd b (fun z => hf z i j) y) m) := by
  have hc : ∀ i j, Continuous fun y => gEta hf η y i j := fun i j => by
    have : (fun y => gEta hf η y i j) = fun y => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + η * hf y i j := by
      funext z; simp [gEta]
    rw [this]; exact continuous_const.add (continuous_const.mul (hsm i j).continuous)
  have hU : IsOpen {y | (gEta hf η y).det ≠ 0} := by
    have : Continuous fun y => (gEta hf η y).det := by
      simp_rw [Matrix.det_apply]
      refine continuous_finsetSum _ fun σ _ => ?_
      refine Continuous.const_smul ?_ _
      exact continuous_finsetProd _ fun i _ => hc _ _
    exact isOpen_ne_fun this continuous_const
  have hg : Lightlike.IsCoordMetric (gEta hf η) {y | (gEta hf η y).det ≠ 0} :=
    { isOpen := hU
      symm := fun x _ => by
        ext i j; simp [gEta, Matrix.transpose_apply, hsymm x i j, Matrix.one_apply, eq_comm]
      isUnit_det := fun x hx => isUnit_iff_ne_zero.mpr hx
      smooth := fun i j => by
        have : (fun y => gEta hf η y i j) = fun y => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j + η * hf y i j := by
          funext z; simp [gEta]
        rw [this]
        exact (contDiff_const.add (contDiff_const.mul (hsm i j))).contDiffOn }
  rw [scalar_curvJ hg hm]
  simp only [pd_pd_gEta hsm]
  simp only [pd_gEta hsm]

/-- The jets `(η, h, ∂h, ∂∂h)`. -/
abbrev JetE := ℝ × (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)

/-- The metric matrix `1 + η h` of a jet. -/
noncomputable def gJ (p : JetE) : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (if i = j then 1 else 0) + p.1 * p.2.1 i j

/-- The curvature-density function `(R/2) √det g` of the jet `(η h, η ∂h, η ∂∂h)`. -/
noncomputable def Feta (p : JetE) : ℝ :=
  curvJ (gJ p)⁻¹ (fun a i j => p.1 * p.2.2.1 a i j) (fun a b i j => p.1 * p.2.2.2 a b i j) / 2 * √((gJ p).det)

theorem gEta_eq (hf : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (η : ℝ) (m : Fin 3 → ℝ) :
    gEta hf η m = gJ (η, fun i j => hf m i j, fun _ _ _ => 0, fun _ _ _ _ => 0) := by
  ext i j; simp [gEta, gJ, Matrix.one_apply]

theorem contDiff_gJ (i j : Fin 3) : ContDiff ℝ ∞ (fun p : JetE => gJ p i j) := by
  unfold gJ
  have h1 : ContDiff ℝ ∞ (fun p : JetE => p.1) := contDiff_fst
  have hH : ContDiff ℝ ∞ (fun p : JetE => p.2.1) := contDiff_fst.comp contDiff_snd
  have h2 : ContDiff ℝ ∞ (fun p : JetE => p.2.1 i j) := contDiff_pi.1 (contDiff_pi.1 hH i) j
  exact contDiff_const.add (h1.mul h2)

theorem contDiff_det_mat (M : JetE → Matrix (Fin 3) (Fin 3) ℝ) (h : ∀ i j, ContDiff ℝ ∞ (fun p => M p i j)) :
    ContDiff ℝ ∞ (fun p => (M p).det) := by
  simp_rw [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.const_smul _ ?_
  exact contDiff_prod fun i _ => h _ _

theorem contDiff_adj_gJ (i j : Fin 3) : ContDiff ℝ ∞ (fun p : JetE => (gJ p).adjugate i j) := by
  simp_rw [Matrix.adjugate_apply]
  refine contDiff_det_mat _ fun a b => ?_
  by_cases ha : a = j
  · subst ha; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne ha]; exact contDiff_gJ _ _

theorem contDiffOn_inv_gJ (i j : Fin 3) :
    ContDiffOn ℝ ∞ (fun p : JetE => (gJ p)⁻¹ i j) {p | 0 < (gJ p).det} := by
  refine ContDiffOn.congr (f := fun p => ((gJ p).det)⁻¹ * (gJ p).adjugate i j) ?_ ?_
  · exact ((contDiff_det_mat gJ contDiff_gJ).contDiffOn.inv fun p hp => (ne_of_gt hp)).mul (contDiff_adj_gJ i j).contDiffOn
  · intro p hp
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    simp

theorem contDiff_dg (a i j : Fin 3) : ContDiff ℝ ∞ (fun p : JetE => p.1 * p.2.2.1 a i j) := by
  have h1 : ContDiff ℝ ∞ (fun p : JetE => p.1) := contDiff_fst
  have hH : ContDiff ℝ ∞ (fun p : JetE => p.2.2.1) := contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  exact h1.mul (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hH a) i) j)

theorem contDiff_ddg (a b i j : Fin 3) : ContDiff ℝ ∞ (fun p : JetE => p.1 * p.2.2.2 a b i j) := by
  have h1 : ContDiff ℝ ∞ (fun p : JetE => p.1) := contDiff_fst
  have hH : ContDiff ℝ ∞ (fun p : JetE => p.2.2.2) := contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  exact h1.mul (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 hH a) b) i) j)

/-- The set of jets with positive determinant of `1 + η h`. -/
def posJ : Set JetE := {p | 0 < (gJ p).det}

theorem contDiffOn_chrJ (i j k : Fin 3) :
    ContDiffOn ℝ ∞ (fun p : JetE => chrJ (gJ p)⁻¹ (fun a i j => p.1 * p.2.2.1 a i j) i j k) posJ := by
  have h1 := fun a i j => (contDiff_dg a i j).contDiffOn (s := posJ)
  unfold chrJ
  refine contDiffOn_const.mul (ContDiffOn.sum fun l _ => (contDiffOn_inv_gJ _ _).mul ?_)
  exact ((h1 _ _ _).add (h1 _ _ _)).sub (h1 _ _ _)

theorem contDiffOn_dChrJ (μ ρ ν σ : Fin 3) :
    ContDiffOn ℝ ∞ (fun p : JetE => dChrJ (gJ p)⁻¹ (fun a i j => p.1 * p.2.2.1 a i j)
      (fun a b i j => p.1 * p.2.2.2 a b i j) μ ρ ν σ) posJ := by
  have h1 := fun a i j => (contDiff_dg a i j).contDiffOn (s := posJ)
  have h2 := fun a b i j => (contDiff_ddg a b i j).contDiffOn (s := posJ)
  have hGi := contDiffOn_inv_gJ
  unfold dChrJ
  refine contDiffOn_const.mul (ContDiffOn.sum fun l _ => ?_)
  refine ContDiffOn.add (ContDiffOn.mul ?_ (((h1 _ _ _).add (h1 _ _ _)).sub (h1 _ _ _))) ?_
  · exact (ContDiffOn.sum fun i _ => ContDiffOn.sum fun r _ =>
      (((hGi _ _).mul (h1 _ _ _)).mul (hGi _ _))).neg
  · exact (hGi _ _).mul (((h2 _ _ _ _).add (h2 _ _ _ _)).sub (h2 _ _ _ _))

/-- **`(R/2) √det` of the jet `(η h, η ∂h, η ∂∂h)` is smooth in the jet where `det (1 + η h) > 0`.** -/
theorem contDiffOn_Feta : ContDiffOn ℝ ∞ Feta posJ := by
  have hd : ContDiffOn ℝ ∞ (fun p : JetE => √((gJ p).det)) posJ :=
    (contDiff_det_mat gJ contDiff_gJ).contDiffOn.sqrt fun p hp => (ne_of_gt hp)
  have hc := contDiffOn_chrJ
  have hD := contDiffOn_dChrJ
  have hGi := contDiffOn_inv_gJ
  unfold Feta curvJ
  refine ContDiffOn.mul (ContDiffOn.div_const ?_ _) hd
  refine ContDiffOn.sum fun σ _ => ContDiffOn.sum fun ν _ => (hGi _ _).mul (ContDiffOn.sum fun ρ _ => ?_)
  refine ContDiffOn.add ((hD _ _ _ _).sub (hD _ _ _ _)) (ContDiffOn.sum fun l _ => ?_)
  exact ((hc _ _ _).mul (hc _ _ _)).sub ((hc _ _ _).mul (hc _ _ _))

/-- **The curvature density of `1 + η h` at `m` is `Feta` of the jet of `h` at `m`.** -/
theorem Feta_eq (hsm : ∀ i j, ContDiff ℝ ∞ (fun y => hf y i j)) (hsymm : ∀ y i j, hf y i j = hf y j i)
    (η : ℝ) {m : Fin 3 → ℝ} (hm : (gEta hf η m).det ≠ 0) :
    scalarCurvature (gEta hf η) m / 2 * √((gEta hf η m).det) =
      Feta (η, fun i j => hf m i j, fun a i j => pd a (fun y => hf y i j) m,
        fun a b i j => pd a (fun y => pd b (fun z => hf z i j) y) m) := by
  have h := gEta_eq hf η m
  have h2 : gJ (η, fun i j => hf m i j, fun a i j => pd a (fun y => hf y i j) m,
      fun a b i j => pd a (fun y => pd b (fun z => hf z i j) y) m) = gEta hf η m := by
    rw [h]; rfl
  rw [scalar_gEta hsm hsymm η hm]
  unfold Feta
  rw [h2]

/-- The zero jet is in the domain: `1 + 0 · h` has determinant `1`. -/
theorem zero_mem_posJ (H : Fin 3 → Fin 3 → ℝ) (dh : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : ((0 : ℝ), H, dh, dd) ∈ posJ := by
  have : gJ ((0 : ℝ), H, dh, dd) = 1 := by ext i j; simp [gJ, Matrix.one_apply]
  simp [posJ, this]

/-- Trust check: at `η = 0` (the flat metric `1`) the curvature density `Feta` is zero. -/
theorem Feta_flat (H : Fin 3 → Fin 3 → ℝ) (dh : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (dd : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : Feta ((0 : ℝ), H, dh, dd) = 0 := by
  simp [Feta, curvJ, chrJ, dChrJ]

end eta

end Lightlike.Regge.Conv3
