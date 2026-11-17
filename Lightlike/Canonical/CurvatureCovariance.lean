import Mathlib
import Lightlike.Canonical.FlowPullback
import Lightlike.Canonical.MomentumBracket

/-!
# Infinitesimal covariance of the scalar curvature

For a smooth metric `h`, nondegenerate everywhere, and a smooth vector field `ξ`, the scalar curvature of
`h + t ℒ_ξ h` at `x` has `t`-derivative `ξ^k ∂_k R(x)` at `t = 0` (`hasDerivAt_scalar_lie`): the scalar
curvature is a scalar under the flow of `ξ`. The proof uses only that `R` is a differentiable function `Rjet` of
the 2-jet (`Lightlike/Canonical/CurvatureJet.lean`), the finite covariance `scalarCurvature_pullback` of
`Lightlike/Spacetime/ChartChange.lean`, and the fact that the pullback by the flow and `h + t ℒ_ξ h` have the
same `t`-derivative of the 2-jet (`Lightlike/Canonical/FlowPullback.lean`). No first-variation formula and no
Bianchi identity is needed.
-/

open Matrix Filter
open scoped ContDiff Topology

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

lemma smoothTensor_add_smul {h k : TensorField d} (hh : SmoothTensor h) (hk : SmoothTensor k) (t : ℝ) :
    SmoothTensor (fun y => h y + t • k y) := fun i j => by
  simpa using (hh i j).add (contDiff_const.mul (hk i j))

lemma jetAt_add_smul {h k : TensorField d} (hh : SmoothTensor h) (hk : SmoothTensor k) (t : ℝ)
    (x : Fin d → ℝ) :
    jetAt (fun y => h y + t • k y) x = jetAt h x + t • jetAt k x := by
  have e0 : ∀ a b : Fin d, ∀ z, (fun y => (h y + t • k y) a b) z = h z a b + t * k z a b := fun a b z => by simp
  have e1 : ∀ c a b : Fin d, ∀ z, Lightlike.pd c (fun y => (h y + t • k y) a b) z =
      Lightlike.pd c (fun y => h y a b) z + t * Lightlike.pd c (fun y => k y a b) z := by
    intro c a b z
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Lightlike.pd_add (diff_of_smooth (hh a b) z) ((diff_of_smooth (hk a b) z).const_mul t),
      Lightlike.pd_const_mul t (diff_of_smooth (hk a b) z)]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext a b; simp [jetAt]
  · funext c a b; simp only [jetAt, jet1, Prod.snd_add, Prod.snd_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact e1 c a b x
  · funext c e a b
    simp only [jetAt, jet2, Prod.snd_add, Prod.snd_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : Lightlike.pd e (fun y => (h y + t • k y) a b) =
        fun z => Lightlike.pd e (fun y => h y a b) z + t * Lightlike.pd e (fun y => k y a b) z :=
      funext (e1 e a b)
    rw [this, Lightlike.pd_add (diff_of_smooth (smooth_pd (hh a b) e) x)
      ((diff_of_smooth (smooth_pd (hk a b) e) x).const_mul t),
      Lightlike.pd_const_mul t (diff_of_smooth (smooth_pd (hk a b) e) x)]
    rfl

lemma differentiable_jetAt {h : TensorField d} (hh : SmoothTensor h) :
    Differentiable ℝ (fun y : Fin d → ℝ => jetAt h y) := by
  refine Differentiable.prodMk ?_ (Differentiable.prodMk ?_ ?_)
  · exact differentiable_pi.mpr fun a => differentiable_pi.mpr fun b => (hh a b).differentiable (by simp)
  · exact differentiable_pi.mpr fun k => differentiable_pi.mpr fun a => differentiable_pi.mpr fun b =>
      (smooth_pd (hh a b) k).differentiable (by simp)
  · exact differentiable_pi.mpr fun k => differentiable_pi.mpr fun l => differentiable_pi.mpr fun a =>
      differentiable_pi.mpr fun b => (smooth_pd (smooth_pd (hh a b) l) k).differentiable (by simp)

lemma continuous_det_jet : Continuous (fun J : Jet d => (Matrix.of J.1).det) := by
  refine Continuous.matrix_det ?_
  exact continuous_pi fun i => continuous_pi fun j => by
    simp only [Matrix.of_apply]
    exact (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)

/-- The flow map is a chart change on the open set where its Jacobian is invertible. -/
lemma isChartChange_flowMap {ξ : VectorField d} (hξ : SmoothVec ξ) (t : ℝ) :
    Lightlike.IsChartChange (flowMap ξ t) {y | (Lightlike.jac (flowMap ξ t) y).det ≠ 0} Set.univ where
  isOpen := by
    refine isOpen_ne_fun ?_ continuous_const
    refine Continuous.matrix_det ?_
    refine continuous_pi fun μ => continuous_pi fun a => ?_
    have : (fun y => Lightlike.jac (flowMap ξ t) y μ a) = fun y => (if μ = a then 1 else 0) +
        t * Lightlike.pd a (fun z => ξ z μ) y := funext fun y => jac_flowMap hξ t y μ a
    simp only [this]
    exact continuous_const.add (continuous_const.mul (smooth_pd (hξ μ) a).continuous)
  mapsTo := fun _ _ => Set.mem_univ _
  smooth := fun μ => by
    have : (fun y => flowMap ξ t y μ) = fun y => y μ + t * ξ y μ := by funext y; simp [flowMap]
    rw [this]
    exact ((contDiff_apply ℝ (fun _ : Fin d => ℝ) μ : ContDiff ℝ ∞ fun y : Fin d → ℝ => y μ).add
      (contDiff_const.mul (hξ μ))).contDiffOn
  isUnit_det := fun y hy => isUnit_iff_ne_zero.mpr hy

lemma pullback_flowMap_zero {ξ : VectorField d} (hξ : SmoothVec ξ) (h : TensorField d) :
    (fun y => Lightlike.pullback h (flowMap ξ 0) y) = h := by
  funext y
  ext a b
  have := flowComp_eq hξ h a b 0 y
  simp only [flowComp] at this
  rw [this]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- The scalar curvature of a smooth, positive definite metric is differentiable. -/
lemma differentiableAt_scalarCurvature {h : TensorField d} (hh : SmoothTensor h) (hpos : ∀ y, (h y).PosDef)
    (x : Fin d → ℝ) : DifferentiableAt ℝ (Lightlike.scalarCurvature h) x := by
  have hdetY : ∀ y, (h y).det ≠ 0 := fun y => (hpos y).det_pos.ne'
  obtain ⟨Rh, hRhdef⟩ : ∃ Rh : (Fin d → ℝ) → ℝ, Rh = Lightlike.scalarCurvature h := ⟨_, rfl⟩
  have hRh : Rh = fun y => Rjet (jetAt h y) := by
    rw [hRhdef]; exact funext fun y => scalarCurvature_eq_Rjet hh (hdetY y)
  have hJ0 : (Matrix.of (jetAt h x).1).det ≠ 0 := hdetY x
  rw [← hRhdef, hRh]
  have hg : DifferentiableAt ℝ Rjet (jetAt h x) := differentiableAt_Rjet hJ0
  exact DifferentiableAt.comp (g := Rjet) (f := fun y => jetAt h y) x hg (differentiable_jetAt hh x)

/-- **The first variation of the scalar curvature along a direction `k`**: the derivative of `R (g + t k)` at
`t = 0` is the derivative of the function `Rjet` of the 2-jet along the 2-jet of `k`. -/
theorem hasDerivAt_scalar_dir {g k : TensorField d} (hg : SmoothTensor g) (hk : SmoothTensor k)
    {x : Fin d → ℝ} (hdet : (g x).det ≠ 0) :
    HasDerivAt (fun t : ℝ => Lightlike.scalarCurvature (fun y => g y + t • k y) x)
      (fderiv ℝ Rjet (jetAt g x) (jetAt k x)) 0 := by
  set J0 := jetAt g x with hJ0def
  set JL := jetAt k x with hJLdef
  have hJ0 : (Matrix.of J0.1).det ≠ 0 := hdet
  have hRd : HasFDerivAt Rjet (fderiv ℝ Rjet J0) J0 := (differentiableAt_Rjet hJ0).hasFDerivAt
  set DR := fderiv ℝ Rjet J0 with hDR
  have hc1 : HasDerivAt (fun t : ℝ => J0 + t • JL) JL 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const JL).const_add J0
  have hR1 : HasDerivAt (fun t : ℝ => Rjet (J0 + t • JL)) (DR JL) 0 := by
    have h1 : HasFDerivAt Rjet DR (J0 + (0 : ℝ) • JL) := by simpa using hRd
    exact h1.comp_hasDerivAt (0 : ℝ) hc1
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), Lightlike.scalarCurvature (fun y => g y + t • k y) x =
      Rjet (J0 + t • JL) := by
    have hcont : Continuous (fun t : ℝ => (Matrix.of (J0 + t • JL).1).det) :=
      continuous_det_jet.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hne : ∀ᶠ t in 𝓝 (0 : ℝ), (Matrix.of (J0 + t • JL).1).det ≠ 0 :=
      hcont.continuousAt.eventually_ne (by simpa using hJ0)
    filter_upwards [hne] with t ht
    have hd : ((fun y => g y + t • k y) x).det ≠ 0 := by
      have e : (fun y => g y + t • k y) x = Matrix.of (J0 + t • JL).1 := by
        ext a b; simp [J0, JL, jetAt]
      rw [e]; exact ht
    rw [scalarCurvature_eq_Rjet (smoothTensor_add_smul hg hk t) hd, jetAt_add_smul hg hk t x]
  exact hR1.congr_of_eventuallyEq hev1

/-- **The derivative of `Rjet` along the jet of `ℒ_ξ h`** is `ξ^k ∂_k R (x)`. -/
theorem fderivRjet_lie {h : TensorField d} {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hh : SmoothTensor h) (hpos : ∀ y, (h y).PosDef) (x : Fin d → ℝ) :
    fderiv ℝ Rjet (jetAt h x) (jetAt (lieTensor ξ h) x) =
      ∑ k, ξ x k * Lightlike.pd k (Lightlike.scalarCurvature h) x := by
  set L := lieTensor ξ h with hLdef
  have hL : SmoothTensor L := smoothTensor_lieTensor hh hξ
  have hdetY : ∀ y, (h y).det ≠ 0 := fun y => (hpos y).det_pos.ne'
  set J0 := jetAt h x with hJ0def
  set JL := jetAt L x with hJLdef
  have hJ0 : (Matrix.of J0.1).det ≠ 0 := hdetY x
  have hRd : HasFDerivAt Rjet (fderiv ℝ Rjet J0) J0 := (differentiableAt_Rjet hJ0).hasFDerivAt
  set DR := fderiv ℝ Rjet J0 with hDR
  -- Part 2: along the pullback by the flow
  have hc2 := hasDerivAt_jet_pullback hξ hh x
  have hc20 : jetAt (fun y => Lightlike.pullback h (flowMap ξ 0) y) x = J0 := by
    rw [pullback_flowMap_zero hξ h]
  have hR2 : HasDerivAt (fun t : ℝ => Rjet (jetAt (fun y => Lightlike.pullback h (flowMap ξ t) y) x))
      (DR JL) 0 := by
    have h2 : HasFDerivAt Rjet DR (jetAt (fun y => Lightlike.pullback h (flowMap ξ 0) y) x) := by
      rw [hc20]; exact hRd
    exact h2.comp_hasDerivAt (0 : ℝ) hc2
  have hcoord : Lightlike.IsCoordMetric h Set.univ :=
    ⟨isOpen_univ, fun y _ => by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (hpos y).1.eq,
      fun y _ => isUnit_iff_ne_zero.mpr (hdetY y), fun i j => (hh i j).contDiffOn⟩
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℝ), Lightlike.scalarCurvature h (x + t • ξ x) =
      Rjet (jetAt (fun y => Lightlike.pullback h (flowMap ξ t) y) x) := by
    have hcont : ContinuousAt (fun t : ℝ =>
        (Matrix.of (jetAt (fun y => Lightlike.pullback h (flowMap ξ t) y) x).1).det) 0 :=
      (continuous_det_jet.continuousAt).comp hc2.continuousAt
    have hne : ∀ᶠ t in 𝓝 (0 : ℝ),
        (Matrix.of (jetAt (fun y => Lightlike.pullback h (flowMap ξ t) y) x).1).det ≠ 0 :=
      hcont.eventually_ne (by rw [hc20]; exact hJ0)
    have hjac : ∀ᶠ t in 𝓝 (0 : ℝ), (Lightlike.jac (flowMap ξ t) x).det ≠ 0 := by
      have hc : Continuous (fun t : ℝ => (Lightlike.jac (flowMap ξ t) x).det) := by
        refine Continuous.matrix_det (continuous_pi fun μ => continuous_pi fun a => ?_)
        have : (fun t : ℝ => Lightlike.jac (flowMap ξ t) x μ a) = fun t => (if μ = a then 1 else 0) +
            t * Lightlike.pd a (fun z => ξ z μ) x := funext fun t => jac_flowMap hξ t x μ a
        simp only [this]
        exact continuous_const.add (continuous_id.mul continuous_const)
      refine hc.continuousAt.eventually_ne ?_
      have h0 : Lightlike.jac (flowMap ξ 0) x = 1 := by
        ext μ a; rw [jac_flowMap hξ]; by_cases hμ : μ = a <;> simp [hμ, Matrix.one_apply]
      simp [h0]
    filter_upwards [hne, hjac] with t ht hj
    have hsm : SmoothTensor (fun y => Lightlike.pullback h (flowMap ξ t) y) := fun a b => by
      have := (jointSmooth_flowComp hξ hh a b).comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ ∞
        fun y : Fin d → ℝ => ((t, y) : ℝ × (Fin d → ℝ)))
      exact this
    have hd : ((fun y => Lightlike.pullback h (flowMap ξ t) y) x).det ≠ 0 := ht
    rw [← scalarCurvature_eq_Rjet hsm hd]
    exact (Lightlike.scalarCurvature_pullback hcoord (isChartChange_flowMap hξ t) hj).symm
  -- Part 3: the derivative of R along x + t ξ(x)
  obtain ⟨Rh, hRhdef⟩ : ∃ Rh : (Fin d → ℝ) → ℝ, Rh = Lightlike.scalarCurvature h := ⟨_, rfl⟩
  have hRh : Rh = fun y => Rjet (jetAt h y) := by
    rw [hRhdef]; exact funext fun y => scalarCurvature_eq_Rjet hh (hdetY y)
  have hRdiff : DifferentiableAt ℝ Rh x := by
    rw [hRh]
    have hg : DifferentiableAt ℝ Rjet (jetAt h x) := differentiableAt_Rjet hJ0
    exact DifferentiableAt.comp (g := Rjet) (f := fun y => jetAt h y) x hg (differentiable_jetAt hh x)
  have hpath : HasDerivAt (fun t : ℝ => x + t • ξ x) (ξ x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ξ x)).const_add x
  have hR3 : HasDerivAt (fun t : ℝ => Rh (x + t • ξ x)) (fderiv ℝ Rh x (ξ x)) 0 := by
    have hd : HasFDerivAt Rh (fderiv ℝ Rh x) (x + (0 : ℝ) • ξ x) := by simpa using hRdiff.hasFDerivAt
    exact hd.comp_hasDerivAt 0 hpath
  rw [← hRhdef] at hev2 ⊢
  have hR2' := hR2.congr_of_eventuallyEq hev2
  have huniq : DR JL = fderiv ℝ Rh x (ξ x) := hR2'.unique hR3
  rw [fderiv_eq_sum_pd] at huniq
  exact huniq

/-- **Infinitesimal covariance of the scalar curvature**: along `h + t ℒ_ξ h` the scalar curvature at `x` has
derivative `ξ^k ∂_k R (x)`. -/
theorem hasDerivAt_scalar_lie {h : TensorField d} {ξ : VectorField d} (hξ : SmoothVec ξ)
    (hh : SmoothTensor h) (hpos : ∀ y, (h y).PosDef) (x : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => Lightlike.scalarCurvature (fun y => h y + t • lieTensor ξ h y) x)
      (∑ k, ξ x k * Lightlike.pd k (Lightlike.scalarCurvature h) x) 0 := by
  have := hasDerivAt_scalar_dir hh (smoothTensor_lieTensor hh hξ) (hpos x).det_pos.ne'
  rwa [fderivRjet_lie hξ hh hpos x] at this

end Lightlike.Canonical

end
