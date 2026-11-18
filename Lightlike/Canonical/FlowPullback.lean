import Mathlib
import Lightlike.Canonical.ParamPd
import Lightlike.Canonical.CurvatureJet
import Lightlike.Spacetime.ChartChange

/-!
# The pullback of a tensor field by the flow `y ↦ y + t ξ(y)`

For smooth `h`, `ξ` the pullback `pullback h (flowMap ξ t)` of `Lightlike/Spacetime/ChartChange.lean` is
jointly smooth in `(t, y)`, its `t`-derivative at `t = 0` is the Lie derivative `ℒ_ξ h` (`lieDeriv`), and the
2-jet at a point is differentiable in `t` at `0` with derivative the 2-jet of `ℒ_ξ h` (`hasDerivAt_jet_pullback`),
because partial derivatives commute with the parameter derivative.
-/

open scoped ContDiff

noncomputable section

namespace Lightlike.Canonical

variable {d : ℕ}

/-- The flow map `y ↦ y + t ξ(y)` (first order flow of the vector field `ξ`). -/
def flowMap (ξ : VectorField d) (t : ℝ) : (Fin d → ℝ) → (Fin d → ℝ) := fun y => y + t • ξ y

lemma pd_coord (a μ : Fin d) (y : Fin d → ℝ) :
    Lightlike.pd a (fun z : Fin d → ℝ => z μ) y = if μ = a then 1 else 0 := by
  simp only [Lightlike.pd]
  rw [(hasFDerivAt_apply μ y).fderiv]
  simp [Pi.single_apply]

/-- The Jacobian of the flow map: `J^μ_a = δ^μ_a + t ∂_a ξ^μ`. -/
lemma jac_flowMap {ξ : VectorField d} (hξ : SmoothVec ξ) (t : ℝ) (y : Fin d → ℝ) (μ a : Fin d) :
    Lightlike.jac (flowMap ξ t) y μ a = (if μ = a then 1 else 0) + t * Lightlike.pd a (fun z => ξ z μ) y := by
  unfold Lightlike.jac flowMap
  have : (fun z : Fin d → ℝ => (z + t • ξ z) μ) = fun z => z μ + t * ξ z μ := by
    funext z; simp
  rw [this, Lightlike.pd_add (differentiableAt_apply μ y) ((diff_of_smooth (hξ μ) y).const_mul t),
    Lightlike.pd_const_mul t (diff_of_smooth (hξ μ) y), pd_coord]

/-- The pulled-back tensor component `(a, b)` of `h` by the flow, as a function of `(t, y)`. -/
def flowComp (ξ : VectorField d) (h : TensorField d) (a b : Fin d) (t : ℝ) (y : Fin d → ℝ) : ℝ :=
  Lightlike.pullback h (flowMap ξ t) y a b

lemma flowComp_eq {ξ : VectorField d} (hξ : SmoothVec ξ) (h : TensorField d) (a b : Fin d) (t : ℝ)
    (y : Fin d → ℝ) :
    flowComp ξ h a b t y = ∑ μ, ∑ ν, ((if μ = a then 1 else 0) + t * Lightlike.pd a (fun z => ξ z μ) y) *
      h (y + t • ξ y) μ ν * ((if ν = b then 1 else 0) + t * Lightlike.pd b (fun z => ξ z ν) y) := by
  unfold flowComp Lightlike.pullback
  simp only [jac_flowMap hξ]
  rfl

lemma jointSmooth_flowComp {ξ : VectorField d} {h : TensorField d} (hξ : SmoothVec ξ) (hh : SmoothTensor h)
    (a b : Fin d) : JointSmooth (flowComp ξ h a b) := by
  unfold JointSmooth
  have e : (fun p : ℝ × (Fin d → ℝ) => flowComp ξ h a b p.1 p.2) = fun p => ∑ μ, ∑ ν,
      ((if μ = a then 1 else 0) + p.1 * Lightlike.pd a (fun z => ξ z μ) p.2) *
      h (p.2 + p.1 • ξ p.2) μ ν * ((if ν = b then 1 else 0) + p.1 * Lightlike.pd b (fun z => ξ z ν) p.2) := by
    funext p; exact flowComp_eq hξ h a b p.1 p.2
  rw [e]
  refine ContDiff.sum fun μ _ => ContDiff.sum fun ν _ => ?_
  have hX : ∀ c ρ, ContDiff ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => Lightlike.pd c (fun z => ξ z ρ) p.2) := fun c ρ =>
    (smooth_pd (hξ ρ) c).comp contDiff_snd
  have hhh : ContDiff ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => h (p.2 + p.1 • ξ p.2) μ ν) := by
    have hc : ContDiff ℝ ∞ (fun p : ℝ × (Fin d → ℝ) => p.2 + p.1 • ξ p.2) :=
      contDiff_snd.add (contDiff_fst.smul (contDiff_pi.mpr fun k => (hξ k).comp contDiff_snd))
    exact (hh μ ν).comp hc
  exact (((contDiff_const.add (contDiff_fst.mul (hX a μ))).mul hhh).mul
    (contDiff_const.add (contDiff_fst.mul (hX b ν))))

lemma fderiv_eq_sum_pd {f : (Fin d → ℝ) → ℝ} (y v : Fin d → ℝ) :
    fderiv ℝ f y v = ∑ k, v k * Lightlike.pd k f y := by
  have hv : v = ∑ k, v k • (Pi.single k (1 : ℝ) : Fin d → ℝ) := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Lightlike.pd]

/-- The `t`-derivative of the pulled-back tensor at `t = 0` is the Lie derivative. -/
lemma deriv_flowComp_zero {ξ : VectorField d} {h : TensorField d} (hξ : SmoothVec ξ) (hh : SmoothTensor h)
    (a b : Fin d) (y : Fin d → ℝ) :
    deriv (fun t => flowComp ξ h a b t y) 0 = lieDeriv ξ h a b y := by
  have e : (fun t => flowComp ξ h a b t y) = fun t => ∑ μ, ∑ ν,
      ((if μ = a then 1 else 0) + t * Lightlike.pd a (fun z => ξ z μ) y) *
      h (y + t • ξ y) μ ν * ((if ν = b then 1 else 0) + t * Lightlike.pd b (fun z => ξ z ν) y) := by
    funext t; exact flowComp_eq hξ h a b t y
  rw [e]
  have hpath : HasDerivAt (fun t : ℝ => y + t • ξ y) (ξ y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (ξ y)).const_add y
  have hterm : ∀ μ ν : Fin d, HasDerivAt (fun t : ℝ => ((if μ = a then (1 : ℝ) else 0) +
        t * Lightlike.pd a (fun z => ξ z μ) y) * h (y + t • ξ y) μ ν *
        ((if ν = b then (1 : ℝ) else 0) + t * Lightlike.pd b (fun z => ξ z ν) y))
      ((Lightlike.pd a (fun z => ξ z μ) y * h y μ ν * (if ν = b then 1 else 0)) +
        ((if μ = a then 1 else 0) * (fderiv ℝ (fun z => h z μ ν) y (ξ y)) * (if ν = b then 1 else 0)) +
        ((if μ = a then 1 else 0) * h y μ ν * Lightlike.pd b (fun z => ξ z ν) y)) 0 := by
    intro μ ν
    have hA : HasDerivAt (fun t : ℝ => (if μ = a then (1 : ℝ) else 0) + t * Lightlike.pd a (fun z => ξ z μ) y)
        (Lightlike.pd a (fun z => ξ z μ) y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Lightlike.pd a (fun z => ξ z μ) y)).const_add
        (if μ = a then (1 : ℝ) else 0)
    have hC : HasDerivAt (fun t : ℝ => (if ν = b then (1 : ℝ) else 0) + t * Lightlike.pd b (fun z => ξ z ν) y)
        (Lightlike.pd b (fun z => ξ z ν) y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (Lightlike.pd b (fun z => ξ z ν) y)).const_add
        (if ν = b then (1 : ℝ) else 0)
    have hB : HasDerivAt (fun t : ℝ => h (y + t • ξ y) μ ν) (fderiv ℝ (fun z => h z μ ν) y (ξ y)) 0 := by
      have hdf : HasFDerivAt (fun z => h z μ ν) (fderiv ℝ (fun z => h z μ ν) y) (y + (0 : ℝ) • ξ y) := by
        simpa using (diff_of_smooth (hh μ ν) y).hasFDerivAt
      exact hdf.comp_hasDerivAt 0 hpath
    have := (hA.mul hB).mul hC
    convert this using 1
    by_cases hμ : μ = a <;> by_cases hν : ν = b <;> simp [hμ, hν]
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun ν _ => hterm μ ν
  rw [hs.deriv]
  unfold lieDeriv
  simp only [Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, fderiv_eq_sum_pd]
  have hi : ∀ x : Fin d, ∑ x_1 : Fin d, (if x = a then h y x x_1 * Lightlike.pd b (fun z => ξ z x_1) y else 0) =
      if x = a then ∑ x_1 : Fin d, h y x x_1 * Lightlike.pd b (fun z => ξ z x_1) y else 0 := fun x => by
    split_ifs <;> simp
  simp only [hi, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hc : ∑ x, Lightlike.pd a (fun z => ξ z x) y * h y x b = ∑ x, h y x b * Lightlike.pd a (fun y => ξ y x) y :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hc]
  ring

lemma hasDerivAt_of_jointSmooth {G : ℝ → (Fin d → ℝ) → ℝ} (hG : JointSmooth G) (y : Fin d → ℝ) :
    HasDerivAt (fun t => G t y) (deriv (fun t => G t y) 0) 0 := by
  have hι : DifferentiableAt ℝ (fun s : ℝ => ((s, y) : ℝ × (Fin d → ℝ))) 0 :=
    (differentiableAt_id.prodMk (differentiableAt_const y))
  exact (((hG.differentiable (by simp)) _).comp 0 hι).hasDerivAt

/-- **The 2-jet of the pullback by the flow is differentiable in `t`, with derivative the 2-jet of `ℒ_ξ h`.** -/
theorem hasDerivAt_jet_pullback {ξ : VectorField d} {h : TensorField d} (hξ : SmoothVec ξ)
    (hh : SmoothTensor h) (x : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => jetAt (fun y => Lightlike.pullback h (flowMap ξ t) y) x)
      (jetAt (lieTensor ξ h) x) 0 := by
  have hL : ∀ a b z, deriv (fun t => flowComp ξ h a b t z) 0 = lieDeriv ξ h a b z :=
    fun a b z => deriv_flowComp_zero hξ hh a b z
  have hLf : ∀ a b, (fun z => deriv (fun t => flowComp ξ h a b t z) 0) = fun z => lieDeriv ξ h a b z :=
    fun a b => funext (hL a b)
  refine HasDerivAt.prodMk ?_ (HasDerivAt.prodMk ?_ ?_)
  · refine hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun b => ?_
    have := hasDerivAt_of_jointSmooth (jointSmooth_flowComp hξ hh a b) x
    rw [hL a b x] at this
    exact this
  · refine hasDerivAt_pi.mpr fun k => hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun b => ?_
    have := hasDerivAt_of_jointSmooth (jointSmooth_pd (jointSmooth_flowComp hξ hh a b) k) x
    rw [deriv_pd_comm (jointSmooth_flowComp hξ hh a b) k 0 x, hLf a b] at this
    exact this
  · refine hasDerivAt_pi.mpr fun k => hasDerivAt_pi.mpr fun l => hasDerivAt_pi.mpr fun a =>
      hasDerivAt_pi.mpr fun b => ?_
    have h1 := jointSmooth_pd (jointSmooth_flowComp hξ hh a b) l
    have := hasDerivAt_of_jointSmooth (jointSmooth_pd h1 k) x
    have e2 : (fun z => deriv (fun t => Lightlike.pd l (flowComp ξ h a b t) z) 0) =
        fun z => Lightlike.pd l (fun w => lieDeriv ξ h a b w) z := by
      funext z
      rw [deriv_pd_comm (jointSmooth_flowComp hξ hh a b) l 0 z, hLf a b]
    rw [deriv_pd_comm h1 k 0 x, e2] at this
    exact this

end Lightlike.Canonical

end
