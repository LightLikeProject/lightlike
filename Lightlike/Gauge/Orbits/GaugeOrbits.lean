import Lightlike.Gauge.FlowDeriv
import Lightlike.Gauge.KernelSpan
import Lightlike.Gauge.PoissonJacobi
import Lightlike.ODE.Frobenius

/-!
# Gauge orbits of first-class constraints (Wipf, Theorem 5)

For constraints `γ_a` on the flat phase space `X × X` that are first class with structure
functions, `{γ_a, γ_b} = ∑ c, s_{ab}^c γ_c` (Wipf's (5.22)), and regular at a point `x₀` of the
constraint surface `Γ` (their gradients are linearly independent there), the Hamiltonian vector
fields `X_a` of the constraints generate `M`-dimensional manifolds in `Γ`: through every point `x`
of `Γ` near `x₀` there is a map `t ↦ f (t, x)` of `t ∈ ℝ^M` near `0`, with values in `Γ`,
`f (0, x) = x`, whose derivative is injective with range the span of the `X_a (f (t, x))`
(`Lightlike.Gauge.exists_gauge_orbit`). These are the gauge orbits.

The proof is Wipf's: `[X_a, X_b] = -X_{{γ_a, γ_b}} ≈ -s_{ab}^c X_c` on `Γ` (his (5.27);
`lieBracket_hamField`, `lieBracket_hamField_mem_hamSpan`), and the Frobenius theorem, in the form
for a family that is involutive on an invariant set
(`Lightlike.ODE.exists_integral_manifold_of_involutive_on`), since for point-dependent structure
functions the fields are involutive on the constraint surface only.

## References

* `wipf-1993`: A. Wipf, *Hamilton's Formalism for Systems with Constraints*, arXiv:hep-th/9312078,
  Section 5.2: equation (5.22), page 28, and Theorem 5 with equation (5.27), page 30; the
  regularity conditions are those of Section 3.1, page 12 (assumed for all constraints in
  Section 3.3, page 17). Differences from the source: the phase space is the flat `X × X` of a
  finite-dimensional inner product space `X` (the source has a `2N`-dimensional phase space with
  a symplectic form), the constraints are `C²` and the structure functions `C¹` (the source says
  smooth), and the statement is local, near a point where the gradients are independent.
-/

open Set Metric Filter Topology VectorField ClassicalMechanics InnerProductSpace
open scoped ContDiff

noncomputable section

namespace Lightlike.Gauge

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] {m : ℕ}

/-- The Hamiltonian vector field of an observable is minus the Hamiltonian vector of its
differential: `X_g = -hamVec (dg)`. -/
theorem hamField_eq_neg_hamVec (g : X → X → ℝ) (z : X × X)
    (hd : DifferentiableAt ℝ (fun y : X × X => g y.1 y.2) z) :
    hamField g z.1 z.2 = -hamVec (fderiv ℝ (fun y : X × X => g y.1 y.2) z) := by
  show (-(gradient (fun q' => g z.1 q') z.2), gradient (fun p' => g p' z.2) z.1) = _
  rw [gradient_p_eq g z hd, gradient_q_eq g z hd, hamVec, Prod.neg_mk, neg_neg]

/-- The derivative of the Hamiltonian vector field of a `C²` observable. -/
theorem hasFDerivAt_hamField (g : X → X → ℝ) (hg : ContDiff ℝ 2 (fun y : X × X => g y.1 y.2))
    (z : X × X) :
    HasFDerivAt (fun y : X × X => hamField g y.1 y.2)
      (-(hamL.comp (fderiv ℝ (fderiv ℝ (fun y : X × X => g y.1 y.2)) z))) z := by
  set G : X × X → ℝ := fun y => g y.1 y.2 with hG
  have heq : (fun y : X × X => hamField g y.1 y.2) = fun y => -(hamL (fderiv ℝ G y)) := by
    funext y
    rw [hamField_eq_neg_hamVec g y (hg.differentiable (by norm_num) y), hamL_apply]
  have hG' : DifferentiableAt ℝ (fderiv ℝ G) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z
  have hl : HasFDerivAt (⇑(hamL (X := X))) hamL (fderiv ℝ G z) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (hamL (X := X))
  have hu : HasFDerivAt (fun y => hamL (fderiv ℝ G y)) (hamL.comp (fderiv ℝ (fderiv ℝ G) z)) z :=
    HasFDerivAt.comp (𝕜 := ℝ) (g := ⇑(hamL (X := X))) (f := fderiv ℝ G) z hl hG'.hasFDerivAt
  rw [heq]
  exact hu.neg

/-- **The Lie bracket of two Hamiltonian vector fields** is the Hamiltonian vector of the
differential of the Poisson bracket: `[X_g, X_h] = hamVec (d{g, h}) = -X_{{g, h}}`
(Wipf, (5.27), first equality). Here `{g, h}` is written `y ↦ dh_y (hamVec dg_y)`
(`poissonBracket_eq_hamVec`). -/
theorem lieBracket_hamField (g h : X → X → ℝ) (hg : ContDiff ℝ 2 (fun y : X × X => g y.1 y.2))
    (hh : ContDiff ℝ 2 (fun y : X × X => h y.1 y.2)) (z : X × X) :
    lieBracket ℝ (fun y : X × X => hamField g y.1 y.2) (fun y : X × X => hamField h y.1 y.2) z =
      hamVec (fderiv ℝ (fun y : X × X => fderiv ℝ (fun y : X × X => h y.1 y.2) y
        (hamVec (fderiv ℝ (fun y : X × X => g y.1 y.2) y))) z) := by
  set G : X × X → ℝ := fun y => g y.1 y.2 with hG
  set H : X × X → ℝ := fun y => h y.1 y.2 with hH
  have sG := (hg.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  have sH := (hh.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  have hdG : DifferentiableAt ℝ G z := hg.differentiable (by norm_num) z
  have hdH : DifferentiableAt ℝ H z := hh.differentiable (by norm_num) z
  rw [lieBracket, (hasFDerivAt_hamField h hh z).fderiv, (hasFDerivAt_hamField g hg z).fderiv,
    (hasFDerivAt_bracket G H hg hh z).fderiv, hamField_eq_neg_hamVec g z hdG,
    hamField_eq_neg_hamVec h z hdH]
  simp only [neg_apply, ContinuousLinearMap.comp_apply, map_neg, neg_neg, ← hG, ← hH]
  simp only [← hamL_apply]
  rw [← map_sub]
  congr 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hamL_apply]
  have e1 := sG.eq v (hamVec (fderiv ℝ H z))
  have e2 := sH.eq v (hamVec (fderiv ℝ G z))
  have e3 := hamVec_antisymm (fderiv ℝ (fderiv ℝ G) z v) (fderiv ℝ H z)
  linarith

omit [CompleteSpace X] in
/-- `pairing` is linear in its second argument over finite combinations. -/
theorem pairing_sum_smul {ι : Type*} (s : Finset ι) (u : X × X) (c : ι → ℝ) (v : ι → X × X) :
    pairing u (∑ k ∈ s, c k • v k) = ∑ k ∈ s, c k * pairing u (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairing]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [pairing, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, inner_add_right,
      inner_smul_right]
    ring

variable (γ : Fin m → X → X → ℝ)

/-- The Hamiltonian vector fields of the constraints, as vector fields on the phase space. -/
def constraintField (a : Fin m) (z : X × X) : X × X := hamField (γ a) z.1 z.2

/-- **Involutivity on the constraint surface** (Wipf, (5.27)): for constraints with structure
functions `{γ_a, γ_b} = ∑ c, s_{ab}^c γ_c`, the bracket `[X_a, X_b]` lies in the span of the `X_c`
at every point of the constraint surface. -/
theorem lieBracket_constraintField_mem_span
    (hγ : ∀ a, ContDiff ℝ 2 (fun z : X × X => γ a z.1 z.2))
    (s : Fin m → Fin m → Fin m → X × X → ℝ) (hs : ∀ a b c, Differentiable ℝ (s a b c))
    (hfc : ∀ a b (z : X × X), poissonBracket (γ a) (γ b) z.1 z.2 = ∑ c, s a b c z * γ c z.1 z.2)
    {y : X × X} (hy : y ∈ constraintSet γ) (a b : Fin m) :
    lieBracket ℝ (constraintField γ a) (constraintField γ b) y ∈
      Submodule.span ℝ (range fun c => constraintField γ c y) := by
  have hd : ∀ a, Differentiable ℝ (fun z : X × X => γ a z.1 z.2) := fun a =>
    (hγ a).differentiable (by norm_num)
  have hbr : (fun z : X × X => fderiv ℝ (fun z : X × X => γ b z.1 z.2) z
      (hamVec (fderiv ℝ (fun z : X × X => γ a z.1 z.2) z))) =
      fun z => ∑ c, s a b c z * γ c z.1 z.2 := by
    funext z
    rw [← poissonBracket_eq_hamVec (γ a) (γ b) z (hd a z) (hd b z), hfc]
  have hder : HasFDerivAt (fun z : X × X => ∑ c, s a b c z * γ c z.1 z.2)
      (∑ c, (s a b c y • fderiv ℝ (fun z : X × X => γ c z.1 z.2) y +
        γ c y.1 y.2 • fderiv ℝ (s a b c) y)) y :=
    HasFDerivAt.fun_sum fun c _ => ((hs a b c y).hasFDerivAt).mul ((hd c y).hasFDerivAt)
  have hzero : ∀ c, γ c y.1 y.2 = 0 := fun c => hy c
  show lieBracket ℝ (fun z : X × X => hamField (γ a) z.1 z.2)
    (fun z : X × X => hamField (γ b) z.1 z.2) y ∈ _
  rw [lieBracket_hamField (γ a) (γ b) (hγ a) (hγ b) y, hbr, hder.fderiv, ← hamL_apply, map_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  rw [hzero c, zero_smul, add_zero, map_smul, hamL_apply]
  have h1 : hamVec (fderiv ℝ (fun z : X × X => γ c z.1 z.2) y) = -constraintField γ c y := by
    rw [constraintField, hamField_eq_neg_hamVec (γ c) y (hd c y), neg_neg]
  rw [h1]
  exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.subset_span ⟨c, rfl⟩))

/-- **First-class constraints with structure functions** (Wipf, (5.22)): the Poisson brackets of
the constraints are combinations `{γ_a, γ_b} = ∑ c, s_{ab}^c γ_c` of the constraints, with `C¹`
coefficients `s_{ab}^c` that may depend on the phase-space point. -/
def IsFirstClassWith (s : Fin m → Fin m → Fin m → X × X → ℝ) : Prop :=
  (∀ a b c, ContDiff ℝ 1 (s a b c)) ∧
    ∀ a b (z : X × X), poissonBracket (γ a) (γ b) z.1 z.2 = ∑ c, s a b c z * γ c z.1 z.2

/-- **The constraint surface is invariant under fields in the span of the `X_a`.** Let `c` solve
`ċ = ∑ k, coef k (c) • X_k (c)` on `[-T, T]`, inside a set `U` on which the coefficients are
continuous, for first-class constraints with structure functions. If `c 0` is on the constraint
surface, so is `c t` for all `t ∈ [-T, T]`. -/
theorem constraintSet_invariant (hγ : ∀ a, ContDiff ℝ 2 (fun z : X × X => γ a z.1 z.2))
    {s : Fin m → Fin m → Fin m → X × X → ℝ} (hs : IsFirstClassWith γ s)
    (coef : Fin m → X × X → ℝ) {U : Set (X × X)} (hcoef : ∀ k, ContinuousOn (coef k) U)
    (c : ℝ → X × X) {T : ℝ}
    (hc : ∀ t ∈ Icc (-T) T,
      HasDerivAt c (∑ k, coef k (c t) • constraintField γ k (c t)) t ∧ c t ∈ U)
    (h0 : c 0 ∈ constraintSet γ) : ∀ t ∈ Icc (-T) T, c t ∈ constraintSet γ := by
  have hd : ∀ a, Differentiable ℝ (fun z : X × X => γ a z.1 z.2) := fun a =>
    (hγ a).differentiable (by norm_num)
  set g : ℝ → Fin m → ℝ := fun t b => γ b (c t).1 (c t).2 with hgdef
  set g' : ℝ → Fin m → ℝ := fun t b =>
    ∑ k, coef k (c t) * ∑ e, s b k e (c t) * γ e (c t).1 (c t).2 with hg'def
  have hg : ∀ t ∈ Icc (-T) T, HasDerivWithinAt g (g' t) (Icc (-T) T) t := by
    intro t ht
    refine HasDerivAt.hasDerivWithinAt (hasDerivAt_pi.2 fun b => ?_)
    have h1 := hasDerivAt_comp_curve (γ b) c (hd b (c t)) (hc t ht).1
    have e : ∀ k, pairing (phaseGrad (γ b) (c t).1 (c t).2) (constraintField γ k (c t)) =
        ∑ e, s b k e (c t) * γ e (c t).1 (c t).2 := fun k => by
      rw [constraintField, pairing_hamField, hs.2]
    rw [pairing_sum_smul] at h1
    simp only [e] at h1
    exact h1
  -- a bound for the coefficient matrix along the curve
  have hcc : ContinuousOn c (Icc (-T) T) := fun t ht =>
    (hc t ht).1.continuousAt.continuousWithinAt
  have hmaps : MapsTo c (Icc (-T) T) U := fun t ht => (hc t ht).2
  set A : ℝ → ℝ := fun t => ∑ b, ∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)| with hA
  have hAc : ContinuousOn A (Icc (-T) T) := by
    refine continuousOn_finsetSum _ fun b _ => continuousOn_finsetSum _ fun k _ =>
      continuousOn_finsetSum _ fun e _ => ?_
    exact (((hcoef k).comp hcc hmaps).abs).mul
      (((hs.1 b k e).continuous.comp_continuousOn hcc).abs)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hAc
  have hbound : ∀ t ∈ Icc (-T) T, ‖g' t‖ ≤ C * ‖g t‖ := by
    intro t ht
    have hA0 : 0 ≤ A t := Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun k _ =>
      Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hAC : A t ≤ C := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC t ht)
    have hC0 : 0 ≤ C := hA0.trans hAC
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (norm_nonneg _))).2 fun b => ?_
    have hge : ∀ e, |γ e (c t).1 (c t).2| ≤ ‖g t‖ := fun e => by
      have := norm_le_pi_norm (g t) e
      simpa [Real.norm_eq_abs, hgdef] using this
    have h1 : |g' t b| ≤ ∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)| * ‖g t‖ := by
      calc |g' t b| ≤ ∑ k, |coef k (c t) * ∑ e, s b k e (c t) * γ e (c t).1 (c t).2| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)| * ‖g t‖ := by
            refine Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul]
            refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
              (abs_nonneg _)).trans ?_
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun e _ => ?_
            rw [abs_mul, ← mul_assoc]
            exact mul_le_mul_of_nonneg_left (hge e)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    have h2 : ∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)| * ‖g t‖ =
        (∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)|) * ‖g t‖ := by
      simp only [Finset.sum_mul]
    have h3 : ∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)| ≤ A t :=
      Finset.single_le_sum (f := fun b => ∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)|)
        (fun b _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun e _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ b)
    rw [Real.norm_eq_abs]
    calc |g' t b| ≤ (∑ k, ∑ e, |coef k (c t)| * |s b k e (c t)|) * ‖g t‖ := h2 ▸ h1
      _ ≤ C * ‖g t‖ := mul_le_mul_of_nonneg_right (h3.trans hAC) (norm_nonneg _)
  intro t ht a
  have h1 := Lightlike.ODE.norm_le_exp_of_deriv_le hg hbound t ht
  have h00 : g 0 = 0 := funext fun b => h0 b
  rw [h00, norm_zero, zero_mul] at h1
  have h2 : g t = 0 := norm_le_zero_iff.1 h1
  exact congrFun h2 a

/-- The Hamiltonian vector fields of constraints with linearly independent gradients are linearly
independent. -/
theorem linearIndependent_constraintField {x₀ : X × X}
    (hreg : LinearIndependent ℝ fun a => phaseGrad (γ a) x₀.1 x₀.2) :
    LinearIndependent ℝ fun a => constraintField γ a x₀ := by
  set J : X × X →ₗ[ℝ] X × X := (-(LinearMap.snd ℝ X X)).prod (LinearMap.fst ℝ X X) with hJ
  have hker : LinearMap.ker J = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => ?_
    have h1 := congrArg Prod.fst hu
    have h2 := congrArg Prod.snd hu
    simp only [hJ, LinearMap.prod_apply, Function.prod, LinearMap.neg_apply, LinearMap.snd_apply,
      LinearMap.fst_apply, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at h1 h2
    exact Prod.ext h2 h1
  have := hreg.map' J hker
  exact this

/-- **Gauge orbits** (Wipf, Theorem 5): on the constraint surface of first-class constraints the
Hamiltonian vector fields `X_a` of the constraints generate `M`-dimensional manifolds.

Let the constraints `γ_a`, `a : Fin m`, on the phase space `X × X` of a finite-dimensional `X` be
`C²` and first class with `C¹` structure functions, `{γ_a, γ_b} = ∑ c, s_{ab}^c γ_c`, and let
their gradients be linearly independent at a point `x₀` (Wipf's regularity condition, which he
assumes on the constraint surface `Γ`; `x₀` itself need not lie on `Γ`). Then there
are `ε > 0` and a map `f` of `(t, x)`, `t ∈ ℝ^m`, with `f (0, x) = x` for `x` within `ε` of `x₀`,
such that for every `x ∈ Γ` within `ε` of `x₀` and every `‖t‖ < ε`: `f (t, x) ∈ Γ`, `f` is
differentiable at `(t, x)`, and its derivative in `t` is injective with range the span of the
`X_a (f (t, x))`. So `t ↦ f (t, x)` is an `m`-dimensional surface in `Γ` through `x` to which the
`X_a` are tangent: the gauge orbit. -/
theorem exists_gauge_orbit [FiniteDimensional ℝ X]
    (hγ : ∀ a, ContDiff ℝ 2 (fun z : X × X => γ a z.1 z.2))
    {s : Fin m → Fin m → Fin m → X × X → ℝ} (hs : IsFirstClassWith γ s)
    {x₀ : X × X}
    (hreg : LinearIndependent ℝ fun a => phaseGrad (γ a) x₀.1 x₀.2) :
    ∃ (ε : ℝ) (f : (Fin m → ℝ) × (X × X) → X × X)
      (f' : (Fin m → ℝ) × (X × X) → ((Fin m → ℝ) × (X × X) →L[ℝ] X × X)), 0 < ε ∧
      (∀ x ∈ ball x₀ ε, f (0, x) = x) ∧
      ∀ t ∈ ball (0 : Fin m → ℝ) ε, ∀ x ∈ ball x₀ ε, x ∈ constraintSet γ →
        f (t, x) ∈ constraintSet γ ∧ HasFDerivAt f (f' (t, x)) (t, x) ∧
        Function.Injective (fun τ : Fin m → ℝ => f' (t, x) (τ, 0)) ∧
        range (fun τ : Fin m → ℝ => f' (t, x) (τ, 0)) =
          (hamSpan γ (f (t, x)).1 (f (t, x)).2 : Set (X × X)) := by
  have hXc : ∀ a (y : X × X), ContDiffAt ℝ 1 (constraintField γ a) y := fun a y =>
    (contDiff_hamField (γ a) (hγ a)).contDiffAt
  obtain ⟨π, hπ⟩ := Lightlike.ODE.exists_clm_apply_eq_single
    (linearIndependent_constraintField γ hreg)
  have hUe := Lightlike.ODE.eventually_isUnit_frameGram (X := constraintField γ)
    (fun k => hXc k x₀) hπ
  obtain ⟨a₀, ha₀, hU⟩ := Metric.eventually_nhds_iff_ball.1 hUe
  have hinv : ∀ᶠ y in 𝓝 x₀, y ∈ constraintSet γ → ∀ i j,
      lieBracket ℝ (constraintField γ i) (constraintField γ j) y ∈
        Submodule.span ℝ (range fun k => constraintField γ k y) :=
    Eventually.of_forall fun y hy i j =>
      lieBracket_constraintField_mem_span γ hγ s
        (fun a b c => (hs.1 a b c).differentiable (by norm_num)) hs.2 hy i j
  obtain ⟨ε, f, f', hε, h0, hd⟩ := Lightlike.ODE.exists_integral_manifold_of_involutive_on
    (Γ := constraintSet γ) (fun k => hXc k x₀) hπ hinv ha₀
    (fun i c T hc hc0 => constraintSet_invariant γ hγ hs
      (fun k => Lightlike.ODE.frameCoeff π (constraintField γ) i k)
      (U := ball x₀ a₀)
      (fun k y hy => ((Lightlike.ODE.contDiffAt_frameCoeff (fun k => hXc k y) (hU y hy) i
        k).continuousAt).continuousWithinAt) c
      (fun t ht => ⟨(hc t ht).1, (hc t ht).2⟩) hc0)
  refine ⟨ε, f, f', hε, fun x hx => (h0 x hx).1, fun t ht x hx hxΓ => ?_⟩
  obtain ⟨hfΓ, hπsum, hrange⟩ := (hd t ht x hx).2 hxΓ
  refine ⟨hfΓ, (hd t ht x hx).1.1, fun τ τ' hττ => ?_, hrange⟩
  have h' : f' (t, x) (τ, 0) = f' (t, x) (τ', 0) := hττ
  rw [← hπsum τ, ← hπsum τ', h']

end Lightlike.Gauge
