import Mathlib
import Lightlike.Dirac.SpinManifold
import Lightlike.Dirac.LichnerowiczGeneral
import Lightlike.Dirac.SecondOrder
import Lightlike.Dirac.Lichnerowicz
import Lightlike.Dirac.LichnerowiczFormula
import Lightlike.Dirac.RicciIdentity
import Lightlike.Dirac.SpinDeriv
import Lightlike.Spacetime.CurvatureSymmetries
import Lightlike.Spacetime.LieDerivation
import Lightlike.Spacetime.HypersurfaceConstraints
import Lightlike.Spacetime.LeviCivitaSmooth
import Lightlike.Spacetime.ChartCurvature

/-!
# The Lichnerowicz formula on a spin manifold

For a spin structure `S` (atlas form) of a metric `g` and a Clifford module `ρ`, in every frame
`i` of `S`: `D² φ = ∇*∇ φ + (R/4) φ`, with `R` the scalar curvature of the Levi-Civita connection
(`SpinStructure.dirac_sq`).  The proof is the classical one: `D² = ∑ₐ_b γₐγ_b ∇²ₐ_b`, the Ricci
identity `∇²ₐ_b - ∇²_bₐ = ¼ ∑ R_abkl γₖγₗ` for the spin connection, and the Clifford contraction
`½ ∑ γₐγ_b ¼ ∑ R_abkl γₖγₗ = R/4` (`curvatureTerm_eq`, with the symmetries of the Riemann tensor of
the Levi-Civita connection).

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, Theorem 8.8 (the
  Lichnerowicz formula `D² = ∇*∇ + κ/4`); the statement here is in the atlas form of a spin
  structure.
-/

open Bundle Manifold CliffordAlgebra Filter VectorField
open scoped Manifold ContDiff Matrix Topology

namespace Lightlike.Dirac

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*} (S : SpinStructure g ι) (ρ : CliffordRep n V)

/-- The connection coefficients in an orthonormal frame are skew: `ω_a bc = -ω_a cb`
(metric compatibility of the Levi-Civita connection). -/
lemma SpinStructure.connForm_skew {i : ι} {x : M} (hx : x ∈ S.dom i) (a b c : Fin n) :
    S.connForm i x a b c = -S.connForm i x a c b := by
  have h := leviCivita_compat g (S.frame i a) (S.frame i b) (S.frame i c) x
    (S.mdiffAt_frame a hx) (S.mdiffAt_frame b hx) (S.mdiffAt_frame c hx)
  have hc : (fun y => g.g y (S.frame i b y) (S.frame i c y)) =ᶠ[𝓝 x]
      fun _ => if b = c then (1 : ℝ) else 0 := by
    filter_upwards [(S.dom_open i).mem_nhds hx] with y hy
    exact S.frame_orthonormal i b c y hy
  rw [hc.mfderiv_eq, mfderiv_const] at h
  simp only [ContinuousLinearMap.zero_apply] at h
  unfold SpinStructure.connForm SpinStructure.connFormV
  rw [g.symm x (S.frame i b x)] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- `∇ₐ` of a finite sum. -/
lemma SpinStructure.nabla_finsum (i : ι) (a : Fin n) {ψ : Fin n → M → V} {x : M}
    (h : ∀ b, FunDiffAt (ψ b) x) :
    S.nabla ρ i a (fun y => ∑ b, ψ b y) x = ∑ b, S.nabla ρ i a (ψ b) x := by
  unfold SpinStructure.nabla SpinStructure.nablaV
  rw [mvfderiv_finsum h]
  simp [map_sum, Finset.sum_add_distrib]

/-- Clifford multiplication is parallel up to the connection coefficients:
`∇ₐ (γₖ ψ) = γₖ ∇ₐ ψ + ∑ⱼ ωₐ,ₖⱼ γⱼ ψ`. -/
lemma SpinStructure.nabla_gam {i : ι} {x : M} (hx : x ∈ S.dom i) (a k : Fin n) {ψ : M → V}
    (hψ : FunDiffAt ψ x) :
    S.nabla ρ i a (fun y => gam ρ k (ψ y)) x =
      gam ρ k (S.nabla ρ i a ψ x) + ∑ j, S.connForm i x a k j • gam ρ j (ψ x) := by
  have hd : mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => gam ρ k (ψ y)) x (S.frame i a x) =
      gam ρ k (mvfderiv 𝓘(ℝ, Fin n → ℝ) ψ x (S.frame i a x)) := by
    rw [mvfderiv_clm_apply (fun _ => gam ρ k) ψ x mdifferentiableAt_const hψ, mvfderiv_const]
    simp
  have hc := congrArg (fun L => L (ψ x)) (spinForm_comm ρ (S.connForm_skew hx a) k)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply] at hc
  unfold SpinStructure.nabla SpinStructure.nablaV
  rw [hd, map_add, add_assoc]
  congr 1
  rw [← hc]
  unfold SpinStructure.connForm
  abel

/-- The second covariant derivative `∇²ₐ_b φ = ∇ₐ ∇_b φ - ∇_{∇ₐ F_b} φ` in the frame `i`. -/
noncomputable def SpinStructure.hess (i : ι) (φ : M → V) (x : M) (a b : Fin n) : V :=
  S.nabla ρ i a (fun y => S.nabla ρ i b φ y) x - ∑ k, S.connForm i x a b k • S.nabla ρ i k φ x

/-- The rough Laplacian is minus the trace of the second covariant derivative. -/
lemma SpinStructure.roughLaplacian_eq_hess (i : ι) (φ : M → V) (x : M) :
    S.roughLaplacian ρ i φ x = -∑ a, S.hess ρ i φ x a a := rfl

/-- `D² φ = ∑ₐ_b γₐγ_b ∇²ₐ_b φ`. -/
theorem SpinStructure.dirac_dirac_hess {i : ι} {x : M} (hx : x ∈ S.dom i) {φ : M → V}
    (hf : ∀ b, FunDiffAt (fun y => S.nabla ρ i b φ y) x) :
    S.dirac ρ i (S.dirac ρ i φ) x = ∑ a, ∑ b, gam ρ a (gam ρ b (S.hess ρ i φ x a b)) := by
  have h1 : ∀ a, S.nabla ρ i a (fun y => ∑ b, gam ρ b (S.nabla ρ i b φ y)) x =
      ∑ b, (gam ρ b (S.nabla ρ i a (fun y => S.nabla ρ i b φ y) x) +
        ∑ k, S.connForm i x a b k • gam ρ k (S.nabla ρ i b φ x)) := by
    intro a
    rw [S.nabla_finsum ρ i a fun b => (gam ρ b).mdifferentiableAt.comp x (hf b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact S.nabla_gam ρ hx a b (hf b)
  have h0 : S.dirac ρ i (S.dirac ρ i φ) x =
      ∑ a, ∑ b, gam ρ a (gam ρ b (S.nabla ρ i a (fun y => S.nabla ρ i b φ y) x)) +
      ∑ a, ∑ b, ∑ k, S.connForm i x a b k • gam ρ a (gam ρ k (S.nabla ρ i b φ x)) := by
    unfold SpinStructure.dirac
    simp only [h1, map_sum, map_add, Finset.sum_add_distrib, map_smul]
  rw [h0]
  have h2 : ∑ a, ∑ b, ∑ k, S.connForm i x a b k • gam ρ a (gam ρ k (S.nabla ρ i b φ x)) =
      ∑ a, ∑ b, ∑ k, S.connForm i x a k b • gam ρ a (gam ρ b (S.nabla ρ i k φ x)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  rw [h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [SpinStructure.hess, map_sub, map_sum, map_smul, S.connForm_skew hx a _ b, neg_smul,
    Finset.sum_neg_distrib]
  abel

/-- `D² φ = -∑ₐ ∇²ₐₐ φ + ½ ∑ₐ_b γₐγ_b (∇²ₐ_b - ∇²_bₐ) φ`. -/
theorem SpinStructure.dirac_dirac_antisymm {i : ι} {x : M} (hx : x ∈ S.dom i) {φ : M → V}
    (hf : ∀ b, FunDiffAt (fun y => S.nabla ρ i b φ y) x) :
    S.dirac ρ i (S.dirac ρ i φ) x = S.roughLaplacian ρ i φ x +
      (1 / 2 : ℝ) • ∑ a, ∑ b, gam ρ a (gam ρ b (S.hess ρ i φ x a b - S.hess ρ i φ x b a)) := by
  rw [S.dirac_dirac_hess ρ hx hf, S.roughLaplacian_eq_hess]
  exact clifford_double_sum ρ (fun a b => S.hess ρ i φ x a b)


/-! ### Regularity -/

section Regularity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The chain rule through the chart at `x`, at a point `y` of its source. -/
lemma mvfderiv_eq_chart_at (φ : M → F) {x y : M}
    (hy : y ∈ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).source) (hφ : FunDiffAt φ y)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) y) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) φ y v =
      fderiv ℝ (φ ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) x y)
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x) y v) := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  have h1 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ y :=
    mdifferentiableAt_extChartAt (by rwa [hψ, extChartAt_source] at hy)
  have h2 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ.symm (ψ y) := by
    have := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℝ, Fin n → ℝ)) (x := x)
      (ψ.map_source hy)
    simpa [hψ, mdifferentiableWithinAt_univ] using this
  have h3 : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) (φ ∘ ψ.symm) (ψ y) := by
    refine MDifferentiableAt.comp (ψ y) ?_ h2
    rw [ψ.left_inv hy]; exact hφ
  have heq : φ =ᶠ[𝓝 y] (φ ∘ ψ.symm) ∘ ψ := by
    filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hy] with z hz
    simp [ψ.left_inv hz]
  rw [mvfderiv_congr_nhds' heq, mvfderiv_comp y h3 h1]
  simp [mvfderiv_eq_fderiv]
  rfl

/-- **The directional derivative of a smooth function along a smooth field is differentiable.** -/
lemma mdiffAt_mvfderiv_apply {φ : M → F} {X : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y} {x : M}
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞ φ y)
    (hX : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun q : M => (⟨q, X q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x) :
    FunDiffAt (fun y => mvfderiv 𝓘(ℝ, Fin n → ℝ) φ y (X y)) x := by
  set ψ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hψ
  have hsrc : x ∈ ψ.source := mem_extChartAt_source x
  have hbase : x ∈ (tTriv (E := Fin n → ℝ) (M := M) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  -- the components of `X` in the chart
  have hXh : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (hat x X) x :=
    (mdiffAt_hat_iff x X hbase).1 (hX.mdifferentiableAt (by simp))
  have hhat : ∀ z ∈ ψ.source, hat x X z =
      mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ z (X z) := by
    intro z hz
    have hz' : z ∈ (chartAt (Fin n → ℝ) x).source := by rwa [hψ, extChartAt_source] at hz
    have := TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, Fin n → ℝ)) hz'
    have hzb : z ∈ (tTriv (E := Fin n → ℝ) (M := M) x).baseSet := by
      simpa [tTriv, TangentBundle.trivializationAt_baseSet] using hz'
    have h2 : hat x X z = (tTriv (E := Fin n → ℝ) (M := M) x).continuousLinearMapAt ℝ z (X z) := by
      rw [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply,
        ite_eq_left hzb]
      rfl
    rw [h2]
    exact congrArg (fun L => L (X z)) this
  -- `φ` in the chart is smooth at `ψ x`
  have hφt : ContDiffAt ℝ ∞ (φ ∘ ψ.symm) (ψ x) := by
    have h2 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ∞ ψ.symm (ψ x) := by
      have := contMDiffWithinAt_extChartAt_symm_target (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
        (ψ.map_source hsrc)
      have ht : ψ.target ∈ 𝓝 (ψ x) := extChartAt_target_mem_nhds x
      exact this.contMDiffAt ht
    have h3 : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞ (φ ∘ ψ.symm) (ψ x) := by
      refine ContMDiffAt.comp (ψ x) ?_ h2
      rw [ψ.left_inv hsrc]; exact hφ.self_of_nhds
    exact contMDiffAt_iff_contDiffAt.1 h3
  have hdφ : DifferentiableAt ℝ (fderiv ℝ (φ ∘ ψ.symm)) (ψ x) :=
    (hφt.fderiv_right (m := ∞) le_rfl).differentiableAt (by simp)
  have hψx : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) ψ x :=
    mdifferentiableAt_extChartAt (by rw [hψ, extChartAt_source] at hsrc; exact hsrc)
  have hD : FunDiffAt (fun y => fderiv ℝ (φ ∘ ψ.symm) (ψ y) (hat x X y)) x :=
    (hdφ.comp_mdifferentiableAt hψx).clm_apply hXh
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ, Fin n → ℝ)) x).mem_nhds hsrc, hφ]
    with y hy hφy
  rw [mvfderiv_eq_chart_at φ hy (hφy.mdifferentiableAt (by simp)), hhat y hy]

end Regularity

/-! ### The orthonormal frame is a basis -/

/-- An orthonormal frame is linearly independent. -/
lemma SpinStructure.frame_linearIndependent {i : ι} {x : M} (hx : x ∈ S.dom i) :
    LinearIndependent ℝ (fun a => S.frame i a x) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc m
  have h := congrArg (fun w => g.g x w (S.frame i m x)) hc
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, S.frame_orthonormal i _ _ x hx, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_zero,
    ContinuousLinearMap.zero_apply] at h
  exact h

/-- **Expansion in an orthonormal frame**: `w = ∑ₗ g(w, F_l) F_l`. -/
lemma SpinStructure.frame_expand {i : ι} {x : M} (hx : x ∈ S.dom i)
    (w : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    w = ∑ l, g.g x w (S.frame i l x) • S.frame i l x := by
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) x) := by
    simp [TangentSpace]
  set b := basisOfLinearIndependentOfCardEqFinrank (S.frame_linearIndependent hx) hcard
  have hb : ∀ l, b l = S.frame i l x := fun l => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hw := (b.sum_repr w).symm
  have hcoef : ∀ l, b.repr w l = g.g x w (S.frame i l x) := by
    intro l
    conv_rhs => rw [hw]
    simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, hb, S.frame_orthonormal i _ _ x hx, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_lhs => rw [hw]
  simp only [hcoef, hb]

/-- `∇_v F_k = ∑_l ω_v,kl F_l`. -/
lemma SpinStructure.cov_frame_expand {i : ι} {x : M} (hx : x ∈ S.dom i)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (k : Fin n) :
    leviCivita g (S.frame i k) x v = ∑ l, S.connFormV i x v k l • S.frame i l x :=
  S.frame_expand hx _

/-! ### Smoothness of the connection coefficients -/

/-- The frames are smooth near every point of their domain. -/
lemma SpinStructure.smoothNear_frame {i : ι} (a : Fin n) {x : M} (hx : x ∈ S.dom i) :
    SmoothNear (S.frame i a) x := by
  filter_upwards [(S.dom_open i).mem_nhds hx] with y hy
  exact S.frame_smooth i a y hy

/-- The connection coefficients `y ↦ ω_a bc(y) = g(∇_{F_a} F_b, F_c)(y)` are smooth on the domain
of the frame. -/
lemma SpinStructure.contMDiffAt_connForm {i : ι} {x : M} (hx : x ∈ S.dom i) (a b c : Fin n) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ (fun y => S.connForm i y a b c) x := by
  have hcov := contMDiffAt_covApply (leviCivita g) (S.frame_smooth i a x hx)
    (S.smoothNear_frame b hx)
  exact contMDiffAt_gpair g hcov (S.frame_smooth i c x hx)

lemma SpinStructure.mdiffAt_connForm {i : ι} {x : M} (hx : x ∈ S.dom i) (a b c : Fin n) :
    FunDiffAt (fun y => S.connForm i y a b c) x :=
  (S.contMDiffAt_connForm hx a b c).mdifferentiableAt (by simp)

/-- The spinorial connection form `y ↦ spinForm ρ (ω_b(y))` is differentiable, with derivative the
spinorial form of the derivative of `ω_b`. -/
lemma SpinStructure.mvfderiv_spinForm {i : ι} {x : M} (hx : x ∈ S.dom i) (b : Fin n)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    FunDiffAt (fun y => spinForm ρ (S.connForm i y b)) x ∧
    mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => spinForm ρ (S.connForm i y b)) x v =
      spinForm ρ (Matrix.of fun k l => mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => S.connForm i y b k l) x v) := by
  have hexp : (fun y => spinForm ρ (S.connForm i y b)) =
      fun y => ∑ k, ∑ l, S.connForm i y b k l • ((1 / 4 : ℝ) • (gam ρ k * gam ρ l)) := by
    funext y
    simp only [spinForm, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hterm : ∀ k l, FunDiffAt (fun y => S.connForm i y b k l • ((1 / 4 : ℝ) • (gam ρ k * gam ρ l))) x :=
    fun k l => (S.mdiffAt_connForm hx b k l).smul mdifferentiableAt_const
  have hrow : ∀ k, FunDiffAt
      (fun y => ∑ l, S.connForm i y b k l • ((1 / 4 : ℝ) • (gam ρ k * gam ρ l))) x :=
    fun k => mdiffAt_finsum fun l => hterm k l
  refine ⟨by rw [hexp]; exact mdiffAt_finsum hrow, ?_⟩
  rw [hexp, mvfderiv_finsum hrow]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  simp only [spinForm, Finset.smul_sum, smul_smul, Matrix.of_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mvfderiv_finsum (hterm k)]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (fun y => S.connForm i y b k l • ((1 / 4 : ℝ) • (gam ρ k * gam ρ l))) =
      (fun y => S.connForm i y b k l) • (fun _ => (1 / 4 : ℝ) • (gam ρ k * gam ρ l)) from rfl,
    mvfderiv_smul (S.mdiffAt_connForm hx b k l) mdifferentiableAt_const, mvfderiv_const]
  simp [smul_smul, mul_comm]

/-! ### Second derivatives along fields commute up to the bracket -/

/-- **The derivative of a vector-valued function along `[X, Y]`** is the commutator of the
derivatives along `X` and `Y` (Hahn–Banach reduces it to `mfderiv_mlieBracket`). -/
theorem deriv_comm_V {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : M} {f : M → F}
    (hf : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) ∞ f y)
    {X Y : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hX : SecDiffAt X p) (hY : SecDiffAt Y p)
    (hDY : FunDiffAt (fun z => mvfderiv 𝓘(ℝ, Fin n → ℝ) f z (Y z)) p)
    (hDX : FunDiffAt (fun z => mvfderiv 𝓘(ℝ, Fin n → ℝ) f z (X z)) p) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) f p (mlieBracket 𝓘(ℝ, Fin n → ℝ) X Y p) =
      mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun z => mvfderiv 𝓘(ℝ, Fin n → ℝ) f z (Y z)) p (X p) -
        mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun z => mvfderiv 𝓘(ℝ, Fin n → ℝ) f z (X z)) p (Y p) := by
  rw [eq_iff_forall_dual_eq ℝ]
  intro ℓ
  rw [map_sub]
  set h : M → ℝ := fun z => ℓ (f z) with hh
  have hgsm : ∀ᶠ y in 𝓝 p, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) ∞ h y := by
    filter_upwards [hf] with y hy
    exact ℓ.contDiff.contMDiff.contMDiffAt.comp y hy
  have hd := mfderiv_mlieBracket h X Y p hgsm hX hY
  have hfd : ∀ᶠ y in 𝓝 p, FunDiffAt f y := by
    filter_upwards [hf] with y hy using hy.mdifferentiableAt (by simp)
  have hder : ∀ (W : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y)
      (hW : FunDiffAt (fun z => mvfderiv 𝓘(ℝ, Fin n → ℝ) f z (W z)) p)
      (u : TangentSpace 𝓘(ℝ, Fin n → ℝ) p),
      mvfderiv 𝓘(ℝ, Fin n → ℝ) (dirDeriv h W) p u =
        ℓ (mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun z => mvfderiv 𝓘(ℝ, Fin n → ℝ) f z (W z)) p u) := by
    intro W hW u
    have heq : dirDeriv h W =ᶠ[𝓝 p] fun z => ℓ (mvfderiv 𝓘(ℝ, Fin n → ℝ) f z (W z)) := by
      filter_upwards [hfd] with z hz
      exact mvfderiv_clm_comp ℓ f z hz (W z)
    rw [mvfderiv_congr_nhds' heq]
    exact mvfderiv_clm_comp ℓ _ p hW u
  have hfp : FunDiffAt f p := hfd.self_of_nhds
  calc ℓ (mvfderiv 𝓘(ℝ, Fin n → ℝ) f p (mlieBracket 𝓘(ℝ, Fin n → ℝ) X Y p)) =
        mvfderiv 𝓘(ℝ, Fin n → ℝ) h p (mlieBracket 𝓘(ℝ, Fin n → ℝ) X Y p) :=
        (mvfderiv_clm_comp ℓ f p hfp _).symm
    _ = mvfderiv 𝓘(ℝ, Fin n → ℝ) (dirDeriv h Y) p (X p) -
          mvfderiv 𝓘(ℝ, Fin n → ℝ) (dirDeriv h X) p (Y p) := hd
    _ = _ := by rw [hder Y hDY, hder X hDX]

/-! ### The curvature in an orthonormal frame -/

/-- The Riemann tensor of the Levi-Civita connection in the frame `i`:
`R_abkl = g(R(F_a, F_b) F_k, F_l)`. -/
noncomputable def SpinStructure.riem (i : ι) (x : M) (a b k l : Fin n) : ℝ :=
  (leviCivita g).riemannLowerAt g x (S.frame i a x) (S.frame i b x) (S.frame i k x) (S.frame i l x)

/-- The derivative `d_{F_a} ω_b` of the connection coefficients, as a matrix. -/
noncomputable def SpinStructure.dConn (i : ι) (x : M) (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k l => mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => S.connForm i y b k l) x (S.frame i a x)

/-- `∇_{F_a} (∇_{F_b} F_k)` paired with `F_m`: `d_a ω_bkm + ∑_l ω_bkl ω_alm`. -/
lemma SpinStructure.cov_cov_frame {i : ι} {x : M} (hx : x ∈ S.dom i) (a b k m : Fin n) :
    g.g x (leviCivita g (fun y => leviCivita g (S.frame i k) y (S.frame i b y)) x (S.frame i a x))
      (S.frame i m x) =
      S.dConn i x a b k m + ∑ l, S.connForm i x b k l * S.connForm i x a l m := by
  set σ : Fin n → Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y :=
    fun l => (fun y => S.connForm i y b k l) • S.frame i l
  have hσ : ∀ l, SecDiffAt (σ l) x := fun l =>
    (S.mdiffAt_connForm hx b k l).smul_section (S.mdiffAt_frame l hx)
  have hfield : leviCivita g (fun y => leviCivita g (S.frame i k) y (S.frame i b y)) x =
      leviCivita g (∑ l, σ l) x := by
    refine (leviCivita g).isCovariantDerivativeOn.congr_of_eventuallyEq ?_ ?_ Filter.univ_mem ?_
    · exact (contMDiffAt_covApply (leviCivita g) (S.frame_smooth i b x hx)
        (S.smoothNear_frame k hx)).mdifferentiableAt (by simp)
    · have := MDifferentiableAt.sum_section (s := Finset.univ) (t := σ) (x₀ := x) fun l _ => hσ l
      simpa [Finset.sum_fn] using this
    · filter_upwards [(S.dom_open i).mem_nhds hx] with y hy
      rw [S.cov_frame_expand hy]
      simp [σ, Finset.sum_apply, SpinStructure.connForm]
  rw [hfield, cov_sum (leviCivita g) hσ]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, map_sum,
    ContinuousLinearMap.coe_sum']
  have hl : ∀ l, leviCivita g (σ l) x (S.frame i a x) =
      S.connForm i x b k l • leviCivita g (S.frame i l) x (S.frame i a x) +
        mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => S.connForm i y b k l) x (S.frame i a x) • S.frame i l x := by
    intro l
    rw [(leviCivita g).isCovariantDerivativeOn.leibniz (S.mdiffAt_frame l hx)
      (S.mdiffAt_connForm hx b k l)]
    simp [mvfderiv]
  simp only [hl, map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, S.frame_orthonormal i _ _ x hx, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rfl

/-- **The structure equation**: in an orthonormal frame,
`R_ab = d_a ω_b - d_b ω_a + ω_b ω_a - ω_a ω_b - ω_{[F_a, F_b]}` (matrices in the last two indices). -/
theorem SpinStructure.riem_eq {i : ι} {x : M} (hx : x ∈ S.dom i) (a b : Fin n) :
    (Matrix.of fun k l => S.riem i x a b k l) =
      S.dConn i x a b - S.dConn i x b a +
        (S.connForm i x b * S.connForm i x a - S.connForm i x a * S.connForm i x b) -
        S.connFormV i x (mlieBracket 𝓘(ℝ, Fin n → ℝ) (S.frame i a) (S.frame i b) x) := by
  ext k m
  simp only [Matrix.of_apply, SpinStructure.riem, Connection.riemannLowerAt]
  rw [curvatureAt_apply_eventually (leviCivita g) (S.frame i a) (S.frame i b) (S.frame i k) x
    (S.smoothNear_frame a hx) (S.smoothNear_frame b hx) (S.smoothNear_frame k hx)]
  simp only [map_sub, ContinuousLinearMap.sub_apply, S.cov_cov_frame hx]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, SpinStructure.connFormV]
  ring

/-! ### The Ricci identity for the spin connection -/

/-- **Ricci identity.**  For `φ` smooth near `x`, the antisymmetrized second covariant derivative is
the action of the spinor curvature: `∇²_ab φ - ∇²_ba φ = ¼ ∑_kl R_abkl γ_k γ_l φ`. -/
theorem SpinStructure.hess_antisymm {i : ι} {x : M} (hx : x ∈ S.dom i) {φ : M → V}
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, V) ∞ φ y) (a b : Fin n) :
    S.hess ρ i φ x a b - S.hess ρ i φ x b a =
      spinForm ρ (Matrix.of fun k l => S.riem i x a b k l) (φ x) := by
  have hφx : FunDiffAt φ x := hφ.self_of_nhds.mdifferentiableAt (by simp)
  have hdir : ∀ c, FunDiffAt (fun y => mvfderiv 𝓘(ℝ, Fin n → ℝ) φ y (S.frame i c y)) x := fun c =>
    mdiffAt_mvfderiv_apply hφ (S.frame_smooth i c x hx)
  have hΩ := fun c => S.mvfderiv_spinForm ρ hx c
  -- `∇_a ∇_c φ` expanded
  have hexp : ∀ a c, S.nabla ρ i a (fun y => S.nabla ρ i c φ y) x =
      mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => mvfderiv 𝓘(ℝ, Fin n → ℝ) φ y (S.frame i c y)) x
          (S.frame i a x) +
        spinForm ρ (S.dConn i x a c) (φ x) +
        spinForm ρ (S.connForm i x c) (mvfderiv 𝓘(ℝ, Fin n → ℝ) φ x (S.frame i a x)) +
        spinForm ρ (S.connForm i x a) (S.nabla ρ i c φ x) := by
    intro a c
    have h1 : (fun y => S.nabla ρ i c φ y) =
        (fun y => mvfderiv 𝓘(ℝ, Fin n → ℝ) φ y (S.frame i c y)) +
          fun y => spinForm ρ (S.connForm i y c) (φ y) := rfl
    have h2 : FunDiffAt (fun y => spinForm ρ (S.connForm i y c) (φ y)) x :=
      (hΩ c (S.frame i a x)).1.clm_apply hφx
    unfold SpinStructure.nabla SpinStructure.nablaV
    rw [h1, mvfderiv_add (hdir c) h2, ContinuousLinearMap.add_apply,
      mvfderiv_clm_apply _ _ x (hΩ c (S.frame i a x)).1 hφx, (hΩ c (S.frame i a x)).2]
    simp only [SpinStructure.dConn, SpinStructure.connForm]
    abel
  -- the bracket terms
  have hbr : ∑ k, S.connForm i x a b k • S.nabla ρ i k φ x -
      ∑ k, S.connForm i x b a k • S.nabla ρ i k φ x =
      S.nablaV ρ i x (mlieBracket 𝓘(ℝ, Fin n → ℝ) (S.frame i a) (S.frame i b) x) φ := by
    have ht := cov_torsion leviCivita_torsion (S.mdiffAt_frame a hx) (S.mdiffAt_frame b hx)
    rw [← ht, S.cov_frame_expand hx, S.cov_frame_expand hx (S.frame i b x) a]
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul]
    rw [S.nablaV_sum ρ i]
    simp only [sub_smul, Finset.sum_sub_distrib]
    rfl
  have hcomm := deriv_comm_V hφ (S.mdiffAt_frame a hx) (S.mdiffAt_frame b hx) (hdir b) (hdir a)
  have hbrack := spinForm_bracket ρ (A := S.connForm i x a) (B := S.connForm i x b)
    (S.connForm_skew hx a)
  have hbφ := congrArg (fun L => L (φ x)) hbrack
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply_eq_comp,
    ContinuousLinearMap.comp_apply] at hbφ
  unfold SpinStructure.hess
  rw [hexp a b, hexp b a, S.riem_eq hx a b]
  rw [show ∀ A B C D E : V, A - B - (C - D) = A - C - (B - D) from fun A B C D E => by abel,
    hbr]
  unfold SpinStructure.nablaV
  unfold SpinStructure.nabla SpinStructure.nablaV
  simp only [spinForm_sub, spinForm_add, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, map_add]
  rw [← hbφ, hcomm]
  abel

/-! ### The scalar curvature in the frame -/

/-- The orthonormal frame as a basis of the tangent space. -/
noncomputable def SpinStructure.frameBasis {i : ι} {x : M} (hx : x ∈ S.dom i) :
    Module.Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :=
  basisOfLinearIndependentOfCardEqFinrank (S.frame_linearIndependent hx) (by simp [TangentSpace])

lemma SpinStructure.frameBasis_apply {i : ι} {x : M} (hx : x ∈ S.dom i) (a : Fin n) :
    S.frameBasis hx a = S.frame i a x := by
  simp [SpinStructure.frameBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- **The scalar curvature in an orthonormal frame**: `R = ∑ₐ_b R_baab`. -/
theorem SpinStructure.scalarCurvature_eq {i : ι} {x : M} (hx : x ∈ S.dom i) :
    (leviCivita g).scalarCurvatureAt g x = ∑ a, ∑ b, S.riem i x b a a b := by
  have hf : ∀ a b, g.g x (S.frameBasis hx a) (S.frameBasis hx b) =
      if a = b then (fun _ => (1 : ℝ)) a else 0 := by
    intro a b
    simp [S.frameBasis_apply, S.frame_orthonormal i a b x hx]
  rw [scalarCurvatureAt_frame (leviCivita g) g leviCivita_torsion (leviCivita_compat g) x
    (S.frameBasis hx) (fun _ => 1) (fun _ => by norm_num) hf]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ricciAt_frame (leviCivita g) g x (S.frameBasis hx) (fun _ => 1) (fun _ => by norm_num) hf]
  simp [S.frameBasis_apply, SpinStructure.riem, Connection.riemannLowerAt]

/-! ### The Lichnerowicz formula -/

/-- The symmetries of the frame Riemann tensor of the Levi-Civita connection. -/
lemma SpinStructure.riem_symm {i : ι} {x : M} (hx : x ∈ S.dom i) :
    (∀ a b k l, S.riem i x a b k l = -S.riem i x b a k l) ∧
    (∀ a b k l, S.riem i x a b k l = S.riem i x k l a b) ∧
    (∀ a b k l, S.riem i x a b k l + S.riem i x b k a l + S.riem i x k a b l = 0) := by
  refine ⟨fun a b k l => ?_, fun a b k l => ?_, fun a b k l => ?_⟩
  · exact riemannLowerAt_antisymm_first (leviCivita g) g x _ _ _ _
  · exact riemannLowerAt_pair_symm (leviCivita g) g leviCivita_torsion (leviCivita_compat g) x _ _ _ _
  · have h := bianchi_first_proved (leviCivita g) leviCivita_torsion x (S.frame i a x)
      (S.frame i b x) (S.frame i k x)
    have := congrArg (fun w => g.g x w (S.frame i l x)) h
    simp only [map_add, ContinuousLinearMap.add_apply, map_zero, ContinuousLinearMap.zero_apply] at this
    simpa [SpinStructure.riem, Connection.riemannLowerAt] using this

/-- **The Lichnerowicz formula** on a manifold with a spin structure (atlas form): in every frame
`i`, for `φ` smooth near a point `x` of the frame domain,
`D² φ = ∇*∇ φ + (R / 4) φ` at `x`, with `R` the scalar curvature of the Levi-Civita connection. -/
theorem SpinStructure.dirac_sq {i : ι} {x : M} (hx : x ∈ S.dom i) {φ : M → V}
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, V) ∞ φ y) :
    S.dirac ρ i (S.dirac ρ i φ) x =
      S.roughLaplacian ρ i φ x + ((1 / 4 : ℝ) * (leviCivita g).scalarCurvatureAt g x) • φ x := by
  -- the covariant derivatives of `φ` are differentiable at `x`
  have hφx : FunDiffAt φ x := hφ.self_of_nhds.mdifferentiableAt (by simp)
  have hf : ∀ b, FunDiffAt (fun y => S.nabla ρ i b φ y) x := by
    intro b
    have h1 := mdiffAt_mvfderiv_apply hφ (S.frame_smooth i b x hx)
    have h2 : FunDiffAt (fun y => spinForm ρ (S.connForm i y b) (φ y)) x :=
      (S.mvfderiv_spinForm ρ hx b (S.frame i b x)).1.clm_apply hφx
    exact h1.add h2
  rw [S.dirac_dirac_antisymm ρ hx hf]
  congr 1
  simp only [S.hess_antisymm ρ hx hφ]
  obtain ⟨hR1, hP, hB⟩ := S.riem_symm hx
  have hct := curvatureTerm_eq (gam ρ) (S.riem i x) (gam_relations ρ) hR1 hP hB
  have hcl : (1 / 2 : ℝ) • ∑ a, ∑ b, gam ρ a (gam ρ b
      (spinForm ρ (Matrix.of fun k l => S.riem i x a b k l) (φ x))) =
      curvatureTerm (gam ρ) (S.riem i x) (φ x) := by
    simp only [curvatureTerm, spinorCurvature_eq_spinForm, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.mul_apply_eq_comp,
      ContinuousLinearMap.comp_apply]
    rfl
  rw [hcl, hct, S.scalarCurvature_eq hx]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  congr 1
  congr 1
  rw [Finset.sum_comm]

end Lightlike.Dirac
