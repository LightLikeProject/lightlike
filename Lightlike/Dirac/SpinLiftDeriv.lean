import Mathlib
import Lightlike.Dirac.SpinStructure
import Lightlike.Dirac.CliffordCenter
import Lightlike.Dirac.CliffordNorm
import Lightlike.Spacetime.ChartCurvature
import Lightlike.Spacetime.LeviCivita

/-!
# The derivative of the spin lifts of a spin structure

For a spin structure `S` (atlas form) and two frames `i`, `j`, the frame change is the matrix of
pairings `rmat i j y a b = g(F_j a, F_i b)`, orthogonal on the overlap, and the spin lift
`lift i j y ∈ Spin(n)` satisfies `lift · eₐ · lift⋆ = ∑_b rmat_ab e_b`.  Differentiating these
identities and using that the even center of the Clifford algebra is the scalars
(`spin_tangent_eq`), the derivative of the lift along a tangent vector `v` is

`d_v lift = clSpinForm (Rᵀ · d_v R) · lift`        (`SpinStructure.mvfderiv_lift`),

and in a Clifford module `ρ`: `d_v (ρ ∘ lift) = spinForm ρ (Rᵀ · d_v R) ∘ ρ(lift)`
(`SpinStructure.mvfderiv_rho_lift`).  This is the identity behind the frame independence of the
spin connection: the lift of the Levi-Civita connection to spinors.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), chapter II, §4 (the spin connection as the
  lift of the Levi-Civita connection); no equation number is claimed.
-/

open Bundle Manifold CliffordAlgebra Filter
open scoped Manifold ContDiff Matrix Topology

namespace Lightlike.Dirac

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]
  {g : NondegMetric 𝓘(ℝ, Fin n → ℝ) M} {ι : Type*} (S : SpinStructure g ι)

/-- Differentiability of a vector field at a point, with the model of `M` written out. -/
abbrev SecDiffAt (X : Π y : M, TangentSpace 𝓘(ℝ, Fin n → ℝ) y) (x : M) : Prop :=
  MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ))
    (fun y => (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) M)) x

/-- Differentiability of a vector-valued function at a point, with the model of `M` written out. -/
abbrev FunDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : M → F) (x : M) : Prop :=
  MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) f x

/-- Eventually equal functions have the same derivative. -/
lemma mvfderiv_congr_nhds' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f₁ f₂ : M → F}
    {x : M} (h : f₁ =ᶠ[𝓝 x] f₂) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) f₁ x = mvfderiv 𝓘(ℝ, Fin n → ℝ) f₂ x := by
  unfold mvfderiv
  rw [h.mfderiv_eq]
  ext v
  simp [tangentSpaceCast, NormedSpace.fromTangentSpace]
  rfl

/-- The frame change as a matrix of pairings: `rmat i j y a b = g(F_j a, F_i b)`.  On the overlap
it is the matrix `Rot i j y` of the frame change (`SpinStructure.rot_eq_rmat`), and unlike `Rot`
it is differentiable wherever the frames are. -/
noncomputable def SpinStructure.rmat (i j : ι) (y : M) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => g.g y (S.frame j a y) (S.frame i b y)

/-- The entries of the frame change, as functions on `M`. -/
noncomputable def SpinStructure.rmatE (i j : ι) (a b : Fin n) : M → ℝ :=
  fun y => S.rmat i j y a b

@[simp] lemma SpinStructure.rmatE_apply (i j : ι) (a b : Fin n) (y : M) :
    (S.rmatE i j a b) y = S.rmat i j y a b := rfl

lemma SpinStructure.rot_eq_rmat {i j : ι} {y : M} (hi : y ∈ S.dom i) (hj : y ∈ S.dom j) :
    S.Rot i j y = S.rmat i j y := by
  ext a c
  rw [show S.rmat i j y a c = g.g y (S.frame j a y) (S.frame i c y) from rfl,
    S.frame_change i j y hi hj a]
  simp [S.frame_orthonormal i _ _ y hi, Finset.sum_apply]

/-- The derivative of the frame-change matrix along a tangent vector `v` at `x`. -/
noncomputable def SpinStructure.rmatD (i j : ι) (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j a b) x v

@[simp] lemma SpinStructure.rmatD_apply (i j : ι) (x : M) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x)
    (a b : Fin n) :
    S.rmatD i j x v a b = mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.rmatE i j a b) x v := rfl

/-- The frame change is orthogonal: `R Rᵀ = 1` on the overlap. -/
lemma SpinStructure.rmat_mul_transpose {i j : ι} {y : M} (hi : y ∈ S.dom i) (hj : y ∈ S.dom j) :
    S.rmat i j y * (S.rmat i j y)ᵀ = 1 := by
  ext a c
  have h := S.frame_orthonormal j a c y hj
  rw [S.frame_change i j y hi hj c, map_sum] at h
  simp only [map_smul, S.rot_eq_rmat hi hj] at h
  rw [Matrix.mul_apply, Matrix.one_apply, ← h]
  simp only [Matrix.transpose_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [SpinStructure.rmat, mul_comm]

lemma SpinStructure.transpose_mul_rmat {i j : ι} {y : M} (hi : y ∈ S.dom i) (hj : y ∈ S.dom j) :
    (S.rmat i j y)ᵀ * S.rmat i j y = 1 :=
  mul_eq_one_comm.mp (S.rmat_mul_transpose hi hj)

/-- The frames are differentiable on their domains. -/
lemma SpinStructure.mdiffAt_frame {i : ι} (a : Fin n) {y : M} (hy : y ∈ S.dom i) :
    SecDiffAt (S.frame i a) y :=
  (S.frame_smooth i a y hy).mdifferentiableAt (by simp)

/-- The entries of the frame change are differentiable on the overlap. -/
lemma SpinStructure.mdiffAt_rmat {i j : ι} {y : M} (hi : y ∈ S.dom i) (hj : y ∈ S.dom j)
    (a b : Fin n) : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ) (S.rmatE i j a b) y :=
  mdiffAt_gpair g (S.mdiffAt_frame a hj) (S.mdiffAt_frame b hi)

/-- The spin lift lifts the frame-change matrix of pairings. -/
lemma SpinStructure.lift_conj {i j : ι} {y : M} (hi : y ∈ S.dom i) (hj : y ∈ S.dom j) (a : Fin n) :
    S.lift i j y * cgen a * star (S.lift i j y) = ∑ b, (S.rmatE i j a b) y • cgen b := by
  have h := (S.isLift i j y hi hj).2 a
  rw [S.rot_eq_rmat hi hj, map_sum] at h
  simpa [cgen, map_smul] using h

/-- A matrix identity: if `R` is orthogonal and `Ṙ Rᵀ + R Ṙᵀ = 0` (the derivative of
`R Rᵀ = 1`), then `Rᵀ Ṙ` is skew. -/
lemma skew_of_orth {R Rd : Matrix (Fin n) (Fin n) ℝ} (hRR : Rᵀ * R = 1)
    (hd : Rd * Rᵀ + R * Rdᵀ = 0) : ∀ p q, (Rᵀ * Rd) p q = -(Rᵀ * Rd) q p := by
  have hk : Rᵀ * Rd = -(Rdᵀ * R) := by
    have e : Rᵀ * (Rd * Rᵀ + R * Rdᵀ) * R = 0 := by rw [hd]; simp
    rw [Matrix.mul_add, Matrix.add_mul] at e
    simp only [Matrix.mul_assoc] at e
    rw [hRR, Matrix.mul_one, ← Matrix.mul_assoc Rᵀ R, hRR, Matrix.one_mul] at e
    exact eq_neg_of_add_eq_zero_left e
  intro p q
  have h := congrFun (congrFun hk p) q
  rw [h]
  simp [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]

section Normed

attribute [local instance] clNormedRing clNormedAlgebra

/-- The spin lifts are smooth as maps into the (normed) Clifford algebra. -/
lemma SpinStructure.contMDiffAt_lift {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, CliffordAlgebra (Qneg n)) ∞ (S.lift i j) x := by
  set b := clBasis n
  have hc : ContMDiffAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (Module.finrank ℝ (CliffordAlgebra (Qneg n))) → ℝ) ∞
      (fun y => b.equivFun (S.lift i j y)) x :=
    contMDiffAt_pi_module_iff.2 fun k => by simpa using S.lift_smooth i j (b.coord k) x hi hj
  have hL : S.lift i j = ((b.equivFun.symm.toContinuousLinearEquiv :
      (Fin (Module.finrank ℝ (CliffordAlgebra (Qneg n))) → ℝ) →L[ℝ] CliffordAlgebra (Qneg n))) ∘
      (fun y => b.equivFun (S.lift i j y)) := by
    funext y
    simp
  rw [hL]
  exact (ContinuousLinearMap.contMDiff _).contMDiffAt.comp x hc

/-- Star as a continuous linear map of the normed Clifford algebra. -/
noncomputable def starCL (n : ℕ) : CliffordAlgebra (Qneg n) →L[ℝ] CliffordAlgebra (Qneg n) :=
  LinearMap.toContinuousLinearMap
    ((reverse : CliffordAlgebra (Qneg n) →ₗ[ℝ] _).comp
      (involute : CliffordAlgebra (Qneg n) →ₐ[ℝ] _).toLinearMap)

lemma starCL_apply (x : CliffordAlgebra (Qneg n)) : starCL n x = star x := by
  simp [starCL, star_def]

/-- The grade involution as a continuous linear map. -/
noncomputable def involuteCL (n : ℕ) : CliffordAlgebra (Qneg n) →L[ℝ] CliffordAlgebra (Qneg n) :=
  LinearMap.toContinuousLinearMap (involute : CliffordAlgebra (Qneg n) →ₐ[ℝ] _).toLinearMap

lemma involuteCL_apply (x : CliffordAlgebra (Qneg n)) : involuteCL n x = involute x := rfl

/-- Two derivatives of eventually equal functions agree. -/
lemma hasFDerivAt_unique_of_eventuallyEq {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f₁ f₂ : F → G} {D₁ D₂ : F →L[ℝ] G} {z : F}
    (h₁ : HasFDerivAt f₁ D₁ z) (h₂ : HasFDerivAt f₂ D₂ z) (h : f₁ =ᶠ[𝓝 z] f₂) : D₁ = D₂ :=
  (h₁.congr_of_eventuallyEq h.symm).unique h₂

/-- **The derivative of a spin lift.**  On the overlap of the frames `i` and `j`, along a tangent
vector `v`: `d_v lift = clSpinForm (Rᵀ · d_v R) · lift`, with `R = rmat i j x`. -/
theorem SpinStructure.mvfderiv_lift {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.lift i j) x v =
      clSpinForm ((S.rmat i j x)ᵀ *
        S.rmatD i j x v) * S.lift i j x := by
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) x with hφ
  set z0 := φ x
  set w : Fin n → ℝ := mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) φ x v
  have hx0 : φ.symm z0 = x := φ.left_inv (mem_extChartAt_source x)
  have hopen : IsOpen (S.dom i ∩ S.dom j) := (S.dom_open i).inter (S.dom_open j)
  have hnearZ : ∀ᶠ z in 𝓝 z0, φ.symm z ∈ S.dom i ∧ φ.symm z ∈ S.dom j := by
    have : S.dom i ∩ S.dom j ∈ 𝓝 (φ.symm z0) := by
      rw [hx0]; exact hopen.mem_nhds ⟨hi, hj⟩
    exact (continuousAt_extChartAt_symm x).preimage_mem_nhds this
  -- the lift in the chart
  set ls := S.lift i j ∘ φ.symm
  have hlsM := (S.contMDiffAt_lift hi hj).mdifferentiableAt (by simp)
  have hls : HasFDerivAt ls (fderiv ℝ ls z0) z0 := (mdiffAt_comp_symm _ x hlsM).hasFDerivAt
  set δ := fderiv ℝ ls z0 w
  have hδ : mvfderiv 𝓘(ℝ, Fin n → ℝ) (S.lift i j) x v = δ := mvfderiv_eq_chart _ x hlsM v
  have hlsz : ls z0 = S.lift i j x := by simp [ls, hx0]
  -- the frame-change entries in the chart
  set rs : Fin n → Fin n → (Fin n → ℝ) → ℝ := fun a b => (S.rmatE i j a b) ∘ φ.symm
  have hrs : ∀ a b, HasFDerivAt (rs a b) (fderiv ℝ (rs a b) z0) z0 := fun a b =>
    (mdiffAt_comp_symm _ x (S.mdiffAt_rmat hi hj a b)).hasFDerivAt
  set R := S.rmat i j x
  set Rd : Matrix (Fin n) (Fin n) ℝ := fun a b => fderiv ℝ (rs a b) z0 w
  have hRd : S.rmatD i j x v = Rd := by
    ext a b
    exact mvfderiv_eq_chart _ x (S.mdiffAt_rmat hi hj a b) v
  have hrsz : ∀ a b, rs a b z0 = R a b := fun a b => by simp [rs, hx0, R]
  rw [hδ, hRd, ← hlsz]
  have hs : ls z0 ∈ spinGroup (Qneg n) := by rw [hlsz]; exact (S.isLift i j x hi hj).1
  have hstar : HasFDerivAt (fun z => star (ls z)) ((starCL n).comp (fderiv ℝ ls z0)) z0 := by
    have := (starCL n).hasFDerivAt.comp z0 hls
    simpa [Function.comp_def, starCL_apply] using this
  -- (1) the derivative of `s s⋆ = 1`
  have h1 : δ * star (ls z0) + ls z0 * star δ = 0 := by
    have hp : HasFDerivAt (fun z => ls z * star (ls z))
        (ls z0 • ((starCL n).comp (fderiv ℝ ls z0)) +
          MulOpposite.op (star (ls z0)) • fderiv ℝ ls z0) z0 := hls.mul' hstar
    have hc : HasFDerivAt (fun _ : Fin n → ℝ => (1 : CliffordAlgebra (Qneg n)))
        (0 : (Fin n → ℝ) →L[ℝ] CliffordAlgebra (Qneg n)) z0 :=
      hasFDerivAt_const (1 : CliffordAlgebra (Qneg n)) z0
    have heq : (fun z => ls z * star (ls z)) =ᶠ[𝓝 z0] fun _ => 1 := by
      filter_upwards [hnearZ] with z hz
      exact spinGroup.mul_star_self_of_mem (S.isLift i j _ hz.1 hz.2).1
    have key := congrArg (fun L => L w) (hasFDerivAt_unique_of_eventuallyEq hp hc heq)
    have eL : (ls z0 • ((starCL n).comp (fderiv ℝ ls z0)) +
        MulOpposite.op (star (ls z0)) • fderiv ℝ ls z0) w = ls z0 * star δ + δ * star (ls z0) := by
      simp [δ, starCL_apply, op_smul_eq_mul]
    simp only [eL, ContinuousLinearMap.zero_apply] at key
    rw [add_comm]; exact key
  -- (2) the derivative is even
  have h2 : involute δ = δ := by
    have hi' : HasFDerivAt (fun z => involute (ls z)) ((involuteCL n).comp (fderiv ℝ ls z0)) z0 := by
      have := (involuteCL n).hasFDerivAt.comp z0 hls
      simpa [Function.comp_def, involuteCL_apply] using this
    have heq : (fun z => involute (ls z)) =ᶠ[𝓝 z0] ls := by
      filter_upwards [hnearZ] with z hz
      exact spinGroup.involute_eq (S.isLift i j _ hz.1 hz.2).1
    have key := congrArg (fun L => L w) (hasFDerivAt_unique_of_eventuallyEq hi' hls heq)
    simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply, involuteCL_apply] using key
  -- (3) the derivative of the conjugation
  have h3 : ∀ a, δ * cgen a * star (ls z0) + ls z0 * cgen a * star δ = ∑ b, Rd a b • cgen b := by
    intro a
    set Lm := (ContinuousLinearMap.mul ℝ (CliffordAlgebra (Qneg n))).flip (cgen a)
    have hl1 : HasFDerivAt (fun z => ls z * cgen a) (Lm.comp (fderiv ℝ ls z0)) z0 := by
      have := Lm.hasFDerivAt.comp z0 hls
      simpa [Function.comp_def, Lm] using this
    have hp : HasFDerivAt (fun z => ls z * cgen a * star (ls z))
        ((ls z0 * cgen a) • ((starCL n).comp (fderiv ℝ ls z0)) +
          MulOpposite.op (star (ls z0)) • (Lm.comp (fderiv ℝ ls z0))) z0 := hl1.mul' hstar
    have hsum : HasFDerivAt (fun z => ∑ b, rs a b z • cgen b)
        (∑ b, (fderiv ℝ (rs a b) z0).smulRight (cgen b)) z0 :=
      HasFDerivAt.fun_sum fun b _ => (hrs a b).smul_const (cgen b)
    have heq : (fun z => ls z * cgen a * star (ls z)) =ᶠ[𝓝 z0] fun z => ∑ b, rs a b z • cgen b := by
      filter_upwards [hnearZ] with z hz
      exact S.lift_conj hz.1 hz.2 a
    have key := congrArg (fun L => L w) (hasFDerivAt_unique_of_eventuallyEq hp hsum heq)
    have eL : ((ls z0 * cgen a) • ((starCL n).comp (fderiv ℝ ls z0)) +
        MulOpposite.op (star (ls z0)) • (Lm.comp (fderiv ℝ ls z0))) w =
        δ * cgen a * star (ls z0) + ls z0 * cgen a * star δ := by
      simp [δ, starCL_apply, op_smul_eq_mul, Lm, add_comm]
    have eR : (∑ b, (fderiv ℝ (rs a b) z0).smulRight (cgen b)) w = ∑ b, Rd a b • cgen b := by
      simp [Rd]
    rw [eL, eR] at key
    exact key
  -- orthogonality and its derivative
  have hRR : Rᵀ * R = 1 := S.transpose_mul_rmat hi hj
  have hskew : ∀ p q, (Rᵀ * Rd) p q = -(Rᵀ * Rd) q p := by
    have hd : Rd * Rᵀ + R * Rdᵀ = 0 := by
      ext a c
      have hprod : HasFDerivAt (fun z => ∑ b, (rs a b * rs c b) z)
          (∑ b, (rs a b z0 • fderiv ℝ (rs c b) z0 + rs c b z0 • fderiv ℝ (rs a b) z0)) z0 :=
        HasFDerivAt.fun_sum fun b _ => (hrs a b).mul (hrs c b)
      have hc : HasFDerivAt (fun _ : Fin n → ℝ => if a = c then (1 : ℝ) else 0)
          (0 : (Fin n → ℝ) →L[ℝ] ℝ) z0 :=
        hasFDerivAt_const (if a = c then (1 : ℝ) else 0) z0
      have heq : (fun z => ∑ b, (rs a b * rs c b) z) =ᶠ[𝓝 z0]
          fun _ => if a = c then (1 : ℝ) else 0 := by
        filter_upwards [hnearZ] with z hz
        have := congrFun (congrFun (S.rmat_mul_transpose hz.1 hz.2) a) c
        simpa [Matrix.mul_apply, Matrix.one_apply, rs] using this
      have := congrArg (fun L => L w) (hasFDerivAt_unique_of_eventuallyEq hprod hc heq)
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply, hrsz] at this
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply]
      rw [← this, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Rd]
      ring
    exact skew_of_orth hRR hd
  have hconj : ∀ a, ls z0 * cgen a * star (ls z0) = ∑ b, R a b • cgen b := by
    intro a; rw [hlsz]; exact S.lift_conj hi hj a
  exact spin_tangent_eq hs hRR hconj hskew h1 h2 h3

end Normed

/-- **The derivative of a spin lift in a Clifford module.**  On the overlap of the frames `i`, `j`,
`d_v (ρ ∘ lift) = spinForm ρ (Rᵀ · d_v R) ∘ ρ(lift)`, with `R = rmat i j x`. -/
theorem SpinStructure.mvfderiv_rho_lift {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep n V) {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => ρ (S.lift i j y)) x v =
      spinForm ρ ((S.rmat i j x)ᵀ *
        S.rmatD i j x v) * ρ (S.lift i j x) := by
  let _ := clNormedRing n
  let _ := clNormedAlgebra n
  set ρL : CliffordAlgebra (Qneg n) →L[ℝ] (V →L[ℝ] V) :=
    LinearMap.toContinuousLinearMap ρ.toLinearMap
  have hlsM := (S.contMDiffAt_lift hi hj).mdifferentiableAt (by simp)
  have hcomp : (fun y => ρ (S.lift i j y)) = ρL ∘ S.lift i j := by
    funext y; rfl
  have hM : MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, V →L[ℝ] V) (fun y => ρ (S.lift i j y)) x := by
    rw [hcomp]; exact ρL.mdifferentiableAt.comp x hlsM
  rw [mvfderiv_eq_chart _ x hM v]
  have := mvfderiv_eq_chart _ x hlsM v
  rw [S.mvfderiv_lift hi hj v] at this
  have hc : (fun y => ρ (S.lift i j y)) ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm =
      ρL ∘ (S.lift i j ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm) := by
    rw [hcomp]; rfl
  have hfd := (ρL.hasFDerivAt.comp _ (mdiffAt_comp_symm _ x hlsM).hasFDerivAt).fderiv
  rw [hc, hfd]
  change ρL (fderiv ℝ (S.lift i j ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) x).symm)
    (extChartAt 𝓘(ℝ, Fin n → ℝ) x x)
      (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) x) x v)) = _
  rw [← this]
  simp [ρL, map_mul, map_clSpinForm]

/-- The derivative of a finite sum of differentiable functions. -/
lemma mvfderiv_finsum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Fin n → M → F}
    {x : M} (h : ∀ b, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) (f b) x) :
    mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => ∑ b, f b y) x = ∑ b, mvfderiv 𝓘(ℝ, Fin n → ℝ) (f b) x := by
  classical
  have key : ∀ s : Finset (Fin n), MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, F) (fun y => ∑ b ∈ s, f b y) x ∧
      mvfderiv 𝓘(ℝ, Fin n → ℝ) (fun y => ∑ b ∈ s, f b y) x =
        ∑ b ∈ s, mvfderiv 𝓘(ℝ, Fin n → ℝ) (f b) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using mdifferentiableAt_const, by simp [mvfderiv_const]⟩
    | insert a s has ih =>
      simp only [Finset.sum_insert has]
      refine ⟨(h a).add ih.1, ?_⟩
      rw [show (fun y => f a y + ∑ b ∈ s, f b y) = f a + fun y => ∑ b ∈ s, f b y from rfl,
        mvfderiv_add (h a) ih.1, ih.2]
  exact (key Finset.univ).2

/-- The derivative of the orthogonality `R Rᵀ = 1` of the frame change. -/
lemma SpinStructure.rmat_deriv_orth {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) :
    S.rmatD i j x v * (S.rmat i j x)ᵀ +
      S.rmat i j x * (S.rmatD i j x v)ᵀ = 0 := by
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ S.dom i ∧ y ∈ S.dom j :=
    ((S.dom_open i).inter (S.dom_open j)).mem_nhds ⟨hi, hj⟩
  ext a c
  have hm : ∀ b, MDifferentiableAt 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, ℝ)
      (S.rmatE i j a b * S.rmatE i j c b) x := fun b =>
    (S.mdiffAt_rmat hi hj a b).mul (S.mdiffAt_rmat hi hj c b)
  have heq : (fun y => ∑ b, (S.rmatE i j a b * (S.rmatE i j c b)) y) =ᶠ[𝓝 x]
      fun _ => if a = c then (1 : ℝ) else 0 := by
    filter_upwards [hnear] with y hy
    have := congrFun (congrFun (S.rmat_mul_transpose hy.1 hy.2) a) c
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have h0 := congrArg (fun L => L v) (mvfderiv_congr_nhds' heq)
  simp only [mvfderiv_const, ContinuousLinearMap.zero_apply] at h0
  rw [mvfderiv_finsum hm] at h0
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply] at h0
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    SpinStructure.rmatD_apply, ← Finset.sum_add_distrib]
  rw [← h0]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mvfderiv_mul (S.mdiffAt_rmat hi hj a b) (S.mdiffAt_rmat hi hj c b)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    SpinStructure.rmatE_apply]
  ring

/-- `Rᵀ Ṙ` is skew for the frame change `R = rmat i j x` and its derivative `Ṙ` along `v`. -/
lemma SpinStructure.rmat_deriv_skew {i j : ι} {x : M} (hi : x ∈ S.dom i) (hj : x ∈ S.dom j)
    (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) x) (p q : Fin n) :
    ((S.rmat i j x)ᵀ * S.rmatD i j x v) p q =
      -((S.rmat i j x)ᵀ * S.rmatD i j x v) q p :=
  skew_of_orth (S.transpose_mul_rmat hi hj) (S.rmat_deriv_orth hi hj v) p q

end Lightlike.Dirac
