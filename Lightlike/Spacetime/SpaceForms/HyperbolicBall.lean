import Lightlike.Spacetime.QuadricCurvature
import Lightlike.Spacetime.ImmersionSection
import Lightlike.Spacetime.KillingMinkowski
import Lightlike.Spacetime.LeviCivita
import Lightlike.Spacetime.MaximallySymmetric
import Lightlike.Spacetime.PullbackMetric

/-!
# The Poincaré ball is maximally symmetric

The Poincaré ball model of hyperbolic space: the open unit ball `hyperbolicDomain n` of `ℝⁿ`, as a manifold (an open
subset, model `𝓘(ℝ, Fin n → ℝ)`), with the metric `poincareBallMetric n` whose components in the coordinates of `ℝⁿ`
are the library's `hyperbolicMetric n x = 4 δ / (1 - |x|²)²` (`poincareBallMetric_single`).

The metric is obtained as the metric induced by `ι(x) = ((1 + |x|²)/(1 - |x|²), 2x/(1 - |x|²))`, a map of the ball onto
the upper sheet of the hyperboloid `η(x, x) = -1` of Minkowski space `ℝ^{1,n}`; the induced form is
`4 ⟨u, v⟩/(1 - |x|²)²` (`poincareBallMetric_apply`). Then:

* `hasConstantCurvature_poincareBall`: every locally smooth Levi-Civita connection has constant curvature `-1`
  (`hasConstantCurvature_of_quadric`, `c = -1`);
* `exists_killing_poincareBall`: `n (n + 1)/2` linearly independent smooth Killing fields, from a basis of the Lorentz
  algebra `skewEta (n + 1)` (`isKillingAt_of_related`, `contMDiffAt_section_of_immersion`);
* `isMaximallySymmetric_poincareBall`: **the Poincaré ball is maximally symmetric with `K = -1`** on the whole ball;
* `poincareBallMetric_pos`: the metric is positive definite at every point.

`exists_eq_of_injective_of_ker`: an injective linear map into the kernel of a nonzero functional, between spaces of
dimensions `n` and `n + 1`, is onto the kernel (used for the tangent space of the hyperboloid).

**References.** S. M. Carroll, *Spacetime and Geometry* (Addison-Wesley, 2004), section 8.1.
-/

open Manifold Set Module TopologicalSpace
open scoped ContDiff Manifold Topology

set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace Lightlike

/-- **Onto the kernel by dimension**: an injective linear map `D : E → V` with image in the kernel of a nonzero
functional `ℓ`, `dim V = dim E + 1`, maps onto `ker ℓ`. -/
theorem exists_eq_of_injective_of_ker {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (D : E →L[ℝ] V) (hD : Function.Injective D)
    (ℓ : V →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hDℓ : ∀ w, ℓ (D w) = 0) (hdim : finrank ℝ V = finrank ℝ E + 1) (z : V)
    (hz : ℓ z = 0) : ∃ w, D w = z := by
  have hℓ' : (ℓ : V →ₗ[ℝ] ℝ) ≠ 0 := fun h => hℓ (ContinuousLinearMap.coe_injective (by simpa using h))
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ'
  have hle : LinearMap.range (D : E →ₗ[ℝ] V) ≤ LinearMap.ker (ℓ : V →ₗ[ℝ] ℝ) := by
    rintro _ ⟨w, rfl⟩; exact hDℓ w
  have hr : finrank ℝ (LinearMap.range (D : E →ₗ[ℝ] V)) = finrank ℝ E := LinearMap.finrank_range_of_inj hD
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have : z ∈ LinearMap.range (D : E →ₗ[ℝ] V) := by rw [heq]; exact hz
  obtain ⟨w, hw⟩ := this
  exact ⟨w, hw⟩

/-- The inclusion of an open subset of a normed space has the identity as derivative. -/
theorem hasMFDerivAt_opens_val' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Opens E) (t : U) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) t
      (ContinuousLinearMap.id ℝ E : TangentSpace 𝓘(ℝ, E) t →L[ℝ] TangentSpace 𝓘(ℝ, E) (t : E)) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
  have hev : (Subtype.val ∘ (extChartAt 𝓘(ℝ, E) t).symm) =ᶠ[nhdsWithin ((extChartAt 𝓘(ℝ, E) t) t) (Set.range 𝓘(ℝ, E))]
      id := by
    filter_upwards [extChartAt_target_mem_nhdsWithin t] with y hy
    have h2 := OpenPartialHomeomorph.subtypeRestr_symm_apply (OpenPartialHomeomorph.refl E) ⟨t⟩ (U := U) (y := y)
    simp [extChartAt, Opens.chartAt_eq] at hy ⊢
    exact h2 hy
  have : HasFDerivWithinAt (id : E → E) (ContinuousLinearMap.id ℝ E) (Set.range 𝓘(ℝ, E)) ((extChartAt 𝓘(ℝ, E) t) t) :=
    (hasFDerivAt_id _).hasFDerivWithinAt
  exact this.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin (by simp))

namespace PoincareBall

variable {n : ℕ}

/-- The open unit ball as an open set. -/
def ballOpens (n : ℕ) : Opens (Fin n → ℝ) := ⟨hyperbolicDomain n, isOpen_hyperbolicDomain n⟩

/-- **The Poincaré ball** as a manifold: the open unit ball of `ℝⁿ`. -/
abbrev Ball (n : ℕ) : Type := ↥(ballOpens n)

example : IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ (Ball n) := inferInstance

/-- `|x|²`. -/
def bsq (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- `⟨x, v⟩`. -/
def ip (x v : Fin n → ℝ) : ℝ := ∑ i, x i * v i

/-- A point of the ball has `|x|² < 1`. -/
theorem sq_lt_one (p : Ball n) : bsq (p : Fin n → ℝ) < 1 := p.2

/-- `1 - |x|² > 0` on the ball. -/
theorem one_sub_sq_pos (p : Ball n) : 0 < 1 - bsq (p : Fin n → ℝ) := by linarith [sq_lt_one p]

/-- `⟨x, x⟩ = |x|²`. -/
theorem ip_self (x : Fin n → ℝ) : ip x x = bsq x := by simp [ip, bsq, pow_two]

/-- `⟨x, v⟩` as a continuous linear functional of `v`. -/
def ipL (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ := ∑ i, x i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)

/-- `ipL x v = ⟨x, v⟩`. -/
theorem ipL_apply (x v : Fin n → ℝ) : ipL x v = ip x v := by simp [ipL, ip]

/-- The map `Φ(x) = ((1 + |x|²) r, 2 r x)`, `r = (1 - |x|²)⁻¹`. -/
def Phi (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons ((1 + bsq x) * (1 - bsq x)⁻¹) ((2 * (1 - bsq x)⁻¹) • x)

/-- The derivative of `Φ`: `v ↦ (4 ⟨x, v⟩/(1 - |x|²)², 2 v/(1 - |x|²) + 4 ⟨x, v⟩ x/(1 - |x|²)²)`. -/
def PhiD (x : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ) : (ℝ × (Fin n → ℝ)) →L[ℝ] _).comp
    (((4 * ((1 - bsq x) ^ 2)⁻¹) • ipL x).prod
      ((2 * (1 - bsq x)⁻¹) • ContinuousLinearMap.id ℝ _ + (4 * ((1 - bsq x) ^ 2)⁻¹) • (ipL x).smulRight x))

/-- The value of the derivative of `Φ`. -/
theorem PhiD_apply (x v : Fin n → ℝ) :
    PhiD x v = Fin.cons (4 * ((1 - bsq x) ^ 2)⁻¹ * ip x v)
      ((2 * (1 - bsq x)⁻¹) • v + (4 * ((1 - bsq x) ^ 2)⁻¹ * ip x v) • x) := by
  simp [PhiD, ipL_apply, smul_smul]
  rfl

/-- The derivative of `|x|²` is `2 ⟨x, ·⟩`. -/
theorem hasFDerivAt_sq (x : Fin n → ℝ) : HasFDerivAt bsq ((2 : ℝ) • ipL x) x := by
  unfold bsq
  refine (HasFDerivAt.fun_sum fun i _ =>
    (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.pow (x := x) 2).congr_fderiv ?_
  ext v
  simp only [ipL, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, FunLike.coe_sum, FunLike.coe_smul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp
  ring

/-- The derivative of `Φ` on the ball is `PhiD`. -/
theorem hasFDerivAt_Phi {x : Fin n → ℝ} (hx : 1 - bsq x ≠ 0) : HasFDerivAt Phi (PhiD x) x := by
  have hs := hasFDerivAt_sq x
  have hq : HasFDerivAt (fun y => 1 - bsq y) (-((2 : ℝ) • ipL x)) x := (hasFDerivAt_const 1 x).sub hs |>.congr_fderiv
    (by simp)
  have hr : HasFDerivAt (fun y => (1 - bsq y)⁻¹) (-((1 - bsq x) ^ 2)⁻¹ • -((2 : ℝ) • ipL x)) x :=
    (hasDerivAt_inv hx).comp_hasFDerivAt x hq
  have ht : HasFDerivAt (fun y => (1 + bsq y) * (1 - bsq y)⁻¹) ((4 * ((1 - bsq x) ^ 2)⁻¹) • ipL x) x := by
    have := ((hasFDerivAt_const 1 x).add hs).mul hr
    refine this.congr_fderiv ?_
    ext v
    simp only [add_apply, smul_apply, smul_eq_mul, neg_apply,
      zero_add, Pi.add_apply]
    field_simp
    ring
  have hX : HasFDerivAt (fun y : Fin n → ℝ => (2 * (1 - bsq y)⁻¹) • y)
      ((2 * (1 - bsq x)⁻¹) • ContinuousLinearMap.id ℝ _ + (4 * ((1 - bsq x) ^ 2)⁻¹) • (ipL x).smulRight x) x := by
    have := (hr.const_mul 2).smul (hasFDerivAt_id x)
    refine this.congr_fderiv ?_
    ext v i
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      id]
    ring
  exact (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).hasFDerivAt.comp x (ht.prodMk hX)

/-- `Φ` is smooth on the ball. -/
theorem contDiffAt_Phi {x : Fin n → ℝ} (hx : 1 - bsq x ≠ 0) : ContDiffAt ℝ ∞ Phi x := by
  have hs : ContDiff ℝ ∞ (bsq (n := n)) :=
    ContDiff.sum fun i _ => (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).contDiff.pow 2
  have hr : ContDiffAt ℝ ∞ (fun y => (1 - bsq y)⁻¹) x := ((contDiffAt_const.sub hs.contDiffAt)).inv hx
  have h1 : ContDiffAt ℝ ∞ (fun y => (1 + bsq y) * (1 - bsq y)⁻¹) x := (contDiffAt_const.add hs.contDiffAt).mul hr
  have h2 : ContDiffAt ℝ ∞ (fun y : Fin n → ℝ => (2 * (1 - bsq y)⁻¹) • y) x :=
    (contDiffAt_const.mul hr).smul contDiffAt_id
  have h := h1.prodMk h2
  exact (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).contDiff.contDiffAt.comp x h

/-- **The map of the ball onto the hyperboloid**. -/
def ballIncl (p : Ball n) : Fin (n + 1) → ℝ := Phi (p : Fin n → ℝ)

/-- The map of the ball onto the hyperboloid is smooth. -/
theorem contMDiff_ballIncl : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) → ℝ) ∞ (ballIncl (n := n)) := fun p =>
  (contDiffAt_Phi (one_sub_sq_pos p).ne').contMDiffAt.comp p (contMDiff_subtype_val p)

/-- **The derivative of the map onto the hyperboloid** is `PhiD`. -/
theorem dι_ballIncl (p : Ball n) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p v = PhiD (p : Fin n → ℝ) v := by
  have h := (hasFDerivAt_Phi (one_sub_sq_pos p).ne').hasMFDerivAt.comp p (hasMFDerivAt_opens_val' (ballOpens n) p)
  unfold dι
  rw [show ballIncl (n := n) = Phi ∘ Subtype.val from rfl, h.mfderiv]
  rfl

/-- The Minkowski form on `(a, u)` and `(b, v)`: `-a b + ⟨u, v⟩`. -/
theorem minkowskiForm_cons (a b : ℝ) (u v : Fin n → ℝ) :
    minkowskiForm (n + 1) (Fin.cons a u) (Fin.cons b v) = -(a * b) + ip u v := by
  rw [minkowskiForm_apply, Fin.sum_univ_succ]
  simp [etaDiag, ip]

/-- `⟨c u, v⟩ = c ⟨u, v⟩`. -/
theorem ip_smul_left (c : ℝ) (u v : Fin n → ℝ) : ip (c • u) v = c * ip u v := by
  simp [ip, Finset.mul_sum, mul_assoc]

/-- `⟨u, c v⟩ = c ⟨u, v⟩`. -/
theorem ip_smul_right (c : ℝ) (u v : Fin n → ℝ) : ip u (c • v) = c * ip u v := by
  simp [ip, Finset.mul_sum, mul_left_comm]

/-- `⟨u + u', v⟩ = ⟨u, v⟩ + ⟨u', v⟩`. -/
theorem ip_add_left (u u' v : Fin n → ℝ) : ip (u + u') v = ip u v + ip u' v := by
  simp [ip, add_mul, Finset.sum_add_distrib]

/-- `⟨u, v + v'⟩ = ⟨u, v⟩ + ⟨u, v'⟩`. -/
theorem ip_add_right (u v v' : Fin n → ℝ) : ip u (v + v') = ip u v + ip u v' := by
  simp [ip, mul_add, Finset.sum_add_distrib]

/-- `⟨u, v⟩ = ⟨v, u⟩`. -/
theorem ip_comm (u v : Fin n → ℝ) : ip u v = ip v u := by simp [ip, mul_comm]

/-- **The image is the hyperboloid** `η(x, x) = -1`. -/
theorem minkowskiForm_ballIncl_self (p : Ball n) : minkowskiForm (n + 1) (ballIncl p) (ballIncl p) = -1 := by
  have hq := (one_sub_sq_pos p).ne'
  rw [ballIncl, Phi, minkowskiForm_cons, ip_smul_left, ip_smul_right, ip_self]
  field_simp
  ring

/-- The form on the derivative of `Φ`: `η(DΦ u, DΦ v) = 4 ⟨u, v⟩/(1 - |x|²)²`. -/
theorem minkowskiForm_PhiD (x u v : Fin n → ℝ) (hq : 1 - bsq x ≠ 0) :
    minkowskiForm (n + 1) (PhiD x u) (PhiD x v) = 4 / (1 - bsq x) ^ 2 * ip u v := by
  rw [PhiD_apply, PhiD_apply, minkowskiForm_cons]
  simp only [ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, ip_self]
  rw [ip_comm u x]
  field_simp
  ring

/-- The derivative of `Φ` is `η`-orthogonal to `Φ`. -/
theorem minkowskiForm_Phi_PhiD (x v : Fin n → ℝ) (hq : 1 - bsq x ≠ 0) :
    minkowskiForm (n + 1) (Phi x) (PhiD x v) = 0 := by
  rw [PhiD_apply, Phi, minkowskiForm_cons]
  simp only [ip_add_right, ip_smul_left, ip_smul_right, ip_self]
  field_simp
  ring

/-- **The induced metric is `4 ⟨u, v⟩/(1 - |x|²)²`.** -/
theorem minkowskiForm_dι_ballIncl (p : Ball n) (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    minkowskiForm (n + 1) (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p u) (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p v) =
      4 / (1 - bsq (p : Fin n → ℝ)) ^ 2 * ip u v := by
  erw [dι_ballIncl, dι_ballIncl]
  exact minkowskiForm_PhiD _ u v (one_sub_sq_pos p).ne'

/-- The image of `dι` is `η`-orthogonal to the point. -/
theorem minkowskiForm_ballIncl_dι (p : Ball n) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    minkowskiForm (n + 1) (ballIncl p) (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p v) = 0 := by
  erw [dι_ballIncl]
  exact minkowskiForm_Phi_PhiD _ v (one_sub_sq_pos p).ne'

/-- The Minkowski form is symmetric. -/
theorem minkowskiForm_symm'' (a b : Fin (n + 1) → ℝ) : minkowskiForm (n + 1) a b = minkowskiForm (n + 1) b a :=
  (minkowskiForm_isLorentzian (n + 1)).symm a b

/-- The Minkowski form is nondegenerate. -/
theorem minkowskiForm_nondeg'' (u : Fin (n + 1) → ℝ) (h : ∀ z, minkowskiForm (n + 1) u z = 0) : u = 0 :=
  (minkowskiForm_isLorentzian (n + 1)).nondegenerate u h

/-- `dι` is injective (the induced form is positive definite). -/
theorem dι_ballIncl_injective (p : Ball n) : Function.Injective (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p) := by
  intro a b hab
  rw [← sub_eq_zero]
  set w := a - b
  have h0 : dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p w = 0 := by
    show dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p (a - b) = 0
    rw [map_sub, hab, sub_self]
  have h1 := minkowskiForm_dι_ballIncl p w w
  rw [h0, map_zero] at h1
  have hq := one_sub_sq_pos p
  have h2 : ip w w = 0 := by
    have : 0 < 4 / (1 - bsq (p : Fin n → ℝ)) ^ 2 := by positivity
    nlinarith [mul_eq_zero.1 h1.symm]
  funext i
  have h3 : ∑ j, w j * w j = 0 := h2
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (w j))).1 h3 i (Finset.mem_univ i)
  simpa using mul_self_eq_zero.1 this

/-- Every vector `η`-orthogonal to the point is in the image of `dι`. -/
theorem exists_dι_ballIncl_eq (p : Ball n) (z : Fin (n + 1) → ℝ)
    (hz : minkowskiForm (n + 1) (ballIncl p) z = 0) : ∃ w, dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p w = z := by
  have hℓ : minkowskiForm (n + 1) (ballIncl p) ≠ 0 := fun h => by
    have := minkowskiForm_ballIncl_self p
    rw [h, zero_apply] at this
    norm_num at this
  exact exists_eq_of_injective_of_ker (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p) (dι_ballIncl_injective p) _ hℓ
    (minkowskiForm_ballIncl_dι p) (by simp) z hz

end PoincareBall

open PoincareBall

/-- **The Poincaré ball metric**: the metric of the open unit ball induced from the hyperboloid, whose coordinate
components are `hyperbolicMetric n` (`poincareBallMetric_single`). -/
def poincareBallMetric (n : ℕ) : NondegMetric 𝓘(ℝ, Fin n → ℝ) (Ball n) :=
  NondegMetric.pullback (minkowskiForm (n + 1)) minkowskiForm_symm'' ballIncl contMDiff_ballIncl fun p v hv =>
    pullback_nondeg_of_quadric (L := minkowskiForm (n + 1)) minkowskiForm_symm'' minkowskiForm_nondeg''
      (x := ballIncl p) (by rw [minkowskiForm_ballIncl_self]; norm_num) (dι_ballIncl_injective p)
      (minkowskiForm_ballIncl_dι p) (exists_dι_ballIncl_eq p) v hv

variable {n : ℕ}

/-- The Poincaré ball metric is the pullback `η(dι u, dι v)`. -/
theorem poincareBallMetric_pullback (p : Ball n) (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    (poincareBallMetric n).g p u v =
      minkowskiForm (n + 1) (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p u) (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p v) :=
  NondegMetric.pullback_apply _ _ _ _ _ p u v

/-- **The Poincaré ball metric** is `g(u, v) = 4 ⟨u, v⟩/(1 - |x|²)²`. -/
theorem poincareBallMetric_apply (p : Ball n) (u v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) :
    (poincareBallMetric n).g p u v = 4 / (1 - ∑ i, (p : Fin n → ℝ) i ^ 2) ^ 2 * ∑ i, u i * v i := by
  rw [poincareBallMetric_pullback, minkowskiForm_dι_ballIncl]
  rfl

/-- **Its components in the coordinates of `ℝⁿ` are `hyperbolicMetric`**: `g(e_i, e_j) = hyperbolicMetric n x i j`. -/
theorem poincareBallMetric_single (p : Ball n) (i j : Fin n) :
    (poincareBallMetric n).g p (Pi.single i 1) (Pi.single j 1) = hyperbolicMetric n (p : Fin n → ℝ) i j := by
  have hs : ∀ (u w : Fin n → ℝ), u = Pi.single i 1 → w = Pi.single j 1 →
      ∑ k, u k * w k = if i = j then 1 else 0 := by
    rintro u w rfl rfl
    by_cases h : i = j
    · subst h; simp [Pi.single_apply]
    · simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_eq_zero fun k _ => ?_]
      · simp [h]
      · split_ifs with h1 h2 <;> simp_all
  erw [poincareBallMetric_apply]
  rw [hs _ _ rfl rfl, hyperbolicMetric, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- **The Poincaré ball metric is positive definite** at every point. -/
theorem poincareBallMetric_pos (p : Ball n) (v : TangentSpace 𝓘(ℝ, Fin n → ℝ) p) (hv : v ≠ 0) :
    0 < (poincareBallMetric n).g p v v := by
  rw [poincareBallMetric_apply]
  have hq : 0 < 1 - ∑ i, (p : Fin n → ℝ) i ^ 2 := one_sub_sq_pos p
  have hv2 : 0 < ∑ i, v i * v i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    exact lt_of_lt_of_le (mul_self_pos.2 hi) (Finset.single_le_sum (f := fun i => v i * v i)
      (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i))
  positivity

/-- **The Poincaré ball has constant curvature `-1`**. -/
theorem hasConstantCurvature_poincareBall : HasConstantCurvature (poincareBallMetric n) (-1) := by
  have h := hasConstantCurvature_of_quadric (L := minkowskiForm (n + 1)) minkowskiForm_symm'' contMDiff_ballIncl
    (poincareBallMetric_pullback (n := n)) (c := -1) (by norm_num) minkowskiForm_ballIncl_self dι_ballIncl_injective
    exists_dι_ballIncl_eq
  simpa using h

/-- A skew map sends every point to an `η`-orthogonal vector. -/
theorem minkowskiForm_self_skew' {A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hA : A ∈ skewEta (n + 1))
    (x : Fin (n + 1) → ℝ) : minkowskiForm (n + 1) x (A x) = 0 := by
  have h := hA x x
  rw [minkowskiForm_symm'' (A x) x] at h
  linarith

/-- **The Killing field of an ambient Lorentz generator** `A` on the ball: the tangent vector with `dι = A ι`. -/
def ballField {A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hA : A ∈ skewEta (n + 1)) :
    Π p : Ball n, TangentSpace 𝓘(ℝ, Fin n → ℝ) p :=
  fun p => Classical.choose (exists_dι_ballIncl_eq p (A (ballIncl p)) (minkowskiForm_self_skew' hA _))

/-- `dι (ballField A) = A ∘ ι`. -/
theorem dι_ballField {A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hA : A ∈ skewEta (n + 1)) (p : Ball n) :
    dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p (ballField hA p) = A (ballIncl p) :=
  Classical.choose_spec (exists_dι_ballIncl_eq p (A (ballIncl p)) (minkowskiForm_self_skew' hA _))

/-- The field is smooth. -/
theorem contMDiff_ballField {A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hA : A ∈ skewEta (n + 1)) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
      (fun p : Ball n => (⟨p, ballField hA p⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) (Ball n))) := by
  intro p
  refine contMDiffAt_section_of_immersion contMDiff_ballIncl (dι_ballIncl_injective p) ?_
  have : (fun q => dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl q (ballField hA q)) = fun q => A (ballIncl q) :=
    funext (dι_ballField hA)
  rw [this]
  exact A.contMDiff.contMDiffAt.comp p (contMDiff_ballIncl p)

/-- **The field is a Killing field** of the Levi-Civita connection of the Poincaré ball metric at every point. -/
theorem isKillingAt_ballField {A : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)} (hA : A ∈ skewEta (n + 1))
    (p : Ball n) : IsKillingAt (leviCivita (poincareBallMetric n)) (poincareBallMetric n) (ballField hA) p :=
  isKillingAt_of_related ⟨leviCivita_torsion _, leviCivita_compat _⟩ contMDiff_ballIncl poincareBallMetric_pullback A
    hA (dι_ballField hA) ((contMDiff_ballField hA p).mdifferentiableAt (by simp))

/-- The point `t e_k` of the ball, `|t| < 1`. -/
def ballPt (t : ℝ) (ht : t ^ 2 < 1) (k : Fin n) : Ball n :=
  ⟨t • Pi.single k 1, by
    show ∑ i, (t • (Pi.single k 1 : Fin n → ℝ)) i ^ 2 < 1
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
    simpa using ht⟩

/-- **The image of the ball spans**: a linear map vanishing at every point `ι(x)` is zero. -/
theorem eq_zero_of_vanish_ballIncl (T : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
    (hT : ∀ p : Ball n, T (ballIncl p) = 0) : T = 0 := by
  have h0mem : (0 : Fin n → ℝ) ∈ ballOpens n := by show ∑ i, (0 : Fin n → ℝ) i ^ 2 < 1; simp
  have e0 : ballIncl (⟨0, h0mem⟩ : Ball n) = Pi.single 0 1 := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [ballIncl, Phi, bsq]
  have h0 : T (Pi.single 0 1) = 0 := by rw [← e0]; exact hT _
  have hk : ∀ k : Fin n, T (Pi.single k.succ 1) = 0 := by
    intro k
    have ht : (1 / 2 : ℝ) ^ 2 < 1 := by norm_num
    have hs : bsq ((1 / 2 : ℝ) • (Pi.single k 1 : Fin n → ℝ)) = 1 / 4 := by
      unfold bsq
      rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (by simp)]
      norm_num
    have e : ballIncl (ballPt (1 / 2) ht k) = (5 / 3 : ℝ) • (Pi.single 0 1 : Fin (n + 1) → ℝ) +
        (4 / 3 : ℝ) • Pi.single k.succ 1 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [ballIncl, ballPt, Phi, Fin.cons_zero, hs]
        simp [(Fin.succ_ne_zero k).symm]
        norm_num
      · simp only [ballIncl, ballPt, Phi, Fin.cons_succ, hs]
        simp [Pi.single_apply, Fin.succ_ne_zero, Fin.succ_inj]
        split_ifs <;> norm_num
    have := hT (ballPt (1 / 2) ht k)
    rw [e, map_add, map_smul, map_smul, h0, smul_zero, zero_add] at this
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  refine ContinuousLinearMap.ext fun x => ?_
  rw [pi_eq_sum_univ x, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, show (fun j => if i = j then (1 : ℝ) else 0) = (Pi.single i 1 : Fin (n + 1) → ℝ) from by
    funext j; simp [Pi.single_apply, eq_comm]]
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [h0, smul_zero]
  · rw [hk k, smul_zero]

/-- **The Poincaré ball has `n (n + 1)/2` independent Killing fields**: smooth, Killing for the Levi-Civita connection
at every point, linearly independent. -/
theorem exists_killing_poincareBall :
    ∃ Y : Fin (n * (n + 1) / 2) → Π p : Ball n, TangentSpace 𝓘(ℝ, Fin n → ℝ) p,
      (∀ i, ContMDiff 𝓘(ℝ, Fin n → ℝ) (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, Fin n → ℝ)) ∞
          (fun q : Ball n => (⟨q, Y i q⟩ : TangentBundle 𝓘(ℝ, Fin n → ℝ) (Ball n))) ∧
        ∀ p, IsKillingAt (leviCivita (poincareBallMetric n)) (poincareBallMetric n) (Y i) p) ∧
      LinearIndependent ℝ Y := by
  have hcard : Fintype.card {q : Fin (n + 1) × Fin (n + 1) // q.1 < q.2} = n * (n + 1) / 2 := by
    rw [card_pairs_lt, Nat.add_sub_cancel, mul_comm]
  obtain ⟨b⟩ : Nonempty (Basis (Fin (n * (n + 1) / 2)) ℝ (skewEta (n + 1))) :=
    ⟨((Pi.basisFun ℝ {q : Fin (n + 1) × Fin (n + 1) // q.1 < q.2}).map
      ((skewEtaEquiv (n + 1)).trans (antisymmEquiv (n + 1))).symm).reindex
      (Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin]))⟩
  let Y : Fin (n * (n + 1) / 2) → Π p : Ball n, TangentSpace 𝓘(ℝ, Fin n → ℝ) p :=
    fun i => ballField (b i).2
  refine ⟨Y, fun i => ⟨contMDiff_ballField (b i).2, isKillingAt_ballField (b i).2⟩, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set S : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ∑ i, c i • ((b i : skewEta (n + 1)) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) with hSdef
  have hT : ∀ p, S (ballIncl p) = 0 := by
    intro p
    have h2 : (∑ i, c i • Y i) p = 0 := congrFun hc p
    rw [Finset.sum_apply] at h2
    simp only [Pi.smul_apply] at h2
    have h3 := congrArg (dι (I := 𝓘(ℝ, Fin n → ℝ)) ballIncl p) h2
    erw [map_sum, map_zero] at h3
    rw [hSdef, sum_apply, ← h3]
    refine Finset.sum_congr rfl fun x _ => ?_
    erw [map_smul, dι_ballField (b x).2]
    rfl
  have hS0 := eq_zero_of_vanish_ballIncl S hT
  have hS : (∑ i, c i • b i : skewEta (n + 1)) = 0 := by
    apply Subtype.ext
    simpa [hSdef, Submodule.coe_sum] using hS0
  intro i
  have h := congrArg (fun v => b.repr v i) hS
  simpa [map_sum, Finsupp.single_apply] using h

/-- **The Poincaré ball is maximally symmetric** on the whole ball: constant curvature `-1` and `n (n + 1)/2`
linearly independent smooth Killing fields, for the metric with coordinate components `hyperbolicMetric n`. -/
theorem isMaximallySymmetric_poincareBall : IsMaximallySymmetric (poincareBallMetric n) (-1) :=
  ⟨hasConstantCurvature_poincareBall, exists_killing_poincareBall⟩

end Lightlike
