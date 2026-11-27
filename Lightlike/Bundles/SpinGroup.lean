import Mathlib
import Lightlike.Dirac.CliffordNorm
import Lightlike.Dirac.CliffordCenter

/-!
# The spin group `Spin(n)` as a topological group

Mathlib's `spinGroup (Qneg n)` is the submonoid `Spin(n)` of the Clifford algebra `Cl(ℝⁿ, -‖·‖²)`
with its group structure (inverse = `star`).  This file gives it the topology of a subspace of the
finite-dimensional Clifford algebra (the unique Hausdorff vector-space topology, realised by the
normed structure `clNormedRing`) and proves that it is a topological group
(`spinGroup.isTopologicalGroup`).  A map into `Spin(n)` is continuous if and only if it is
continuous as a map into the Clifford algebra (`continuous_spinGroup_iff`).

This is the structure group of the principal `Spin(n)`-bundle of a spin structure and of the
associated spinor bundles (`Lightlike.Dirac.SpinorBundle`).
-/

open CliffordAlgebra

namespace Lightlike.Dirac

variable {n : ℕ}

/-- The topology of the Clifford algebra `Cl(ℝⁿ, -‖·‖²)`: the one of its normed structure
`clNormedRing`, i.e. the unique Hausdorff vector-space topology of a finite-dimensional real space. -/
@[reducible] noncomputable def clTopology (n : ℕ) : TopologicalSpace (CliffordAlgebra (Qneg n)) :=
  (clNormedRing n).toUniformSpace.toTopologicalSpace

/-- `Spin(n)` carries the subspace topology of the Clifford algebra. -/
noncomputable instance spinGroup.instTopologicalSpace :
    TopologicalSpace (spinGroup (Qneg n)) :=
  TopologicalSpace.induced (fun s => (s : CliffordAlgebra (Qneg n))) (clTopology n)

/-- The inclusion of `Spin(n)` in the Clifford algebra is an embedding. -/
lemma spinGroup.isInducing_coe :
    @Topology.IsInducing _ _ _ (clTopology n) (fun s : spinGroup (Qneg n) => (s : CliffordAlgebra (Qneg n))) :=
  @Topology.IsInducing.mk _ _ _ (clTopology n) _ rfl

/-- A map into `Spin(n)` is continuous iff it is continuous into the Clifford algebra. -/
lemma continuous_spinGroup_iff {X : Type*} [TopologicalSpace X] {f : X → spinGroup (Qneg n)} :
    Continuous f ↔
      @Continuous X (CliffordAlgebra (Qneg n)) _ (clTopology n) (fun x => (f x : CliffordAlgebra (Qneg n))) :=
  letI := clTopology n
  (spinGroup.isInducing_coe (n := n)).continuous_iff

/-- A map into `Spin(n)` is continuous on a set iff it is continuous on it into the Clifford algebra. -/
lemma continuousOn_spinGroup_iff {X : Type*} [TopologicalSpace X] {f : X → spinGroup (Qneg n)}
    {s : Set X} :
    ContinuousOn f s ↔
      @ContinuousOn _ _ _ (clTopology n) (fun x => (f x : CliffordAlgebra (Qneg n))) s :=
  letI := clTopology n
  (spinGroup.isInducing_coe (n := n)).continuousOn_iff

/-- **`Spin(n)` is a topological group.** -/
instance spinGroup.isTopologicalGroup : IsTopologicalGroup (spinGroup (Qneg n)) := by
  let _ := clNormedRing n
  let _ := clNormedAlgebra n
  have hmul : Continuous fun p : spinGroup (Qneg n) × spinGroup (Qneg n) => p.1 * p.2 := by
    rw [continuous_spinGroup_iff]
    have h1 : Continuous fun p : spinGroup (Qneg n) × spinGroup (Qneg n) =>
        (p.1 : CliffordAlgebra (Qneg n)) :=
      (continuous_spinGroup_iff.1 continuous_id).comp continuous_fst
    have h2 : Continuous fun p : spinGroup (Qneg n) × spinGroup (Qneg n) =>
        (p.2 : CliffordAlgebra (Qneg n)) :=
      (continuous_spinGroup_iff.1 continuous_id).comp continuous_snd
    exact h1.mul h2
  have hinv : Continuous fun s : spinGroup (Qneg n) => s⁻¹ := by
    rw [continuous_spinGroup_iff]
    have hstar : Continuous fun x : CliffordAlgebra (Qneg n) => star x := by
      have : (fun x : CliffordAlgebra (Qneg n) => star x) =
          (LinearMap.toContinuousLinearMap ((reverse : CliffordAlgebra (Qneg n) →ₗ[ℝ] _).comp
            (involute : CliffordAlgebra (Qneg n) →ₐ[ℝ] _).toLinearMap) : _ → _) := by
        funext x; simp [star_def]
      rw [this]; exact ContinuousLinearMap.continuous _
    have : (fun s : spinGroup (Qneg n) => ((s⁻¹ : spinGroup (Qneg n)) : CliffordAlgebra (Qneg n))) =
        fun s : spinGroup (Qneg n) => star (s : CliffordAlgebra (Qneg n)) := by
      funext s; rw [← spinGroup.star_eq_inv]; rfl
    rw [this]
    exact hstar.comp (continuous_spinGroup_iff.1 continuous_id)
  exact { continuous_mul := hmul, continuous_inv := hinv }

/-- A Clifford-module representation restricted to `Spin(n)`, as a monoid homomorphism into the
operators. -/
noncomputable def spinRep {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep n V) : spinGroup (Qneg n) →* (V →L[ℝ] V) :=
  ρ.toMonoidHom.comp (spinGroup (Qneg n)).subtype

@[simp] lemma spinRep_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep n V) (s : spinGroup (Qneg n)) : spinRep ρ s = ρ s := rfl

/-- The restriction of a Clifford-module representation to `Spin(n)` is continuous. -/
lemma continuous_spinRep {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : CliffordRep n V) : Continuous (spinRep ρ) := by
  let _ := clNormedRing n
  let _ := clNormedAlgebra n
  have hρ : Continuous fun x : CliffordAlgebra (Qneg n) => ρ x :=
    (LinearMap.toContinuousLinearMap ρ.toLinearMap).continuous
  exact hρ.comp (continuous_spinGroup_iff.1 continuous_id)

/-! ## The vector action `Spin(n) → GL(ℝⁿ)` -/

/-- `ι` is injective for the negative definite form: `ι v = 0` forces `-‖v‖² = 0`. -/
theorem ι_injective_Qneg : Function.Injective (ι (Qneg n)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h := ι_sq_scalar (Qneg n) v
  rw [hv, zero_mul] at h
  have hnt : Nontrivial (CliffordAlgebra (Qneg n)) := by
    have : Nontrivial (ExteriorAlgebra ℝ (E n)) := inferInstance
    exact (CliffordAlgebra.equivExterior (Qneg n)).toEquiv.nontrivial
  have h0 : Qneg n v = 0 := (algebraMap ℝ (CliffordAlgebra (Qneg n))).injective (by rw [← h, map_zero])
  rw [Qneg_apply, neg_eq_zero, sq_eq_zero_iff, norm_eq_zero] at h0
  exact h0

/-- `ι` as a linear equivalence onto its range. -/
noncomputable def ιRange (n : ℕ) : E n ≃ₗ[ℝ] LinearMap.range (ι (Qneg n)) :=
  LinearEquiv.ofInjective (ι (Qneg n)) ι_injective_Qneg

/-- Conjugation by a spin element keeps vectors as vectors: `s ι(v) s⋆ ∈ range ι`. -/
lemma conj_mem_range (s : spinGroup (Qneg n)) (v : E n) :
    (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v * star (s : CliffordAlgebra (Qneg n)) ∈
      LinearMap.range (ι (Qneg n)) := by
  have h := spinGroup.involute_act_ι_mem_range_ι (x := spinGroup.toUnits s) s.2 v
  have hi : involute (Q := Qneg n) (s : CliffordAlgebra (Qneg n)) = s := spinGroup.involute_eq s.2
  simpa [hi, ← spinGroup.star_eq_inv] using h

/-- The vector action of `s` on `ℝⁿ = E n`: `v ↦ ι⁻¹ (s ι(v) s⋆)`, as a linear map. -/
noncomputable def vecConj (s : spinGroup (Qneg n)) : E n →ₗ[ℝ] E n :=
  (ιRange n).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (ι (Qneg n)))
      ((LinearMap.mulRight ℝ (star (s : CliffordAlgebra (Qneg n)))) ∘ₗ
        (LinearMap.mulLeft ℝ (s : CliffordAlgebra (Qneg n))) ∘ₗ ι (Qneg n))
      (fun v => by simpa [mul_assoc] using conj_mem_range s v)

/-- The defining property: `ι (vecConj s v) = s ι(v) s⋆`. -/
lemma ι_vecConj (s : spinGroup (Qneg n)) (v : E n) :
    ι (Qneg n) (vecConj s v) =
      (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v * star (s : CliffordAlgebra (Qneg n)) := by
  have key : ∀ y : E n, ι (Qneg n) y =
      ((ιRange n y : LinearMap.range (ι (Qneg n))) : CliffordAlgebra (Qneg n)) := fun y => by
    simp [ιRange]
  rw [key]
  simp only [vecConj, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply]

lemma vecConj_eq_iff (s : spinGroup (Qneg n)) (v w : E n) :
    vecConj s v = w ↔
      (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) v * star (s : CliffordAlgebra (Qneg n)) =
        ι (Qneg n) w := by
  rw [← ι_vecConj]
  exact ⟨fun h => by rw [h], fun h => ι_injective_Qneg h⟩

lemma vecConj_mul (s t : spinGroup (Qneg n)) (v : E n) :
    vecConj (s * t) v = vecConj s (vecConj t v) := by
  rw [vecConj_eq_iff, ι_vecConj, ι_vecConj]
  simp only [Submonoid.coe_mul, star_mul]
  simp only [mul_assoc]

lemma vecConj_one (v : E n) : vecConj (1 : spinGroup (Qneg n)) v = v := by
  rw [vecConj_eq_iff]; simp

/-- **The vector action** `Spin(n) →* GL(ℝⁿ)`, `s ↦ (v ↦ s v s⋆)`, on the coordinate space
`Fin n → ℝ` (the model of the orthonormal frames, `EuclideanSpace ℝ (Fin n)` read through
`WithLp`). -/
noncomputable def vectorAction (n : ℕ) : spinGroup (Qneg n) →* ((Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) where
  toFun s :=
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap ∘ₗ vecConj s ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
      invFun := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap ∘ₗ vecConj s⁻¹ ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
      left_inv := fun v => by
        simp [← vecConj_mul, vecConj_one]
      right_inv := fun v => by
        simp [← vecConj_mul, vecConj_one] }
  map_one' := by ext v; simp [vecConj_one]
  map_mul' s t := by ext v; simp [vecConj_mul]

/-- `vectorAction` in terms of the conjugation. -/
lemma vectorAction_apply (s : spinGroup (Qneg n)) (v : Fin n → ℝ) :
    ι (Qneg n) (WithLp.toLp 2 (vectorAction n s v)) =
      (s : CliffordAlgebra (Qneg n)) * ι (Qneg n) (WithLp.toLp 2 v) *
        star (s : CliffordAlgebra (Qneg n)) := by
  simp [vectorAction, ← ι_vecConj]

end Lightlike.Dirac
