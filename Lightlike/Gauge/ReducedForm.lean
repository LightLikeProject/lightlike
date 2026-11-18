import Lightlike.Gauge.ConstraintsAPI

/-!
# The induced symplectic form of a linear symplectic reduction

For an isotropic subspace `D` of a finite-dimensional symplectic vector space `(E, σ)` (the orbit directions of a
group action at a zero of its moment map are such a subspace), the form `σ` descends to the quotient
`D^⊥ / (D^⊥ ∩ D)` (the tangent space of the reduced space of Marsden and Weinstein, Cannas da Silva Section 23),
and the descended form is nondegenerate.

* `reducedForm`: the descended bilinear form on `D^⊥ ⧸ D`.
* `reducedForm_mk`, `reducedForm_nondegenerate`.

Linear case only: the nonlinear reduction of a manifold by a free proper action is not covered here.
-/

namespace Lightlike.Gauge

open LinearMap.BilinForm

variable {E : Type} [AddCommGroup E] [Module ℝ E] {σ : LinearMap.BilinForm ℝ E}

/-- `D` is isotropic: `D ⊆ D^⊥`. -/
abbrev IsIsotropicSub (σ : LinearMap.BilinForm ℝ E) (D : Submodule ℝ E) : Prop := D ≤ σ.orthogonal D

/-- The quotient `D^⊥ / D` of the `σ`-orthogonal of an isotropic subspace by the subspace. -/
abbrev ReducedSpace (σ : LinearMap.BilinForm ℝ E) (D : Submodule ℝ E) : Type :=
  σ.orthogonal D ⧸ Submodule.comap (σ.orthogonal D).subtype D

variable {D : Submodule ℝ E}

lemma sigma_orth_zero (hr : σ.IsRefl) (u : σ.orthogonal D) {d : E} (hd : d ∈ D) : σ u d = 0 := by
  have := (LinearMap.BilinForm.mem_orthogonal_iff.mp u.2) d hd
  exact hr _ _ this

/-- **The descended form**: `σ` on `D^⊥ ⧸ D`, for `D` isotropic. -/
noncomputable def reducedForm (hr : σ.IsRefl) (hD : IsIsotropicSub σ D) :
    LinearMap.BilinForm ℝ (ReducedSpace σ D) := by
  let N := σ.orthogonal D
  let K : Submodule ℝ N := Submodule.comap N.subtype D
  let B0 : N →ₗ[ℝ] N →ₗ[ℝ] ℝ := σ.compl₁₂ N.subtype N.subtype
  let B1 : N →ₗ[ℝ] (N ⧸ K) →ₗ[ℝ] ℝ :=
    { toFun := fun u => K.liftQ (B0 u) (fun k hk => sigma_orth_zero hr u hk)
      map_add' := fun u v => by
        refine LinearMap.ext fun k => Submodule.Quotient.induction_on K k fun k => ?_
        simp [B0]; rfl
      map_smul' := fun c u => by
        refine LinearMap.ext fun k => Submodule.Quotient.induction_on K k fun k => ?_
        show σ ((c • u : N) : E) (k : E) = c * σ (u : E) (k : E)
        simp }
  exact K.liftQ B1 (fun k hk => by
    refine LinearMap.ext fun w => Submodule.Quotient.induction_on K w fun w => ?_
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) k hk
    exact this)

/-- The descended form is computed on representatives. -/
theorem reducedForm_mk (hr : σ.IsRefl) (hD : IsIsotropicSub σ D) (u v : σ.orthogonal D) :
    reducedForm hr hD (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = σ u v := rfl

/-- **The reduced space is symplectic**: the descended form is nondegenerate (finite dimension, `σ`
nondegenerate and reflexive, `D` isotropic). -/
theorem reducedForm_nondegenerate [FiniteDimensional ℝ E] (hσ : σ.Nondegenerate) (hr : σ.IsRefl)
    (hD : IsIsotropicSub σ D) : (reducedForm hr hD).Nondegenerate := by
  have key : ∀ m : ReducedSpace σ D, (∀ n, reducedForm hr hD m n = 0) → m = 0 := by
    intro m hm
    induction m using Submodule.Quotient.induction_on with
    | H u =>
      have hu : (u : E) ∈ σ.orthogonal (σ.orthogonal D) := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro y hy
        exact hr _ _ (by simpa [reducedForm_mk] using hm (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [LinearMap.BilinForm.orthogonal_orthogonal hσ hr] at hu
      exact (Submodule.Quotient.mk_eq_zero _).mpr hu
  refine ⟨fun m hm => key m hm, fun m hm => key m fun n => ?_⟩
  induction m using Submodule.Quotient.induction_on with
  | H u =>
    induction n using Submodule.Quotient.induction_on with
    | H v =>
      have := hm (Submodule.Quotient.mk v)
      rw [reducedForm_mk] at this ⊢
      exact hr _ _ this

end Lightlike.Gauge
