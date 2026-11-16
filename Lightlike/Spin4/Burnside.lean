import Mathlib

/-!
# Burnside's theorem and irreducible external tensor products

General representation theory used for Spin(4) = SU(2) × SU(2); nothing here is specific to SU(2).

## Main results

* `lsmul_surjective_of_isAlgClosed` (**Burnside's theorem**): if `V` is a simple module over a
  `k`-algebra `A` and finite-dimensional over an algebraically closed field `k`, every
  `k`-linear endomorphism of `V` is the action of some element of `A`. The proof combines Schur's
  lemma and the Jacobson density theorem, both in Mathlib (the same argument as Mathlib pull
  request #43894).
* `span_range_eq_top`: for an irreducible finite-dimensional representation `ρ` of a monoid over
  an algebraically closed field, the operators `ρ g` span `End k V`.
* `extTprod ρ σ`: the external tensor product, the representation `(g, h) ↦ ρ g ⊗ σ h` of `G × H`
  on `V ⊗ W` (Mathlib's `Representation.tprod` of the two pulled back to `G × H`).
* `isIrreducible_extTprod`: the external tensor product of two irreducible finite-dimensional
  representations over an algebraically closed field is irreducible.
* `IsIrreducible.of_equiv`: irreducibility transfers along an equivalence of representations.

`IsAlgClosed k` is needed: over `ℝ`, rotation by `π/2` is an irreducible representation of `ℤ`
on `ℝ²` whose external tensor square is reducible (`Spin4.Test.rot90_isIrreducible`,
`Spin4.Test.not_isIrreducible_rot90_tensor` in `Lightlike/Spin4/Tests.lean`).

## References

* P. Etingof et al., *Introduction to Representation Theory*, Student Mathematical Library 59,
  AMS (2011), Ch. 3 (the density theorem, Burnside's theorem, representations of tensor
  products).
* S. Lang, *Algebra*, rev. 3rd ed., Graduate Texts in Mathematics 211, Springer (2002), Ch. XVII
  (the Jacobson density theorem and Burnside's theorem).
-/

open TensorProduct

namespace Lightlike.Spin4

/-! ## Burnside's theorem -/

section Burnside

variable {A V : Type*} (k : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V] [IsSimpleModule A V] [FiniteDimensional k V] [IsAlgClosed k]

/-- **Burnside's theorem.** If `V` is a simple module over a `k`-algebra `A`, finite-dimensional
over the algebraically closed field `k`, then every `k`-linear endomorphism of `V` is the action
of an element of `A`. (Schur's lemma makes the commutant of `A` equal to `k`; the Jacobson density
theorem then makes `A` act as the full bicommutant `End k V`.) -/
theorem lsmul_surjective_of_isAlgClosed :
    Function.Surjective (Algebra.lsmul k k V : A →ₐ[k] Module.End k V) := by
  have : Module.Finite (Module.End A V) V := Module.Finite.of_restrictScalars_finite k _ V
  intro f
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) <|
    LinearMap.extendScalarsOfSurjective
      (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).surjective f
  exact ⟨a, LinearMap.ext fun m => congrArg (fun f => f m) ha⟩

end Burnside

section Group

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

omit [IsAlgClosed k] [FiniteDimensional k V] in
/-- Every element of the group algebra acts by an operator in the span of the `ρ g`. -/
lemma asAlgebraHom_mem_span (ρ : Representation k G V) (r : MonoidAlgebra k G) :
    ρ.asAlgebraHom r ∈ Submodule.span k (Set.range ρ) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single g a =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- **Burnside for group representations.** The operators `ρ g` of an irreducible
finite-dimensional representation over an algebraically closed field span `End k V`. -/
theorem span_range_eq_top (ρ : Representation k G V) [ρ.IsIrreducible] :
    Submodule.span k (Set.range ρ) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  obtain ⟨r, hr⟩ := lsmul_surjective_of_isAlgClosed k (A := MonoidAlgebra k G)
    (V := ρ.asModule) f
  have hf : f = ρ.asAlgebraHom r := by
    ext v
    exact (LinearMap.congr_fun hr v).symm
  rw [hf]
  exact asAlgebraHom_mem_span ρ r

end Group

/-! ## External tensor products -/

section Tensor

variable {k G H V W : Type*} [Field k] [Monoid G] [Monoid H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The **external tensor product** of a representation `ρ` of `G` on `V` and a representation
`σ` of `H` on `W`: the representation `(g, h) ↦ ρ g ⊗ σ h` of `G × H` on `V ⊗ W`. It is Mathlib's
`Representation.tprod` of `ρ ∘ fst` and `σ ∘ snd`. -/
noncomputable def extTprod (ρ : Representation k G V) (σ : Representation k H W) :
    Representation k (G × H) (V ⊗[k] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

@[simp] lemma extTprod_apply (ρ : Representation k G V) (σ : Representation k H W) (g : G × H) :
    extTprod ρ σ g = TensorProduct.map (ρ g.1) (σ g.2) := rfl

lemma extTprod_apply_tmul (ρ : Representation k G V) (σ : Representation k H W) (g : G × H)
    (v : V) (w : W) : extTprod ρ σ g (v ⊗ₜ w) = ρ g.1 v ⊗ₜ σ g.2 w := rfl

/-- An irreducible representation lives on a nonzero space. -/
lemma nontrivial_of_isIrreducible {G' V' : Type*} [Monoid G'] [AddCommGroup V'] [Module k V']
    (ρ : Representation k G' V') [ρ.IsIrreducible] : Nontrivial V' := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact bot_ne_top (α := Subrepresentation ρ)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

/-- A subspace of `V ⊗ W` invariant under every `A ⊗ B` is invariant under every endomorphism,
since the maps `A ⊗ B` span `End (V ⊗ W)` (finite-dimensional case). -/
lemma mem_of_map_mem [FiniteDimensional k V] [FiniteDimensional k W]
    (S : Submodule k (V ⊗[k] W))
    (hS : ∀ (A : Module.End k V) (B : Module.End k W), ∀ x ∈ S, TensorProduct.map A B x ∈ S)
    (φ : Module.End k (V ⊗[k] W)) {x : V ⊗[k] W} (hx : x ∈ S) : φ x ∈ S := by
  obtain ⟨t, rfl⟩ := (homTensorHomEquiv k V W V W).surjective φ
  induction t using TensorProduct.inductionOn with
  | tmul A B => simpa using hS A B x hx
  | add t₁ t₂ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact S.add_mem h₁ h₂

/-- A nonzero subspace of a vector space invariant under every endomorphism is everything. -/
lemma eq_top_of_forall_end {U : Type*} [AddCommGroup U] [Module k U] (S : Submodule k U)
    (hS : ∀ φ : Module.End k U, ∀ x ∈ S, φ x ∈ S) (hbot : S ≠ ⊥) : S = ⊤ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual k U, f x ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx0 ((Module.forall_dual_apply_eq_zero_iff k x).mp h)
  rw [eq_top_iff]
  intro y _
  have := hS ((f x)⁻¹ • f.smulRight y) x hx
  simpa [smul_smul, inv_mul_cancel₀ hf] using this

variable [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W]

/-- **The external tensor product of irreducible representations is irreducible** (finite
dimensions, algebraically closed field). By Burnside's theorem the operators `ρ g ⊗ 1` and
`1 ⊗ σ h` generate every `A ⊗ B`, hence all of `End (V ⊗ W)`, and a nonzero subspace invariant
under all endomorphisms is everything. -/
theorem isIrreducible_extTprod (ρ : Representation k G V) (σ : Representation k H W)
    [ρ.IsIrreducible] [σ.IsIrreducible] : (extTprod ρ σ).IsIrreducible := by
  have := nontrivial_of_isIrreducible ρ
  have := nontrivial_of_isIrreducible σ
  have hpos : 0 < Module.finrank k (V ⊗[k] W) := by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  have : Nontrivial (V ⊗[k] W) := Module.nontrivial_of_finrank_pos hpos
  have : Nontrivial (Subrepresentation (extTprod ρ σ)) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine { eq_bot_or_eq_top := fun S => ?_ }
  set T := S.toSubmodule
  -- invariance under `A ⊗ 1` for every `A`, by Burnside for `ρ`
  have hL : ∀ A : Module.End k V, ∀ x ∈ T, TensorProduct.map A LinearMap.id x ∈ T := by
    intro A
    have hA : A ∈ Submodule.span k (Set.range ρ) := by rw [span_range_eq_top]; trivial
    induction hA using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      intro x hx
      have := S.apply_mem_toSubmodule (g, 1) hx
      simpa [Module.End.one_eq_id] using this
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [TensorProduct.map_add_left, LinearMap.add_apply]
      exact T.add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact T.smul_mem c (hB x hx)
  -- invariance under `1 ⊗ B` for every `B`, by Burnside for `σ`
  have hR : ∀ B : Module.End k W, ∀ x ∈ T, TensorProduct.map LinearMap.id B x ∈ T := by
    intro B
    have hB : B ∈ Submodule.span k (Set.range σ) := by rw [span_range_eq_top]; trivial
    induction hB using Submodule.span_induction with
    | mem C hC =>
      obtain ⟨h, rfl⟩ := hC
      intro x hx
      have := S.apply_mem_toSubmodule (1, h) hx
      simpa [Module.End.one_eq_id] using this
    | zero => intro x _; simp
    | add C D _ _ hC hD =>
      intro x hx
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
      exact T.add_mem (hC x hx) (hD x hx)
    | smul c C _ hC =>
      intro x hx
      rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
      exact T.smul_mem c (hC x hx)
  have hAB : ∀ (A : Module.End k V) (B : Module.End k W), ∀ x ∈ T,
      TensorProduct.map A B x ∈ T := by
    intro A B x hx
    have : TensorProduct.map A B x =
        TensorProduct.map A LinearMap.id (TensorProduct.map LinearMap.id B x) := by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
    rw [this]
    exact hL A _ (hR B x hx)
  by_cases hbot : T = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hbot)
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (eq_top_of_forall_end T (fun φ x hx => mem_of_map_mem T hAB φ hx) hbot))

end Tensor

/-! ## Transport along an equivalence -/

/-- **Irreducibility is invariant under equivalence of representations.** -/
theorem IsIrreducible.of_equiv {k G V W : Type*} [Field k] [Monoid G] [AddCommGroup V]
    [Module k V] [AddCommGroup W] [Module k W] {ρ : Representation k G V}
    {σ : Representation k G W} (φ : ρ.Equiv σ) [ρ.IsIrreducible] : σ.IsIrreducible := by
  have := nontrivial_of_isIrreducible ρ
  let e : V ≃ₗ[k] W := φ.toLinearEquiv
  have he : ∀ g v, e (ρ g v) = σ g (e v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v
  have : Nontrivial W := e.injective.nontrivial
  have : Nontrivial (Subrepresentation σ) :=
    ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  refine { eq_bot_or_eq_top := fun S => ?_ }
  let S' : Subrepresentation ρ :=
    { toSubmodule := S.toSubmodule.comap e.toLinearMap
      apply_mem_toSubmodule := fun g v hv => by
        change e (ρ g v) ∈ S.toSubmodule
        rw [he]
        exact S.apply_mem_toSubmodule g hv }
  have hmem : ∀ w, w ∈ S.toSubmodule ↔ e.symm w ∈ S'.toSubmodule := fun w => by
    change w ∈ S.toSubmodule ↔ e (e.symm w) ∈ S.toSubmodule
    rw [e.apply_symm_apply]
  rcases IsSimpleOrder.eq_bot_or_eq_top S' with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro w hw
    rw [hmem, h] at hw
    change e.symm w ∈ (⊥ : Submodule k V) at hw
    rw [Submodule.mem_bot, LinearEquiv.map_eq_zero_iff] at hw
    simp [hw]
  · right
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    rw [eq_top_iff]
    intro w _
    rw [hmem, h]
    trivial

end Lightlike.Spin4
