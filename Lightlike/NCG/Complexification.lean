import Lightlike.NCG.Uniqueness

/-!
# Real finite spectral triples through a complexification

T. Krajewski, arXiv:hep-th/9701081, Section 3.1, p. 10 (read): for a real algebra `A = ⊕ Mₙᵢ(K)`, `K = ℝ, ℂ, ℍ`, "all our
formulae remain valid, provided the indices `i` and `j` label irreducible representations of `A`". Here the irreducible
representations are encoded by a **complexification** of the triple: a faithful complex-linear `*`-representation `σ` of
`⊕ M_dₖ(ℂ)` on `H` and a real `*`-homomorphism `φ : A → ⊕ M_dₖ(ℂ)` with `π = σ ∘ φ`, every `σ(x)` a complex combination
of the `π(a)`. Then the order-zero and first-order conditions pass from `π` to `σ`, so `σ`, `D` and `J` form a
complex-linear real finite spectral triple, and the uniqueness theorem for complex summands gives a unitary
`H ≅ ⊕ ℂ^{dₖ} ⊗ ℂ^{rₖₗ} ⊗ ℂ^{dₗ}` intertwining `π` with the model's representation of `φ(A)` and `J` with the model's
`J`.

* `commJ_span`: if `L(s)` commutes with `J s' J` for `s ∈ S`, `s' ∈ S'` and `L` is complex-linear, then `L(X)` commutes with
  `J Y J` for `X ∈ span S`, `Y ∈ span S'`;
* `commL`: `X ↦ [D, X]`, complex-linear;
* `Complexification`, `Complexification.triple`, `Complexification.realStructure`, `Complexification.isComplexLinear`;
* `Complexification.exists_unitary`: the uniqueness theorem for a real algebra with a complexification.
-/

namespace Lightlike.NCG

noncomputable section

open FiniteSpectralTriple

variable {A H : Type*} [Ring A] [StarRing A] [Algebra ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
variable {T : FiniteSpectralTriple A H} (R : RealStructure T)

/-- **Commutation with `J Y J` passes to complex spans**: `J` is antilinear, so `J (c Y) J = c̄ J Y J`, and the
condition is complex-linear in both slots. -/
lemma commJ_span (L : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)) {S S' : Set (H →L[ℂ] H)}
    (h : ∀ s ∈ S, ∀ s' ∈ S', ∀ v, L s (R.J (s' (R.J v))) = R.J (s' (R.J (L s v))))
    {X Y : H →L[ℂ] H} (hX : X ∈ Submodule.span ℂ S) (hY : Y ∈ Submodule.span ℂ S') (v : H) :
    L X (R.J (Y (R.J v))) = R.J (Y (R.J (L X v))) := by
  induction hY using Submodule.span_induction generalizing v with
  | mem s' hs' =>
    induction hX using Submodule.span_induction generalizing v with
    | mem s hs => exact h s hs s' hs' v
    | zero => simp
    | add X₁ X₂ _ _ h₁ h₂ =>
      simp only [map_add, ContinuousLinearMap.add_apply, h₁, h₂]
    | smul c X _ hX' =>
      simp only [map_smul, ContinuousLinearMap.smul_apply, hX', LinearMap.map_smulₛₗ, ContinuousLinearMap.map_smul,
        starRingEnd_self_apply]
  | zero => simp
  | add Y₁ Y₂ _ _ h₁ h₂ =>
    simp only [ContinuousLinearMap.add_apply, map_add, h₁, h₂]
  | smul c Y _ hY' =>
    simp only [ContinuousLinearMap.smul_apply, LinearMap.map_smulₛₗ, ContinuousLinearMap.map_smul, hY']

/-- `X ↦ [D, X]`, a complex-linear map. -/
def commL (D : H →L[ℂ] H) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun X := FiniteSpectralTriple.comm D X
  map_add' X Y := by simp only [FiniteSpectralTriple.comm, mul_add, add_mul]; abel
  map_smul' c X := by
    simp only [FiniteSpectralTriple.comm, mul_smul_comm, smul_mul_assoc, smul_sub, RingHom.id_apply]

/-- `commL D X = [D, X]`. -/
lemma commL_apply (D X : H →L[ℂ] H) : commL D X = FiniteSpectralTriple.comm D X := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (T) in
/-- **A complexification** of a finite spectral triple: a faithful complex-linear `*`-representation `σ` of
`⊕ M_dₖ(ℂ)` and a real `*`-homomorphism `φ : A → ⊕ M_dₖ(ℂ)` with `π = σ ∘ φ`, every `σ(x)` in the complex span of
`π(A)`. -/
structure Complexification (d : ι → ℕ) where
  /-- The complex-linear representation. -/
  σ : MatSum d →⋆ₐ[ℂ] (H →L[ℂ] H)
  /-- `σ` is faithful. -/
  injective_σ : Function.Injective σ
  /-- The real algebra inside `⊕ M_dₖ(ℂ)`. -/
  φ : A →⋆ₐ[ℝ] MatSum d
  /-- `π = σ ∘ φ`. -/
  pi_eq : ∀ a, T.π a = σ (φ a)
  /-- `σ(x)` is a complex combination of the `π(a)`. -/
  mem_span : ∀ x, σ x ∈ Submodule.span ℂ (Set.range T.π)

variable {d : ι → ℕ}

/-- `σ` as a real `*`-homomorphism. -/
def Complexification.σℝ (C : Complexification T d) : MatSum d →⋆ₐ[ℝ] (H →L[ℂ] H) :=
  { (C.σ.toAlgHom : MatSum d →ₐ[ℂ] (H →L[ℂ] H)).restrictScalars ℝ with map_star' := C.σ.map_star' }

/-- `σℝ` is `σ`. -/
lemma Complexification.σℝ_apply (C : Complexification T d) (x : MatSum d) : C.σℝ x = C.σ x := rfl

/-- **The complexified triple** `(⊕ M_dₖ(ℂ), H, D)`. -/
def Complexification.triple (C : Complexification T d) : FiniteSpectralTriple (MatSum d) H where
  π := C.σℝ
  injective_π := C.injective_σ
  D := T.D
  isSelfAdjoint_D := T.isSelfAdjoint_D

/-- **The complexified triple is complex-linear.** -/
theorem Complexification.isComplexLinear (C : Complexification T d) : IsComplexLinear C.triple :=
  fun c a => map_smul C.σ c a

/-- **`J` is a real structure for the complexified triple**: the order-zero and first-order conditions pass from `π(A)`
to its complex span (`commJ_span`). -/
def Complexification.realStructure (C : Complexification T d) : RealStructure C.triple where
  J := R.J
  inner_J := R.inner_J
  J_J := R.J_J
  order_zero a b x := by
    have h := commJ_span R LinearMap.id (S := Set.range T.π) (S' := Set.range T.π)
      (fun s hs s' hs' v => by
        obtain ⟨a', rfl⟩ := hs
        obtain ⟨b', rfl⟩ := hs'
        exact R.order_zero a' b' v) (C.mem_span a) (C.mem_span b) x
    simp only [LinearMap.id_apply] at h
    exact h
  first_order a b x := by
    have h := commJ_span R (commL T.D) (S := Set.range T.π) (S' := Set.range T.π)
      (fun s hs s' hs' v => by
        obtain ⟨a', rfl⟩ := hs
        obtain ⟨b', rfl⟩ := hs'
        exact R.first_order a' b' v) (C.mem_span a) (C.mem_span b) x
    simp only [commL_apply] at h
    exact h
  D_J := R.D_J

/-- **Uniqueness for a real algebra with a complexification** (Krajewski, Section 3.1, p. 10, with Section 3.2, p. 13):
`H` is unitarily equivalent to the model `⊕ ℂ^{dₖ} ⊗ ℂ^{rₖₗ} ⊗ ℂ^{dₗ}` of the multiplicity matrix of the complexified
triple, by a unitary taking `π(a)` to the model's action of `φ(a)` and `J` to the model's `J`. -/
theorem Complexification.exists_unitary [∀ i, NeZero (d i)] (C : Complexification T d) :
    ∃ U : H ≃ₗᵢ[ℂ] HK d (fun i j => multiplicity (C.realStructure R) i j),
      (∀ a x, U (T.π a x) = piK (C.φ a) (U x)) ∧
        ∀ x, U (R.J x) = JK (multiplicity_symm (C.realStructure R)) (U x) := by
  obtain ⟨U, hU, hJ⟩ := exists_unitary_krajewski (C.realStructure R) C.isComplexLinear
  refine ⟨U, fun a x => ?_, hJ⟩
  rw [C.pi_eq a]
  exact hU (C.φ a) x

end

end Lightlike.NCG
