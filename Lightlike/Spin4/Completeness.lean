import Lightlike.Spin4.Rep
import Lightlike.SU2.Completeness

/-!
# Completeness: every irreducible representation of Spin(4) is some `(j₊, j₋)`

`spin4Rep_complete`: every continuous representation `ρ : SU(2) × SU(2) →* M_d(ℂ)` (`d ≥ 1`)
that is irreducible (no invariant subspace other than `0` and `ℂ^d`) is equivalent to
`spin4Mat n m` for some `n`, `m`. Together with `spin4Representation_equiv_iff`, the labels
`(j₊, j₋) = (n/2, m/2)` classify the continuous irreducible representations of Spin(4).
`spin4_complete` is the same statement for an irreducible `Representation ℂ Spin4 V` on any
finite-dimensional space `V` with continuous matrix coefficients: it is equivalent (Mathlib's
`Representation.Equiv`) to `spin4Representation n m`.

## Implementation notes

It reduces to the group-level completeness of SU(2) (`SU2.spinRep_complete`), applied twice.

1. Let `V₁ ⊆ ℂ^d` be a nonzero subspace invariant under `SU(2) × 1`, of minimal dimension. It is
   irreducible for `SU(2) × 1`, hence equivalent to some `spinMat n`.
2. The space `M` of linear maps `A : ℂ^{n+1} → ℂ^d` with `A ∘ D^{n/2}(g) = ρ(g, 1) ∘ A` is
   nonzero (it contains the embedding of `V₁`), and `1 × SU(2)` acts on it by
   `A ↦ ρ(1, h) ∘ A`. A minimal nonzero invariant subspace `M₁ ⊆ M` is equivalent to some
   `spinMat m`, through `U : ℂ^{m+1} ≃ M₁`.
3. `Φ(x ⊗ y) = U(y)(x)` is a nonzero intertwiner from `(n, m)` to `ρ`. Its image is invariant,
   hence everything (`ρ` irreducible); its kernel is invariant, hence `0`
   (`(n, m)` irreducible, `isInvariant_eq_bot_or_eq_top`). So `Φ` is an equivalence.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer (1985), Ch. II (irreducible representations of products, characters).
* P. Etingof et al., *Introduction to Representation Theory*, Student Mathematical Library 59,
  AMS (2011), Ch. 3 (irreducible representations of tensor products).
-/

open Matrix TensorProduct

namespace Lightlike.Spin4

open SU2

/-! ## A. Tools -/

section Tools

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- A nonzero subspace with property `P` of minimal dimension, given one nonzero subspace with
property `P`: every smaller subspace with property `P` is `0` or the whole subspace. -/
lemma exists_minimal_submodule (P : Submodule ℂ V → Prop) {W₀ : Submodule ℂ V} (hP : P W₀)
    (h0 : W₀ ≠ ⊥) : ∃ W, P W ∧ W ≠ ⊥ ∧ ∀ W', P W' → W' ≤ W → W' = ⊥ ∨ W' = W := by
  classical
  have hex : ∃ k, ∃ W : Submodule ℂ V, P W ∧ W ≠ ⊥ ∧ Module.finrank ℂ W = k :=
    ⟨_, W₀, hP, h0, rfl⟩
  obtain ⟨W, hPW, hW0, hWk⟩ := Nat.find_spec hex
  refine ⟨W, hPW, hW0, fun W' hP' hle => ?_⟩
  by_cases hW' : W' = ⊥
  · exact Or.inl hW'
  · right
    have hmin := Nat.find_min' hex ⟨W', hP', hW', rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)

/-- **SU(2) completeness on an abstract finite-dimensional space**: a weakly continuous
irreducible representation of SU(2) is equivalent to some `spinMat n`. -/
lemma su2_classify [Nontrivial V] (σ : SU2 →* (V →ₗ[ℂ] V))
    (hσ : ∀ (v : V) (f : Module.Dual ℂ V), Continuous fun g => f (σ g v))
    (hirr : ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ n : ℕ, ∃ T : V ≃ₗ[ℂ] (Fin (n + 1) → ℂ), ∀ g v, T (σ g v) = spinMat n g *ᵥ T v := by
  set k := Module.finrank ℂ V
  have : NeZero k := ⟨Module.finrank_pos.ne'⟩
  let b : Module.Basis (Fin k) ℂ V := Module.finBasis ℂ V
  let ρ' : SU2 →* Matrix (Fin k) (Fin k) ℂ :=
    { toFun := fun g => LinearMap.toMatrix b b (σ g)
      map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }
  have hrel : ∀ g v, b.equivFun (σ g v) = ρ' g *ᵥ b.equivFun v := fun g v => by
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr b b (σ g) v).symm
  have hcont : Continuous ρ' := continuous_matrix fun i j => by
    simp only [ρ', MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix_apply]
    exact hσ (b j) (b.coord i)
  have hirr' : ∀ W : Submodule ℂ (Fin k → ℂ), (∀ g : SU2, ∀ v ∈ W, ρ' g *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hmap : (W.comap b.equivFun.toLinearMap).map b.equivFun.toLinearMap = W :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective W
    rcases hirr (W.comap b.equivFun.toLinearMap) (fun g v hv => by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
        rw [hrel]; exact hW g _ hv) with h | h
    · left; rw [← hmap, h, Submodule.map_bot]
    · right; rw [← hmap, h, Submodule.map_top, LinearMap.range_eq_top]
      exact b.equivFun.surjective
  obtain ⟨n, T', hT'⟩ := spinRep_complete ρ' hcont hirr'
  exact ⟨n, b.equivFun.trans T', fun g v => by
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hrel, hT', spinRep_apply]⟩

/-- Coefficients of `h ↦ F (toLin' (φ h) ∘ B)` are continuous when `φ` is. -/
lemma continuous_comp_toLin' {X : Type*} [AddCommGroup X] [Module ℂ X] {d : ℕ}
    (F : (X →ₗ[ℂ] (Fin d → ℂ)) →ₗ[ℂ] ℂ) (B : X →ₗ[ℂ] (Fin d → ℂ))
    {φ : SU2 → Matrix (Fin d) (Fin d) ℂ} (hφ : Continuous φ) :
    Continuous fun h => F ((Matrix.toLin' (φ h)).comp B) := by
  let G : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] ℂ :=
    F ∘ₗ (LinearMap.lcomp ℂ (Fin d → ℂ) B) ∘ₗ Matrix.toLin'.toLinearMap
  have hG : ∀ h, F ((Matrix.toLin' (φ h)).comp B) = G (φ h) := fun h => rfl
  have hexp : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      G X = ∑ a, ∑ c, X a c * G (Matrix.single a c 1) := by
    intro X
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show Matrix.single a c (X a c) = X a c • Matrix.single a c (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  have hfun : (fun h => F ((Matrix.toLin' (φ h)).comp B)) =
      fun h => ∑ a, ∑ c, φ h a c * G (Matrix.single a c 1) :=
    funext fun h => (hG h).trans (hexp _)
  rw [hfun]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
    (hφ.matrix_elem a c).mul continuous_const

end Tools

/-! ## B. Completeness -/

/-- **Completeness for Spin(4).** Every continuous irreducible representation of
`Spin4 = SU(2) × SU(2)` on `ℂ^d` (`d ≥ 1`) is equivalent to the spin-`(n/2, m/2)`
representation `spin4Mat n m` for some `n`, `m`. -/
theorem spin4Rep_complete {d : ℕ} [NeZero d] (ρ : Spin4 →* Matrix (Fin d) (Fin d) ℂ)
    (hρ : Continuous ρ)
    (hirr : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ g : Spin4, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ n m : ℕ, ∃ T : (Fin d → ℂ) ≃ₗ[ℂ] (Idx n m → ℂ),
      ∀ (g : Spin4) (v : Fin d → ℂ), T (ρ g *ᵥ v) = spin4Mat n m g *ᵥ T v := by
  -- the two factors
  set ρp : SU2 →* Matrix (Fin d) (Fin d) ℂ := ρ.comp (MonoidHom.inl SU2 SU2)
  set ρm : SU2 →* Matrix (Fin d) (Fin d) ℂ := ρ.comp (MonoidHom.inr SU2 SU2)
  have hsplit : ∀ g h : SU2, ρ (g, h) = ρp g * ρm h := fun g h => by
    simp only [ρp, ρm, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hsplit' : ∀ g h : SU2, ρ (g, h) = ρm h * ρp g := fun g h => by
    simp only [ρp, ρm, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hcp : Continuous ρp := hρ.comp (continuous_id.prodMk continuous_const)
  have hcm : Continuous ρm := hρ.comp (continuous_const.prodMk continuous_id)
  -- Step 1: a minimal subspace `V₁` invariant under `SU(2) × 1`, equivalent to `spinMat n`
  obtain ⟨V₁, hV₁, hV₁0, hV₁min⟩ := exists_minimal_submodule
    (fun W : Submodule ℂ (Fin d → ℂ) => ∀ g, ∀ v ∈ W, ρp g *ᵥ v ∈ W)
    (W₀ := ⊤) (fun _ _ _ => Submodule.mem_top) top_ne_bot
  have : Nontrivial V₁ := Submodule.nontrivial_iff_ne_bot.mpr hV₁0
  let σ₁ : SU2 →* (V₁ →ₗ[ℂ] V₁) :=
    { toFun := fun g => (Matrix.toLin' (ρp g)).restrict (fun v hv => hV₁ g v hv)
      map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
      map_mul' := fun g h => LinearMap.ext fun v => Subtype.ext (by
        change ρp (g * h) *ᵥ (v : Fin d → ℂ) = ρp g *ᵥ (ρp h *ᵥ (v : Fin d → ℂ))
        rw [map_mul, mulVec_mulVec]) }
  have hσ₁v : ∀ g (v : V₁), ((σ₁ g v : V₁) : Fin d → ℂ) = ρp g *ᵥ v := fun _ _ => rfl
  have hσ₁c : ∀ (v : V₁) (f : Module.Dual ℂ V₁), Continuous fun g => f (σ₁ g v) := by
    intro v f
    obtain ⟨F, hF⟩ := LinearMap.exists_extend f
    have : (fun g => f (σ₁ g v)) = fun g => F (ρp g *ᵥ v) := funext fun g => by
      rw [← hF, LinearMap.comp_apply, Submodule.subtype_apply, hσ₁v]
    rw [this]
    exact (LinearMap.continuous_of_finiteDimensional F).comp
      (hcp.matrix_mulVec continuous_const)
  have hσ₁i : ∀ W : Submodule ℂ V₁, (∀ g, ∀ v ∈ W, σ₁ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hP : ∀ g, ∀ v ∈ W.map V₁.subtype, ρp g *ᵥ v ∈ W.map V₁.subtype := by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨σ₁ g w, hW g w hw, rfl⟩
    rcases hV₁min _ hP (Submodule.map_subtype_le _ _) with h | h
    · left
      apply Submodule.map_injective_of_injective V₁.injective_subtype
      rw [h, Submodule.map_bot]
    · right
      apply Submodule.map_injective_of_injective V₁.injective_subtype
      rw [h, Submodule.map_subtype_top]
  obtain ⟨n, T₁, hT₁⟩ := su2_classify σ₁ hσ₁c hσ₁i
  -- the embedding `S : ℂ^{n+1} → V₁ ⊆ ℂ^d` intertwines `spinMat n` with `ρp`
  let S : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := V₁.subtype ∘ₗ T₁.symm.toLinearMap
  have hT₁s : ∀ (g : SU2) x, T₁.symm (spinMat n g *ᵥ x) = σ₁ g (T₁.symm x) := fun g x => by
    apply T₁.injective
    rw [LinearEquiv.apply_symm_apply, hT₁, LinearEquiv.apply_symm_apply]
  have hS0 : S ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : Fin (n + 1) → ℂ)
    apply hx
    apply T₁.symm.injective
    rw [map_zero]
    apply Subtype.ext
    exact LinearMap.congr_fun h0 x
  -- Step 2: the intertwiners `M = Hom_{SU(2)×1}(spinMat n, ρp)`, with the action of `1 × SU(2)`
  obtain ⟨M, hM⟩ : ∃ M : Submodule ℂ ((Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)),
      ∀ A, A ∈ M ↔ ∀ (g : SU2) x, A (spinMat n g *ᵥ x) = ρp g *ᵥ A x :=
    ⟨{ carrier := {A | ∀ (g : SU2) x, A (spinMat n g *ᵥ x) = ρp g *ᵥ A x}
       add_mem' := fun {A B} hA hB g x => by
         simp only [LinearMap.add_apply, hA g x, hB g x, mulVec_add]
       zero_mem' := fun g x => by simp
       smul_mem' := fun c A hA g x => by
         simp only [LinearMap.smul_apply, hA g x, mulVec_smul] }, fun A => Iff.rfl⟩
  have hSM : S ∈ M := (hM S).mpr fun g x => by
    change ((T₁.symm (spinMat n g *ᵥ x) : V₁) : Fin d → ℂ) = ρp g *ᵥ ((T₁.symm x : V₁) : _)
    rw [hT₁s, hσ₁v]
  have hcomm : ∀ g h : SU2, ρm h * ρp g = ρp g * ρm h := fun g h => by
    rw [← hsplit, ← hsplit']
  let L : SU2 → ((Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)) →ₗ[ℂ]
      ((Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :=
    fun h => LinearMap.llcomp ℂ (Fin (n + 1) → ℂ) (Fin d → ℂ) (Fin d → ℂ) (Matrix.toLin' (ρm h))
  have hLM : ∀ h, ∀ A ∈ M, L h A ∈ M := fun h A hA => (hM _).mpr fun g x => by
    change ρm h *ᵥ A (spinMat n g *ᵥ x) = ρp g *ᵥ (ρm h *ᵥ A x)
    rw [(hM A).mp hA g x, mulVec_mulVec, mulVec_mulVec, hcomm]
  have hM0 : M ≠ ⊥ := fun h => hS0 (by
    have := hSM; rw [h, Submodule.mem_bot] at this; exact this)
  obtain ⟨M₁, ⟨hM₁M, hM₁⟩, hM₁0, hM₁min⟩ := exists_minimal_submodule
    (fun W => W ≤ M ∧ ∀ h : SU2, ∀ A ∈ W, L h A ∈ W) (W₀ := M) ⟨le_rfl, hLM⟩ hM0
  have : Nontrivial M₁ := Submodule.nontrivial_iff_ne_bot.mpr hM₁0
  let σ₂ : SU2 →* (M₁ →ₗ[ℂ] M₁) :=
    { toFun := fun h => (L h).restrict (fun A hA => hM₁ h A hA)
      map_one' := LinearMap.ext fun A => Subtype.ext (LinearMap.ext fun x => by
        change ρm 1 *ᵥ (A : _ →ₗ[ℂ] _) x = (A : _ →ₗ[ℂ] _) x
        rw [map_one, one_mulVec])
      map_mul' := fun h h' => LinearMap.ext fun A => Subtype.ext (LinearMap.ext fun x => by
        change ρm (h * h') *ᵥ (A : _ →ₗ[ℂ] _) x = ρm h *ᵥ (ρm h' *ᵥ (A : _ →ₗ[ℂ] _) x)
        rw [map_mul, mulVec_mulVec]) }
  let ι₁ : M₁ →ₗ[ℂ] ((Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)) := M₁.subtype
  have hι₁ : Function.Injective ι₁ := M₁.injective_subtype
  have hσ₂v : ∀ h (A : M₁), ι₁ (σ₂ h A) = (Matrix.toLin' (ρm h)).comp (ι₁ A) := fun _ _ => rfl
  have hσ₂c : ∀ (A : M₁) (f : Module.Dual ℂ M₁), Continuous fun h => f (σ₂ h A) := by
    intro A f
    obtain ⟨F, hF⟩ := LinearMap.exists_extend f
    have : (fun h => f (σ₂ h A)) = fun h => F ((Matrix.toLin' (ρm h)).comp (ι₁ A)) :=
      funext fun h => by
        rw [← hσ₂v, ← hF, LinearMap.comp_apply]
    rw [this]
    exact continuous_comp_toLin' F (ι₁ A) hcm
  have hσ₂i : ∀ W : Submodule ℂ M₁, (∀ h, ∀ A ∈ W, σ₂ h A ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hP : W.map M₁.subtype ≤ M ∧ ∀ h : SU2, ∀ A ∈ W.map M₁.subtype, L h A ∈ W.map M₁.subtype :=
      ⟨(Submodule.map_subtype_le _ _).trans hM₁M, by
        rintro h _ ⟨B, hB, rfl⟩
        exact ⟨σ₂ h B, hW h B hB, rfl⟩⟩
    rcases hM₁min _ hP (Submodule.map_subtype_le _ _) with h | h
    · left
      apply Submodule.map_injective_of_injective M₁.injective_subtype
      rw [h, Submodule.map_bot]
    · right
      apply Submodule.map_injective_of_injective M₁.injective_subtype
      rw [h, Submodule.map_subtype_top]
  obtain ⟨m, T₂, hT₂⟩ := su2_classify (V := M₁) σ₂ hσ₂c hσ₂i
  -- `U : ℂ^{m+1} → M₁ ⊆ M` intertwines `spinMat m` with the action of `1 × SU(2)`
  let U : (Fin (m + 1) → ℂ) →ₗ[ℂ] ((Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :=
    ι₁ ∘ₗ T₂.symm.toLinearMap
  have hUM : ∀ y (g : SU2) x, U y (spinMat n g *ᵥ x) = ρp g *ᵥ U y x := fun y =>
    (hM _).mp (hM₁M (T₂.symm y).2)
  have hUh : ∀ (h : SU2) y, U (spinMat m h *ᵥ y) = (Matrix.toLin' (ρm h)).comp (U y) :=
      fun h y => by
    have : T₂.symm (spinMat m h *ᵥ y) = σ₂ h (T₂.symm y) := by
      apply T₂.injective
      rw [LinearEquiv.apply_symm_apply, hT₂, LinearEquiv.apply_symm_apply]
    change ι₁ (T₂.symm _) = _
    rw [this, hσ₂v]; rfl
  have hU0 : ∃ y x, U y x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy⟩ := exists_ne (0 : Fin (m + 1) → ℂ)
    apply hy
    apply T₂.symm.injective
    rw [map_zero]
    apply hι₁
    rw [map_zero]
    exact LinearMap.ext fun x => hcon y x
  -- Step 3: `Φ(x ⊗ y) = U(y)(x)`
  let ΦT : TensorSpace n m →ₗ[ℂ] (Fin d → ℂ) := TensorProduct.lift U.flip
  have hΦT : ∀ (g : Spin4) (t : TensorSpace n m), ΦT (spin4Tensor n m g t) = ρ g *ᵥ ΦT t := by
    intro g t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [spin4Tensor_apply_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul,
        LinearMap.flip_apply, LinearMap.flip_apply, hUh, LinearMap.comp_apply, hUM,
        Matrix.toLin'_apply, mulVec_mulVec, ← hsplit']
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, ← mulVec_add, ← map_add]
  let Φ : (Idx n m → ℂ) →ₗ[ℂ] (Fin d → ℂ) := ΦT ∘ₗ (tensorEquiv n m).symm.toLinearMap
  have hΦ : ∀ (g : Spin4) (z : Idx n m → ℂ), Φ (spin4Mat n m g *ᵥ z) = ρ g *ᵥ Φ z := by
    intro g z
    obtain ⟨t, rfl⟩ := (tensorEquiv n m).surjective z
    change ΦT ((tensorEquiv n m).symm _) = ρ g *ᵥ ΦT ((tensorEquiv n m).symm _)
    rw [← tensorEquiv_spin4Tensor, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      hΦT]
  have hΦ0 : Φ ≠ 0 := by
    obtain ⟨y, x, hxy⟩ := hU0
    intro h0
    apply hxy
    have := LinearMap.congr_fun h0 (tensorEquiv n m (x ⊗ₜ y))
    change ΦT ((tensorEquiv n m).symm _) = 0 at this
    rwa [LinearEquiv.symm_apply_apply, TensorProduct.lift.tmul, LinearMap.flip_apply] at this
  -- Step 4: `Φ` is bijective
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range Φ) (fun g v hv => by
        obtain ⟨z, rfl⟩ := hv
        exact ⟨_, hΦ g z⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hΦ0
    · exact h
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot]
    rcases isInvariant_eq_bot_or_eq_top (n := n) (m := m) (W := LinearMap.ker Φ)
        (fun g z hz => by
          rw [LinearMap.mem_ker] at hz ⊢
          rw [hΦ, hz, mulVec_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hΦ0
  let E := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  refine ⟨n, m, E.symm, fun g v => ?_⟩
  apply E.injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = Φ (spin4Mat n m g *ᵥ E.symm v)
  rw [hΦ]
  change _ = ρ g *ᵥ E (E.symm v)
  rw [LinearEquiv.apply_symm_apply]

/-- **Completeness, abstract form.** Every irreducible representation of Spin(4) on a
finite-dimensional complex vector space whose matrix coefficients `g ↦ f (ρ g v)` are continuous
is equivalent to the spin-`(n/2, m/2)` representation for some `n`, `m`. -/
theorem spin4_complete {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Spin4 V) [ρ.IsIrreducible]
    (hρ : ∀ (v : V) (f : Module.Dual ℂ V), Continuous fun g => f (ρ g v)) :
    ∃ n m : ℕ, Nonempty (ρ.Equiv (spin4Representation n m)) := by
  have := nontrivial_of_isIrreducible ρ
  set d := Module.finrank ℂ V
  have : NeZero d := ⟨Module.finrank_pos.ne'⟩
  let b : Module.Basis (Fin d) ℂ V := Module.finBasis ℂ V
  let ρ' : Spin4 →* Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun g => LinearMap.toMatrix b b (ρ g)
      map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b] }
  have hrel : ∀ g v, b.equivFun (ρ g v) = ρ' g *ᵥ b.equivFun v := fun g v => by
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr b b (ρ g) v).symm
  have hcont : Continuous ρ' := continuous_matrix fun i j => by
    simp only [ρ', MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix_apply]
    exact hρ (b j) (b.coord i)
  have hirr : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ g : Spin4, ∀ v ∈ W, ρ' g *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hmap : (W.comap b.equivFun.toLinearMap).map b.equivFun.toLinearMap = W :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective W
    let S : Subrepresentation ρ :=
      { toSubmodule := W.comap b.equivFun.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
          rw [hrel]; exact hW g _ hv }
    rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
    · left
      rw [← hmap, show W.comap b.equivFun.toLinearMap = ⊥ from
        congrArg Subrepresentation.toSubmodule h, Submodule.map_bot]
    · right
      rw [← hmap, show W.comap b.equivFun.toLinearMap = ⊤ from
        congrArg Subrepresentation.toSubmodule h, Submodule.map_top, LinearMap.range_eq_top]
      exact b.equivFun.surjective
  obtain ⟨n, m, T, hT⟩ := spin4Rep_complete ρ' hcont hirr
  refine ⟨n, m, ⟨Representation.Equiv.mk (b.equivFun.trans T) fun g => LinearMap.ext fun v => ?_⟩⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    spin4Representation_apply]
  rw [hrel, hT]

end Lightlike.Spin4
