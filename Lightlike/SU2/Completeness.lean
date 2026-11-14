module

public import Lightlike.SU2.Brackets

/-!
# Group-level completeness of the spin representations

**Theorem (`spinRep_complete`).** Every continuous irreducible representation
`ρ : SU2 →* M_d(ℂ)` is equivalent to some `spinRep n`: there is a linear isomorphism
`T : ℂ^d ≃ ℂ^{n+1}` with `T (ρ g v) = spinRep n g (T v)` for all `g, v`.

Proof (stages D and E; stages A to C are in `OneParameter`, `LieProduct`, `Su2Exp`,
`Differential` and `Brackets`):
1. Complexify the differential. `H = -i dρZ`, `E = (-dρY - i dρX)/2`, `F = (dρY - i dρX)/2` form an
   `sl₂`-triple acting on `ℂ^d` (`sl2_rel`, `isSl2Triple_ops`).
2. A subspace invariant under `E, F, H` is invariant under every `dρ X`, `X ∈ su(2)`. Hence it is
   invariant under `exp(dρ X) = ρ(exp X)`, so under all of `ρ`, since `exp` is onto. So the
   `sl₂`-module is irreducible.
3. Physlib's classification (via `exists_dSpin_equiv`) gives `T` intertwining `E, F, H` with
   `dSpin n E, F, H`.
4. The differential of `spinRep n` is `dSpin n` (`dσ_eq`, from `hasDerivAt_spinMat`).
   So `T` intertwines `dρ X` with it, then `exp(dρ X)` with `exp(dSpin X)`, so `ρ(g)` with
   `spinRep n g` for every `g`.

The degenerate case `H = 0` is handled separately: then `ρ` is trivial, `d = 1`, and the
representation is spin 0.

**References.** B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed. (Springer, 2015), ch. 4 (the classification of the irreducible representations of su(2) and sl(2,ℂ)); T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups* (Springer, 1985), ch. II.
-/

@[expose] public section

open Matrix Filter Topology PhyslibAlpha.Sl2

namespace Lightlike.SU2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ## Algebra of `su(2)` -/

/-- Every `X ∈ su(2)` is a real combination of `Z, Y, X`. -/
lemma IsSu2.decomp {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) :
    X = (X 0 0).im • suZ + (-(X 0 1).re) • suY + (X 0 1).im • suX := by
  have h11 := hX.trace_eq
  have h10 := hX.entry10
  have hre := hX.re00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suZ, suY, suX, Complex.ext_iff, h11, h10, hre]

lemma suZ_eq : suZ = Complex.I • matH := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [suZ, matH]
lemma suY_eq : suY = matF - matE := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [suY, matE, matF]
lemma suX_eq : suX = Complex.I • (matE + matF) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [suX, matE, matF]

/-! ## The complexified differential -/

variable {d : ℕ} [NeZero d] {ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ}

/-- `H = -i dρZ`. -/
noncomputable def opH (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (-Complex.I) • dρ ρ suZ
/-- `E = (-dρY - i dρX)/2`. -/
noncomputable def opE (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (-dρ ρ suY - Complex.I • dρ ρ suX)
/-- `F = (dρY - i dρX)/2`. -/
noncomputable def opF (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (dρ ρ suY - Complex.I • dρ ρ suX)

omit [NeZero d] in
lemma dρZ_eq (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) : dρ ρ suZ = Complex.I • opH ρ := by
  rw [opH, smul_smul, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg],
    one_smul]
omit [NeZero d] in
lemma dρY_eq (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) : dρ ρ suY = opF ρ - opE ρ := by
  rw [opF, opE, ← smul_sub]; module
omit [NeZero d] in
lemma dρX_eq (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) : dρ ρ suX = Complex.I • (opE ρ + opF ρ) := by
  rw [opE, opF, ← smul_add, smul_smul]
  rw [show -dρ ρ suY - Complex.I • dρ ρ suX + (dρ ρ suY - Complex.I • dρ ρ suX) =
    (-2 * Complex.I) • dρ ρ suX by module, smul_smul]
  rw [show Complex.I * (1 / 2) * (-2 * Complex.I) = 1 by
    ring_nf; rw [Complex.I_sq]; ring, one_smul]

/-- **The sl₂ relations** `[H,E] = 2E`, `[H,F] = -2F`, `[E,F] = H`. -/
theorem sl2_rel (hρ : Continuous ρ) :
    opH ρ * opE ρ - opE ρ * opH ρ = (2 : ℂ) • opE ρ ∧
    opH ρ * opF ρ - opF ρ * opH ρ = (-2 : ℂ) • opF ρ ∧
    opE ρ * opF ρ - opF ρ * opE ρ = opH ρ := by
  obtain ⟨b1, b2, b3⟩ := brackets hρ
  unfold opH opE opF
  generalize dρ ρ suZ = z at b1 b2 b3 ⊢
  generalize dρ ρ suY = y at b1 b2 b3 ⊢
  generalize dρ ρ suX = x at b1 b2 b3 ⊢
  have r : ∀ (r : ℝ) (m : Matrix (Fin d) (Fin d) ℂ), r • m = (r : ℂ) • m := fun r m => rfl
  rw [r] at b1 b2 b3
  push_cast at b1 b2 b3
  have h1 : y * z = z * y + (2 : ℂ) • x := by rw [← sub_eq_iff_eq_add', ← neg_sub, b1]; module
  have h2 : x * z = z * x - (2 : ℂ) • y := by
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', b2]
  have h3 : x * y = y * x + (2 : ℂ) • z := by rw [← sub_eq_iff_eq_add', ← neg_sub, b3]; module
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, neg_mul, mul_neg,
      smul_sub, smul_neg, smul_smul, h1, h2, smul_add]
    match_scalars <;> first | ring1 | (ring_nf; simp only [Complex.I_sq])
  · simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, neg_mul, mul_neg,
      smul_sub, smul_smul, h1, h2, smul_add]
    match_scalars <;> first | ring1 | (ring_nf; simp only [Complex.I_sq])
  · simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, neg_mul,
      mul_neg, smul_sub, smul_neg, smul_smul, h3, smul_add, neg_sub]
    match_scalars <;> ring1

/-! ## The sl₂-triple of endomorphisms -/

section Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A matrix as an endomorphism of `ℂ^d`. -/
noncomputable abbrev endo (A : Matrix (Fin d) (Fin d) ℂ) : Module.End ℂ (Fin d → ℂ) := Matrix.toLin' A

omit [NeZero d] in
lemma endo_mul (A B : Matrix (Fin d) (Fin d) ℂ) : endo (A * B) = endo A * endo B := by
  rw [endo, Matrix.toLin'_mul]; rfl

omit [NeZero d] in
lemma endo_lie (A B : Matrix (Fin d) (Fin d) ℂ) : ⁅endo A, endo B⁆ = endo (A * B - B * A) := by
  rw [LieRing.of_associative_ring_bracket, ← endo_mul, ← endo_mul]
  exact (map_sub Matrix.toLin' _ _).symm

/-- **`(H, E, F)` is an sl₂-triple** of endomorphisms of `ℂ^d` (when `H ≠ 0`). -/
theorem isSl2Triple_ops (hρ : Continuous ρ) (hH : opH ρ ≠ 0) :
    IsSl2Triple (endo (opH ρ)) (endo (opE ρ)) (endo (opF ρ)) where
  h_ne_zero := fun h => hH (Matrix.toLin'.injective (by rw [map_zero]; exact h))
  lie_e_f := by rw [endo_lie, (sl2_rel hρ).2.2]
  lie_h_e_nsmul := by
    rw [endo_lie, (sl2_rel hρ).1, endo, map_smul, ← endo, ofNat_smul_eq_nsmul (R := ℂ)]
  lie_h_f_nsmul := by
    rw [endo_lie, (sl2_rel hρ).2.1, endo, map_smul, ← endo]
    module

end Lie

/-! ## Invariant subspaces -/

/-- A subspace invariant under `A` is invariant under `exp A`. -/
lemma exp_mulVec_mem {m : ℕ} [NeZero m] (W : Submodule ℂ (Fin m → ℂ))
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : ∀ v ∈ W, A *ᵥ v ∈ W) :
    ∀ v ∈ W, NormedSpace.exp A *ᵥ v ∈ W := by
  intro v hv
  have hpow : ∀ k : ℕ, A ^ k *ᵥ v ∈ W := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih => rw [pow_succ', ← mulVec_mulVec]; exact hA _ ih
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  let g : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] (Fin m → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => add_mulVec M N v
      map_smul' := fun r M => by simp [smul_mulVec] }
  have hg : Continuous g := LinearMap.continuous_of_finiteDimensional g
  have hs' := hs.map g hg
  refine (Submodule.closed_of_finiteDimensional W).mem_of_tendsto hs'.tendsto_sum_nat
    (Eventually.of_forall fun n => W.sum_mem fun k _ => ?_)
  show g (((k.factorial : ℝ)⁻¹) • A ^ k) ∈ W
  rw [map_smul]
  exact W.smul_of_tower_mem _ (hpow k)

/-- Every `g ∈ SU(2)` is `Γ X 1` for some `X ∈ su(2)`. -/
lemma exists_Γ_one (g : SU2) : ∃ X, ∃ hX : IsSu2 X, Γ X hX 1 = g := by
  obtain ⟨X, hX, hexp⟩ := exists_exp_eq g
  exact ⟨X, hX, Subtype.ext (by rw [Γ_coe, one_smul, hexp])⟩

/-- **Invariance transfer**: a subspace invariant under `E, F, H` is invariant under `ρ`. -/
theorem invariant_of_ops (hρ : Continuous ρ) (W : Submodule ℂ (Fin d → ℂ))
    (hE : ∀ v ∈ W, opE ρ *ᵥ v ∈ W) (hF : ∀ v ∈ W, opF ρ *ᵥ v ∈ W)
    (hH : ∀ v ∈ W, opH ρ *ᵥ v ∈ W) (g : SU2) : ∀ v ∈ W, ρ g *ᵥ v ∈ W := by
  have hZ : ∀ v ∈ W, dρ ρ suZ *ᵥ v ∈ W := fun v hv => by
    rw [dρZ_eq, smul_mulVec]; exact W.smul_mem _ (hH v hv)
  have hY : ∀ v ∈ W, dρ ρ suY *ᵥ v ∈ W := fun v hv => by
    rw [dρY_eq, sub_mulVec]; exact W.sub_mem (hF v hv) (hE v hv)
  have hX' : ∀ v ∈ W, dρ ρ suX *ᵥ v ∈ W := fun v hv => by
    rw [dρX_eq, smul_mulVec, add_mulVec]
    exact W.smul_mem _ (W.add_mem (hE v hv) (hF v hv))
  obtain ⟨X, hX, rfl⟩ := exists_Γ_one g
  have hdX : ∀ v ∈ W, dρ ρ X *ᵥ v ∈ W := by
    intro v hv
    rw [hX.decomp, dρ_add hρ ((isSu2_Z.smul _).add (isSu2_Y.smul _)) (isSu2_X.smul _),
      dρ_add hρ (isSu2_Z.smul _) (isSu2_Y.smul _), dρ_smul hρ isSu2_Z, dρ_smul hρ isSu2_Y,
      dρ_smul hρ isSu2_X, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec,
      smul_mulVec]
    exact W.add_mem (W.add_mem (W.smul_of_tower_mem _ (hZ v hv))
      (W.smul_of_tower_mem _ (hY v hv))) (W.smul_of_tower_mem _ (hX' v hv))
  intro v hv
  rw [rho_Γ hρ hX, one_smul]
  exact exp_mulVec_mem W _ hdX v hv

/-! ## The spin representations and their differentials -/

/-- Entrywise derivative of a matrix-valued curve. -/
lemma hasDerivAt_entry {m : ℕ} {f : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {f' : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : HasDerivAt f f' t) (a b : Fin m) :
    HasDerivAt (fun θ => f θ a b) (f' a b) t := by
  let L : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t h

lemma hasDerivAt_exp_entry {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    HasDerivAt (fun θ : ℝ => (NormedSpace.exp (θ • A)) a b) (A a b) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) A 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact hasDerivAt_entry h a b

/-- The spin representation as a monoid homomorphism into matrices. -/
noncomputable def σ (n : ℕ) : SU2 →* Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (unitaryGroup (Fin (n + 1)) ℂ).subtype.comp (spinRep n)

lemma σ_apply (n : ℕ) (g : SU2) : σ n g = spinMat n g := rfl

lemma continuous_σ (n : ℕ) : Continuous (σ n) := continuous_spinRep

/-- **The differential of `spinRep n` is `dSpin n`** (from `hasDerivAt_spinMat`). -/
theorem dσ_eq (n : ℕ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) :
    dρ (σ n) X = dSpin n X := by
  ext a b
  have h1 := hasDerivAt_exp_entry (dρ (σ n) X) a b
  have h2 := hasDerivAt_spinMat (n := n) (γ := fun θ => (Γ X hX θ : Matrix (Fin 2) (Fin 2) ℂ))
    (by rw [Γ_coe, zero_smul, NormedSpace.exp_zero])
    (fun i j => by simpa only [Γ_coe] using hasDerivAt_exp_entry X i j) a b
  have heq : (fun θ : ℝ => spinMat n (Γ X hX θ : Matrix (Fin 2) (Fin 2) ℂ) a b) =
      fun θ => (NormedSpace.exp (θ • dρ (σ n) X)) a b := by
    funext θ
    rw [← σ_apply, rho_Γ (continuous_σ n) hX]
  rw [heq] at h2
  exact h1.unique h2

/-- Intertwining passes to exponentials: `T A = B T` implies `T exp A = exp B T`. -/
lemma intertwine_exp {m m' : ℕ} (T : (Fin m → ℂ) →ₗ[ℂ] (Fin m' → ℂ))
    {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin m') (Fin m') ℂ}
    (hT : ∀ v, T (A *ᵥ v) = B *ᵥ T v) (v : Fin m → ℂ) :
    T (NormedSpace.exp A *ᵥ v) = NormedSpace.exp B *ᵥ T v := by
  have hpow : ∀ k : ℕ, T (A ^ k *ᵥ v) = B ^ k *ᵥ T v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, hT, ih, pow_succ', ← mulVec_mulVec]
  let gA : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] (Fin m' → ℂ) :=
    { toFun := fun M => T (M *ᵥ v)
      map_add' := fun M N => by rw [add_mulVec, map_add]
      map_smul' := fun r M => by rw [smul_mulVec, T.map_smul_of_tower]; rfl }
  let gB : Matrix (Fin m') (Fin m') ℂ →ₗ[ℝ] (Fin m' → ℂ) :=
    { toFun := fun M => M *ᵥ T v
      map_add' := fun M N => add_mulVec M N _
      map_smul' := fun r M => by rw [smul_mulVec]; rfl }
  have hA := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map gA
    (LinearMap.continuous_of_finiteDimensional gA)
  have hB := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) B).map gB
    (LinearMap.continuous_of_finiteDimensional gB)
  refine hA.unique ?_
  convert hB using 1
  funext k
  show T ((((k.factorial : ℝ)⁻¹) • A ^ k) *ᵥ v) = (((k.factorial : ℝ)⁻¹) • B ^ k) *ᵥ T v
  rw [smul_mulVec, T.map_smul_of_tower, hpow, smul_mulVec]
  rfl

lemma dSpin_rsmul (n : ℕ) (r : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    dSpin n (r • X) = r • dSpin n X := by
  rw [show r • X = (r : ℂ) • X from rfl, dSpin_smul]; rfl

lemma spinMat_zero' (g : Matrix (Fin 2) (Fin 2) ℂ) : spinMat 0 g = 1 := by
  have hk : kron 0 g = 1 := by
    ext s t
    rw [Subsingleton.elim s t, one_apply_eq, kron_apply, Finset.univ_eq_empty, Finset.prod_empty]
  rw [spinMat, hk, Matrix.mul_one, emb_conjTranspose_mul_emb]

/-! ## The completeness theorem -/

section Main

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Group-level completeness.** Every continuous irreducible representation of SU(2)
on `ℂ^d` is equivalent to a spin representation `spinRep n`. -/
theorem spinRep_complete (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ)
    (hirr : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ g : SU2, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ n : ℕ, ∃ T : (Fin d → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ), ∀ (g : SU2) (v : Fin d → ℂ),
      T (ρ g *ᵥ v) = (spinRep n g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ T v := by
  by_cases hH : opH ρ = 0
  · -- degenerate case: `dρ = 0`, so `ρ` is trivial and `d = 1`
    obtain ⟨b1, b2, -⟩ := brackets hρ
    have hz : dρ ρ suZ = 0 := by rw [dρZ_eq, hH, smul_zero]
    have hx : dρ ρ suX = 0 := by
      rw [hz, zero_mul, mul_zero, sub_zero] at b1
      have := b1.symm
      rwa [neg_smul, neg_eq_zero, smul_eq_zero, or_iff_right (by norm_num)] at this
    have hy : dρ ρ suY = 0 := by
      rw [hz, zero_mul, mul_zero, sub_zero] at b2
      have := b2.symm
      rwa [smul_eq_zero, or_iff_right (by norm_num)] at this
    have htriv : ∀ g, ρ g = 1 := by
      intro g
      obtain ⟨X, hX, rfl⟩ := exists_Γ_one g
      rw [rho_Γ hρ hX, one_smul, hX.decomp,
        dρ_add hρ ((isSu2_Z.smul _).add (isSu2_Y.smul _)) (isSu2_X.smul _),
        dρ_add hρ (isSu2_Z.smul _) (isSu2_Y.smul _), dρ_smul hρ isSu2_Z, dρ_smul hρ isSu2_Y,
        dρ_smul hρ isSu2_X, hz, hy, hx]
      simp
    have hd1 : d = 1 := by
      set x : Fin d → ℂ := Pi.single 0 1
      have hx0 : x ≠ 0 := fun h => by simpa [x] using congrFun h 0
      rcases hirr (Submodule.span ℂ {x}) (fun g v hv => by rw [htriv g, one_mulVec]; exact hv)
        with h | h
      · exact absurd (Submodule.span_singleton_eq_bot.mp h) hx0
      · have h1 := finrank_span_singleton (K := ℂ) hx0
        rw [h, finrank_top, Module.finrank_fin_fun] at h1
        exact h1
    subst hd1
    refine ⟨0, LinearEquiv.refl ℂ _, fun g v => ?_⟩
    simp [htriv g, spinMat_zero']
  · -- regular case: an irreducible sl₂-module, classified by Physlib
    have t := isSl2Triple_ops hρ hH
    have : LieModule.IsIrreducible ℂ ↥(t.toLieSubalgebra (R := ℂ)) (Fin d → ℂ) := by
      refine LieModule.IsIrreducible.mk fun N hN => ?_
      have hmem : ∀ (y : Module.End ℂ (Fin d → ℂ)) (hy : y ∈ t.toLieSubalgebra (R := ℂ)),
          ∀ v ∈ N, y v ∈ N := by
        intro y hy v hv
        have := N.lie_mem (x := (⟨y, hy⟩ : t.toLieSubalgebra (R := ℂ))) hv
        rwa [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply] at this
      have hinv := invariant_of_ops hρ N.toSubmodule
        (fun v hv => by simpa [endo, Matrix.toLin'_apply] using hmem _ (e_mem_subalgebra t) v hv)
        (fun v hv => by simpa [endo, Matrix.toLin'_apply] using hmem _ (f_mem_subalgebra t) v hv)
        (fun v hv => by simpa [endo, Matrix.toLin'_apply] using hmem _ (h_mem_subalgebra t) v hv)
      rcases hirr N.toSubmodule hinv with h | h
      · rw [LieSubmodule.toSubmodule_eq_bot] at h
        exact absurd h hN
      · rwa [LieSubmodule.toSubmodule_eq_top] at h
    obtain ⟨n, T, hT⟩ := exists_dSpin_equiv (M := Fin d → ℂ) t
    refine ⟨n, T, fun g v => ?_⟩
    have hTE : ∀ v, T (opE ρ *ᵥ v) = dSpin n matE *ᵥ T v := fun v => by
      have := (hT v).1; rwa [Module.End.lie_apply, endo, Matrix.toLin'_apply] at this
    have hTF : ∀ v, T (opF ρ *ᵥ v) = dSpin n matF *ᵥ T v := fun v => by
      have := (hT v).2.1; rwa [Module.End.lie_apply, endo, Matrix.toLin'_apply] at this
    have hTH : ∀ v, T (opH ρ *ᵥ v) = dSpin n matH *ᵥ T v := fun v => by
      have := (hT v).2.2; rwa [Module.End.lie_apply, endo, Matrix.toLin'_apply] at this
    have hTZ : ∀ v, T (dρ ρ suZ *ᵥ v) = dSpin n suZ *ᵥ T v := fun v => by
      rw [dρZ_eq, smul_mulVec, map_smul, hTH, suZ_eq, dSpin_smul, smul_mulVec]
    have hTY : ∀ v, T (dρ ρ suY *ᵥ v) = dSpin n suY *ᵥ T v := fun v => by
      rw [dρY_eq, sub_mulVec, map_sub, hTF, hTE, suY_eq, dSpin_sub, sub_mulVec]
    have hTX : ∀ v, T (dρ ρ suX *ᵥ v) = dSpin n suX *ᵥ T v := fun v => by
      rw [dρX_eq, smul_mulVec, add_mulVec, map_smul, map_add, hTE, hTF, suX_eq, dSpin_smul,
        dSpin_add, smul_mulVec, add_mulVec]
    obtain ⟨X, hX, rfl⟩ := exists_Γ_one g
    have hTd : ∀ v, T (dρ ρ X *ᵥ v) = dSpin n X *ᵥ T v := by
      intro v
      have hdec := hX.decomp
      rw [hdec, dρ_add hρ ((isSu2_Z.smul _).add (isSu2_Y.smul _)) (isSu2_X.smul _),
        dρ_add hρ (isSu2_Z.smul _) (isSu2_Y.smul _), dρ_smul hρ isSu2_Z, dρ_smul hρ isSu2_Y,
        dρ_smul hρ isSu2_X, dSpin_add, dSpin_add, dSpin_rsmul, dSpin_rsmul, dSpin_rsmul]
      have hr : ∀ (r : ℝ) (w : Fin d → ℂ), T (r • w) = r • T w :=
        fun r w => T.toLinearMap.map_smul_of_tower r w
      simp only [add_mulVec, smul_mulVec, map_add]
      rw [hr, hr, hr, hTZ, hTY, hTX]
    have hσ : (spinRep n (Γ X hX 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
        NormedSpace.exp (dSpin n X) := by
      rw [← dσ_eq n hX, show (spinRep n (Γ X hX 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
        σ n (Γ X hX 1) from rfl, rho_Γ (continuous_σ n) hX, one_smul]
    rw [rho_Γ hρ hX, one_smul, hσ]
    exact intertwine_exp T.toLinearMap hTd v

end Main

end Lightlike.SU2
