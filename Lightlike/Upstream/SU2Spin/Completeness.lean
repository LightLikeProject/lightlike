module

public import Lightlike.Upstream.SU2Spin.Brackets
public import Lightlike.Upstream.SU2Spin.Sl2Standard
public import Lightlike.Upstream.SU2Spin.SpinRep

/-!
# Completeness of the spin representations: the Lie-algebra part

For a continuous representation `ρ` of `SU(2)` on `ℂᵈ`, the complexified differential gives matrices
`opH ρ`, `opE ρ`, `opF ρ` with the `sl₂` relations (`sl2_rel`), hence (when `opH ρ ≠ 0`) an
`sl₂`-triple in the sense of Mathlib (`isSl2Triple_ops`). A subspace stable under `opH, opE, opF`
is stable under `ρ` (`invariant_of_ops`).

Two `sl₂`-triples of matrices with primitive vectors of the same weight `n` whose `F`-orbits span
are intertwined by a linear equivalence (`exists_intertwiner`).
-/

@[expose] public section

open Matrix Filter Topology Module

namespace SU2Spin

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ## Algebra of `su(2)` -/

/-- Every `X ∈ su(2)` is a real combination of `suZ, suY, suX`. -/
lemma IsSu2.decomp {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) :
    X = (X 0 0).im • suZ + (-(X 0 1).re) • suY + (X 0 1).im • suX := by
  have h11 := hX.trace_eq
  have h10 := hX.entry10
  have hre := hX.re00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suZ, suY, suX, Complex.ext_iff, h11, h10, hre]

/-! ## The complexified differential -/

variable {d : ℕ} [NeZero d] {ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ}

/-- `H = -i dρ(Z)`. -/
noncomputable def opH (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (-Complex.I) • dρ ρ suZ

/-- `E = (-dρ(Y) - i dρ(X)) / 2`. -/
noncomputable def opE (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (-dρ ρ suY - Complex.I • dρ ρ suX)

/-- `F = (dρ(Y) - i dρ(X)) / 2`. -/
noncomputable def opF (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (dρ ρ suY - Complex.I • dρ ρ suX)

omit [NeZero d] in
lemma dρZ_eq (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    dρ ρ suZ = Complex.I • opH ρ := by
  rw [opH, smul_smul, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg],
    one_smul]

omit [NeZero d] in
lemma dρY_eq (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    dρ ρ suY = opF ρ - opE ρ := by
  rw [opF, opE, ← smul_sub]; module

omit [NeZero d] in
lemma dρX_eq (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    dρ ρ suX = Complex.I • (opE ρ + opF ρ) := by
  rw [opE, opF, ← smul_add, smul_smul]
  rw [show -dρ ρ suY - Complex.I • dρ ρ suX + (dρ ρ suY - Complex.I • dρ ρ suX) =
    (-2 * Complex.I) • dρ ρ suX by module, smul_smul]
  rw [show Complex.I * (1 / 2) * (-2 * Complex.I) = 1 by
    ring_nf; rw [Complex.I_sq]; ring, one_smul]

/-- **The `sl₂` relations** `[H,E] = 2E`, `[H,F] = -2F`, `[E,F] = H` for the complexified
differential of a continuous representation. -/
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

section Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **`(H, E, F)` is an `sl₂`-triple** of matrices (when `H ≠ 0`). -/
theorem isSl2Triple_ops (hρ : Continuous ρ) (hH : opH ρ ≠ 0) :
    IsSl2Triple (opH ρ) (opE ρ) (opF ρ) where
  h_ne_zero := hH
  lie_e_f := by rw [LieRing.of_associative_ring_bracket]; exact (sl2_rel hρ).2.2
  lie_h_e_nsmul := by
    rw [LieRing.of_associative_ring_bracket, (sl2_rel hρ).1]; module
  lie_h_f_nsmul := by
    rw [LieRing.of_associative_ring_bracket, (sl2_rel hρ).2.1]; module

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

/-- **Invariance transfer**: a subspace invariant under `E, F, H` is invariant under `ρ`. -/
theorem invariant_of_ops (hρ : Continuous ρ) (W : Submodule ℂ (Fin d → ℂ))
    (hE : ∀ v ∈ W, opE ρ *ᵥ v ∈ W) (hF : ∀ v ∈ W, opF ρ *ᵥ v ∈ W)
    (hH : ∀ v ∈ W, opH ρ *ᵥ v ∈ W) (g : specialUnitaryGroup (Fin 2) ℂ) :
    ∀ v ∈ W, ρ g *ᵥ v ∈ W := by
  have hZ : ∀ v ∈ W, dρ ρ suZ *ᵥ v ∈ W := fun v hv => by
    rw [dρZ_eq, smul_mulVec]; exact W.smul_mem _ (hH v hv)
  have hY : ∀ v ∈ W, dρ ρ suY *ᵥ v ∈ W := fun v hv => by
    rw [dρY_eq, sub_mulVec]; exact W.sub_mem (hF v hv) (hE v hv)
  have hX' : ∀ v ∈ W, dρ ρ suX *ᵥ v ∈ W := fun v hv => by
    rw [dρX_eq, smul_mulVec, add_mulVec]
    exact W.smul_mem _ (W.add_mem (hE v hv) (hF v hv))
  obtain ⟨X, hX, hexp⟩ := exists_exp_eq g
  have hdX : ∀ v ∈ W, dρ ρ X *ᵥ v ∈ W := by
    intro v hv
    rw [hX.decomp, dρ_add hρ ((isSu2_Z.smul _).add (isSu2_Y.smul _)) (isSu2_X.smul _),
      dρ_add hρ (isSu2_Z.smul _) (isSu2_Y.smul _), dρ_smul hρ isSu2_Z, dρ_smul hρ isSu2_Y,
      dρ_smul hρ isSu2_X, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec,
      smul_mulVec]
    exact W.add_mem (W.add_mem (W.smul_of_tower_mem _ (hZ v hv))
      (W.smul_of_tower_mem _ (hY v hv))) (W.smul_of_tower_mem _ (hX' v hv))
  intro v hv
  have hg : g = expCurve X hX 1 := Subtype.ext (by rw [expCurve_coe, one_smul, hexp])
  rw [hg, rho_expCurve hρ hX, one_smul]
  exact exp_mulVec_mem W _ hdX v hv

/-! ## Intertwiners and the spin representation as matrices -/

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

/-- The spin representation as a monoid homomorphism into matrices. -/
noncomputable def σ (n : ℕ) : SU2 →* Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (Matrix.unitaryGroup (Fin (n + 1)) ℂ).subtype.comp (spinRep n)

lemma σ_apply (n : ℕ) (g : SU2) : σ n g = spinMat n g := rfl

lemma continuous_σ (n : ℕ) : Continuous (σ n) := continuous_spinRep

section Intertwiner

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Two matrix `sl₂`-triples with primitive vectors of the same weight `n` whose `F`-orbits span
are intertwined by a linear isomorphism (sending `Fᵏ m` to `F'ᵏ m'`). -/
lemma exists_intertwiner {d d' : ℕ} {H E F : Matrix (Fin d) (Fin d) ℂ}
    {H' E' F' : Matrix (Fin d') (Fin d') ℂ} (t : IsSl2Triple H E F) (t' : IsSl2Triple H' E' F')
    {m : Fin d → ℂ} {m' : Fin d' → ℂ} {n : ℕ}
    (P : t.HasPrimitiveVectorWith m (n : ℂ)) (P' : t'.HasPrimitiveVectorWith m' (n : ℂ))
    (hspan : Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F m k) = ⊤)
    (hspan' : Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow F' m' k) = ⊤) :
    ∃ T : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d' → ℂ),
      (∀ v, T (H *ᵥ v) = H' *ᵥ T v) ∧ (∀ v, T (E *ᵥ v) = E' *ᵥ T v) ∧
      (∀ v, T (F *ᵥ v) = F' *ᵥ T v) := by
  set b := fpowBasis t P hspan with hbdef
  set b' := fpowBasis t' P' hspan' with hb'def
  let T := b.equiv b' (Equiv.refl _)
  have hb : ∀ k, b k = fpow F m k := fpowBasis_apply t P hspan
  have hb' : ∀ k, b' k = fpow F' m' k := fpowBasis_apply t' P' hspan'
  have hT : ∀ j : ℕ, j ≤ n → T (fpow F m j) = fpow F' m' j := fun j hj => by
    have h : T (b ⟨j, by omega⟩) = b' ⟨j, by omega⟩ := Basis.equiv_apply ..
    rw [hb, hb'] at h
    exact h
  have key : ∀ (A : Matrix (Fin d) (Fin d) ℂ) (A' : Matrix (Fin d') (Fin d') ℂ),
      (∀ k : Fin (n + 1), T (A *ᵥ fpow F m k) = A' *ᵥ T (fpow F m k)) →
      ∀ v, T (A *ᵥ v) = A' *ᵥ T v := by
    intro A A' h v
    have : (T : (Fin d → ℂ) →ₗ[ℂ] (Fin d' → ℂ)) ∘ₗ A.mulVecLin =
        A'.mulVecLin ∘ₗ (T : (Fin d → ℂ) →ₗ[ℂ] (Fin d' → ℂ)) :=
      b.ext fun k => by simpa [hb] using h k
    exact LinearMap.congr_fun this v
  refine ⟨T, key _ _ fun k => ?_, key _ _ fun k => ?_, key _ _ fun k => ?_⟩
  · rw [mulVec_H_fpow t P, map_smul, hT k (by omega), mulVec_H_fpow t' P']
  · rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | hpos
    · have h := hT 0 (by omega)
      rw [fpow_zero, fpow_zero] at h
      rw [h0, fpow_zero, mulVec_E_m t P, map_zero, h, mulVec_E_m t' P']
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hj, Nat.succ_eq_add_one, mulVec_E_fpow_succ t P, map_smul, hT j (by omega),
        hT (j + 1) (by omega), mulVec_E_fpow_succ t' P']
  · rw [hT k (by omega), ← fpow_succ, ← fpow_succ]
    by_cases hk : (k : ℕ) + 1 ≤ n
    · exact hT _ hk
    · have : (k : ℕ) = n := by omega
      rw [this, fpow_succ_eq_zero t P, fpow_succ_eq_zero t' P', map_zero]

end Intertwiner

/-! ## The completeness theorem -/

/-- `dρ` on a general element of `su(2)`, in terms of the basis `suZ, suY, suX`. -/
lemma dρ_decomp (hρ : Continuous ρ) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) :
    dρ ρ X = (X 0 0).im • dρ ρ suZ + (-(X 0 1).re) • dρ ρ suY + (X 0 1).im • dρ ρ suX := by
  rw [show dρ ρ X = dρ ρ ((X 0 0).im • suZ + (-(X 0 1).re) • suY + (X 0 1).im • suX) from
      congrArg _ hX.decomp,
    dρ_add hρ ((isSu2_Z.smul _).add (isSu2_Y.smul _)) (isSu2_X.smul _),
    dρ_add hρ (isSu2_Z.smul _) (isSu2_Y.smul _), dρ_smul hρ isSu2_Z, dρ_smul hρ isSu2_Y,
    dρ_smul hρ isSu2_X]

/-- **Intertwining transfer**: a linear map intertwining `H, E, F` of two continuous
representations of `SU(2)` intertwines the representations. -/
theorem intertwine_of_ops {d' : ℕ} [NeZero d'] {ρ' : specialUnitaryGroup (Fin 2) ℂ →*
      Matrix (Fin d') (Fin d') ℂ}
    (hρ : Continuous ρ) (hρ' : Continuous ρ') (T : (Fin d → ℂ) →ₗ[ℂ] (Fin d' → ℂ))
    (hTH : ∀ v, T (opH ρ *ᵥ v) = opH ρ' *ᵥ T v) (hTE : ∀ v, T (opE ρ *ᵥ v) = opE ρ' *ᵥ T v)
    (hTF : ∀ v, T (opF ρ *ᵥ v) = opF ρ' *ᵥ T v) (g : specialUnitaryGroup (Fin 2) ℂ)
    (v : Fin d → ℂ) : T (ρ g *ᵥ v) = ρ' g *ᵥ T v := by
  have hTZ : ∀ v, T (dρ ρ suZ *ᵥ v) = dρ ρ' suZ *ᵥ T v := fun v => by
    rw [dρZ_eq, smul_mulVec, map_smul, hTH, dρZ_eq, smul_mulVec]
  have hTY : ∀ v, T (dρ ρ suY *ᵥ v) = dρ ρ' suY *ᵥ T v := fun v => by
    rw [dρY_eq, sub_mulVec, map_sub, hTF, hTE, dρY_eq, sub_mulVec]
  have hTX : ∀ v, T (dρ ρ suX *ᵥ v) = dρ ρ' suX *ᵥ T v := fun v => by
    rw [dρX_eq, smul_mulVec, add_mulVec, map_smul, map_add, hTE, hTF, dρX_eq, smul_mulVec,
      add_mulVec]
  obtain ⟨X, hX, hexp⟩ := exists_exp_eq g
  have hTd : ∀ v, T (dρ ρ X *ᵥ v) = dρ ρ' X *ᵥ T v := by
    intro v
    rw [dρ_decomp hρ hX, dρ_decomp hρ' hX]
    have hr : ∀ (r : ℝ) (w : Fin d → ℂ), T (r • w) = r • T w :=
      fun r w => T.map_smul_of_tower r w
    simp only [add_mulVec, smul_mulVec, map_add]
    rw [hr, hr, hr, hTZ, hTY, hTX]
  have hg : g = expCurve X hX 1 := Subtype.ext (by rw [expCurve_coe, one_smul, hexp])
  rw [hg, rho_expCurve hρ hX, rho_expCurve hρ' hX, one_smul, one_smul]
  exact intertwine_exp T hTd v

/-- If `opH ρ = 0` then `ρ` is trivial. -/
lemma eq_one_of_opH_eq_zero (hρ : Continuous ρ) (hH : opH ρ = 0)
    (g : specialUnitaryGroup (Fin 2) ℂ) : ρ g = 1 := by
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
  obtain ⟨X, hX, hexp⟩ := exists_exp_eq g
  have hg : g = expCurve X hX 1 := Subtype.ext (by rw [expCurve_coe, one_smul, hexp])
  rw [hg, rho_expCurve hρ hX, one_smul, dρ_decomp hρ hX, hz, hy, hx]
  simp

/-- An irreducible representation on which every element acts trivially is one-dimensional. -/
lemma eq_one_of_trivial {d : ℕ} [NeZero d] {ρ : specialUnitaryGroup (Fin 2) ℂ →*
      Matrix (Fin d) (Fin d) ℂ}
    (hirr : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ g : SU2, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (htriv : ∀ g, ρ g = 1) : d = 1 := by
  set x : Fin d → ℂ := Pi.single 0 1
  have hx0 : x ≠ 0 := fun h => by simpa [x] using congrFun h 0
  rcases hirr (Submodule.span ℂ {x}) (fun g v hv => by rw [htriv g, one_mulVec]; exact hv)
    with h | h
  · exact absurd (Submodule.span_singleton_eq_bot.mp h) hx0
  · have h1 := finrank_span_singleton (K := ℂ) hx0
    rw [h, finrank_top, Module.finrank_fin_fun] at h1
    exact h1

lemma spinMat_zero' (g : Matrix (Fin 2) (Fin 2) ℂ) : spinMat 0 g = 1 := by
  have hk : kron 0 g = 1 := by
    ext s t
    rw [Subsingleton.elim s t, one_apply_eq, kron_apply, Finset.univ_eq_empty, Finset.prod_empty]
  rw [spinMat, hk, Matrix.mul_one, emb_conjTranspose_mul_emb]

section Main

attribute [local instance 100] LieRing.ofAssociativeRing

/-- For an irreducible `ρ` with `opH ρ ≠ 0`, the weight `n` of a cyclic primitive vector. -/
lemma exists_primitive_of_irreducible (hρ : Continuous ρ) (hH : opH ρ ≠ 0)
    (hirr : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ g : SU2, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ (n : ℕ) (m : Fin d → ℂ), (isSl2Triple_ops hρ hH).HasPrimitiveVectorWith m (n : ℂ) ∧
      Submodule.span ℂ (Set.range fun k : Fin (n + 1) => fpow (opF ρ) m k) = ⊤ :=
  exists_primitive_span_eq_top (isSl2Triple_ops hρ hH) (Nat.pos_of_ne_zero (NeZero.ne d))
    fun W hH' hE hF => hirr W (invariant_of_ops hρ W hE hF hH')

/-- **Group-level completeness.** Every continuous irreducible representation of SU(2)
on `ℂ^d` is equivalent to a spin representation `spinRep n`. -/
theorem spinRep_complete (ρ : SU2 →* Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ)
    (hirr : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ g : SU2, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ n : ℕ, ∃ T : (Fin d → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ), ∀ (g : SU2) (v : Fin d → ℂ),
      T (ρ g *ᵥ v) = (spinRep n g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ T v := by
  by_cases hH : opH ρ = 0
  · have htriv := eq_one_of_opH_eq_zero hρ hH
    have hd1 := eq_one_of_trivial hirr htriv
    subst hd1
    refine ⟨0, LinearEquiv.refl ℂ _, fun g v => ?_⟩
    simp [htriv g, spinMat_zero']
  · obtain ⟨n, m, P, hspan⟩ := exists_primitive_of_irreducible hρ hH hirr
    have hd := dim_eq_succ (isSl2Triple_ops hρ hH) P hspan
    have hirrσ : ∀ W : Submodule ℂ (Fin (n + 1) → ℂ),
        (∀ g : SU2, ∀ v ∈ W, σ n g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ :=
      fun W h => isInvariant_eq_bot_or_eq_top (n := n) h
    have hn : n ≠ 0 := by
      rintro rfl
      refine hH ?_
      have hv : ∀ v : Fin d → ℂ, opH ρ *ᵥ v = 0 := by
        intro v
        have hv : v ∈ Submodule.span ℂ
            (Set.range fun k : Fin (0 + 1) => fpow (opF ρ) m k) := by
          rw [hspan]; trivial
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
        simp only [mulVec_sum, mulVec_smul]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [mulVec_H_fpow _ P]
        simp
      ext i j
      simpa [mulVec_single_one] using congrFun (hv (Pi.single j 1)) i
    have hH' : opH (σ n) ≠ 0 := by
      intro h0
      have := eq_one_of_trivial hirrσ (eq_one_of_opH_eq_zero (continuous_σ n) h0)
      omega
    obtain ⟨n', m', P', hspan'⟩ :=
      exists_primitive_span_eq_top (isSl2Triple_ops (continuous_σ n) hH')
      (Nat.pos_of_ne_zero (NeZero.ne (n + 1)))
      fun W hH'' hE hF => hirrσ W (invariant_of_ops (continuous_σ n) W hE hF hH'')
    have hd' := dim_eq_succ (isSl2Triple_ops (continuous_σ n) hH') P' hspan'
    obtain rfl : n = n' := by omega
    obtain ⟨T, hTH, hTE, hTF⟩ := exists_intertwiner (isSl2Triple_ops hρ hH)
      (isSl2Triple_ops (continuous_σ n) hH') P P' hspan hspan'
    exact ⟨n, T, fun g v =>
      intertwine_of_ops hρ (continuous_σ n) T.toLinearMap hTH hTE hTF g v⟩

end Main

end SU2Spin
