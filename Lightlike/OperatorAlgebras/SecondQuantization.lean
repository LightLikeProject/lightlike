import Lightlike.OperatorAlgebras.FockUnique
import Lightlike.OperatorAlgebras.FockIrreducible
import Lightlike.OperatorAlgebras.FockContinuity
import Lightlike.OperatorAlgebras.StoneGenerator
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Second quantization in a Fock representation

J. Dereziński, arXiv:math-ph/0511030 (read): Section 5.2, Theorem 13, p. 19 (`Γ(p₂)Γ(p₁) = Γ(p₂p₁)`, `Γ(p)` unitary iff
`p` is); Section 6.4, Theorem 24, p. 27 (for `r ∈ Sp₂(Y)` there is a unitary `U` with `U W(y) U* = W(ry)`, unique up to
a phase, and the normalization `(Ω|U Ω) > 0` fixes it; for a unitary `r` of `Z`, `p = r`, `d = c = 0` in (46), it is
`Γ(r)`). For a Fock representation `R` (the repository's characterization: a cyclic vacuum with
`⟪Ω, W f Ω⟫ = exp(-‖f‖²/4)`) and a unitary `U` of `h`:

* `FockRep.precomp R U`: the Fock representation `f ↦ W(U f)`;
* `FockRep.secondQuant R U` (`Γ(U)`): the unitary with `Γ(U) Ω = Ω` and `Γ(U) W(f) = W(U f) Γ(U)`
  (`secondQuant_vacuum`, `secondQuant_W`, `secondQuant_conj`), the unique one (`secondQuant_unique`);
* functoriality: `Γ(1) = 1`, `Γ(V ∘ U) = Γ(V) Γ(U)` (`secondQuant_refl`, `secondQuant_trans`);
* `FockRep.gamma R p` (`Γ(p)` for a contraction `p`, Theorem 13 and §5.5): `Γ(p) e(f) = e(p f)` on the exponential vectors,
  `‖Γ(p)‖ ≤ 1`, `Γ(q) Γ(p) = Γ(q p)`, `Γ(p)* = Γ(p*)`, unitary iff `p` is, bounded only if `‖p‖ ≤ 1`; `Γ(U) = secondQuant U`;
* `FockRep.secondQuantGroup R U` (`t ↦ Γ(U(t))`, a strongly continuous unitary group) and `FockRep.dGamma R U`, its
  self-adjoint generator (`Γ(e^{ith}) = e^{it dΓ(h)}`, Theorem 13 (35));
* Theorem 24 (2) for a unitary `U`: every unitary `V` with `V W(f) V* = W(U f)` is `c Γ(U)` with `|c| = 1`
  (`eq_smul_secondQuant`, from the triviality of the commutant, `commutant_scalar`), and `Γ(U)` is the only one with
  `(Ω|V Ω) > 0` (`eq_secondQuant_of_pos`).
-/

open scoped InnerProductSpace ComplexOrder Matrix

namespace Lightlike.OperatorAlgebras

variable {h : Type*} [NormedAddCommGroup h] [InnerProductSpace ℂ h]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma symp_map (U : h ≃ₗᵢ[ℂ] h) (f g : h) : symp h (U f) (U g) = symp h f g := by
  unfold symp; rw [LinearIsometryEquiv.inner_map_map]

/-- **The Fock representation `f ↦ W(U f)`** for a unitary `U` of `h`. -/
noncomputable def FockRep.precomp (R : FockRep h K) (U : h ≃ₗᵢ[ℂ] h) : FockRep h K where
  W f := R.W (U f)
  W_zero := by rw [map_zero]; exact R.W_zero
  weyl f g ψ := by rw [R.weyl, symp_map, map_add]
  continuous_line f ψ := by
    simpa only [map_smul] using R.continuous_line (U f) ψ
  Ω := R.Ω
  norm_Ω := R.norm_Ω
  cyclic := by
    have : (Set.range fun f => R.W (U f) R.Ω) = Set.range fun g => R.W g R.Ω :=
      U.surjective.range_comp (fun g => R.W g R.Ω)
    rw [this]; exact R.cyclic
  vacuum_expectation f := by rw [R.vacuum_expectation, LinearIsometryEquiv.norm_map]

lemma FockRep.precomp_W (R : FockRep h K) (U : h ≃ₗᵢ[ℂ] h) (f : h) : (R.precomp U).W f = R.W (U f) := rfl

/-- Two unitaries that agree on the vectors `W f Ω` are equal (the vacuum is cyclic). -/
lemma FockRep.ext_W_Ω (R : FockRep h K) {V V' : K ≃ₗᵢ[ℂ] K} (hV : ∀ f, V (R.W f R.Ω) = V' (R.W f R.Ω)) : V = V' := by
  let E : Submodule ℂ K := LinearMap.eqLocus V.toLinearEquiv.toLinearMap V'.toLinearEquiv.toLinearMap
  have hE : IsClosed (E : Set K) := isClosed_eq V.continuous V'.continuous
  have hspan : Submodule.span ℂ (Set.range fun f => R.W f R.Ω) ≤ E :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun f => hV f)
  have htop : ⊤ ≤ E := by
    rw [← R.cyclic]; exact Submodule.topologicalClosure_minimal _ hspan hE
  ext ψ
  exact htop Submodule.mem_top

variable [CompleteSpace K]

/-- **Second quantization** `Γ(U)` of a unitary `U` of `h`: the unitary of the Fock space with `Γ(U) Ω = Ω` and
`Γ(U) W(f) = W(U f) Γ(U)`. -/
noncomputable def FockRep.secondQuant (R : FockRep h K) (U : h ≃ₗᵢ[ℂ] h) : K ≃ₗᵢ[ℂ] K := fockUnitary R (R.precomp U)

variable (R : FockRep h K)

/-- `Γ(U) Ω = Ω`: in particular `(Ω|Γ(U) Ω) = 1 > 0`, the normalization of Dereziński's (47). -/
theorem FockRep.secondQuant_vacuum (U : h ≃ₗᵢ[ℂ] h) : R.secondQuant U R.Ω = R.Ω :=
  (fockUnitary_spec R (R.precomp U)).1

/-- `Γ(U) W(f) = W(U f) Γ(U)`. -/
theorem FockRep.secondQuant_W (U : h ≃ₗᵢ[ℂ] h) (f : h) (ψ : K) :
    R.secondQuant U (R.W f ψ) = R.W (U f) (R.secondQuant U ψ) :=
  (fockUnitary_spec R (R.precomp U)).2 f ψ

/-- **`Γ(U)` implements `U`** (Dereziński, Theorem 24, (45)): `Γ(U) W(f) Γ(U)* = W(U f)`. -/
theorem FockRep.secondQuant_conj (U : h ≃ₗᵢ[ℂ] h) (f : h) (ψ : K) :
    R.secondQuant U (R.W f ((R.secondQuant U).symm ψ)) = R.W (U f) ψ := by
  rw [R.secondQuant_W, LinearIsometryEquiv.apply_symm_apply]

lemma FockRep.secondQuant_W_Ω (U : h ≃ₗᵢ[ℂ] h) (f : h) : R.secondQuant U (R.W f R.Ω) = R.W (U f) R.Ω := by
  rw [R.secondQuant_W, R.secondQuant_vacuum]

/-- **Uniqueness**: a unitary fixing `Ω` and with `V W(f) Ω = W(U f) Ω` is `Γ(U)`. -/
theorem FockRep.secondQuant_unique (U : h ≃ₗᵢ[ℂ] h) {V : K ≃ₗᵢ[ℂ] K} (hV : ∀ f, V (R.W f R.Ω) = R.W (U f) R.Ω) :
    V = R.secondQuant U :=
  R.ext_W_Ω fun f => by rw [hV, R.secondQuant_W_Ω]

/-- **Functoriality**: `Γ(1) = 1`. -/
theorem FockRep.secondQuant_refl : R.secondQuant (LinearIsometryEquiv.refl ℂ h) = LinearIsometryEquiv.refl ℂ K :=
  (R.secondQuant_unique _ fun f => rfl).symm

/-- **Functoriality** (Dereziński, Theorem 13, `Γ(p₂)Γ(p₁) = Γ(p₂p₁)`, for unitaries): `Γ(V ∘ U) = Γ(V) Γ(U)`. -/
theorem FockRep.secondQuant_trans (U V : h ≃ₗᵢ[ℂ] h) :
    R.secondQuant (U.trans V) = (R.secondQuant U).trans (R.secondQuant V) :=
  (R.secondQuant_unique _ fun _ => by
    simp only [LinearIsometryEquiv.trans_apply, R.secondQuant_W_Ω]).symm

/-- `Γ(U⁻¹) = Γ(U)⁻¹`. -/
theorem FockRep.secondQuant_symm (U : h ≃ₗᵢ[ℂ] h) : R.secondQuant U.symm = (R.secondQuant U).symm := by
  have h1 := R.secondQuant_trans U U.symm
  rw [LinearIsometryEquiv.self_trans_symm, R.secondQuant_refl] at h1
  ext ψ
  have := congrArg (fun T : K ≃ₗᵢ[ℂ] K => T ((R.secondQuant U).symm ψ)) h1
  simpa using this.symm

/-- **Uniqueness up to a phase** (Dereziński, Theorem 24 (2), p. 27, for a unitary `U`): a unitary `V` with
`V W(f) = W(U f) V` is `c Γ(U)` for some `|c| = 1`. -/
theorem FockRep.eq_smul_secondQuant (U : h ≃ₗᵢ[ℂ] h) {V : K ≃ₗᵢ[ℂ] K}
    (hV : ∀ f ψ, V (R.W f ψ) = R.W (U f) (V ψ)) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ ψ, V ψ = c • R.secondQuant U ψ := by
  have hG : ∀ f φ, (R.secondQuant U).symm (R.W (U f) φ) = R.W f ((R.secondQuant U).symm φ) := by
    intro f φ
    apply (R.secondQuant U).injective
    rw [LinearIsometryEquiv.apply_symm_apply, R.secondQuant_W, LinearIsometryEquiv.apply_symm_apply]
  let C : K →L[ℂ] K := ((V.trans (R.secondQuant U).symm : K ≃ₗᵢ[ℂ] K) : K →L[ℂ] K)
  have hC : ∀ f ψ, C (R.W f ψ) = R.W f (C ψ) := by
    intro f ψ
    show (R.secondQuant U).symm (V (R.W f ψ)) = R.W f ((R.secondQuant U).symm (V ψ))
    rw [hV, hG]
  obtain ⟨c, hc⟩ := commutant_scalar R C hC
  have hVc : ∀ ψ, V ψ = c • R.secondQuant U ψ := by
    intro ψ
    have h1 : (R.secondQuant U).symm (V ψ) = c • ψ := hc ψ
    rw [← LinearIsometryEquiv.apply_symm_apply (R.secondQuant U) (V ψ), h1, map_smul]
  refine ⟨c, ?_, hVc⟩
  have h2 := congrArg norm (hVc R.Ω)
  rw [LinearIsometryEquiv.norm_map, norm_smul, LinearIsometryEquiv.norm_map, R.norm_Ω, mul_one] at h2
  exact h2.symm

/-- **The normalized implementer** (Dereziński, Theorem 24 (2), (47), for a unitary `U`): `Γ(U)` is the only unitary `V`
with `V W(f) = W(U f) V` and `(Ω|V Ω) > 0`. -/
theorem FockRep.eq_secondQuant_of_pos (U : h ≃ₗᵢ[ℂ] h) {V : K ≃ₗᵢ[ℂ] K}
    (hV : ∀ f ψ, V (R.W f ψ) = R.W (U f) (V ψ)) (hpos : 0 < ⟪R.Ω, V R.Ω⟫_ℂ) : V = R.secondQuant U := by
  obtain ⟨c, hc1, hc⟩ := R.eq_smul_secondQuant U hV
  have hΩ : ⟪R.Ω, V R.Ω⟫_ℂ = c := by
    rw [hc, R.secondQuant_vacuum, inner_smul_right, inner_self_eq_norm_sq_to_K, R.norm_Ω]; simp
  rw [hΩ] at hpos
  have hre : 0 < c.re := (Complex.lt_def.mp hpos).1
  have him : c.im = 0 := (Complex.lt_def.mp hpos).2.symm
  have hc' : c = 1 := by
    have hn : ‖c‖ = |c.re| := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, him]; simp [Real.sqrt_sq_eq_abs]
    rw [hn, abs_of_pos hre] at hc1
    exact Complex.ext (by simpa using hc1) (by simpa using him)
  ext ψ
  rw [hc, hc', one_smul]

/-! ### Positive semidefinite kernels

The Schur product theorem (`Matrix.PosSemidef.hadamard`) makes the entrywise powers of a positive semidefinite matrix
positive semidefinite, and hence also its entrywise image under a power series with nonnegative coefficients. -/

lemma posSemidef_map_pow {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    ∀ n : ℕ, (M.map fun z => z ^ n).PosSemidef
  | 0 => by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨Matrix.IsHermitian.ext fun i j => by simp, fun x => ?_⟩
    have : star x ⬝ᵥ ((M.map fun z => z ^ 0) *ᵥ x) = star (∑ i, x i) * ∑ i, x i := by
      simp [dotProduct, Matrix.mulVec, star_sum, Finset.sum_mul]
    rw [this]; exact star_mul_self_nonneg _
  | n + 1 => by
    have : (M.map fun z => z ^ (n + 1)) = M ⊙ M.map fun z => z ^ n := by
      ext i j; simp [Matrix.hadamard, pow_succ, mul_comm]
    rw [this]; exact hM.hadamard (posSemidef_map_pow hM n)

/-- A power series with nonnegative coefficients, applied entrywise, preserves positive semidefinite matrices. -/
lemma posSemidef_map_series {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) {F : ℂ → ℂ} (hF : ∀ z, HasSum (fun n => (a n : ℂ) * z ^ n) (F z)) :
    (M.map F).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · have hFs : ∀ z, F (star z) = star (F z) := fun z => by
      have h1 := (hF z).star
      have h2 : (fun n => star ((a n : ℂ) * z ^ n)) = fun n => (a n : ℂ) * star z ^ n := by
        funext n; simp [star_pow]
      rw [h2] at h1
      exact (hF (star z)).unique h1
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [← hFs, hM.1.apply]
  · have key : ∀ i j, HasSum (fun n => (a n : ℂ) * (star (x i) * ((M i j) ^ n * x j)))
        (star (x i) * (F (M i j) * x j)) := fun i j => by
      have := ((hF (M i j)).mul_left (star (x i))).mul_right (x j)
      convert this using 1
      · funext n; ring
      · ring
    have hs := hasSum_sum fun i (_ : i ∈ Finset.univ) => hasSum_sum fun j (_ : j ∈ Finset.univ) => key i j
    have e1 : ∀ n, (a n : ℂ) * (star x ⬝ᵥ ((M.map fun z => z ^ n) *ᵥ x)) =
        ∑ i, ∑ j, (a n : ℂ) * (star (x i) * ((M i j) ^ n * x j)) := by
      intro n; simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
    have e2 : star x ⬝ᵥ ((M.map F) *ᵥ x) = ∑ i, ∑ j, star (x i) * (F (M i j) * x j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
    rw [e2]
    rw [← funext e1] at hs
    exact hs.nonneg fun n => mul_nonneg (by exact_mod_cast ha n)
      ((Matrix.posSemidef_iff_dotProduct_mulVec.1 (posSemidef_map_pow hM n)).2 x)

lemma hasSum_cexp (z : ℂ) : HasSum (fun n => (((n.factorial : ℝ)⁻¹ : ℝ) : ℂ) * z ^ n) (Complex.exp z) := by
  have := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z
  rw [← Complex.exp_eq_exp_ℂ] at this
  convert this using 2 with n <;> simp [smul_eq_mul]

lemma hasSum_cexp_sub_one (z : ℂ) :
    HasSum (fun n => ((if n = 0 then 0 else (n.factorial : ℝ)⁻¹ : ℝ) : ℂ) * z ^ n) (Complex.exp z - 1) := by
  have := (hasSum_cexp z).update 0 0
  convert this using 1
  · funext n
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  · simp; ring

/-- `⟪∑ xᵢ wᵢ, ∑ xᵢ wᵢ⟫` as a quadratic form of the Gram matrix. -/
lemma dotProduct_gram {ι : Type*} [Fintype ι] (w : ι → h) (x : ι → ℂ) :
    star x ⬝ᵥ ((Matrix.of fun i j => ⟪w i, w j⟫_ℂ) *ᵥ x) = ⟪∑ i, x i • w i, ∑ i, x i • w i⟫_ℂ := by
  rw [sum_inner]
  simp only [dotProduct, Matrix.mulVec, inner_sum, inner_smul_left, inner_smul_right, Pi.star_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]; ring

/-- **The kernel of a contraction** `exp(⟪f, g⟫/2) - exp(⟪p f, p g⟫/2)` is positive semidefinite for `‖p‖ ≤ 1`. -/
lemma posSemidef_kernel {ι : Type*} [Fintype ι] (p : h →L[ℂ] h) (hp : ‖p‖ ≤ 1) (v : ι → h) :
    (Matrix.of fun i j => Complex.exp (⟪v i, v j⟫_ℂ / 2) - Complex.exp (⟪p (v i), p (v j)⟫_ℂ / 2)).PosSemidef := by
  have herm : ∀ (A : ι → ι → ℂ), (∀ i j, star (A j i) = A i j) → (Matrix.of A).IsHermitian := fun A hA =>
    Matrix.IsHermitian.ext fun i j => by simpa using hA i j
  -- `⟪p vᵢ, p vⱼ⟫ / 2`
  have h1 : (Matrix.of fun i j => ⟪p (v i), p (v j)⟫_ℂ / 2).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨herm _ fun i j => by simp [inner_conj_symm], fun x => ?_⟩
    have := dotProduct_gram (fun i => p (v i)) x
    have e : (Matrix.of fun i j => ⟪p (v i), p (v j)⟫_ℂ / 2) = (1 / 2 : ℂ) • Matrix.of fun i j => ⟪p (v i), p (v j)⟫_ℂ := by
      ext i j; simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e, Matrix.smul_mulVec, dotProduct_smul, this, smul_eq_mul]
    exact mul_nonneg (by rw [Complex.le_def]; norm_num)
      (RCLike.nonneg_iff.mpr ⟨inner_self_nonneg, inner_self_im _⟩)
  -- `(⟪vᵢ, vⱼ⟫ - ⟪p vᵢ, p vⱼ⟫) / 2`
  have h2 : (Matrix.of fun i j => (⟪v i, v j⟫_ℂ - ⟪p (v i), p (v j)⟫_ℂ) / 2).PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨herm _ fun i j => by simp [inner_conj_symm], fun x => ?_⟩
    have ha := dotProduct_gram v x
    have hb := dotProduct_gram (fun i => p (v i)) x
    have e : (Matrix.of fun i j => (⟪v i, v j⟫_ℂ - ⟪p (v i), p (v j)⟫_ℂ) / 2) =
        (1 / 2 : ℂ) • ((Matrix.of fun i j => ⟪v i, v j⟫_ℂ) - Matrix.of fun i j => ⟪p (v i), p (v j)⟫_ℂ) := by
      ext i j; simp; ring
    have hpX : ∑ i, x i • p (v i) = p (∑ i, x i • v i) := by simp [map_sum, map_smul]
    rw [e, Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, ha, hb, hpX, smul_eq_mul]
    have hle : ‖p (∑ i, x i • v i)‖ ≤ ‖∑ i, x i • v i‖ :=
      (p.le_opNorm _).trans (by nlinarith [norm_nonneg (∑ i, x i • v i)])
    have hsq : ‖p (∑ i, x i • v i)‖ ^ 2 ≤ ‖∑ i, x i • v i‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    have hX : (0 : ℂ) ≤ ⟪∑ i, x i • v i, ∑ i, x i • v i⟫_ℂ - ⟪p (∑ i, x i • v i), p (∑ i, x i • v i)⟫_ℂ := by
      refine RCLike.nonneg_iff.mpr ⟨?_, ?_⟩
      · rw [map_sub, inner_self_eq_norm_sq, inner_self_eq_norm_sq]; linarith
      · rw [map_sub, inner_self_im, inner_self_im, sub_zero]
    exact mul_nonneg (by rw [Complex.le_def]; norm_num) hX
  have hA := posSemidef_map_series h1 (fun n => (n.factorial : ℝ)⁻¹) (fun n => by positivity) hasSum_cexp
  have hB := posSemidef_map_series h2 (fun n => if n = 0 then 0 else (n.factorial : ℝ)⁻¹)
    (fun n => by split_ifs <;> positivity) hasSum_cexp_sub_one
  have e : (Matrix.of fun i j => Complex.exp (⟪v i, v j⟫_ℂ / 2) - Complex.exp (⟪p (v i), p (v j)⟫_ℂ / 2)) =
      ((Matrix.of fun i j => ⟪p (v i), p (v j)⟫_ℂ / 2).map Complex.exp) ⊙
        ((Matrix.of fun i j => (⟪v i, v j⟫_ℂ - ⟪p (v i), p (v j)⟫_ℂ) / 2).map fun z => Complex.exp z - 1) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.hadamard_apply, Matrix.map_apply]
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2; ring
  rw [e]
  exact hA.hadamard hB

/-! ### Second quantization of a contraction -/

/-- `⟪W f Ω, W g Ω⟫ = e^{-‖f‖²/4} e^{-‖g‖²/4} exp(⟪f, g⟫/2)`. -/
lemma FockRep.inner_W_Ω_exp (f g : h) :
    ⟪R.W f R.Ω, R.W g R.Ω⟫_ℂ =
      ((Real.exp (-(‖f‖ ^ 2 / 4)) * Real.exp (-(‖g‖ ^ 2 / 4)) : ℝ) : ℂ) * Complex.exp (⟪f, g⟫_ℂ / 2) := by
  have hs : symp h (-f) g = -(⟪f, g⟫_ℂ).im := by simp [symp, inner_neg_left]
  have hn : ‖-f + g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 - 2 * (⟪f, g⟫_ℂ).re := by
    rw [neg_add_eq_sub, @norm_sub_sq ℂ, ← inner_conj_symm g f, RCLike.re_to_complex, Complex.conj_re]; ring
  rw [R.inner_W_Ω, fockGram, hs, hn, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp <;> ring

/-- The factor `exp((‖p f‖² - ‖f‖²)/4)` in `Γ(p) W(f) Ω = exp((‖p f‖² - ‖f‖²)/4) W(p f) Ω`, that is `Γ(p) e(f) = e(p f)`
for the exponential vectors `e(f) = e^{‖f‖²/4} W(f) Ω`. -/
noncomputable def cohFactor (p : h →L[ℂ] h) (f : h) : ℝ := Real.exp ((‖p f‖ ^ 2 - ‖f‖ ^ 2) / 4)

/-- `Γ(p)` on the finite combinations of the vectors `W f Ω`. -/
noncomputable def FockRep.gammaPre (p : h →L[ℂ] h) : (h →₀ ℂ) →ₗ[ℂ] K :=
  Finsupp.linearCombination ℂ fun f => (cohFactor p f : ℂ) • R.W (p f) R.Ω

/-- **`Γ(p)` is a contraction on the finite combinations of the `W f Ω`** when `‖p‖ ≤ 1`. -/
theorem FockRep.norm_gammaPre_le (p : h →L[ℂ] h) (hp : ‖p‖ ≤ 1) (c : h →₀ ℂ) :
    ‖R.gammaPre p c‖ ≤ ‖fockMap R c‖ := by
  classical
  set S := c.support
  let d : S → ℂ := fun i => c i * (Real.exp (-(‖(i : h)‖ ^ 2 / 4)) : ℂ)
  have hK := posSemidef_kernel p hp (fun i : S => (i : h))
  have hX : ⟪fockMap R c, fockMap R c⟫_ℂ =
      ∑ i : S, ∑ j : S, star (d i) * d j * Complex.exp (⟪(i : h), (j : h)⟫_ℂ / 2) := by
    rw [fockMap, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, R.inner_W_Ω_exp]
    simp only [d, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hf : ∀ f : h, cohFactor p f * Real.exp (-(‖p f‖ ^ 2 / 4)) = Real.exp (-(‖f‖ ^ 2 / 4)) := fun f => by
    simp only [cohFactor, ← Real.exp_add]; congr 1; ring
  have hY : ⟪R.gammaPre p c, R.gammaPre p c⟫_ℂ =
      ∑ i : S, ∑ j : S, star (d i) * d j * Complex.exp (⟪p (i : h), p (j : h)⟫_ℂ / 2) := by
    rw [FockRep.gammaPre, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right, R.inner_W_Ω_exp]
    simp only [d, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← hf (i : h), ← hf (j : h)]
    push_cast
    ring
  have hdiff : ⟪fockMap R c, fockMap R c⟫_ℂ - ⟪R.gammaPre p c, R.gammaPre p c⟫_ℂ =
      star d ⬝ᵥ ((Matrix.of fun i j : S => Complex.exp (⟪(i : h), (j : h)⟫_ℂ / 2) -
        Complex.exp (⟪p (i : h), p (j : h)⟫_ℂ / 2)) *ᵥ d) := by
    rw [hX, hY, ← Finset.sum_sub_distrib]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h0 : (0 : ℂ) ≤ ⟪fockMap R c, fockMap R c⟫_ℂ - ⟪R.gammaPre p c, R.gammaPre p c⟫_ℂ := by
    rw [hdiff]; exact (Matrix.posSemidef_iff_dotProduct_mulVec.1 hK).2 d
  have hre := (Complex.le_def.mp h0).1
  rw [Complex.sub_re, Complex.zero_re] at hre
  have hsq : ‖R.gammaPre p c‖ ^ 2 ≤ ‖fockMap R c‖ ^ 2 := by
    have a1 := inner_self_eq_norm_sq (𝕜 := ℂ) (fockMap R c)
    have a2 := inner_self_eq_norm_sq (𝕜 := ℂ) (R.gammaPre p c)
    simp only [RCLike.re_to_complex] at a1 a2
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma FockRep.denseRange_fockMap' : DenseRange (fockMap R) := by
  have := dense_range_fockMap R
  rwa [LinearMap.coe_range] at this

/-- **The second quantization `Γ(p)` of a contraction** `p` (`‖p‖ ≤ 1`; Dereziński, Section 5.2 and Section 5.5): the
contraction of the Fock space with `Γ(p) W(f) Ω = exp((‖p f‖² - ‖f‖²)/4) W(p f) Ω`, i.e. `Γ(p) e(f) = e(p f)`. -/
noncomputable def FockRep.gamma (p : h →L[ℂ] h) : K →L[ℂ] K := (R.gammaPre p).extendOfNorm (fockMap R)

variable {R} in
lemma FockRep.gamma_fockMap {p : h →L[ℂ] h} (hp : ‖p‖ ≤ 1) (c : h →₀ ℂ) : R.gamma p (fockMap R c) = R.gammaPre p c :=
  LinearMap.extendOfNorm_eq R.denseRange_fockMap' ⟨1, fun c => by rw [one_mul]; exact R.norm_gammaPre_le p hp c⟩ c

variable {R} in
/-- `Γ(p) W(f) Ω = exp((‖p f‖² - ‖f‖²)/4) W(p f) Ω`. -/
theorem FockRep.gamma_W_Ω {p : h →L[ℂ] h} (hp : ‖p‖ ≤ 1) (f : h) :
    R.gamma p (R.W f R.Ω) = (cohFactor p f : ℂ) • R.W (p f) R.Ω := by
  have := R.gamma_fockMap hp (Finsupp.single f 1)
  simpa [fockMap, FockRep.gammaPre] using this

variable {R} in
/-- **`Γ(p)` is a contraction**: `‖Γ(p)‖ ≤ 1`. -/
theorem FockRep.norm_gamma_le {p : h →L[ℂ] h} (hp : ‖p‖ ≤ 1) : ‖R.gamma p‖ ≤ 1 :=
  LinearMap.opNorm_extendOfNorm_le R.denseRange_fockMap' zero_le_one
    fun c => by rw [one_mul]; exact R.norm_gammaPre_le p hp c

/-- Two bounded operators that agree on the vectors `W f Ω` are equal. -/
lemma FockRep.clm_ext_W_Ω {A B : K →L[ℂ] K} (hAB : ∀ f, A (R.W f R.Ω) = B (R.W f R.Ω)) : A = B := by
  let E : Submodule ℂ K := LinearMap.eqLocus A.toLinearMap B.toLinearMap
  have hE : IsClosed (E : Set K) := isClosed_eq A.continuous B.continuous
  have hspan : Submodule.span ℂ (Set.range fun f => R.W f R.Ω) ≤ E :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hAB)
  have htop : ⊤ ≤ E := by
    rw [← R.cyclic]; exact Submodule.topologicalClosure_minimal _ hspan hE
  ext ψ
  exact htop Submodule.mem_top

variable {R} in
/-- `Γ(1) = 1`. -/
theorem FockRep.gamma_one : R.gamma (1 : h →L[ℂ] h) = 1 :=
  R.clm_ext_W_Ω fun f => by
    rw [R.gamma_W_Ω (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp)]
    simp [cohFactor]

variable {R} in
/-- **Functoriality** (Dereziński, Theorem 13, p. 19): `Γ(q) Γ(p) = Γ(q p)` for contractions. -/
theorem FockRep.gamma_comp {p q : h →L[ℂ] h} (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    R.gamma q ∘L R.gamma p = R.gamma (q ∘L p) := by
  have hqp : ‖q ∘L p‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le q p).trans (by nlinarith [norm_nonneg p])
  refine R.clm_ext_W_Ω fun f => ?_
  rw [ContinuousLinearMap.comp_apply, R.gamma_W_Ω hp, map_smul, R.gamma_W_Ω hq, R.gamma_W_Ω hqp, smul_smul,
    ContinuousLinearMap.comp_apply]
  congr 1
  simp only [cohFactor, ContinuousLinearMap.comp_apply, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2; ring

/-- A vector orthogonal to all the `W g Ω` is zero. -/
lemma FockRep.eq_zero_of_inner_W_Ω {u : K} (hu : ∀ g, ⟪R.W g R.Ω, u⟫_ℂ = 0) : u = 0 := by
  have hspan : Submodule.span ℂ (Set.range fun g => R.W g R.Ω) ≤ (ℂ ∙ u)ᗮ :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr fun g =>
      (Submodule.mem_orthogonal_singleton_iff_inner_left).mpr (hu g))
  have htop : ⊤ ≤ (ℂ ∙ u)ᗮ := by
    rw [← R.cyclic]; exact Submodule.topologicalClosure_minimal _ hspan (Submodule.isClosed_orthogonal _)
  have := (Submodule.mem_orthogonal_singleton_iff_inner_left (𝕜 := ℂ) (u := u) (v := u)).mp (htop Submodule.mem_top)
  exact inner_self_eq_zero.mp this

variable {R} in
/-- **`Γ(p)* = Γ(p*)`**. -/
theorem FockRep.adjoint_gamma [CompleteSpace h] {p : h →L[ℂ] h} (hp : ‖p‖ ≤ 1) :
    ContinuousLinearMap.adjoint (R.gamma p) = R.gamma (ContinuousLinearMap.adjoint p) := by
  have hp' : ‖ContinuousLinearMap.adjoint p‖ ≤ 1 := by rwa [ContinuousLinearMap.adjoint.norm_map]
  have hmat : ∀ f g, ⟪R.W g R.Ω, ContinuousLinearMap.adjoint (R.gamma p) (R.W f R.Ω)⟫_ℂ =
      ⟪R.W g R.Ω, R.gamma (ContinuousLinearMap.adjoint p) (R.W f R.Ω)⟫_ℂ := by
    intro f g
    rw [ContinuousLinearMap.adjoint_inner_right, R.gamma_W_Ω hp, R.gamma_W_Ω hp', inner_smul_left, inner_smul_right,
      R.inner_W_Ω_exp, R.inner_W_Ω_exp, ContinuousLinearMap.adjoint_inner_right p g f, Complex.conj_ofReal,
      ← mul_assoc, ← mul_assoc]
    congr 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    simp only [cohFactor, ← Real.exp_add]
    congr 1; ring
  refine R.clm_ext_W_Ω fun f => ?_
  have horth : ∀ g, ⟪R.W g R.Ω, ContinuousLinearMap.adjoint (R.gamma p) (R.W f R.Ω) -
      R.gamma (ContinuousLinearMap.adjoint p) (R.W f R.Ω)⟫_ℂ = 0 := fun g => by
    rw [inner_sub_right, hmat, sub_self]
  exact sub_eq_zero.mp (R.eq_zero_of_inner_W_Ω horth)

lemma norm_unitary_le (U : h ≃ₗᵢ[ℂ] h) : ‖(U : h →L[ℂ] h)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [show (U : h →L[ℂ] h) x = U x from rfl, LinearIsometryEquiv.norm_map, one_mul]

variable {R} in
/-- **For a unitary `U`, `Γ(U)` is the second quantization of the unitary**: `Γ(U) = secondQuant U`, a unitary
(Dereziński, Theorem 13: `Γ(p)` is unitary when `p` is). -/
theorem FockRep.gamma_unitary (U : h ≃ₗᵢ[ℂ] h) : R.gamma (U : h →L[ℂ] h) = (R.secondQuant U : K →L[ℂ] K) :=
  R.clm_ext_W_Ω fun f => by
    have hU : ∀ x, (U : h →L[ℂ] h) x = U x := fun x => rfl
    have hG : ∀ x, (R.secondQuant U : K →L[ℂ] K) x = R.secondQuant U x := fun x => rfl
    rw [R.gamma_W_Ω (norm_unitary_le U), hG, R.secondQuant_W_Ω]
    simp only [cohFactor, hU, LinearIsometryEquiv.norm_map, sub_self, zero_div, Real.exp_zero, Complex.ofReal_one,
      one_smul]

/-- **`Γ(p)` is bounded only if `‖p‖ ≤ 1`** (Dereziński, Theorem 13, p. 19): a bounded operator `T` with
`T W(f) Ω = exp((‖p f‖² - ‖f‖²)/4) W(p f) Ω` for all `f` forces `‖p‖ ≤ 1`. -/
theorem FockRep.norm_le_one_of_gamma {p : h →L[ℂ] h} (T : K →L[ℂ] K)
    (hT : ∀ f, T (R.W f R.Ω) = (cohFactor p f : ℂ) • R.W (p f) R.Ω) : ‖p‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  rw [one_mul]
  by_contra hlt
  push_neg at hlt
  set δ := ‖p f‖ ^ 2 - ‖f‖ ^ 2 with hδ
  have hδpos : 0 < δ := by nlinarith [norm_nonneg f]
  have hb : ∀ t : ℝ, Real.exp (t ^ 2 * δ / 4) ≤ ‖T‖ := by
    intro t
    have h1 := T.le_opNorm (R.W ((t : ℂ) • f) R.Ω)
    rw [hT, norm_smul, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, R.norm_Ω, mul_one, mul_one,
      Complex.norm_real, cohFactor, Real.norm_of_nonneg (Real.exp_pos _).le, map_smul, norm_smul, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs] at h1
    convert h1 using 2
    rw [hδ]; ring
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  set t := Real.sqrt (4 * (‖T‖ + 1) / δ)
  have ht : t ^ 2 * δ / 4 = ‖T‖ + 1 := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  have := hb t
  rw [ht] at this
  linarith [Real.add_one_le_exp (‖T‖ + 1)]

variable {R} in
/-- `Γ(q) = 1` only for `q = 1`. -/
theorem FockRep.eq_one_of_gamma_eq_one {q : h →L[ℂ] h} (hq : ‖q‖ ≤ 1) (h1 : R.gamma q = 1) : q = 1 := by
  ext f
  -- `exp(⟪g, q f⟫/2) = exp(⟪g, f⟫/2)` for all `g`
  have hg : ∀ g : h, Complex.exp (⟪g, q f⟫_ℂ / 2) = Complex.exp (⟪g, f⟫_ℂ / 2) := by
    intro g
    have := congrArg (fun T : K →L[ℂ] K => ⟪R.W g R.Ω, T (R.W f R.Ω)⟫_ℂ) h1
    simp only [ContinuousLinearMap.one_apply] at this
    rw [R.gamma_W_Ω hq, inner_smul_right, R.inner_W_Ω_exp, R.inner_W_Ω_exp, ← mul_assoc] at this
    have hne : ((Real.exp (-(‖g‖ ^ 2 / 4)) * Real.exp (-(‖f‖ ^ 2 / 4)) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
    have e : (cohFactor q f : ℂ) * ((Real.exp (-(‖g‖ ^ 2 / 4)) * Real.exp (-(‖q f‖ ^ 2 / 4)) : ℝ) : ℂ) =
        ((Real.exp (-(‖g‖ ^ 2 / 4)) * Real.exp (-(‖f‖ ^ 2 / 4)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]; congr 1
      simp only [cohFactor, ← Real.exp_add]; congr 1; ring
    rw [e] at this
    exact mul_left_cancel₀ hne this
  -- differentiate `s ↦ exp(s ⟪g, ·⟫/2)` at `0`
  have hinner : ∀ g : h, ⟪g, q f⟫_ℂ = ⟪g, f⟫_ℂ := by
    intro g
    have hd : ∀ a : ℂ, HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * a / 2)) (a / 2) 0 := by
      intro a
      have := ((((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const a).div_const 2).cexp).comp_ofReal
      simpa using this
    have heq : (fun s : ℝ => Complex.exp ((s : ℂ) * ⟪g, q f⟫_ℂ / 2)) =
        fun s : ℝ => Complex.exp ((s : ℂ) * ⟪g, f⟫_ℂ / 2) := by
      funext s
      have := hg ((s : ℂ) • g)
      rwa [inner_smul_left, inner_smul_left, Complex.conj_ofReal] at this
    have := (hd ⟪g, q f⟫_ℂ).unique (heq ▸ hd ⟪g, f⟫_ℂ)
    linear_combination 2 * this
  have := hinner (q f - f)
  rw [← sub_eq_zero, ← inner_sub_right, inner_self_eq_zero, sub_eq_zero] at this
  simpa using this

variable {R} in
/-- **`Γ(p)` is unitary iff `p` is** (Dereziński, Theorem 13, p. 19), for a contraction `p`. -/
theorem FockRep.gamma_mem_unitary_iff [CompleteSpace h] {p : h →L[ℂ] h} (hp : ‖p‖ ≤ 1) :
    R.gamma p ∈ unitary (K →L[ℂ] K) ↔ p ∈ unitary (h →L[ℂ] h) := by
  have hp' : ‖ContinuousLinearMap.adjoint p‖ ≤ 1 := by rwa [ContinuousLinearMap.adjoint.norm_map]
  have hc1 : ‖ContinuousLinearMap.adjoint p ∘L p‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg p])
  have hc2 : ‖p ∘L ContinuousLinearMap.adjoint p‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg p])
  simp only [Unitary.mem_iff, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
  rw [R.adjoint_gamma hp, R.gamma_comp hp hp', R.gamma_comp hp' hp]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨R.eq_one_of_gamma_eq_one hc1 h1, R.eq_one_of_gamma_eq_one hc2 h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, R.gamma_one]
    exact ⟨rfl, rfl⟩

/-! ### Second quantization of a unitary group -/

/-- **`t ↦ Γ(U(t))`** for a strongly continuous unitary group `U` of `h`: a strongly continuous unitary group of `K`. -/
noncomputable def FockRep.secondQuantGroup (U : UnitaryGroup h) : UnitaryGroup K where
  toFun t := R.secondQuant (U t)
  map_zero' := by
    rw [show U 0 = LinearIsometryEquiv.refl ℂ h from U.map_zero', R.secondQuant_refl]
  map_add' s t := by
    rw [show U (s + t) = (U t).trans (U s) from U.map_add' s t, R.secondQuant_trans]
  continuous' ψ := by
    refine continuous_of_dense_isometries (fun t => R.secondQuant (U t)) (dense_range_fockMap R) (fun χ hχ => ?_) ψ
    obtain ⟨c, rfl⟩ := hχ
    have e : ∀ t, R.secondQuant (U t) (fockMap R c) = ∑ f ∈ c.support, c f • R.W (U t f) R.Ω := by
      intro t
      rw [fockMap, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [map_smul, R.secondQuant_W_Ω]
    simp only [e]
    exact continuous_finset_sum _ fun f _ =>
      ((FockRep.continuous_W R R.Ω).comp (U.continuous' f)).const_smul (c f)

lemma FockRep.secondQuantGroup_apply (U : UnitaryGroup h) (t : ℝ) (ψ : K) :
    R.secondQuantGroup U t ψ = R.secondQuant (U t) ψ := rfl

/-- **`dΓ`** of the self-adjoint generator of a unitary group `U(t) = e^{ith}` of `h`: the generator of `t ↦ Γ(U(t))`, so
that `Γ(e^{ith}) = e^{it dΓ(h)}` (Dereziński, Theorem 13, (35)). -/
noncomputable def FockRep.dGamma (U : UnitaryGroup h) : K →ₗ.[ℂ] K := (R.secondQuantGroup U).generator

/-- `dΓ(h)` is self-adjoint (Stone's theorem). -/
theorem FockRep.isSelfAdjoint_dGamma (U : UnitaryGroup h) : IsSelfAdjoint (R.dGamma U) :=
  UnitaryGroup.generator_isSelfAdjoint _

end Lightlike.OperatorAlgebras
