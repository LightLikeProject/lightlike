import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lightlike.OperatorAlgebras.SecondQuantSlot
import Lightlike.OperatorAlgebras.FermiFockGeneral
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The sign of an injective tuple

For the embedding of the `n`-particle fermionic Fock space `Γₙ` (the closed span of the wedges `B S`, `|S| = n`, in
`ℓ²(Finset ι)`) into the coordinate tensor power `ℓ²(Fin n → ι)` (J. Dereziński, arXiv:math-ph/0511030, Section 5.2:
`Γₙ^a(Z)` is the antisymmetric subspace of `⊗ⁿZ`): a wedge `B S` goes to `(n!)^{-1/2} ∑ sign(f) e_f` over the injective tuples
`f` enumerating `S`, where the sign of `f` is that of the permutation sorting it (Mathlib's `Tuple.sort`).

* `tupleSign`, `sort_comp_perm`, `tupleSign_comp`: `sign(f ∘ τ) = sign τ · sign f` for injective `f`;
* `sign_eq_signAux`, `tupleSign_eq_prod`, `tupleSign_cons`: the sign is the inversion product, and
  `sign (cons a p) = ∏ᵢ (-1)^{[p i ≤ a]} · sign p`;
* `Enum`, `enumEquiv`, `card_enum`: an `n`-element set has `n!` enumerations by injective tuples;
* `embFun`, `hasSum_fiber`, `hasSum_norm_embFun`, `embL`, `norm_sq_embL`, `norm_embL_le`, `norm_embL_of_support`, `embCLM`:
  the embedding `Eₙ ψ (f) = (n!)^{-1/2} sign(f) ψ(image f)`, a contraction, isometric on the `n`-particle vectors;
* `permEquiv`, `permL`, `antisym`, `antisym_apply`, `embFun_comp`, `antisym_embL`, `sign_mul_self`, `antisym_comp`,
  `antisym_apply_of_not_injective`, `sum_perm_apply_zero`: the antisymmetrizer, `A Eₙ = Eₙ`, `A Φ` antisymmetric;
* `tensorFun`, `hasSum_norm_tensorFun`: `c ⊗ Φ` in coordinates, `‖c ⊗ Φ‖² = ‖c‖² ‖Φ‖²`;
* `hasSum_norm_sq_lp`, `memℓp_tensorFun`, `creTL`, `creTL_apply`, `norm_creTL`, `creT`, `creT_apply`, `slotOp_zero_creT`:
  creation `Φ ↦ w ⊗ Φ` on the tensor power, and `h` on slot `0` of `w ⊗ Φ` is `(h w) ⊗ Φ`;
* `removeNth_succ_eq`, `slotOp_succ_creT`, `dGammaTensor_creT`, `dGammaTensor_zero_creT`: `(∑ⱼ hⱼ)(w ⊗ Φ) =
  (h w) ⊗ Φ + w ⊗ (∑ⱼ hⱼ) Φ`, the commutator before antisymmetrization;
* `tupleSign_of_strictMono`, `prod_succ_lt_zero`, `prod_comp_le_zero`, `fermiSign_strictMono`, `image_tail_comp`: counting
  for sorted tuples;
* `factorial_sqrt_identity`, `embFun_creW_strictMono`, `embFun_creW`, `embL_creW`: the core identity
  `Eₙ₊₁ a*(w) = √(n+1) A (w ⊗ Eₙ ·)`;
* `norm_embCLM_le`, `dGammaFock`, `norm_dGammaFock_le`: `dΓₙ₊₁(h) = Eₙ₊₁* (∑ⱼ hⱼ) Eₙ₊₁` and `‖dΓₙ₊₁(h)‖ ≤ (n + 1) ‖h‖`.
-/

namespace Lightlike.OperatorAlgebras.SecondQuantWedge

variable {ι : Type*} [LinearOrder ι]

/-- **The sign of a tuple**: the sign of the permutation `Tuple.sort f` that sorts it. -/
def tupleSign {n : ℕ} (f : Fin n → ι) : ℤˣ := Equiv.Perm.sign (Tuple.sort f)

/-- **Sorting a permuted injective tuple**: `sort (f ∘ τ) = τ⁻¹ * sort f`, as the monotone rearrangement of an injective
tuple is unique. -/
lemma sort_comp_perm {n : ℕ} {f : Fin n → ι} (hf : Function.Injective f) (τ : Equiv.Perm (Fin n)) :
    Tuple.sort (f ∘ τ) = τ⁻¹ * Tuple.sort f := by
  have hmono : Monotone ((f ∘ τ) ∘ (τ⁻¹ * Tuple.sort f)) := by
    have : (f ∘ τ) ∘ (τ⁻¹ * Tuple.sort f) = f ∘ Tuple.sort f := by
      funext x; simp [Equiv.Perm.mul_apply]
    rw [this]
    exact Tuple.monotone_sort f
  have heq := (Tuple.comp_sort_eq_comp_iff_monotone (f := f ∘ τ) (σ := τ⁻¹ * Tuple.sort f)).mpr hmono
  ext x
  have := congrFun heq x
  exact congrArg Fin.val ((hf.comp τ.injective) this).symm

/-- **`sign(f ∘ τ) = sign τ · sign f`** for an injective tuple `f`. -/
lemma tupleSign_comp {n : ℕ} {f : Fin n → ι} (hf : Function.Injective f) (τ : Equiv.Perm (Fin n)) :
    tupleSign (f ∘ τ) = Equiv.Perm.sign τ * tupleSign f := by
  rw [tupleSign, sort_comp_perm hf, map_mul, Equiv.Perm.sign_inv, tupleSign]

/-- `sign = signAux` on permutations of `Fin n` (both are multiplicative and `-1` on transpositions). -/
lemma sign_eq_signAux {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm.sign σ = Equiv.Perm.signAux σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy ih =>
    rw [Equiv.Perm.sign_mul, Equiv.Perm.signAux_mul, ih, Equiv.Perm.sign_swap hxy, Equiv.Perm.signAux_swap hxy]

/-- **The sign of an injective tuple is its inversion product**: `sign f = ∏_{j < i} (-1)^{[f i ≤ f j]}`. -/
lemma tupleSign_eq_prod {n : ℕ} {f : Fin n → ι} (hf : Function.Injective f) :
    tupleSign f = ∏ i, ∏ j, if j < i then (if f i ≤ f j then -1 else 1) else 1 := by
  have hq : StrictMono (f ∘ Tuple.sort f) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  have hle : ∀ a b : Fin n, (Tuple.sort f)⁻¹ a ≤ (Tuple.sort f)⁻¹ b ↔ f a ≤ f b := fun a b => by
    rw [← hq.le_iff_le]
    simp [Function.comp_apply, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  rw [tupleSign, ← Equiv.Perm.sign_inv, sign_eq_signAux, Equiv.Perm.signAux]
  simp only [hle]
  rw [show Equiv.Perm.finPairsLT n = Finset.univ.filter (fun x : Σ _ : Fin n, Fin n => x.2 < x.1) by
    ext x; simp [Equiv.Perm.mem_finPairsLT], Finset.prod_filter, ← Finset.univ_sigma_univ, Finset.prod_sigma]

/-- **The sign of `cons a p`**: `sign (cons a p) = ∏ᵢ (-1)^{[p i ≤ a]} · sign p`. -/
lemma tupleSign_cons {n : ℕ} (a : ι) (p : Fin n → ι) (hinj : Function.Injective (Fin.cons a p : Fin (n + 1) → ι)) :
    tupleSign (Fin.cons a p : Fin (n + 1) → ι) = (∏ i, if p i ≤ a then -1 else 1) * tupleSign p := by
  have hp : Function.Injective p := fun i j h => Fin.succ_injective _ (hinj (by simpa using h))
  rw [tupleSign_eq_prod hinj, tupleSign_eq_prod hp, Fin.prod_univ_succ]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.not_lt_zero, if_false, Finset.prod_const_one,
    one_mul, Fin.succ_pos, if_true, Fin.succ_lt_succ_iff]
  rw [Finset.prod_mul_distrib]

/-- The injective tuples enumerating a finite set `S`. -/
def Enum (n : ℕ) (S : Finset ι) := {f : Fin n → ι // Function.Injective f ∧ Finset.univ.image f = S}

/-- **The enumerations of `S` are the bijections `Fin n ≃ S`.** -/
noncomputable def enumEquiv (n : ℕ) (S : Finset ι) (hS : S.card = n) : Enum n S ≃ (Fin n ≃ S) where
  toFun f := Equiv.ofBijective (fun i => ⟨f.1 i, (Finset.ext_iff.mp f.2.2 (f.1 i)).mp (Finset.mem_image_of_mem f.1 (Finset.mem_univ i))⟩)
    ⟨fun i j h => f.2.1 (congrArg Subtype.val h), fun s => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ((Finset.ext_iff.mp f.2.2 s).mpr s.2)
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨fun i => (e i : ι), fun i j h => e.injective (Subtype.ext h), by
    ext s
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hs
      exact ⟨e.symm ⟨s, hs⟩, by simp⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    rfl
  right_inv e := by
    ext i
    rfl

/-- The enumerations of `S` form a finite type. -/
noncomputable instance (n : ℕ) (S : Finset ι) : Fintype (Enum n S) := by
  classical
  by_cases hS : S.card = n
  · exact Fintype.ofEquiv _ (enumEquiv n S hS).symm
  · refine ⟨∅, fun f => absurd ?_ hS⟩
    rw [← f.2.2, Finset.card_image_of_injective _ f.2.1, Finset.card_univ, Fintype.card_fin]

/-- **An `n`-element set has `n!` enumerations.** -/
theorem card_enum (n : ℕ) (S : Finset ι) (hS : S.card = n) : Fintype.card (Enum n S) = n.factorial := by
  classical
  rw [Fintype.card_congr (enumEquiv n S hS), Fintype.card_equiv (Fintype.equivOfCardEq (by simp [hS])),
    Fintype.card_fin]

section Embedding

variable {n : ℕ}

/-- **The coefficients of the embedding** `Γₙ → ℓ²(Fin n → ι)`: `(n!)^{-1/2} sign(f) ψ(image f)` on injective tuples. -/
noncomputable def embFun (n : ℕ) (ψ : Finset ι → ℂ) (f : Fin n → ι) : ℂ :=
  if Function.Injective f then ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ) * ψ (Finset.univ.image f)
  else 0

/-- `|sign| = 1`. -/
lemma norm_tupleSign (f : Fin n → ι) : ‖((tupleSign f : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (tupleSign f) with h | h <;> simp [h]

/-- `‖embFun ψ f‖² = ‖ψ(image f)‖² / n!` on injective tuples. -/
lemma norm_embFun_sq (ψ : Finset ι → ℂ) (f : Fin n → ι) :
    ‖embFun n ψ f‖ ^ 2 = if Function.Injective f then ‖ψ (Finset.univ.image f)‖ ^ 2 / n.factorial else 0 := by
  unfold embFun
  split_ifs
  · rw [norm_mul, norm_mul, norm_tupleSign, mul_one, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by positivity)]
    ring
  · simp

/-- The tuples with image `S`. -/
abbrev Fiber (n : ℕ) (S : Finset ι) := {f : Fin n → ι // Finset.univ.image f = S}

/-- A fiber is finite. -/
instance (S : Finset ι) : Finite (Fiber n S) := by
  refine Finite.of_injective (fun f : Fiber n S => fun i : Fin n =>
    (⟨f.1 i, (Finset.ext_iff.mp f.2 (f.1 i)).mp (Finset.mem_image_of_mem f.1 (Finset.mem_univ i))⟩ : S)) fun f g h => ?_
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- A tuple of `n` entries whose image has `n` elements is injective. -/
lemma injective_of_card_image {f : Fin n → ι} (h : (Finset.univ.image f).card = n) : Function.Injective f := by
  have hinj := Finset.card_image_iff.mp (by rw [h, Finset.card_univ, Fintype.card_fin])
  exact fun a b hab => hinj (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab

/-- **The fiber sum**: over the tuples with image `S`, `∑ ‖embFun ψ f‖² = ‖ψ S‖²` if `|S| = n`, and `0` otherwise. -/
lemma hasSum_fiber (ψ : Finset ι → ℂ) (S : Finset ι) :
    HasSum (fun f : Fiber n S => ‖embFun n ψ f.1‖ ^ 2) (if S.card = n then ‖ψ S‖ ^ 2 else 0) := by
  have := Fintype.ofFinite (Fiber n S)
  convert hasSum_fintype (fun f : Fiber n S => ‖embFun n ψ f.1‖ ^ 2) using 1
  simp only [norm_embFun_sq]
  split_ifs with hS
  · have hinj : ∀ f : Fiber n S, Function.Injective f.1 := fun f => injective_of_card_image (by rw [f.2, hS])
    simp only [hinj, if_true]
    rw [Finset.sum_congr rfl fun f _ => by rw [f.2]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : Fintype.card (Fiber n S) = n.factorial := by
      rw [← card_enum n S hS]
      exact Fintype.card_congr ⟨fun f => ⟨f.1, hinj f, f.2⟩, fun f => ⟨f.1, f.2.2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [hcard]
    field_simp
  · refine (Finset.sum_eq_zero fun f _ => ?_).symm
    rw [if_neg]
    intro hf
    apply hS
    rw [← f.2, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]

/-- **`‖Eₙ ψ‖² = ∑_{|S| = n} ‖ψ S‖²`**: the sum over all tuples, arranged by their images. -/
theorem hasSum_norm_embFun (ψ : Finset ι → ℂ) (hψ : Summable fun S => ‖ψ S‖ ^ 2) :
    HasSum (fun f : Fin n → ι => ‖embFun n ψ f‖ ^ 2) (∑' S : Finset ι, if S.card = n then ‖ψ S‖ ^ 2 else 0) := by
  set g : Finset ι → ℝ := fun S => if S.card = n then ‖ψ S‖ ^ 2 else 0 with hg_def
  have hg : Summable g := hψ.of_nonneg_of_le (fun S => by simp only [hg_def]; split_ifs <;> positivity)
    (fun S => by simp only [hg_def]; split_ifs <;> [exact le_rfl; positivity])
  let e := Equiv.sigmaFiberEquiv (fun f : Fin n → ι => Finset.univ.image f)
  rw [← e.hasSum_iff]
  have hfib : ∀ S, HasSum (fun c : Fiber n S => ‖embFun n ψ (e ⟨S, c⟩)‖ ^ 2) (g S) := fun S => hasSum_fiber ψ S
  refine HasSum.sigma_of_hasSum hg.hasSum hfib ?_
  exact (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun S => (hfib S).summable, hg.congr fun S => ((hfib S).tsum_eq).symm⟩

/-- The squares of an `ℓ²` vector are summable. -/
lemma summable_sq_of_lp (ψ : lp (fun _ : Finset ι => ℂ) 2) : Summable fun S => ‖ψ S‖ ^ 2 := by
  have h := (lp.memℓp ψ).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  simpa [Real.rpow_two] using h

/-- **`Eₙ ψ` is square-summable.** -/
lemma memℓp_embFun (ψ : lp (fun _ : Finset ι => ℂ) 2) : Memℓp (embFun n ψ) 2 := by
  refine memℓp_gen ?_
  simpa [Real.rpow_two] using (hasSum_norm_embFun (n := n) ψ (summable_sq_of_lp ψ)).summable

variable (n) in
/-- **The embedding `Eₙ : ℓ²(Finset ι) → ℓ²(Fin n → ι)`**, a linear map. -/
noncomputable def embL : lp (fun _ : Finset ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 where
  toFun ψ := ⟨embFun n ψ, memℓp_embFun ψ⟩
  map_add' ψ φ := by
    apply Subtype.ext
    funext f
    show embFun n (ψ + φ : lp _ 2) f = embFun n ψ f + embFun n φ f
    unfold embFun
    split_ifs <;> simp [lp.coeFn_add] <;> ring
  map_smul' c ψ := by
    apply Subtype.ext
    funext f
    show embFun n (c • ψ : lp _ 2) f = c * embFun n ψ f
    unfold embFun
    split_ifs <;> simp [lp.coeFn_smul] <;> ring

/-- The coefficients of `Eₙ ψ`. -/
lemma embL_apply (ψ : lp (fun _ : Finset ι => ℂ) 2) (f : Fin n → ι) : embL n ψ f = embFun n ψ f := rfl

/-- **`‖Eₙ ψ‖² = ∑_{|S| = n} ‖ψ S‖²`.** -/
lemma norm_sq_embL (ψ : lp (fun _ : Finset ι => ℂ) 2) :
    ‖embL n ψ‖ ^ 2 = ∑' S : Finset ι, if S.card = n then ‖ψ S‖ ^ 2 else 0 := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (embL n ψ)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h.unique (hasSum_norm_embFun ψ (summable_sq_of_lp ψ))

/-- `‖ψ‖² = ∑_S ‖ψ S‖²`. -/
lemma norm_sq_lp (ψ : lp (fun _ : Finset ι => ℂ) 2) : ‖ψ‖ ^ 2 = ∑' S, ‖ψ S‖ ^ 2 := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) ψ
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h.tsum_eq.symm

/-- **`‖Eₙ ψ‖ ≤ ‖ψ‖`.** -/
lemma norm_embL_le (ψ : lp (fun _ : Finset ι => ℂ) 2) : ‖embL n ψ‖ ≤ ‖ψ‖ := by
  have h : ‖embL n ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [norm_sq_embL, norm_sq_lp]
    refine Summable.tsum_le_tsum (fun S => ?_) ?_ (summable_sq_of_lp ψ)
    · split_ifs <;> [exact le_rfl; positivity]
    · exact (summable_sq_of_lp ψ).of_nonneg_of_le (fun S => by split_ifs <;> positivity)
        (fun S => by split_ifs <;> [exact le_rfl; positivity])
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **`Eₙ` is isometric on the `n`-particle vectors.** -/
lemma norm_embL_of_support (ψ : lp (fun _ : Finset ι => ℂ) 2) (hψ : ∀ S : Finset ι, S.card ≠ n → ψ S = 0) :
    ‖embL n ψ‖ = ‖ψ‖ := by
  have h : ‖embL n ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [norm_sq_embL, norm_sq_lp]
    refine tsum_congr fun S => ?_
    split_ifs with hS
    · rfl
    · rw [hψ S hS, norm_zero]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

variable (n) in
/-- **`Eₙ` as a contraction.** -/
noncomputable def embCLM : lp (fun _ : Finset ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 :=
  (embL n).mkContinuous 1 fun ψ => by simpa using norm_embL_le ψ

end Embedding

section Antisym

variable {n : ℕ}

/-- `f ↦ f ∘ σ` on tuples. -/
def permEquiv (σ : Equiv.Perm (Fin n)) : (Fin n → ι) ≃ (Fin n → ι) := σ.symm.arrowCongr (Equiv.refl ι)

/-- `permEquiv σ f = f ∘ σ`. -/
lemma permEquiv_apply (σ : Equiv.Perm (Fin n)) (f : Fin n → ι) : permEquiv σ f = f ∘ σ := by
  funext i; simp [permEquiv, Equiv.arrowCongr_apply]

/-- **The permutation of the slots**, `P_σ Φ (f) = Φ(f ∘ σ)`, an isometry. -/
noncomputable def permL (σ : Equiv.Perm (Fin n)) :
    lp (fun _ : Fin n → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 :=
  (SecondQuantSlot.reindexL (permEquiv (ι := ι) σ)).toLinearIsometry.toContinuousLinearMap

/-- The coefficients of `P_σ Φ`. -/
lemma permL_apply (σ : Equiv.Perm (Fin n)) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (f : Fin n → ι) :
    permL σ Φ f = Φ (f ∘ σ) := by
  show Φ (permEquiv σ f) = _
  rw [permEquiv_apply]

variable (n) in
/-- **The antisymmetrizer** `A = (n!)⁻¹ ∑_σ sign σ P_σ` on `ℓ²(Fin n → ι)`. -/
noncomputable def antisym : lp (fun _ : Fin n → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 :=
  ((n.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • permL (ι := ι) σ

/-- `A Φ (f) = (n!)⁻¹ ∑_σ sign σ Φ(f ∘ σ)`. -/
lemma antisym_apply (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (f : Fin n → ι) :
    antisym n Φ f = (n.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (f ∘ σ) := by
  simp only [antisym, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, permL_apply]
  rw [lp.coeFn_sum] <;> simp [Finset.sum_apply, lp.coeFn_smul, permL_apply]

/-- **`Eₙ ψ` is antisymmetric**: `Eₙ ψ (f ∘ σ) = sign σ · Eₙ ψ (f)`. -/
lemma embFun_comp (ψ : Finset ι → ℂ) (f : Fin n → ι) (σ : Equiv.Perm (Fin n)) :
    embFun n ψ (f ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * embFun n ψ f := by
  unfold embFun
  by_cases hf : Function.Injective f
  · have hfσ : Function.Injective (f ∘ σ) := hf.comp σ.injective
    rw [if_pos hfσ, if_pos hf, tupleSign_comp hf σ]
    have himg : Finset.univ.image (f ∘ σ) = Finset.univ.image f := by
      ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
      exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩, fun ⟨i, hi⟩ => ⟨σ.symm i, by simp [hi]⟩⟩
    rw [himg]
    push_cast
    ring
  · have hfσ : ¬ Function.Injective (f ∘ σ) := fun h => hf (by
      have := h.comp σ.symm.injective
      simpa [Function.comp_def] using this)
    rw [if_neg hfσ, if_neg hf, mul_zero]

/-- **`A Eₙ = Eₙ`**: the embedded vectors are antisymmetric. -/
lemma antisym_embL (ψ : lp (fun _ : Finset ι => ℂ) 2) : antisym n (embL n ψ) = embL n ψ := by
  ext f
  rw [antisym_apply]
  simp only [embL_apply, embFun_comp]
  have hsq : ∀ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := fun σ => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  simp only [← mul_assoc, hsq, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)

/-- `sign σ ² = 1` in `ℂ`. -/
lemma sign_mul_self (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign σ : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- **`A Φ` is antisymmetric**: `A Φ (f ∘ τ) = sign τ · A Φ (f)`. -/
lemma antisym_comp (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (f : Fin n → ι) (τ : Equiv.Perm (Fin n)) :
    antisym n Φ (f ∘ τ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) * antisym n Φ f := by
  have key : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ ((f ∘ τ) ∘ σ) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (f ∘ σ) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft τ⁻¹)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hcomp : (f ∘ ⇑τ) ∘ ⇑(τ⁻¹ * ρ) = f ∘ ⇑ρ := by
      funext x; simp [Equiv.Perm.mul_apply]
    simp only [Equiv.coe_mulLeft, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Units.val_mul, Int.cast_mul]
    simp only [hcomp, mul_assoc]
  rw [antisym_apply, antisym_apply, key]
  ring

/-- **`A Φ` vanishes on non-injective tuples.** -/
lemma antisym_apply_of_not_injective (Φ : lp (fun _ : Fin n → ι => ℂ) 2) {f : Fin n → ι}
    (hf : ¬ Function.Injective f) : antisym n Φ f = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    by_contra h
    push_neg at h
    exact hf fun i j hij => by_contra fun hne => hne (h i j hij)
  have hf' : f ∘ Equiv.swap i j = f := by
    funext x
    by_cases hx : x = i
    · subst hx; simp [Equiv.swap_apply_left, hij]
    · by_cases hy : x = j
      · subst hy; simp [Equiv.swap_apply_right, hij]
      · simp [Equiv.swap_apply_of_ne_of_ne hx hy]
  have h := antisym_comp Φ f (Equiv.swap i j)
  rw [hf', Equiv.Perm.sign_swap hne] at h
  have h2 : (2 : ℂ) * antisym n Φ f = 0 := by
    have : antisym n Φ f = -antisym n Φ f := by simpa using h
    linear_combination this
  simpa using h2

/-- **Summing over the permutations by their value at `0`**: `∑_σ F(σ 0) = n! ∑_k F k`. -/
lemma sum_perm_apply_zero {m : ℕ} (F : Fin (m + 1) → ℂ) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), F (σ 0) = m.factorial * ∑ k, F k := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]

end Antisym

section Counting

/-- A strictly increasing tuple has sign `1`. -/
lemma tupleSign_of_strictMono {m : ℕ} {g : Fin m → ι} (hg : StrictMono g) : tupleSign g = 1 := by
  rw [tupleSign, (Tuple.sort_eq_refl_iff_monotone).mpr hg.monotone]
  exact Equiv.Perm.sign_one

/-- **`∏ᵢ (-1)^{[σ(i+1) < σ 0]} = (-1)^{σ 0}`.** -/
lemma prod_succ_lt_zero {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) :
    (∏ i : Fin m, if σ i.succ < σ 0 then (-1 : ℤˣ) else 1) = (-1) ^ ((σ 0 : Fin (m + 1)) : ℕ) := by
  set G : Fin (m + 1) → ℤˣ := fun j => if j < σ 0 then -1 else 1 with hG
  have h1 : ∏ i : Fin (m + 1), G (σ i) = ∏ j, G j := Equiv.prod_comp σ G
  rw [Fin.prod_univ_succ] at h1
  simp only [hG, lt_irrefl, if_false, one_mul] at h1
  rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1
  rw [show Finset.univ.filter (fun j : Fin (m + 1) => j < σ 0) = Finset.Iio (σ 0) by ext; simp, Fin.card_Iio]

/-- For a strictly increasing `f`, `∏ᵢ (-1)^{[f(σ(i+1)) ≤ f(σ 0)]} = (-1)^{σ 0}`. -/
lemma prod_comp_le_zero {m : ℕ} {f : Fin (m + 1) → ι} (hf : StrictMono f) (σ : Equiv.Perm (Fin (m + 1))) :
    (∏ i : Fin m, if (f ∘ σ) i.succ ≤ f (σ 0) then (-1 : ℤˣ) else 1) = (-1) ^ ((σ 0 : Fin (m + 1)) : ℕ) := by
  rw [← prod_succ_lt_zero σ]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : σ i.succ ≠ σ 0 := fun h => Fin.succ_ne_zero i (σ.injective h)
  have : (f ∘ σ) i.succ ≤ f (σ 0) ↔ σ i.succ < σ 0 := by
    rw [Function.comp_apply, hf.le_iff_le]
    exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
  simp only [this]

/-- For a strictly increasing `f`, the fermion sign of `f k` in the image of `f` is `(-1)^k`. -/
lemma fermiSign_strictMono {m : ℕ} {f : Fin m → ι} (hf : StrictMono f) (k : Fin m) :
    fermiSign ((Finset.univ.image f).erase (f k)) (f k) = (-1) ^ (k : ℕ) := by
  rw [fermiSign]
  congr 1
  have : ((Finset.univ.image f).erase (f k)).filter (· < f k) = (Finset.Iio k).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Iio]
    constructor
    · rintro ⟨⟨-, j, rfl⟩, hj⟩
      exact ⟨j, hf.lt_iff_lt.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨(hf.injective.ne (ne_of_lt hj)), j, rfl⟩, hf hj⟩
  rw [this, Finset.card_image_of_injective _ hf.injective, Fin.card_Iio]

/-- The image of `tail (f ∘ σ)` is the image of `f` without `f (σ 0)`. -/
lemma image_tail_comp {m : ℕ} {f : Fin (m + 1) → ι} (hf : Function.Injective f) (σ : Equiv.Perm (Fin (m + 1))) :
    Finset.univ.image (Fin.tail (f ∘ σ)) = (Finset.univ.image f).erase (f (σ 0)) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, Fin.tail, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨fun h => Fin.succ_ne_zero i (σ.injective (hf h)), σ i.succ, rfl⟩
  · rintro ⟨hx, j, rfl⟩
    have hj : σ.symm j ≠ 0 := fun h => hx (by rw [← h, Equiv.apply_symm_apply])
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hj
    exact ⟨i, by rw [hi, Equiv.apply_symm_apply]⟩

end Counting

section Tensor

variable {n : ℕ}

/-- **The tensor product `c ⊗ Φ`** in coordinates: `(c ⊗ Φ)(f) = c(f 0) Φ(tail f)`. -/
def tensorFun (c : ι → ℂ) (Φ : (Fin n → ι) → ℂ) (f : Fin (n + 1) → ι) : ℂ := c (f 0) * Φ (Fin.tail f)

/-- **`‖c ⊗ Φ‖² = ‖c‖² ‖Φ‖²`.** -/
lemma hasSum_norm_tensorFun {c : ι → ℂ} {Φ : (Fin n → ι) → ℂ} {s t : ℝ}
    (hc : HasSum (fun i => ‖c i‖ ^ 2) s) (hΦ : HasSum (fun g => ‖Φ g‖ ^ 2) t) :
    HasSum (fun f => ‖tensorFun c Φ f‖ ^ 2) (s * t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).hasSum_iff]
  have hfun : (fun f : Fin (n + 1) → ι => ‖tensorFun c Φ f‖ ^ 2) ∘ Fin.consEquiv (fun _ : Fin (n + 1) => ι) =
      fun x : ι × (Fin n → ι) => ‖c x.1‖ ^ 2 * ‖Φ x.2‖ ^ 2 := by
    funext x
    have hx : (Fin.consEquiv (fun _ : Fin (n + 1) => ι)) x = Fin.cons x.1 x.2 :=
      funext fun i => Fin.consEquiv_apply (fun _ : Fin (n + 1) => ι) x i
    simp only [Function.comp_apply, hx, tensorFun, Fin.cons_zero, Fin.tail_cons, norm_mul, mul_pow]
  rw [hfun]
  refine hc.mul hΦ ?_
  refine summable_mul_of_summable_norm (f := fun i => ‖c i‖ ^ 2) (g := fun g => ‖Φ g‖ ^ 2) ?_ ?_
  · simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hc.summable
  · simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hΦ.summable

end Tensor

section TensorCre

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (b : HilbertBasis ι ℂ Z)
variable {n : ℕ}

/-- `‖Φ‖²` as a sum of squares. -/
lemma hasSum_norm_sq_lp {α : Type*} (Φ : lp (fun _ : α => ℂ) 2) : HasSum (fun a => ‖Φ a‖ ^ 2) (‖Φ‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) Φ
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- `w ⊗ Φ` is square-summable. -/
lemma memℓp_tensorFun (w : Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) : Memℓp (tensorFun (b.repr w) Φ) 2 := by
  refine memℓp_gen ?_
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (hasSum_norm_tensorFun (SecondQuantSlot.hasSum_repr_sq b w) (hasSum_norm_sq_lp Φ)).summable

/-- **Creation on the tensor power**, `Φ ↦ w ⊗ Φ`, a linear map. -/
noncomputable def creTL (w : Z) : lp (fun _ : Fin n → ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : Fin (n + 1) → ι => ℂ) 2 where
  toFun Φ := ⟨tensorFun (b.repr w) Φ, memℓp_tensorFun b w Φ⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    funext f
    show tensorFun (b.repr w) (Φ + Ψ : lp _ 2) f = tensorFun (b.repr w) Φ f + tensorFun (b.repr w) Ψ f
    simp [tensorFun, lp.coeFn_add, mul_add]
  map_smul' c Φ := by
    apply Subtype.ext
    funext f
    show tensorFun (b.repr w) (c • Φ : lp _ 2) f = c * tensorFun (b.repr w) Φ f
    simp [tensorFun, lp.coeFn_smul]
    ring

/-- The coefficients of `w ⊗ Φ`. -/
lemma creTL_apply (w : Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (f : Fin (n + 1) → ι) :
    creTL b w Φ f = b.repr w (f 0) * Φ (Fin.tail f) := rfl

/-- **`‖w ⊗ Φ‖ = ‖w‖ ‖Φ‖`.** -/
lemma norm_creTL (w : Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) : ‖creTL b w Φ‖ = ‖w‖ * ‖Φ‖ := by
  have h1 := hasSum_norm_sq_lp (creTL b w Φ)
  have h2 := hasSum_norm_tensorFun (SecondQuantSlot.hasSum_repr_sq b w) (hasSum_norm_sq_lp Φ)
  have h : ‖creTL b w Φ‖ ^ 2 = (‖w‖ * ‖Φ‖) ^ 2 := by rw [mul_pow]; exact h1.unique h2
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- **Creation on the tensor power** as a bounded operator of norm `≤ ‖w‖`. -/
noncomputable def creT (w : Z) : lp (fun _ : Fin n → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin (n + 1) → ι => ℂ) 2 :=
  (creTL b w).mkContinuous ‖w‖ fun Φ => (norm_creTL b w Φ).le

/-- The coefficients of `creT`. -/
lemma creT_apply (w : Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (f : Fin (n + 1) → ι) :
    creT b w Φ f = b.repr w (f 0) * Φ (Fin.tail f) := rfl

/-- **`h` on slot `0` of `w ⊗ Φ` is `(h w) ⊗ Φ`.** -/
lemma slotOp_zero_creT (h : Z →L[ℂ] Z) (w : Z) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    SecondQuantSlot.slotOp b 0 h (creT b w Φ) = creT b (h w) Φ := by
  ext f
  set e := SecondQuantSlot.slotEquiv (ι := ι) (n := n) 0
  have he : ∀ g : Fin (n + 1) → ι, e g = (Fin.tail g, g 0) := fun g => by
    simp [e, SecondQuantSlot.slotEquiv, Fin.insertNthEquiv, Fin.removeNth_zero]
  have hesymm : ∀ (m : Fin n → ι) (k : ι), e.symm (m, k) = Fin.cons k m := fun m k => by
    apply e.injective
    rw [Equiv.apply_symm_apply, he, Fin.tail_cons, Fin.cons_zero]
  have hfib : ∀ m : Fin n → ι, SecondQuantSlot.fiber
      ((SecondQuantSlot.reindexL e).symm (creT b w Φ)) m = Φ m • b.repr w := fun m => by
    ext k
    show (creT b w Φ) (e.symm (m, k)) = (Φ m • b.repr w) k
    rw [hesymm, creT_apply, Fin.cons_zero, Fin.tail_cons, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  show (SecondQuantSlot.slotC b h ((SecondQuantSlot.reindexL e).symm (creT b w Φ))) (e f) = creT b (h w) Φ f
  rw [he f, creT_apply]
  show b.repr ((SecondQuantSlot.slotMap h (SecondQuantSlot.uncoordL b
      ((SecondQuantSlot.reindexL e).symm (creT b w Φ)))) (Fin.tail f)) (f 0) = _
  rw [SecondQuantSlot.slotMap_apply]
  show b.repr (h (b.repr.symm (SecondQuantSlot.fiber ((SecondQuantSlot.reindexL e).symm (creT b w Φ)) (Fin.tail f))))
    (f 0) = _
  rw [hfib, map_smul, LinearIsometryEquiv.symm_apply_apply, map_smul, map_smul, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, mul_comm]

/-- `removeNth (j + 1) g = cons (g 0) (removeNth j (tail g))`. -/
lemma removeNth_succ_eq {m : ℕ} (j : Fin (m + 1)) (g : Fin (m + 2) → ι) :
    Fin.removeNth j.succ g = Fin.cons (g 0) (Fin.removeNth j (Fin.tail g)) := by
  set p := Fin.removeNth j.succ g with hp
  have key : g = Fin.insertNth j.succ (g j.succ) p := (Fin.insertNth_self_removeNth j.succ g).symm
  rw [← Fin.cons_self_tail p, Fin.insertNth_succ_cons] at key
  have h0 : g 0 = p 0 := by rw [key]; rfl
  have ht : Fin.tail g = Fin.insertNth j (g j.succ) (Fin.tail p) := by
    conv_lhs => rw [key]
    exact Fin.tail_cons _ _
  rw [ht, Fin.removeNth_insertNth, h0, Fin.cons_self_tail]

/-- **`h` on slot `j + 1` of `w ⊗ Φ` is `w ⊗ (h on slot j of Φ)`.** -/
lemma slotOp_succ_creT {m : ℕ} (j : Fin (m + 1)) (h : Z →L[ℂ] Z) (w : Z) (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.slotOp b j.succ h (creT b w Φ) = creT b w (SecondQuantSlot.slotOp b j h Φ) := by
  ext f
  set e := SecondQuantSlot.slotEquiv (ι := ι) (n := m + 1) j.succ
  set e' := SecondQuantSlot.slotEquiv (ι := ι) (n := m) j
  have he : ∀ g : Fin (m + 2) → ι, e g = (Fin.removeNth j.succ g, g j.succ) := fun g => by
    simp [e, SecondQuantSlot.slotEquiv, Fin.insertNthEquiv]
  have he' : ∀ g : Fin (m + 1) → ι, e' g = (Fin.removeNth j g, g j) := fun g => by
    simp [e', SecondQuantSlot.slotEquiv, Fin.insertNthEquiv]
  have hesymm : ∀ (p : Fin (m + 1) → ι) (k : ι), e.symm (p, k) = Fin.insertNth j.succ k p := fun p k => by
    apply e.injective
    rw [Equiv.apply_symm_apply, he, Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  have he'symm : ∀ (q : Fin m → ι) (k : ι), e'.symm (q, k) = Fin.insertNth j k q := fun q k => by
    apply e'.injective
    rw [Equiv.apply_symm_apply, he', Fin.removeNth_insertNth, Fin.insertNth_apply_same]
  have hfib : ∀ p : Fin (m + 1) → ι, SecondQuantSlot.fiber ((SecondQuantSlot.reindexL e).symm (creT b w Φ)) p =
      b.repr w (p 0) • SecondQuantSlot.fiber ((SecondQuantSlot.reindexL e').symm Φ) (Fin.tail p) := fun p => by
    ext k
    show (creT b w Φ) (e.symm (p, k)) = (b.repr w (p 0) • SecondQuantSlot.fiber
      ((SecondQuantSlot.reindexL e').symm Φ) (Fin.tail p)) k
    rw [hesymm, creT_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [← Fin.cons_self_tail p, Fin.insertNth_succ_cons, Fin.cons_zero, Fin.tail_cons]
    show _ = b.repr w (p 0) * Φ (e'.symm (Fin.tail p, k))
    rw [he'symm]
  show (SecondQuantSlot.slotC b h ((SecondQuantSlot.reindexL e).symm (creT b w Φ))) (e f) =
    creT b w (SecondQuantSlot.slotOp b j h Φ) f
  rw [he f, creT_apply]
  show b.repr ((SecondQuantSlot.slotMap h (SecondQuantSlot.uncoordL b
      ((SecondQuantSlot.reindexL e).symm (creT b w Φ)))) (Fin.removeNth j.succ f)) (f j.succ) =
    b.repr w (f 0) * (SecondQuantSlot.slotC b h ((SecondQuantSlot.reindexL e').symm Φ)) (e' (Fin.tail f))
  rw [SecondQuantSlot.slotMap_apply, he' (Fin.tail f)]
  show b.repr (h (b.repr.symm (SecondQuantSlot.fiber ((SecondQuantSlot.reindexL e).symm (creT b w Φ))
      (Fin.removeNth j.succ f)))) (f j.succ) =
    b.repr w (f 0) * b.repr (h (b.repr.symm (SecondQuantSlot.fiber ((SecondQuantSlot.reindexL e').symm Φ)
      (Fin.removeNth j (Fin.tail f))))) (Fin.tail f j)
  rw [hfib, removeNth_succ_eq, Fin.cons_zero, Fin.tail_cons, map_smul, map_smul, map_smul, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rfl

/-- **The commutator on the tensor power**: `(∑ⱼ hⱼ)(w ⊗ Φ) = (h w) ⊗ Φ + w ⊗ (∑ⱼ hⱼ) Φ`, i.e.
`[dΓ(h), a*(w)] = a*(h w)` before antisymmetrization (Dereziński, Section 5.2 and Theorem 18 (4), p. 22). -/
theorem dGammaTensor_creT {m : ℕ} (h : Z →L[ℂ] Z) (w : Z) (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.dGammaTensor b (m + 1) h (creT b w Φ) =
      creT b (h w) Φ + creT b w (SecondQuantSlot.dGammaTensor b m h Φ) := by
  rw [SecondQuantSlot.dGammaTensor, Fin.sum_univ_succ, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    slotOp_zero_creT, SecondQuantSlot.dGammaTensor, ContinuousLinearMap.sum_apply, map_sum]
  simp only [slotOp_succ_creT]

/-- On one particle `(∑ⱼ hⱼ)(w ⊗ Φ) = (h w) ⊗ Φ`. -/
theorem dGammaTensor_zero_creT (h : Z →L[ℂ] Z) (w : Z) (Φ : lp (fun _ : Fin 0 → ι => ℂ) 2) :
    SecondQuantSlot.dGammaTensor b 0 h (creT b w Φ) = creT b (h w) Φ := by
  rw [SecondQuantSlot.dGammaTensor, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, slotOp_zero_creT]

/-- `(slotEquiv j).symm (m, k) = insertNth j k m`. -/
lemma slotEquiv_symm_apply {m : ℕ} (j : Fin (m + 1)) (q : Fin m → ι) (k : ι) :
    (SecondQuantSlot.slotEquiv (ι := ι) j).symm (q, k) = Fin.insertNth j k q := by
  simp [SecondQuantSlot.slotEquiv, Fin.insertNthEquiv]

/-- **The coefficients of `h` on slot `j`**: the `f j`-th coordinate of `h` applied to the vector with coefficients
`k ↦ Φ(f with k in slot j)`. -/
lemma slotOp_apply_eq {m : ℕ} (j : Fin (m + 1)) (h : Z →L[ℂ] Z) (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2)
    (f : Fin (m + 1) → ι) :
    SecondQuantSlot.slotOp b j h Φ f = b.repr (h (b.repr.symm (SecondQuantSlot.fiber
      ((SecondQuantSlot.reindexL (SecondQuantSlot.slotEquiv j)).symm Φ) (Fin.removeNth j f)))) (f j) := by
  have he : SecondQuantSlot.slotEquiv (ι := ι) j f = (Fin.removeNth j f, f j) := by
    simp [SecondQuantSlot.slotEquiv, Fin.insertNthEquiv]
  show (SecondQuantSlot.slotC b h ((SecondQuantSlot.reindexL (SecondQuantSlot.slotEquiv j)).symm Φ))
    (SecondQuantSlot.slotEquiv j f) = _
  rw [he]
  rfl

/-- **Slots are permuted covariantly**: `h` on slot `σ j` after `P_σ` is `P_σ` after `h` on slot `j`. -/
lemma slotOp_permL {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) (h : Z →L[ℂ] Z)
    (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.slotOp b (σ j) h (permL σ Φ) = permL σ (SecondQuantSlot.slotOp b j h Φ) := by
  ext f
  have hfib : SecondQuantSlot.fiber ((SecondQuantSlot.reindexL (SecondQuantSlot.slotEquiv (σ j))).symm (permL σ Φ))
      (Fin.removeNth (σ j) f) =
      SecondQuantSlot.fiber ((SecondQuantSlot.reindexL (SecondQuantSlot.slotEquiv j)).symm Φ)
        (Fin.removeNth j (f ∘ σ)) := by
    ext k
    show (permL σ Φ) ((SecondQuantSlot.slotEquiv (σ j)).symm (Fin.removeNth (σ j) f, k)) =
      Φ ((SecondQuantSlot.slotEquiv j).symm (Fin.removeNth j (f ∘ σ), k))
    rw [slotEquiv_symm_apply, slotEquiv_symm_apply, permL_apply, Fin.insertNth_removeNth, Fin.insertNth_removeNth,
      Function.update_comp_equiv, Equiv.symm_apply_apply]
  rw [permL_apply, slotOp_apply_eq, slotOp_apply_eq, hfib, Function.comp_apply]

/-- **`∑ⱼ hⱼ` commutes with the slot permutations.** -/
theorem dGammaTensor_permL {m : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (h : Z →L[ℂ] Z)
    (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.dGammaTensor b m h (permL σ Φ) = permL σ (SecondQuantSlot.dGammaTensor b m h Φ) := by
  simp only [SecondQuantSlot.dGammaTensor, ContinuousLinearMap.sum_apply, map_sum]
  rw [← Equiv.sum_comp σ]
  exact Finset.sum_congr rfl fun j _ => slotOp_permL b σ j h Φ

/-- **`∑ⱼ hⱼ` commutes with the antisymmetrizer.** -/
theorem dGammaTensor_antisym {m : ℕ} (h : Z →L[ℂ] Z) (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.dGammaTensor b m h (antisym (m + 1) Φ) = antisym (m + 1) (SecondQuantSlot.dGammaTensor b m h Φ) := by
  simp only [antisym, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, map_smul, map_sum,
    dGammaTensor_permL]

end TensorCre

section Core

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (b : HilbertBasis ι ℂ Z)
variable {n : ℕ}

/-- The normalisation `((n+1)!)^{-1/2} = √(n+1) n! / ((n+1)! √(n!))`. -/
lemma factorial_sqrt_identity (n : ℕ) :
    ((Real.sqrt (n + 1).factorial)⁻¹ : ℝ) =
      Real.sqrt (n + 1) * ((n + 1).factorial : ℝ)⁻¹ * n.factorial * (Real.sqrt n.factorial)⁻¹ := by
  have h1 : (0 : ℝ) < n + 1 := by positivity
  have h2 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have ha := Real.sq_sqrt h1.le
  have hc := Real.sq_sqrt h2.le
  have ha0 : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.mpr h1
  have hc0 : 0 < Real.sqrt n.factorial := Real.sqrt_pos.mpr h2
  have e1 : (Real.sqrt (n + 1))⁻¹ = Real.sqrt (n + 1) * ((n : ℝ) + 1)⁻¹ := by
    rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Real.sqrt_mul h1.le, mul_inv, e1]
  field_simp

/-- **The core identity on sorted tuples**: `Eₙ₊₁ (a*(w) ψ)(f) = √(n+1) (A (w ⊗ Eₙ ψ))(f)` for strictly increasing `f`. -/
lemma embFun_creW_strictMono (w : Z) (ψ : FermiL2 ι) {f : Fin (n + 1) → ι} (hf : StrictMono f) :
    embFun (n + 1) (creWCoeff b w ψ) f =
      (Real.sqrt (n + 1) : ℂ) * antisym (n + 1) (creT b w (embL n ψ)) f := by
  have hinj := hf.injective
  set T := Finset.univ.image f with hT
  set F : Fin (n + 1) → ℂ := fun k => (-1 : ℂ) ^ (k : ℕ) * (b.repr w (f k) * ψ (T.erase (f k))) with hF
  have hL : embFun (n + 1) (creWCoeff b w ψ) f = ((Real.sqrt (n + 1).factorial)⁻¹ : ℝ) * ∑ k, F k := by
    rw [embFun, if_pos hinj, tupleSign_of_strictMono hf, creWCoeff_apply, ← hT,
      Finset.sum_image (fun i _ j _ h => hinj h)]
    simp only [Units.val_one, Int.cast_one, mul_one, Complex.ofReal_inv]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [creFun, if_pos (Finset.mem_image_of_mem f (Finset.mem_univ k)), hF, fermiSign_strictMono hf]
    ring
  have hs : ∀ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((tupleSign (Fin.tail (f ∘ σ)) : ℤ) : ℂ) = (-1 : ℂ) ^ ((σ 0 : Fin (n + 1)) : ℕ) := fun σ => by
    have hinjσ : Function.Injective (f ∘ σ) := hinj.comp σ.injective
    have hcons : (Fin.cons ((f ∘ σ) 0) (Fin.tail (f ∘ σ)) : Fin (n + 1) → ι) = f ∘ σ := Fin.cons_self_tail _
    have hc := tupleSign_cons ((f ∘ σ) 0) (Fin.tail (f ∘ σ)) (by rw [hcons]; exact hinjσ)
    rw [hcons, tupleSign_comp hinj σ, tupleSign_of_strictMono hf, mul_one] at hc
    have hprod : (∏ i : Fin n, if Fin.tail (f ∘ σ) i ≤ (f ∘ σ) 0 then (-1 : ℤˣ) else 1) =
        (-1) ^ ((σ 0 : Fin (n + 1)) : ℕ) := prod_comp_le_zero hf σ
    rw [hprod] at hc
    rw [hc]
    have ht : ((tupleSign (Fin.tail (f ∘ σ)) : ℤ) : ℂ) * ((tupleSign (Fin.tail (f ∘ σ)) : ℤ) : ℂ) = 1 := by
      rcases Int.units_eq_one_or (tupleSign (Fin.tail (f ∘ σ))) with h | h <;> simp [h]
    push_cast
    linear_combination ((-1 : ℂ) ^ ((σ 0 : Fin (n + 1)) : ℕ)) * ht
  have hR : antisym (n + 1) (creT b w (embL n ψ)) f =
      ((n + 1).factorial : ℂ)⁻¹ * (((Real.sqrt n.factorial)⁻¹ : ℝ) * ∑ σ : Equiv.Perm (Fin (n + 1)), F (σ 0)) := by
    rw [antisym_apply]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have htinj : Function.Injective (Fin.tail (f ∘ σ)) := fun i j h =>
      Fin.succ_injective _ ((hinj.comp σ.injective) h)
    rw [creT_apply, embL_apply, embFun, if_pos htinj, image_tail_comp hinj σ]
    simp only [Function.comp_apply, hF, Complex.ofReal_inv]
    linear_combination (((Real.sqrt n.factorial : ℝ) : ℂ)⁻¹ * b.repr w (f (σ 0)) * ψ (T.erase (f (σ 0)))) * hs σ
  rw [hL, hR, sum_perm_apply_zero]
  have key : (((Real.sqrt (n + 1).factorial)⁻¹ : ℝ) : ℂ) = ((Real.sqrt (n + 1) * ((n + 1).factorial : ℝ)⁻¹ *
      n.factorial * (Real.sqrt n.factorial)⁻¹ : ℝ) : ℂ) := by rw [factorial_sqrt_identity n]
  rw [key]
  push_cast
  ring

/-- **The core identity** (D4d): `Eₙ₊₁ (a*(w) ψ) = √(n+1) A (w ⊗ Eₙ ψ)` coefficientwise. -/
theorem embFun_creW (w : Z) (ψ : FermiL2 ι) (f : Fin (n + 1) → ι) :
    embFun (n + 1) (creWCoeff b w ψ) f =
      (Real.sqrt (n + 1) : ℂ) * antisym (n + 1) (creT b w (embL n ψ)) f := by
  by_cases hf : Function.Injective f
  · have hg : StrictMono (f ∘ Tuple.sort f) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
    have hfg : f = (f ∘ Tuple.sort f) ∘ ⇑(Tuple.sort f)⁻¹ := by
      funext x; simp [Equiv.Perm.inv_def]
    rw [hfg, embFun_comp, antisym_comp, embFun_creW_strictMono b w ψ hg]
    ring
  · rw [embFun, if_neg hf, antisym_apply_of_not_injective _ hf, mul_zero]

/-- **`Eₙ₊₁ a*(w) = √(n+1) A C_w Eₙ`** on `ℓ²(Finset ι)`. -/
theorem embL_creW (w : Z) (ψ : FermiL2 ι) :
    embL (n + 1) (creWCoeff b w ψ) = (Real.sqrt (n + 1) : ℂ) • antisym (n + 1) (creT b w (embL n ψ)) := by
  ext f
  rw [embL_apply, embFun_creW, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

end Core

section EmbAdjoint

variable {n : ℕ}

/-- Two injective tuples with the same image differ by a permutation. -/
lemma exists_perm_of_image_eq {f g : Fin n → ι} (hf : Function.Injective f) (hg : Function.Injective g)
    (h : Finset.univ.image g = Finset.univ.image f) : ∃ σ : Equiv.Perm (Fin n), f ∘ σ = g := by
  have hr : Set.range g = Set.range f := by
    have := congrArg (fun s : Finset ι => (s : Set ι)) h
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using this
  let τ : Fin n → Fin n := fun i => (Equiv.ofInjective f hf).symm ⟨g i, by rw [← hr]; exact ⟨i, rfl⟩⟩
  have hτ : ∀ i, f (τ i) = g i := fun i => Equiv.apply_ofInjective_symm hf _
  have hτi : Function.Injective τ := fun i j h => hg (by rw [← hτ i, ← hτ j, h])
  exact ⟨Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτi), funext fun i => hτ i⟩

/-- The coefficient of `Eₙ e_{image f}` at `f`. -/
lemma embFun_single_self {f : Fin n → ι} (hf : Function.Injective f) :
    embFun n (lp.single (E := fun _ : Finset ι => ℂ) 2 (Finset.univ.image f) (1 : ℂ)) f =
      ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ) := by
  rw [embFun, if_pos hf, lp.single_apply_self, mul_one]

/-- `Eₙ e_T` vanishes off the enumerations of `T`. -/
lemma embFun_single_eq_zero {T : Finset ι} {g : Fin n → ι}
    (hg : ¬ (Function.Injective g ∧ Finset.univ.image g = T)) : embFun n (lp.single (E := fun _ : Finset ι => ℂ) 2 T (1 : ℂ)) g = 0 := by
  unfold embFun
  split_ifs with hinj
  · rw [lp.single_apply_ne _ _ _ (fun h => hg ⟨hinj, h⟩), mul_zero]
  · rfl

/-- **The inner product against `Eₙ e_{image f}`**: `⟪Eₙ e_{image f}, Φ⟫ = (n!)^{-1/2} sign f ∑_σ sign σ Φ(f ∘ σ)`. -/
lemma inner_embL_single {f : Fin n → ι} (hf : Function.Injective f) (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    inner ℂ (embL n (lp.single (E := fun _ : Finset ι => ℂ) 2 (Finset.univ.image f) (1 : ℂ))) Φ =
      ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ) *
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (f ∘ σ) := by
  set e := lp.single (E := fun _ : Finset ι => ℂ) 2 (Finset.univ.image f) (1 : ℂ) with he
  have hinjσ : Function.Injective (fun σ : Equiv.Perm (Fin n) => f ∘ ⇑σ) := fun σ τ h =>
    Equiv.ext fun i => hf (congrFun h i)
  rw [lp.inner_eq_tsum, tsum_eq_sum (s := Finset.univ.image (fun σ : Equiv.Perm (Fin n) => f ∘ ⇑σ)),
    Finset.sum_image (fun σ _ τ _ h => hinjσ h), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [embL_apply, embFun_comp, he, embFun_single_self hf, RCLike.inner_apply']
    simp only [map_mul, map_intCast, Complex.conj_ofReal, map_inv₀]
    ring
  · intro g hg
    have h0 : embFun n e g = 0 := by
      refine embFun_single_eq_zero fun ⟨hginj, himg⟩ => hg ?_
      obtain ⟨σ, hσ⟩ := exists_perm_of_image_eq hf hginj himg
      exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
    rw [embL_apply, h0, inner_zero_left]

/-- **The coefficients of `Eₙ*`**: `(Eₙ* Φ)(T) = ⟪Eₙ e_T, Φ⟫`. -/
lemma adjoint_embCLM_apply (Φ : lp (fun _ : Fin n → ι => ℂ) 2) (T : Finset ι) :
    ContinuousLinearMap.adjoint (embCLM n) Φ T = inner ℂ (embL n (lp.single (E := fun _ : Finset ι => ℂ) 2 T (1 : ℂ))) Φ := by
  have h := lp.inner_single_left (𝕜 := ℂ) T (1 : ℂ) (ContinuousLinearMap.adjoint (embCLM n) Φ)
  rw [ContinuousLinearMap.adjoint_inner_right, RCLike.inner_apply', map_one, one_mul] at h
  exact h.symm

/-- **`Eₙ*` takes values in the `n`-particle vectors.** -/
lemma adjoint_embCLM_apply_of_card (Φ : lp (fun _ : Fin n → ι => ℂ) 2) {T : Finset ι} (hT : T.card ≠ n) :
    ContinuousLinearMap.adjoint (embCLM n) Φ T = 0 := by
  rw [adjoint_embCLM_apply]
  have : embL n (lp.single (E := fun _ : Finset ι => ℂ) 2 T (1 : ℂ)) = 0 := by
    ext g
    rw [embL_apply, embFun_single_eq_zero fun ⟨hginj, himg⟩ => hT (by
      rw [← himg, Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_fin])]
    rfl
  rw [this, inner_zero_left]

/-- The coefficients of `Eₙ*` at the image of an injective tuple. -/
lemma adjoint_embCLM_apply_image (Φ : lp (fun _ : Fin n → ι => ℂ) 2) {f : Fin n → ι} (hf : Function.Injective f) :
    ContinuousLinearMap.adjoint (embCLM n) Φ (Finset.univ.image f) =
      ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ) *
        ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (f ∘ σ) := by
  rw [adjoint_embCLM_apply, inner_embL_single hf]

/-- `((n!)^{-1/2})² = (n!)⁻¹` and `sign² = 1`. -/
lemma sqrt_sign_sq (f : Fin n → ι) :
    (((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ)) *
      (((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ)) = (n.factorial : ℂ)⁻¹ := by
  have hs : ((tupleSign f : ℤ) : ℂ) * ((tupleSign f : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or (tupleSign f) with h | h <;> simp [h]
  have hr : ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) = (n.factorial : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  linear_combination ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * hs + hr

/-- **`Eₙ Eₙ* = A`.** -/
theorem embCLM_adjoint_apply (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    embCLM n (ContinuousLinearMap.adjoint (embCLM n) Φ) = antisym n Φ := by
  ext f
  show embL n _ f = _
  by_cases hf : Function.Injective f
  · rw [embL_apply, embFun, if_pos hf, adjoint_embCLM_apply_image Φ hf, antisym_apply, ← mul_assoc,
      sqrt_sign_sq]
  · rw [embL_apply, embFun, if_neg hf, antisym_apply_of_not_injective _ hf]

/-- **`Eₙ* Eₙ = 1` on the `n`-particle vectors.** -/
theorem adjoint_embCLM_embCLM (ψ : lp (fun _ : Finset ι => ℂ) 2) (hψ : ∀ S : Finset ι, S.card ≠ n → ψ S = 0) :
    ContinuousLinearMap.adjoint (embCLM n) (embCLM n ψ) = ψ := by
  ext T
  by_cases hT : T.card = n
  · obtain ⟨⟨f, hf, rfl⟩⟩ : Nonempty (Enum n T) := by
      rw [← Fintype.card_pos_iff, card_enum n T hT]
      exact Nat.factorial_pos n
    rw [adjoint_embCLM_apply_image _ hf]
    have hterm : ∀ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * embCLM n ψ (f ∘ σ) =
        embL n ψ f := fun σ => by
      show _ * embL n ψ (f ∘ σ) = _
      rw [embL_apply, embFun_comp, ← mul_assoc, sign_mul_self, one_mul, embL_apply]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul,
      embL_apply, embFun, if_pos hf]
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    calc ((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ) *
          (n.factorial * (((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ) *
            ψ (Finset.univ.image f)))
        = ((((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ)) *
            (((Real.sqrt n.factorial : ℝ)⁻¹ : ℂ) * ((tupleSign f : ℤ) : ℂ))) * n.factorial *
              ψ (Finset.univ.image f) := by ring
      _ = ψ (Finset.univ.image f) := by rw [sqrt_sign_sq, inv_mul_cancel₀ hn, one_mul]
  · rw [adjoint_embCLM_apply_of_card _ hT, hψ T hT]

/-- **`Eₙ* A = Eₙ*`.** -/
theorem adjoint_embCLM_antisym (Φ : lp (fun _ : Fin n → ι => ℂ) 2) :
    ContinuousLinearMap.adjoint (embCLM n) (antisym n Φ) = ContinuousLinearMap.adjoint (embCLM n) Φ := by
  ext T
  by_cases hT : T.card = n
  · obtain ⟨⟨f, hf, rfl⟩⟩ : Nonempty (Enum n T) := by
      rw [← Fintype.card_pos_iff, card_enum n T hT]
      exact Nat.factorial_pos n
    rw [adjoint_embCLM_apply_image _ hf, adjoint_embCLM_apply_image _ hf]
    congr 1
    have hterm : ∀ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * antisym n Φ (f ∘ σ) = antisym n Φ f :=
      fun σ => by rw [antisym_comp, ← mul_assoc, sign_mul_self, one_mul]
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    rw [antisym_apply, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  · rw [adjoint_embCLM_apply_of_card _ hT, adjoint_embCLM_apply_of_card _ hT]

end EmbAdjoint

section Gamma

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z] (b : HilbertBasis ι ℂ Z)

/-- `‖Eₙ‖ ≤ 1`. -/
lemma norm_embCLM_le (n : ℕ) : ‖embCLM (ι := ι) n‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **`dΓₙ₊₁(h)` on the fermionic Fock space**: `Eₙ₊₁* (∑ⱼ hⱼ) Eₙ₊₁`, with `∑ⱼ hⱼ` acting on the coordinate tensor power
`ℓ²(Fin (n+1) → ι)` (J. Dereziński, arXiv:math-ph/0511030, Section 5.2: `dΓₙ(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1`, restricted to the
antisymmetric subspace). -/
noncomputable def dGammaFock (n : ℕ) (h : Z →L[ℂ] Z) :
    lp (fun _ : Finset ι => ℂ) 2 →L[ℂ] lp (fun _ : Finset ι => ℂ) 2 :=
  ContinuousLinearMap.adjoint (embCLM (n + 1)) ∘L SecondQuantSlot.dGammaTensor b n h ∘L embCLM (n + 1)

/-- **`‖dΓₙ₊₁(h)‖ ≤ (n + 1) ‖h‖`.** -/
theorem norm_dGammaFock_le (n : ℕ) (h : Z →L[ℂ] Z) : ‖dGammaFock b n h‖ ≤ (n + 1) * ‖h‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans ?_
  rw [LinearIsometryEquiv.norm_map, ← mul_assoc]
  calc ‖embCLM (ι := ι) (n + 1)‖ * ‖SecondQuantSlot.dGammaTensor b n h‖ * ‖embCLM (ι := ι) (n + 1)‖
      ≤ 1 * ((n + 1) * ‖h‖) * 1 := by
        gcongr
        · exact norm_embCLM_le _
        · exact SecondQuantSlot.norm_dGammaTensor_le b n h
        · exact norm_embCLM_le _
    _ = (n + 1) * ‖h‖ := by ring

/-- **`a*(w)` raises the particle number by one.** -/
lemma creWCoeff_apply_of_card (w : Z) (ψ : FermiL2 ι) {m : ℕ} (hψ : ∀ S : Finset ι, S.card ≠ m → ψ S = 0)
    {T : Finset ι} (hT : T.card ≠ m + 1) : creWCoeff b w ψ T = 0 := by
  rw [creWCoeff_apply]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hpos := Finset.card_pos.mpr ⟨j, hj⟩
  rw [creFun, if_pos hj, hψ _ (by rw [Finset.card_erase_of_mem hj]; omega), mul_zero, mul_zero]

/-- **`dΓ(h)` keeps the particle number**: `dΓₙ₊₁(h)` takes values in the `(n+1)`-particle vectors. -/
lemma dGammaFock_apply_of_card (n : ℕ) (h : Z →L[ℂ] Z) (ψ : FermiL2 ι) {S : Finset ι} (hS : S.card ≠ n + 1) :
    dGammaFock b n h ψ S = 0 :=
  adjoint_embCLM_apply_of_card _ hS

/-- **The commutator `[dΓ(h), a*(w)] = a*(hw)` on the `(n+1)`-particle vectors**:
`dΓₙ₊₂(h) a*(w) ψ = a*(hw) ψ + a*(w) dΓₙ₊₁(h) ψ`. -/
theorem dGammaFock_creW (n : ℕ) (h : Z →L[ℂ] Z) (w : Z) (ψ : FermiL2 ι)
    (hψ : ∀ S : Finset ι, S.card ≠ n + 1 → ψ S = 0) :
    dGammaFock b (n + 1) h (creWCoeff b w ψ) = creWCoeff b (h w) ψ + creWCoeff b w (dGammaFock b n h ψ) := by
  set c : ℂ := (Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) : ℂ) with hcdef
  have hc : ∀ (w' : Z) (φ : FermiL2 ι), embCLM (n + 2) (creWCoeff b w' φ) =
      c • antisym (n + 2) (creT b w' (embCLM (n + 1) φ)) := fun w' φ => embL_creW b w' φ
  have hY : antisym (n + 1) (SecondQuantSlot.dGammaTensor b n h (embCLM (n + 1) ψ)) =
      SecondQuantSlot.dGammaTensor b n h (embCLM (n + 1) ψ) := by
    rw [← dGammaTensor_antisym]
    exact congrArg (fun Φ => SecondQuantSlot.dGammaTensor b n h Φ) (antisym_embL (n := n + 1) ψ)
  have h2 : embCLM (n + 2) (creWCoeff b w (dGammaFock b n h ψ)) =
      c • antisym (n + 2) (creT b w (SecondQuantSlot.dGammaTensor b n h (embCLM (n + 1) ψ))) := by
    rw [hc, show dGammaFock b n h ψ = ContinuousLinearMap.adjoint (embCLM (n + 1))
      (SecondQuantSlot.dGammaTensor b n h (embCLM (n + 1) ψ)) from rfl, embCLM_adjoint_apply, hY]
  calc dGammaFock b (n + 1) h (creWCoeff b w ψ)
      = ContinuousLinearMap.adjoint (embCLM (n + 2))
          (SecondQuantSlot.dGammaTensor b (n + 1) h (embCLM (n + 2) (creWCoeff b w ψ))) := rfl
    _ = ContinuousLinearMap.adjoint (embCLM (n + 2))
          (embCLM (n + 2) (creWCoeff b (h w) ψ) + embCLM (n + 2) (creWCoeff b w (dGammaFock b n h ψ))) := by
        rw [hc, hc, h2, map_smul, dGammaTensor_antisym, dGammaTensor_creT, map_add, smul_add]
    _ = _ := by
        rw [map_add, adjoint_embCLM_embCLM _ fun S hS => creWCoeff_apply_of_card b (h w) ψ hψ hS,
          adjoint_embCLM_embCLM _ fun S hS => creWCoeff_apply_of_card b w _
            (fun S' hS' => dGammaFock_apply_of_card b n h ψ hS') hS]

/-- **`[dΓ(h), a*(w)] = a*(hw)` on the vacuum sector**: `dΓ₁(h) a*(w) ψ = a*(hw) ψ` for `ψ` supported on `∅`. -/
theorem dGammaFock_zero_creW (h : Z →L[ℂ] Z) (w : Z) (ψ : FermiL2 ι) (hψ : ∀ S : Finset ι, S.card ≠ 0 → ψ S = 0) :
    dGammaFock b 0 h (creWCoeff b w ψ) = creWCoeff b (h w) ψ := by
  set c : ℂ := (Real.sqrt (((0 : ℕ) : ℝ) + 1) : ℂ) with hcdef
  have hc : ∀ (w' : Z) (φ : FermiL2 ι), embCLM 1 (creWCoeff b w' φ) =
      c • antisym 1 (creT b w' (embCLM 0 φ)) := fun w' φ => embL_creW (n := 0) b w' φ
  calc dGammaFock b 0 h (creWCoeff b w ψ)
      = ContinuousLinearMap.adjoint (embCLM 1)
          (SecondQuantSlot.dGammaTensor b 0 h (embCLM 1 (creWCoeff b w ψ))) := rfl
    _ = ContinuousLinearMap.adjoint (embCLM 1) (embCLM 1 (creWCoeff b (h w) ψ)) := by
        rw [hc, hc, map_smul, dGammaTensor_antisym, dGammaTensor_zero_creT]
    _ = _ := adjoint_embCLM_embCLM _ fun S hS => creWCoeff_apply_of_card b (h w) ψ hψ hS

/-- **Conjugating by a unitary commutes with the adjoint**: `(U X V)* = U X* V` when `U V = 1`. -/
lemma adjoint_conj {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (U : E →ₗᵢ[ℂ] F) (V : F →ₗᵢ[ℂ] E)
    (hUV : ∀ y, U (V y) = y) (X : E →L[ℂ] E) :
    ContinuousLinearMap.adjoint (U.toContinuousLinearMap ∘L X ∘L V.toContinuousLinearMap) =
      U.toContinuousLinearMap ∘L ContinuousLinearMap.adjoint X ∘L V.toContinuousLinearMap := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  calc inner ℂ (U (ContinuousLinearMap.adjoint X (V x))) y
      = inner ℂ (U (ContinuousLinearMap.adjoint X (V x))) (U (V y)) := by rw [hUV]
    _ = inner ℂ (ContinuousLinearMap.adjoint X (V x)) (V y) := U.inner_map_map _ _
    _ = inner ℂ (V x) (X (V y)) := ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = inner ℂ (U (V x)) (U (X (V y))) := (U.inner_map_map _ _).symm
    _ = inner ℂ x (U (X (V y))) := by rw [hUV]

/-- **`(h ⊗ 1)* = h* ⊗ 1`** on `ℓ²(M, Z)`. -/
lemma adjoint_slotMap {M : Type*} (h : Z →L[ℂ] Z) :
    ContinuousLinearMap.adjoint (SecondQuantSlot.slotMap h : lp (fun _ : M => Z) 2 →L[ℂ] _) =
      SecondQuantSlot.slotMap (ContinuousLinearMap.adjoint h) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext m
  rw [SecondQuantSlot.slotMap_apply, SecondQuantSlot.slotMap_apply, ContinuousLinearMap.adjoint_inner_left]

/-- The coordinates are onto: `coordL (uncoordL c) = c`. -/
lemma coordL_uncoordL {M : Type*} (c : lp (fun _ : M × ι => ℂ) 2) :
    SecondQuantSlot.coordL b (SecondQuantSlot.uncoordL b c) = c := by
  ext ⟨m, k⟩
  show b.repr (b.repr.symm (SecondQuantSlot.fiber c m)) k = c (m, k)
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- **`(h ⊗ 1)* = h* ⊗ 1`** in coordinates. -/
lemma adjoint_slotC {M : Type*} (h : Z →L[ℂ] Z) :
    ContinuousLinearMap.adjoint (SecondQuantSlot.slotC b h : lp (fun _ : M × ι => ℂ) 2 →L[ℂ] _) =
      SecondQuantSlot.slotC b (ContinuousLinearMap.adjoint h) := by
  rw [SecondQuantSlot.slotC, SecondQuantSlot.slotC, adjoint_conj _ _ (coordL_uncoordL b), adjoint_slotMap]

/-- **`(hⱼ)* = (h*)ⱼ`.** -/
lemma adjoint_slotOp {m : ℕ} (j : Fin (m + 1)) (h : Z →L[ℂ] Z) :
    ContinuousLinearMap.adjoint (SecondQuantSlot.slotOp b j h) =
      SecondQuantSlot.slotOp b j (ContinuousLinearMap.adjoint h) := by
  rw [SecondQuantSlot.slotOp, SecondQuantSlot.slotOp,
    adjoint_conj _ _ (fun y => LinearIsometryEquiv.apply_symm_apply _ y), adjoint_slotC]

/-- **`(∑ⱼ hⱼ)* = ∑ⱼ (h*)ⱼ`.** -/
lemma adjoint_dGammaTensor (m : ℕ) (h : Z →L[ℂ] Z) :
    ContinuousLinearMap.adjoint (SecondQuantSlot.dGammaTensor b m h) =
      SecondQuantSlot.dGammaTensor b m (ContinuousLinearMap.adjoint h) := by
  rw [SecondQuantSlot.dGammaTensor, SecondQuantSlot.dGammaTensor, map_sum]
  exact Finset.sum_congr rfl fun j _ => adjoint_slotOp b j h

/-- **`dΓ(h)* = dΓ(h*)`.** -/
theorem adjoint_dGammaFock (n : ℕ) (h : Z →L[ℂ] Z) :
    ContinuousLinearMap.adjoint (dGammaFock b n h) = dGammaFock b n (ContinuousLinearMap.adjoint h) := by
  rw [dGammaFock, dGammaFock, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, adjoint_dGammaTensor, ContinuousLinearMap.comp_assoc]

/-- The fermionic creation operator `a*(w)` on `ℓ²(Finset ι)`, as a bounded operator. -/
noncomputable def creL2 (w : Z) : FermiL2 ι →L[ℂ] FermiL2 ι :=
  (creWCoeff b w).mkContinuous ‖w‖ (norm_creWCoeff_le b w)

/-- `creL2 w = creWCoeff w`. -/
lemma creL2_apply (w : Z) (ψ : FermiL2 ι) : creL2 b w ψ = creWCoeff b w ψ := rfl

/-- **The fermionic annihilation operator** `a(w) = a*(w)*` on `ℓ²(Finset ι)`. -/
noncomputable def annL2 (w : Z) : FermiL2 ι →L[ℂ] FermiL2 ι := ContinuousLinearMap.adjoint (creL2 b w)

/-- A coefficient as an inner product: `v(S) = ⟪e_S, v⟫`. -/
lemma apply_eq_inner_single (v : FermiL2 ι) (S : Finset ι) :
    v S = inner ℂ (lp.single (E := fun _ : Finset ι => ℂ) 2 S (1 : ℂ)) v := by
  rw [lp.inner_single_left, RCLike.inner_apply', map_one, one_mul]

/-- `e_S` is an `|S|`-particle vector. -/
lemma single_apply_of_card {S T : Finset ι} (hT : T.card ≠ S.card) :
    (lp.single (E := fun _ : Finset ι => ℂ) 2 S (1 : ℂ)) T = 0 :=
  lp.single_apply_ne _ _ _ fun h => hT (by rw [h])

/-- **Vectors with different particle numbers are orthogonal.** -/
lemma inner_eq_zero_of_card (x y : FermiL2 ι) {m m' : ℕ} (hm : m ≠ m') (hx : ∀ S : Finset ι, S.card ≠ m → x S = 0)
    (hy : ∀ S : Finset ι, S.card ≠ m' → y S = 0) : inner ℂ x y = 0 := by
  rw [lp.inner_eq_tsum]
  refine (tsum_congr fun S => ?_).trans tsum_zero
  by_cases hS : S.card = m
  · rw [hy S (by rw [hS]; exact hm), inner_zero_right]
  · rw [hx S hS, inner_zero_left]

/-- **`a(w)` lowers the particle number by one.** -/
lemma annL2_apply_of_card (w : Z) (v : FermiL2 ι) {m : ℕ} (hv : ∀ S : Finset ι, S.card ≠ m + 1 → v S = 0)
    {S : Finset ι} (hS : S.card ≠ m) : annL2 b w v S = 0 := by
  rw [apply_eq_inner_single, annL2, ContinuousLinearMap.adjoint_inner_right, creL2_apply]
  exact inner_eq_zero_of_card _ _ (m := S.card + 1) (m' := m + 1) (by omega)
    (fun T hT => creWCoeff_apply_of_card b w _ (fun S' hS' => single_apply_of_card hS') hT) hv

/-- **The commutator `[dΓ(h), a(w)] = -a(h* w)` on the `(n+2)`-particle vectors**:
`a(w) dΓₙ₊₂(h) φ = a(h* w) φ + dΓₙ₊₁(h) a(w) φ`. -/
theorem annL2_dGammaFock (n : ℕ) (h : Z →L[ℂ] Z) (w : Z) (φ : FermiL2 ι)
    (hφ : ∀ S : Finset ι, S.card ≠ n + 2 → φ S = 0) :
    annL2 b w (dGammaFock b (n + 1) h φ) =
      annL2 b (ContinuousLinearMap.adjoint h w) φ + dGammaFock b n h (annL2 b w φ) := by
  ext S
  rw [lp.coeFn_add, Pi.add_apply]
  by_cases hS : S.card = n + 1
  · set ψ := lp.single (E := fun _ : Finset ι => ℂ) 2 S (1 : ℂ) with hψdef
    have hψ : ∀ T : Finset ι, T.card ≠ n + 1 → ψ T = 0 := fun T hT => single_apply_of_card (by rw [hS]; exact hT)
    have key := dGammaFock_creW b n (ContinuousLinearMap.adjoint h) w ψ hψ
    rw [apply_eq_inner_single, apply_eq_inner_single, apply_eq_inner_single, ← hψdef]
    calc inner ℂ ψ (annL2 b w (dGammaFock b (n + 1) h φ))
        = inner ℂ (creL2 b w ψ) (dGammaFock b (n + 1) h φ) := ContinuousLinearMap.adjoint_inner_right _ _ _
      _ = inner ℂ (ContinuousLinearMap.adjoint (dGammaFock b (n + 1) h) (creL2 b w ψ)) φ :=
          (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
      _ = inner ℂ (creL2 b (ContinuousLinearMap.adjoint h w) ψ) φ +
            inner ℂ (creL2 b w (dGammaFock b n (ContinuousLinearMap.adjoint h) ψ)) φ := by
          rw [adjoint_dGammaFock, creL2_apply, key, inner_add_left]
          rfl
      _ = inner ℂ ψ (annL2 b (ContinuousLinearMap.adjoint h w) φ) +
            inner ℂ (dGammaFock b n (ContinuousLinearMap.adjoint h) ψ) (annL2 b w φ) := by
          rw [annL2, annL2, ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right]
      _ = inner ℂ ψ (annL2 b (ContinuousLinearMap.adjoint h w) φ) + inner ℂ ψ (dGammaFock b n h (annL2 b w φ)) := by
          rw [← ContinuousLinearMap.adjoint_inner_right (dGammaFock b n (ContinuousLinearMap.adjoint h)),
            adjoint_dGammaFock, ContinuousLinearMap.adjoint_adjoint]
  · rw [annL2_apply_of_card b w _ (fun T hT => dGammaFock_apply_of_card b (n + 1) h φ hT) hS,
      annL2_apply_of_card b _ φ hφ hS, dGammaFock_apply_of_card b n h _ hS, add_zero]

/-- **`[dΓ(h), a(w)] = -a(h* w)` on the one-particle vectors**: `a(w) dΓ₁(h) φ = a(h* w) φ`. -/
theorem annL2_dGammaFock_zero (h : Z →L[ℂ] Z) (w : Z) (φ : FermiL2 ι) (hφ : ∀ S : Finset ι, S.card ≠ 1 → φ S = 0) :
    annL2 b w (dGammaFock b 0 h φ) = annL2 b (ContinuousLinearMap.adjoint h w) φ := by
  ext S
  by_cases hS : S.card = 0
  · set ψ := lp.single (E := fun _ : Finset ι => ℂ) 2 S (1 : ℂ) with hψdef
    have hψ : ∀ T : Finset ι, T.card ≠ 0 → ψ T = 0 := fun T hT => single_apply_of_card (by rw [hS]; exact hT)
    have key := dGammaFock_zero_creW b (ContinuousLinearMap.adjoint h) w ψ hψ
    rw [apply_eq_inner_single, apply_eq_inner_single, ← hψdef]
    calc inner ℂ ψ (annL2 b w (dGammaFock b 0 h φ))
        = inner ℂ (creL2 b w ψ) (dGammaFock b 0 h φ) := ContinuousLinearMap.adjoint_inner_right _ _ _
      _ = inner ℂ (ContinuousLinearMap.adjoint (dGammaFock b 0 h) (creL2 b w ψ)) φ :=
          (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
      _ = inner ℂ (creL2 b (ContinuousLinearMap.adjoint h w) ψ) φ := by
          rw [adjoint_dGammaFock, creL2_apply, key]
          rfl
      _ = inner ℂ ψ (annL2 b (ContinuousLinearMap.adjoint h w) φ) :=
          (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
  · rw [annL2_apply_of_card b w _ (m := 0) (fun T hT => dGammaFock_apply_of_card b 0 h φ hT) hS,
      annL2_apply_of_card b _ φ (m := 0) hφ hS]

/-- The coordinates are injective: `uncoordL (coordL ψ) = ψ`. -/
lemma uncoordL_coordL {M : Type*} (ψ : lp (fun _ : M => Z) 2) :
    SecondQuantSlot.uncoordL b (SecondQuantSlot.coordL b ψ) = ψ := by
  refine lp.ext (funext fun m => ?_)
  show b.repr.symm (SecondQuantSlot.fiber (SecondQuantSlot.coordL b ψ) m) = ψ m
  have : SecondQuantSlot.fiber (SecondQuantSlot.coordL b ψ) m = b.repr (ψ m) := by
    ext k
    rfl
  rw [this, LinearIsometryEquiv.symm_apply_apply]

/-- **`hⱼ h'ⱼ = (h h')ⱼ`.** -/
lemma slotOp_slotOp {m : ℕ} (j : Fin (m + 1)) (h h' : Z →L[ℂ] Z) (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.slotOp b j h (SecondQuantSlot.slotOp b j h' Φ) = SecondQuantSlot.slotOp b j (h ∘L h') Φ := by
  simp only [SecondQuantSlot.slotOp, SecondQuantSlot.slotC, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.symm_apply_apply, uncoordL_coordL]
  rfl

/-- **`(h - h')ⱼ = hⱼ - h'ⱼ`.** -/
lemma slotOp_sub {m : ℕ} (j : Fin (m + 1)) (h h' : Z →L[ℂ] Z) (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.slotOp b j (h - h') Φ = SecondQuantSlot.slotOp b j h Φ - SecondQuantSlot.slotOp b j h' Φ := by
  simp only [SecondQuantSlot.slotOp, SecondQuantSlot.slotC, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  have hs : ∀ x : lp (fun _ : Fin m → ι => Z) 2,
      SecondQuantSlot.slotMap (h - h') x = SecondQuantSlot.slotMap h x - SecondQuantSlot.slotMap h' x := fun x =>
    lp.ext (funext fun m => by
      simp only [SecondQuantSlot.slotMap_apply, lp.coeFn_sub, Pi.sub_apply, ContinuousLinearMap.sub_apply])
  rw [hs, map_sub, map_sub]

/-- **Bounded operators on `ℓ²` agreeing on the basis vectors are equal.** -/
lemma clm_ext_single {α β : Type*} [DecidableEq α] (X Y : lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : β => ℂ) 2)
    (h : ∀ a, X (lp.single 2 a (1 : ℂ)) = Y (lp.single 2 a (1 : ℂ))) : X = Y := by
  ext1 Φ
  have hs := lp.hasSum_single (E := fun _ : α => ℂ) (p := 2) (by norm_num) Φ
  have hX := X.hasSum hs
  have hY := Y.hasSum hs
  have he : (fun a => X (lp.single 2 a (Φ a))) = fun a => Y (lp.single 2 a (Φ a)) := funext fun a => by
    have e : lp.single (E := fun _ : α => ℂ) 2 a (Φ a) = Φ a • lp.single 2 a (1 : ℂ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul, h]
  rw [he] at hX
  exact hX.unique hY

/-- **`h` on slot `j`, when the slot-`j` fibre is a multiple of a basis vector.** -/
lemma slotOp_apply_of_fiber {m : ℕ} (j : Fin (m + 1)) (h : Z →L[ℂ] Z) (X : lp (fun _ : Fin (m + 1) → ι => ℂ) 2)
    (g : Fin (m + 1) → ι) (c : ℂ) (i₀ : ι) (hX : ∀ i, X (Function.update g j i) = if i = i₀ then c else 0) :
    SecondQuantSlot.slotOp b j h X g = c * b.repr (h (b i₀)) (g j) := by
  rw [slotOp_apply_eq]
  have hfib : SecondQuantSlot.fiber ((SecondQuantSlot.reindexL (SecondQuantSlot.slotEquiv j)).symm X)
      (Fin.removeNth j g) = c • lp.single 2 i₀ (1 : ℂ) := by
    ext i
    show X ((SecondQuantSlot.slotEquiv j).symm (Fin.removeNth j g, i)) = _
    rw [slotEquiv_symm_apply, Fin.insertNth_removeNth, hX, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
      Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hfib, map_smul, HilbertBasis.repr_symm_single, map_smul, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]

/-- **`h` on slot `k` of a basis vector**: `(hₖ e_f)(g) = [g = f off k] ⟨b_{g k}, h b_{f k}⟩`. -/
lemma slotOp_single_apply {m : ℕ} (k : Fin (m + 1)) (h : Z →L[ℂ] Z) (f g : Fin (m + 1) → ι) :
    SecondQuantSlot.slotOp b k h (lp.single 2 f (1 : ℂ)) g =
      if ∀ l, l ≠ k → g l = f l then b.repr (h (b (f k))) (g k) else 0 := by
  split_ifs with hc
  · rw [slotOp_apply_of_fiber b k h _ g 1 (f k), one_mul]
    intro i
    rw [lp.single_apply, Pi.single_apply]
    have : Function.update g k i = f ↔ i = f k := by
      constructor
      · rintro rfl; simp
      · rintro rfl
        funext l
        by_cases hl : l = k
        · subst hl; simp
        · rw [Function.update_of_ne hl, hc l hl]
    simp only [this]
  · rw [slotOp_apply_of_fiber b k h _ g 0 (f k), zero_mul]
    intro i
    rw [lp.single_apply, Pi.single_apply, if_neg, ite_self]
    rintro hu
    push_neg at hc
    obtain ⟨l, hl, hne⟩ := hc
    exact hne (by rw [← hu, Function.update_of_ne hl])

/-- **Two slots on a basis vector**: for `j ≠ k`, `(hⱼ h'ₖ e_f)(g) = [g = f off j, k] ⟨b_{g j}, h b_{f j}⟩ ⟨b_{g k}, h' b_{f k}⟩`. -/
lemma slotOp_slotOp_single_apply {m : ℕ} {j k : Fin (m + 1)} (hjk : j ≠ k) (h h' : Z →L[ℂ] Z)
    (f g : Fin (m + 1) → ι) :
    SecondQuantSlot.slotOp b j h (SecondQuantSlot.slotOp b k h' (lp.single 2 f (1 : ℂ))) g =
      if ∀ l, l ≠ j → l ≠ k → g l = f l then b.repr (h (b (f j))) (g j) * b.repr (h' (b (f k))) (g k) else 0 := by
  set c : ℂ := if ∀ l, l ≠ j → l ≠ k → g l = f l then b.repr (h' (b (f k))) (g k) else 0 with hcdef
  rw [slotOp_apply_of_fiber b j h _ g c (f j)]
  · rw [hcdef]
    split_ifs <;> ring
  · intro i
    rw [slotOp_single_apply, Function.update_of_ne hjk.symm]
    have : (∀ l, l ≠ k → Function.update g j i l = f l) ↔ i = f j ∧ ∀ l, l ≠ j → l ≠ k → g l = f l := by
      constructor
      · intro hu
        refine ⟨by simpa using hu j hjk, fun l hlj hlk => ?_⟩
        rw [← Function.update_of_ne hlj i g]
        exact hu l hlk
      · rintro ⟨rfl, hg⟩ l hlk
        by_cases hlj : l = j
        · subst hlj; simp
        · rw [Function.update_of_ne hlj]; exact hg l hlj hlk
    simp only [this, hcdef]
    by_cases hi : i = f j <;> by_cases hg : ∀ l, l ≠ j → l ≠ k → g l = f l <;> simp [hi, hg]

/-- **Different slots commute**: `hⱼ h'ₖ = h'ₖ hⱼ` for `j ≠ k`. -/
theorem slotOp_comm {m : ℕ} {j k : Fin (m + 1)} (hjk : j ≠ k) (h h' : Z →L[ℂ] Z) :
    SecondQuantSlot.slotOp b j h ∘L SecondQuantSlot.slotOp b k h' =
      SecondQuantSlot.slotOp b k h' ∘L SecondQuantSlot.slotOp b j h := by
  refine clm_ext_single _ _ fun f => ?_
  ext g
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, slotOp_slotOp_single_apply b hjk,
    slotOp_slotOp_single_apply b hjk.symm]
  have : (∀ l, l ≠ j → l ≠ k → g l = f l) ↔ ∀ l, l ≠ k → l ≠ j → g l = f l :=
    ⟨fun H l hk hj => H l hj hk, fun H l hj hk => H l hk hj⟩
  simp only [this]
  split_ifs <;> ring

/-- **`[∑ⱼ hⱼ, ∑ⱼ h'ⱼ] = ∑ⱼ [h, h']ⱼ`.** -/
theorem dGammaTensor_comm (m : ℕ) (h h' : Z →L[ℂ] Z) (Φ : lp (fun _ : Fin (m + 1) → ι => ℂ) 2) :
    SecondQuantSlot.dGammaTensor b m h (SecondQuantSlot.dGammaTensor b m h' Φ) -
        SecondQuantSlot.dGammaTensor b m h' (SecondQuantSlot.dGammaTensor b m h Φ) =
      SecondQuantSlot.dGammaTensor b m (h ∘L h' - h' ∘L h) Φ := by
  simp only [SecondQuantSlot.dGammaTensor, ContinuousLinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm (f := fun x i => SecondQuantSlot.slotOp b i h' (SecondQuantSlot.slotOp b x h Φ)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · rw [slotOp_slotOp, slotOp_slotOp, slotOp_sub]
  · intro k _ hkj
    have := congrArg (fun T => T Φ) (slotOp_comm b hkj h h')
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this, sub_self]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- `dΓ(h) dΓ(h') = E* (∑ⱼ hⱼ)(∑ⱼ h'ⱼ) E`. -/
lemma dGammaFock_dGammaFock (n : ℕ) (h h' : Z →L[ℂ] Z) (ψ : FermiL2 ι) :
    dGammaFock b n h (dGammaFock b n h' ψ) = ContinuousLinearMap.adjoint (embCLM (n + 1))
      (SecondQuantSlot.dGammaTensor b n h (SecondQuantSlot.dGammaTensor b n h' (embCLM (n + 1) ψ))) := by
  show ContinuousLinearMap.adjoint (embCLM (n + 1)) (SecondQuantSlot.dGammaTensor b n h (embCLM (n + 1)
    (ContinuousLinearMap.adjoint (embCLM (n + 1)) (SecondQuantSlot.dGammaTensor b n h' (embCLM (n + 1) ψ))))) = _
  rw [embCLM_adjoint_apply, ← dGammaTensor_antisym]
  have hA : antisym (n + 1) (embCLM (n + 1) ψ) = embCLM (n + 1) ψ := antisym_embL ψ
  rw [hA]

/-- **`[dΓ(h), dΓ(h')] = dΓ([h, h'])`** on every particle sector. -/
theorem dGammaFock_comm (n : ℕ) (h h' : Z →L[ℂ] Z) (ψ : FermiL2 ι) :
    dGammaFock b n h (dGammaFock b n h' ψ) - dGammaFock b n h' (dGammaFock b n h ψ) =
      dGammaFock b n (h ∘L h' - h' ∘L h) ψ := by
  rw [dGammaFock_dGammaFock, dGammaFock_dGammaFock, ← map_sub, dGammaTensor_comm]
  rfl

end Gamma

end Lightlike.OperatorAlgebras.SecondQuantWedge
