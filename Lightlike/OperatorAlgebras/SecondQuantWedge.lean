import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lightlike.OperatorAlgebras.SecondQuantSlot
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The sign of an injective tuple

For the embedding of the `n`-particle fermionic Fock space `Γₙ` (the closed span of the wedges `B S`, `|S| = n`, in
`ℓ²(Finset ι)`) into the coordinate tensor power `ℓ²(Fin n → ι)` (J. Dereziński, arXiv:math-ph/0511030, Section 5.2:
`Γₙ^a(Z)` is the antisymmetric subspace of `⊗ⁿZ`): a wedge `B S` goes to `(n!)^{-1/2} ∑ sign(f) e_f` over the injective tuples
`f` enumerating `S`, where the sign of `f` is that of the permutation sorting it (Mathlib's `Tuple.sort`).

* `tupleSign`, `sort_comp_perm`, `tupleSign_comp`: `sign(f ∘ τ) = sign τ · sign f` for injective `f`;
* `Enum`, `enumEquiv`, `card_enum`: an `n`-element set has `n!` enumerations by injective tuples;
* `embFun`, `hasSum_fiber`, `hasSum_norm_embFun`, `embL`, `norm_sq_embL`, `norm_embL_le`, `norm_embL_of_support`, `embCLM`:
  the embedding `Eₙ ψ (f) = (n!)^{-1/2} sign(f) ψ(image f)`, a contraction, isometric on the `n`-particle vectors;
* `permEquiv`, `permL`, `antisym`, `antisym_apply`, `embFun_comp`, `antisym_embL`: the antisymmetrizer, and `A Eₙ = Eₙ`;
* `tensorFun`, `hasSum_norm_tensorFun`: `c ⊗ Φ` in coordinates, `‖c ⊗ Φ‖² = ‖c‖² ‖Φ‖²`;
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

lemma permEquiv_apply (σ : Equiv.Perm (Fin n)) (f : Fin n → ι) : permEquiv σ f = f ∘ σ := by
  funext i; simp [permEquiv, Equiv.arrowCongr_apply]

/-- **The permutation of the slots**, `P_σ Φ (f) = Φ(f ∘ σ)`, an isometry. -/
noncomputable def permL (σ : Equiv.Perm (Fin n)) :
    lp (fun _ : Fin n → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin n → ι => ℂ) 2 :=
  (SecondQuantSlot.reindexL (permEquiv (ι := ι) σ)).toLinearIsometry.toContinuousLinearMap

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

end Antisym

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

end Gamma

end Lightlike.OperatorAlgebras.SecondQuantWedge
