module

public import Lightlike.Lorentz.Density

/-!
# The restriction of the principal series to SU(2)

**Theorem (`principalSeries_isHilbertSum`).** Restricted to `SU(2)`, the principal series
`(k, ρ)` (`n = 2k`) is the Hilbert direct sum of the spins `j = |k|, |k|+1, |k|+2, …`, each once:
there are linear isometries `suV n ρ ℓ : ℂ^{2j+1} → L²(ℂ)`, `j = |k| + ℓ`, with mutually
orthogonal ranges whose span is dense (Mathlib's `IsHilbertSum`), each intertwining the spin-`j`
representation `spinMat (2j)` of `Lightlike/SU2/SpinRep.lean` with `π|_{SU(2)}`
(`principalSeries_suV`).

**Theorem (`intertwiner_eq_zero`, `intertwiner_eq_smul`).** No other spin occurs, and each occurs
once: an SU(2)-intertwiner from spin `m/2` into `L²(ℂ)` vanishes unless `m = 2ℓ + |n|` for some
`ℓ`, and then it is a multiple of `suV n ρ ℓ`.

Proof.
1. For two intertwiners `A, B` from spins `m/2, m'/2` the Gram map `x ↦ (⟪B e_k, A x⟫)_k` is an
   intertwiner between the spin representations (`gram_isSpinIntertwiner`, by unitarity of `π` and
   of `spinMat`). Schur's lemma makes it `0` for `m ≠ m'` (orthogonality) and a scalar for
   `m = m'`, which normalises `tlin` to an isometry (`normalize`).
2. The ranges of the levels `ℓ' ≤ ℓ` are orthogonal, have total dimension
   `Σ_{ℓ' ≤ ℓ} (2ℓ' + |n| + 1) = (ℓ + p₀ + 1)(ℓ + q₀ + 1)` and lie in the level space of `ℓ`, whose
   dimension is at most that number; so they fill it (`levelSpace_le_iSup`).
3. The level spaces are dense (`eq_zero_of_orthogonal_levels`).

References: I. M. Gelfand, R. A. Minlos, Z. Ya. Shapiro, *Representations of the Rotation and
Lorentz Groups and their Applications* (Pergamon, 1963); W. Rühl, *The Lorentz Group and Harmonic
Analysis* (Benjamin, 1970): the principal series `(k, ρ)` contains each spin `j ≥ |k|` with
`j - k ∈ ℤ` exactly once.
-/

@[expose] public section

open Matrix Complex MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace Lightlike.Lorentz

open Lightlike.SU2

variable (n : ℤ) (ρ : ℝ)

/-! ## Gram maps of intertwiners -/

/-- `A` intertwines spin `m/2` with the principal series restricted to `SU(2)`. -/
def IsPSIntertwiner {m : ℕ} (A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C) : Prop :=
  ∀ (u : SU2) (x : Fin (m + 1) → ℂ),
    principalSeries n ρ (SL2C.ofSU2 u) (A x) = A (spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x)

/-- The standard basis vector `e_k`. -/
def bv {m : ℕ} (k : Fin (m + 1)) : Fin (m + 1) → ℂ := fun j => if k = j then 1 else 0

/-- **The Gram map** `x ↦ (⟪B e_k, A x⟫)_k` of two maps into `L²(ℂ)`. -/
noncomputable def gram {m m' : ℕ} (A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C)
    (B : (Fin (m' + 1) → ℂ) →ₗ[ℂ] L2C) : (Fin (m + 1) → ℂ) →ₗ[ℂ] (Fin (m' + 1) → ℂ) where
  toFun x k := ⟪B (bv k), A x⟫_ℂ
  map_add' x y := by funext k; simp [inner_add_right]
  map_smul' c x := by funext k; simp [inner_smul_right]

lemma gram_apply {m m' : ℕ} (A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C) (B : (Fin (m' + 1) → ℂ) →ₗ[ℂ] L2C)
    (x : Fin (m + 1) → ℂ) (k : Fin (m' + 1)) : gram A B x k = ⟪B (bv k), A x⟫_ℂ := rfl

/-- `⟪B y, A x⟫ = Σ_k ȳ_k (gram A B x)_k`. -/
lemma inner_eq_gram {m m' : ℕ} (A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C)
    (B : (Fin (m' + 1) → ℂ) →ₗ[ℂ] L2C) (x : Fin (m + 1) → ℂ) (y : Fin (m' + 1) → ℂ) :
    ⟪B y, A x⟫_ℂ = ∑ k, conj (y k) * gram A B x k := by
  rw [LinearMap.pi_apply_eq_sum_univ B y, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_left]; rfl

/-- `⟪a, π(g) b⟫ = ⟪π(g⁻¹) a, b⟫`. -/
lemma inner_principalSeries_right (g : SL2C) (a b : L2C) :
    ⟪a, principalSeries n ρ g b⟫_ℂ = ⟪principalSeries n ρ g⁻¹ a, b⟫_ℂ := by
  have := principalSeries_inner n ρ g (principalSeries n ρ g⁻¹ a) b
  rwa [← mul_apply_eq_comp, ← principalSeries_mul, mul_inv_cancel,
    principalSeries_one, one_apply_eq_self] at this

lemma coe_inv_su2 (u : SU2) :
    ((u⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = star (u : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]

lemma spinMat_inv_apply (m : ℕ) (u : SU2) (l k : Fin (m + 1)) :
    spinMat m ((u⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) l k =
      conj (spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ) k l) := by
  rw [coe_inv_su2, Matrix.star_eq_conjTranspose, ← spinMat_conjTranspose]; rfl

lemma mulVec_bv {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (k l : Fin (m + 1)) :
    (M *ᵥ bv k) l = M l k := by
  simp [mulVec, dotProduct, bv]

/-- **The Gram map of two intertwiners intertwines the spin representations.** -/
theorem gram_isSpinIntertwiner {m m' : ℕ} {A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C}
    {B : (Fin (m' + 1) → ℂ) →ₗ[ℂ] L2C} (hA : IsPSIntertwiner n ρ A)
    (hB : IsPSIntertwiner n ρ B) : IsSpinIntertwiner m m' (gram A B) := by
  intro u x
  funext k
  rw [gram_apply, ← hA, inner_principalSeries_right, ← map_inv, hB, inner_eq_gram]
  simp only [mulVec_bv, spinMat_inv_apply, Complex.conj_conj]
  simp only [mulVec, dotProduct]

/-- **Orthogonality**: intertwiners from different spins have orthogonal ranges. -/
theorem inner_eq_zero_of_ne {m m' : ℕ} (hm : m ≠ m') {A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C}
    {B : (Fin (m' + 1) → ℂ) →ₗ[ℂ] L2C} (hA : IsPSIntertwiner n ρ A)
    (hB : IsPSIntertwiner n ρ B) (x : Fin (m + 1) → ℂ) (y : Fin (m' + 1) → ℂ) :
    ⟪B y, A x⟫_ℂ = 0 := by
  rw [inner_eq_gram, schur_eq_zero hm (gram_isSpinIntertwiner n ρ hA hB)]
  simp

/-! ## Normalisation -/

/-- The scalar `c` with `gram A A = c • id`. -/
lemma exists_gram_self {m : ℕ} {A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C} (hA : IsPSIntertwiner n ρ A) :
    ∃ c : ℂ, ∀ x y, ⟪A y, A x⟫_ℂ = c * ∑ k, conj (y k) * x k := by
  obtain ⟨c, hc⟩ := schur_eq_smul (gram_isSpinIntertwiner n ρ hA hA)
  refine ⟨c, fun x y => ?_⟩
  rw [inner_eq_gram, hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- The norm `‖A e₀‖` used to normalise. -/
noncomputable def nrmA {m : ℕ} (A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C) : ℝ := ‖A (bv 0)‖

lemma inner_A_eq {m : ℕ} {A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C} (hA : IsPSIntertwiner n ρ A) (x y) :
    ⟪A y, A x⟫_ℂ = ((nrmA A ^ 2 : ℝ) : ℂ) * ∑ k, conj (y k) * x k := by
  obtain ⟨c, hc⟩ := exists_gram_self n ρ hA
  have h0 := hc (bv 0) (bv 0)
  have hsum : ∑ k : Fin (m + 1), conj (bv (0 : Fin (m + 1)) k) * bv 0 k = 1 := by
    rw [Finset.sum_eq_single 0] <;> simp [bv]; intro b hb; simp [Ne.symm hb]
  rw [hsum, mul_one, inner_self_eq_norm_sq_to_K] at h0
  rw [hc, nrmA, ← h0]; norm_cast

lemma nrmA_pos {m : ℕ} {A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C} (hA : IsPSIntertwiner n ρ A)
    (hA0 : A ≠ 0) : 0 < nrmA A := by
  refine lt_of_le_of_ne (norm_nonneg _) fun h => hA0 ?_
  refine LinearMap.ext fun x => ?_
  have := inner_A_eq n ρ hA x x
  rw [← h, inner_self_eq_norm_sq_to_K] at this
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_zero,
    zero_mul] at this
  simpa using this

/-- The domain `ℂ^{m+1}` with its Hilbert-space structure. -/
abbrev Espace (m : ℕ) := EuclideanSpace ℂ (Fin (m + 1))

/-- **The normalised intertwiner**, a linear isometry `ℂ^{m+1} → L²(ℂ)`. -/
noncomputable def normalize {m : ℕ} (A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C) (hA : IsPSIntertwiner n ρ A)
    (hA0 : A ≠ 0) : Espace m →ₗᵢ[ℂ] L2C :=
  LinearMap.isometryOfInner
    (((nrmA A)⁻¹ : ℂ) • (A ∘ₗ (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).toLinearMap))
    fun x y => by
      have hpos := nrmA_pos n ρ hA hA0
      simp only [LinearMap.smul_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        inner_smul_left, inner_smul_right, inner_A_eq n ρ hA,
        EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, RCLike.star_def]
      have hr : ((nrmA A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      simp only [map_inv₀, Complex.conj_ofReal]
      push_cast
      field_simp
      refine Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma normalize_apply {m : ℕ} (A : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C) (hA : IsPSIntertwiner n ρ A)
    (hA0 : A ≠ 0) (x : Espace m) :
    normalize n ρ A hA hA0 x = ((nrmA A)⁻¹ : ℂ) • A x.ofLp := rfl

/-! ## The isometries of the SU(2) decomposition -/

/-- `p₀ = max(n, 0)`. -/
def p0 : ℕ := n.toNat
/-- `q₀ = max(-n, 0)`. -/
def q0 : ℕ := (-n).toNat

lemma p0_sub_q0 : ((p0 n : ℕ) : ℤ) - (q0 n : ℕ) = n := by simp [p0, q0]

lemma p0_mul_q0 : p0 n * q0 n = 0 := by
  rcases le_total 0 n with h | h
  · have : q0 n = 0 := by simp [q0]; omega
    simp [this]
  · have : p0 n = 0 := by simp [p0]; omega
    simp [this]

/-- The doubled spin `2j = 2ℓ + |n|` of the level `ℓ`. -/
abbrev dsp (ℓ : ℕ) : ℕ := (ℓ + p0 n) + (ℓ + q0 n)

lemma dsp_eq (ℓ : ℕ) : dsp n ℓ = 2 * ℓ + n.natAbs := by simp [dsp, p0, q0]; omega

lemma tlin_isPS (ℓ : ℕ) : IsPSIntertwiner n ρ (tlin (ℓ + p0 n) (ℓ + q0 n) ρ) := by
  intro u x
  exact principalSeries_tlin (by have := p0_sub_q0 n; push_cast; omega) ρ u x

/-- **The spin-`(|k| + ℓ)` isometry** `ℂ^{2ℓ+|n|+1} → L²(ℂ)` of the decomposition. -/
noncomputable def suV (ℓ : ℕ) : Espace (dsp n ℓ) →ₗᵢ[ℂ] L2C :=
  normalize n ρ (tlin (ℓ + p0 n) (ℓ + q0 n) ρ) (tlin_isPS n ρ ℓ) (tlin_ne_zero _ _ ρ)

/-- The spin representation on `ℂ^{m+1}` as a map of `Espace m`. -/
noncomputable def spinE (m : ℕ) (u : SU2) (x : Espace m) : Espace m :=
  WithLp.toLp 2 (spinMat m (u : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x.ofLp)

/-- **`suV n ρ ℓ` intertwines spin `|k| + ℓ` with the principal series restricted to `SU(2)`.** -/
theorem principalSeries_suV (ℓ : ℕ) (u : SU2) (x : Espace (dsp n ℓ)) :
    principalSeries n ρ (SL2C.ofSU2 u) (suV n ρ ℓ x) = suV n ρ ℓ (spinE (dsp n ℓ) u x) := by
  simp only [suV, normalize_apply, map_smul, spinE]
  rw [tlin_isPS n ρ ℓ u]

lemma isPS_suV (ℓ : ℕ) :
    IsPSIntertwiner n ρ ((suV n ρ ℓ).toLinearMap ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Fin (dsp n ℓ + 1) → ℂ)).symm.toLinearMap) := by
  intro u x
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearIsometry.coe_toLinearMap]
  rw [principalSeries_suV]; rfl

/-- **Orthogonality of the spins.** -/
theorem suV_orthogonal : OrthogonalFamily ℂ (fun ℓ => Espace (dsp n ℓ)) (suV n ρ) := by
  intro ℓ ℓ' hne x y
  have hd : dsp n ℓ' ≠ dsp n ℓ := by rw [dsp_eq, dsp_eq]; omega
  have := inner_eq_zero_of_ne n ρ hd (isPS_suV n ρ ℓ') (isPS_suV n ρ ℓ) y.ofLp x.ofLp
  simpa using this

/-! ## The levels are filled -/

lemma sum_dims (ℓ : ℕ) :
    ∑ k : Fin (ℓ + 1), (dsp n k + 1) = (ℓ + p0 n + 1) * (ℓ + q0 n + 1) := by
  have hpq := p0_mul_q0 n
  rw [Fin.sum_univ_eq_sum_range (fun k => dsp n k + 1) (ℓ + 1)]
  induction ℓ with
  | zero => simp [dsp]; nlinarith
  | succ ℓ ih => rw [Finset.sum_range_succ, ih]; simp [dsp]; ring

lemma range_suV_le (k : ℕ) : LinearMap.range (suV n ρ k).toLinearMap ≤
    levelSpace (k + p0 n) (k + q0 n) ρ := by
  rintro _ ⟨x, rfl⟩
  simp only [LinearIsometry.coe_toLinearMap, normalize_apply, suV]
  exact Submodule.smul_mem _ _ (tlin_mem_levelSpace _ _ ρ _)

lemma levelSpace_mono_le {k ℓ : ℕ} (h : k ≤ ℓ) :
    levelSpace (k + p0 n) (k + q0 n) ρ ≤ levelSpace (ℓ + p0 n) (ℓ + q0 n) ρ := by
  have := levelSpace_le_add (k + p0 n) (k + q0 n) (ℓ - k) ρ
  rwa [show k + p0 n + (ℓ - k) = ℓ + p0 n by omega, show k + q0 n + (ℓ - k) = ℓ + q0 n by omega]
    at this

/-- The sum map `(x_k)_{k ≤ ℓ} ↦ Σ_k suV k x_k`. -/
noncomputable def sumMap (ℓ : ℕ) : ((k : Fin (ℓ + 1)) → Espace (dsp n k)) →ₗ[ℂ] L2C :=
  ∑ k : Fin (ℓ + 1), (suV n ρ k).toLinearMap ∘ₗ LinearMap.proj k

lemma sumMap_apply (ℓ : ℕ) (x : (k : Fin (ℓ + 1)) → Espace (dsp n k)) :
    sumMap n ρ ℓ x = ∑ k : Fin (ℓ + 1), suV n ρ k (x k) := by
  simp [sumMap]

lemma sumMap_injective (ℓ : ℕ) : Function.Injective (sumMap n ρ ℓ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  funext k
  have h1 : ⟪suV n ρ k (x k), sumMap n ρ ℓ x⟫_ℂ = ⟪x k, x k⟫_ℂ := by
    rw [sumMap_apply, inner_sum, Finset.sum_eq_single k]
    · exact (suV n ρ k).inner_map_map _ _
    · intro j _ hj
      exact suV_orthogonal n ρ (fun h => hj (Fin.ext h).symm) _ _
    · simp
  rw [hx, inner_zero_right] at h1
  exact (inner_self_eq_zero.mp h1.symm)

/-- **Each level space is filled by the spins `≤ ℓ`.** -/
theorem levelSpace_le_iSup (ℓ : ℕ) :
    levelSpace (ℓ + p0 n) (ℓ + q0 n) ρ ≤ ⨆ k, LinearMap.range (suV n ρ k).toLinearMap := by
  have hle : LinearMap.range (sumMap n ρ ℓ) ≤ levelSpace (ℓ + p0 n) (ℓ + q0 n) ρ := by
    rintro _ ⟨x, rfl⟩
    rw [sumMap_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact levelSpace_mono_le n ρ (Nat.lt_succ_iff.mp k.isLt) (range_suV_le n ρ k ⟨x k, rfl⟩)
  have hrank : Module.finrank ℂ (LinearMap.range (sumMap n ρ ℓ)) =
      (ℓ + p0 n + 1) * (ℓ + q0 n + 1) := by
    rw [LinearMap.finrank_range_of_inj (sumMap_injective n ρ ℓ), Module.finrank_pi_fintype]
    simp only [finrank_euclideanSpace_fin]
    exact sum_dims n ℓ
  have heq : LinearMap.range (sumMap n ρ ℓ) = levelSpace (ℓ + p0 n) (ℓ + q0 n) ρ := by
    refine Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) ?_)
    rw [hrank]; exact finrank_levelSpace_le _ _ ρ
  rw [← heq]
  rintro _ ⟨x, rfl⟩
  rw [sumMap_apply]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.mem_iSup_of_mem (k : ℕ) ⟨x k, rfl⟩

/-- **Completeness**: the spins span a dense subspace of `L²(ℂ)`. -/
theorem iSup_range_suV_orthogonal :
    (⨆ k, LinearMap.range (suV n ρ k).toLinearMap)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro h hh
  refine eq_zero_of_orthogonal_levels (p0 n) (q0 n) ρ h fun ℓ f hf => ?_
  exact Submodule.inner_right_of_mem_orthogonal (levelSpace_le_iSup n ρ ℓ hf) hh

/-- **The SU(2) decomposition of the principal series**: `L²(ℂ)` is the Hilbert direct sum of the
spins `|k| + ℓ`, `ℓ ∈ ℕ`, embedded by the isometries `suV n ρ ℓ`. -/
theorem principalSeries_isHilbertSum :
    IsHilbertSum ℂ (fun ℓ => Espace (dsp n ℓ)) (suV n ρ) := by
  refine IsHilbertSum.mk (suV_orthogonal n ρ) ?_
  rw [Submodule.topologicalClosure_eq_top_iff.mpr (iSup_range_suV_orthogonal n ρ)]

/-! ## Exactly these spins, each once -/

/-- **Only the spins `|k| + ℓ` occur**: an SU(2)-intertwiner from spin `m/2` into the principal
series vanishes unless `m = 2ℓ + |n|` for some `ℓ ∈ ℕ`. -/
theorem intertwiner_eq_zero {m : ℕ} (hm : ∀ ℓ : ℕ, m ≠ 2 * ℓ + n.natAbs)
    {S : (Fin (m + 1) → ℂ) →ₗ[ℂ] L2C} (hS : IsPSIntertwiner n ρ S) : S = 0 := by
  refine LinearMap.ext fun x => ?_
  have hx : S x ∈ (⨆ k, LinearMap.range (suV n ρ k).toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    refine Submodule.iSup_induction _ (motive := fun v => ⟪v, S x⟫_ℂ = 0) hv ?_ ?_ ?_
    · rintro k _ ⟨y, rfl⟩
      have hd : dsp n k ≠ m := by rw [dsp_eq]; exact fun h => hm k h.symm
      have := inner_eq_zero_of_ne n ρ hd.symm hS (isPS_suV n ρ k) x y.ofLp
      simpa using this
    · simp
    · intro a b ha hb; rw [inner_add_left, ha, hb, add_zero]
  rw [iSup_range_suV_orthogonal n ρ, Submodule.mem_bot] at hx
  simpa using hx

/-- **Each spin occurs once**: an SU(2)-intertwiner from spin `|k| + ℓ` into the principal series
is a multiple of `suV n ρ ℓ`. -/
theorem intertwiner_eq_smul (ℓ : ℕ) {S : (Fin (dsp n ℓ + 1) → ℂ) →ₗ[ℂ] L2C}
    (hS : IsPSIntertwiner n ρ S) :
    ∃ c : ℂ, ∀ x, S x = c • suV n ρ ℓ (WithLp.toLp 2 x) := by
  set V := (suV n ρ ℓ).toLinearMap ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (dsp n ℓ + 1) → ℂ)).symm.toLinearMap
  have hV := isPS_suV n ρ ℓ
  obtain ⟨c, hc⟩ := schur_eq_smul (gram_isSpinIntertwiner n ρ hS hV)
  refine ⟨c, fun x => ?_⟩
  have hx : S x - c • V x ∈ (⨆ k, LinearMap.range (suV n ρ k).toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    refine Submodule.iSup_induction _ (motive := fun v => ⟪v, S x - c • V x⟫_ℂ = 0) hv ?_ ?_ ?_
    · rintro k _ ⟨y, rfl⟩
      by_cases hk : k = ℓ
      · subst hk
        have h1 : ⟪V y.ofLp, S x⟫_ℂ = c * ⟪V y.ofLp, V x⟫_ℂ := by
          rw [inner_eq_gram, hc, inner_eq_gram V V]
          obtain ⟨c', hc'⟩ := schur_eq_smul (gram_isSpinIntertwiner n ρ hV hV)
          have hVV : ∀ z w, ⟪V w, V z⟫_ℂ = ∑ k, conj (w k) * z k := by
            intro z w
            have := (suV n ρ k).inner_map_map (WithLp.toLp 2 w) (WithLp.toLp 2 z)
            simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
              RCLike.star_def] at this
            simp only [V, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
              LinearIsometry.coe_toLinearMap]
            rw [show (WithLp.linearEquiv 2 ℂ (Fin (dsp n k + 1) → ℂ)).symm w = WithLp.toLp 2 w
              from rfl, show (WithLp.linearEquiv 2 ℂ (Fin (dsp n k + 1) → ℂ)).symm z =
                WithLp.toLp 2 z from rfl, this]
            refine Finset.sum_congr rfl fun j _ => mul_comm _ _
          rw [← inner_eq_gram V V, hVV, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]; ring
        change ⟪V y.ofLp, S x - c • V x⟫_ℂ = 0
        rw [inner_sub_right, inner_smul_right, h1, sub_self]
      · have hd : dsp n k ≠ dsp n ℓ := by rw [dsp_eq, dsp_eq]; omega
        have h1 := inner_eq_zero_of_ne n ρ hd.symm hS (isPS_suV n ρ k) x y.ofLp
        have h2 := (suV_orthogonal n ρ hk y (WithLp.toLp 2 x))
        have e1 : ⟪(suV n ρ k) y, S x⟫_ℂ = 0 := by simpa using h1
        have e2 : ⟪(suV n ρ k) y, V x⟫_ℂ = 0 := h2
        change ⟪(suV n ρ k) y, S x - c • V x⟫_ℂ = 0
        rw [inner_sub_right, inner_smul_right, e1, e2, mul_zero, sub_zero]
    · simp
    · intro a b ha hb; rw [inner_add_left, ha, hb, add_zero]
  rw [iSup_range_suV_orthogonal n ρ, Submodule.mem_bot, sub_eq_zero] at hx
  rw [hx]; rfl

end Lightlike.Lorentz
