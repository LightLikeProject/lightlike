import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# One slot of a tensor power: `h ⊗ 1` on `ℓ²(M, Z)`

For a bounded operator `h` on a Hilbert space `Z` and any index type `M`, the pointwise application `ψ ↦ h ∘ ψ` is a
bounded operator on `ℓ²(M, Z)` of norm at most `‖h‖`; `ℓ²(M, Z)` is `Z ⊗ ℓ²(M)`, and this is `h ⊗ 1`.

* `slotMap h`, `slotMap_apply`, `norm_slotMap_le`;
* `hasSum_repr_sq`, `coordFun`, `hasSum_coordFun_sq`, `coordL`: the coordinate isometry `ℓ²(M, Z) → ℓ²(M × ι)` for a
  Hilbert basis of `Z`;
* `fiber`, `uncoordL`, `slotC`, `norm_slotC_le`: `h ⊗ 1` on `ℓ²(M × ι)`, of norm at most `‖h‖`;
* `reindexL`, `slotEquiv`, `slotOp`, `norm_slotOp_le`, `dGammaTensor`, `norm_dGammaTensor_le`: `dΓₙ₊₁(h)` on
  `ℓ²(Fin (n+1) → ι)`, of norm at most `(n + 1) ‖h‖`.
-/

open scoped InnerProductSpace ENNReal

namespace Lightlike.OperatorAlgebras.SecondQuantSlot

variable {M : Type*} {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]

lemma two_toReal_pos : 0 < (2 : ℝ≥0∞).toReal := by norm_num

lemma norm_comp_rpow_le (h : Z →L[ℂ] Z) (z : Z) :
    ‖h z‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖h‖ ^ (2 : ℝ≥0∞).toReal * ‖z‖ ^ (2 : ℝ≥0∞).toReal := by
  rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (h.le_opNorm _) two_toReal_pos.le

lemma summable_comp (h : Z →L[ℂ] Z) (ψ : lp (fun _ : M => Z) 2) :
    Summable fun m => ‖h (ψ m)‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable fun m => ‖ψ m‖ ^ (2 : ℝ≥0∞).toReal := (lp.memℓp ψ).summable two_toReal_pos
  exact (hs.mul_left _).of_nonneg_of_le (fun m => by positivity) fun m => norm_comp_rpow_le h (ψ m)

lemma memℓp_comp (h : Z →L[ℂ] Z) (ψ : lp (fun _ : M => Z) 2) : Memℓp (fun m => h (ψ m)) 2 :=
  memℓp_gen (summable_comp h ψ)

/-- **`h ⊗ 1` on `ℓ²(M, Z)`**: `ψ ↦ h ∘ ψ`, of norm at most `‖h‖`. -/
noncomputable def slotMap (h : Z →L[ℂ] Z) : lp (fun _ : M => Z) 2 →L[ℂ] lp (fun _ : M => Z) 2 :=
  LinearMap.mkContinuous
    { toFun := fun ψ => ⟨fun m => h (ψ m), memℓp_comp h ψ⟩
      map_add' := fun ψ φ => by
        ext m
        show h ((ψ + φ) m) = h (ψ m) + h (φ m)
        simp
      map_smul' := fun c ψ => by
        ext m
        show h ((c • ψ) m) = c • h (ψ m)
        simp }
    ‖h‖ fun ψ => by
      refine lp.norm_le_of_tsum_le two_toReal_pos (by positivity) ?_
      have hs : Summable fun m => ‖ψ m‖ ^ (2 : ℝ≥0∞).toReal := (lp.memℓp ψ).summable two_toReal_pos
      calc ∑' m, ‖h (ψ m)‖ ^ (2 : ℝ≥0∞).toReal
          ≤ ∑' m, ‖h‖ ^ (2 : ℝ≥0∞).toReal * ‖ψ m‖ ^ (2 : ℝ≥0∞).toReal :=
            (summable_comp h ψ).tsum_le_tsum (fun m => norm_comp_rpow_le h (ψ m)) (hs.mul_left _)
        _ = ‖h‖ ^ (2 : ℝ≥0∞).toReal * ‖ψ‖ ^ (2 : ℝ≥0∞).toReal := by
            rw [tsum_mul_left, lp.norm_rpow_eq_tsum two_toReal_pos]
        _ = (‖h‖ * ‖ψ‖) ^ (2 : ℝ≥0∞).toReal := (Real.mul_rpow (norm_nonneg _) (norm_nonneg _)).symm

lemma slotMap_apply (h : Z →L[ℂ] Z) (ψ : lp (fun _ : M => Z) 2) (m : M) : slotMap h ψ m = h (ψ m) := rfl

/-- **`‖h ⊗ 1‖ ≤ ‖h‖`.** -/
theorem norm_slotMap_le (h : Z →L[ℂ] Z) : ‖(slotMap h : lp (fun _ : M => Z) 2 →L[ℂ] _)‖ ≤ ‖h‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg h) _

variable {ι : Type*} [CompleteSpace Z] (b : HilbertBasis ι ℂ Z)

/-- Parseval: `∑ₖ |⟪bₖ, z⟫|² = ‖z‖²`. -/
lemma hasSum_repr_sq (z : Z) : HasSum (fun k => ‖b.repr z k‖ ^ 2) (‖z‖ ^ 2) := by
  have := lp.hasSum_norm two_toReal_pos (b.repr z)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at this
  exact this

/-- The coordinates `(m, k) ↦ ⟪bₖ, ψ m⟫` of `ψ ∈ ℓ²(M, Z)`. -/
noncomputable def coordFun (ψ : lp (fun _ : M => Z) 2) (p : M × ι) : ℂ := b.repr (ψ p.1) p.2

/-- **`∑_{(m, k)} |⟪bₖ, ψ m⟫|² = ‖ψ‖²`.** -/
lemma hasSum_coordFun_sq (ψ : lp (fun _ : M => Z) 2) :
    HasSum (fun p => ‖coordFun b ψ p‖ ^ 2) (‖ψ‖ ^ 2) := by
  have hfib : ∀ m, HasSum (fun k => ‖b.repr (ψ m) k‖ ^ 2) (‖ψ m‖ ^ 2) := fun m => hasSum_repr_sq b (ψ m)
  have hout : HasSum (fun m => ‖ψ m‖ ^ 2) (‖ψ‖ ^ 2) := by
    have := lp.hasSum_norm two_toReal_pos ψ
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using this
  have hs : Summable (fun p : M × ι => ‖coordFun b ψ p‖ ^ 2) := by
    refine (summable_prod_of_nonneg fun p => sq_nonneg _).2 ⟨fun m => (hfib m).summable, ?_⟩
    simp only [coordFun, (hfib _).tsum_eq]
    exact hout.summable
  convert hs.hasSum using 1
  rw [hs.tsum_prod' fun m => (hfib m).summable]
  simp only [coordFun, (hfib _).tsum_eq]
  exact hout.tsum_eq.symm

lemma memℓp_coordFun (ψ : lp (fun _ : M => Z) 2) : Memℓp (coordFun b ψ) 2 :=
  memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (hasSum_coordFun_sq b ψ).summable)

/-- **The coordinate isometry** `ℓ²(M, Z) → ℓ²(M × ι)`, `ψ ↦ ((m, k) ↦ ⟪bₖ, ψ m⟫)`. -/
noncomputable def coordL : lp (fun _ : M => Z) 2 →ₗᵢ[ℂ] lp (fun _ : M × ι => ℂ) 2 where
  toFun ψ := ⟨coordFun b ψ, memℓp_coordFun b ψ⟩
  map_add' ψ φ := by
    ext p
    show b.repr ((ψ + φ) p.1) p.2 = b.repr (ψ p.1) p.2 + b.repr (φ p.1) p.2
    simp
  map_smul' c ψ := by
    ext p
    show b.repr ((c • ψ) p.1) p.2 = c • b.repr (ψ p.1) p.2
    simp
  norm_map' ψ := by
    have h1 := lp.norm_rpow_eq_tsum two_toReal_pos (⟨coordFun b ψ, memℓp_coordFun b ψ⟩ : lp (fun _ : M × ι => ℂ) 2)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
    have h2 : ‖(⟨coordFun b ψ, memℓp_coordFun b ψ⟩ : lp (fun _ : M × ι => ℂ) 2)‖ ^ 2 = ‖ψ‖ ^ 2 :=
      h1.trans (hasSum_coordFun_sq b ψ).tsum_eq
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

lemma summable_sq (c : lp (fun _ : M × ι => ℂ) 2) : Summable fun p => ‖c p‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (lp.memℓp c).summable two_toReal_pos

lemma summable_fiber (c : lp (fun _ : M × ι => ℂ) 2) (m : M) : Summable fun k => ‖c (m, k)‖ ^ 2 :=
  ((summable_prod_of_nonneg fun p => sq_nonneg _).1 (summable_sq c)).1 m

/-- The fiber `k ↦ c (m, k)`, in `ℓ²(ι)`. -/
noncomputable def fiber (c : lp (fun _ : M × ι => ℂ) 2) (m : M) : lp (fun _ : ι => ℂ) 2 :=
  ⟨fun k => c (m, k), memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using summable_fiber c m)⟩

lemma norm_fiber_sq (c : lp (fun _ : M × ι => ℂ) 2) (m : M) : ‖fiber c m‖ ^ 2 = ∑' k, ‖c (m, k)‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum two_toReal_pos (fiber c m)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
  exact this

/-- `c ↦ (m ↦ ∑ₖ c (m, k) bₖ)`. -/
noncomputable def uncoordFun (c : lp (fun _ : M × ι => ℂ) 2) (m : M) : Z := b.repr.symm (fiber c m)

lemma hasSum_uncoordFun_sq (c : lp (fun _ : M × ι => ℂ) 2) :
    HasSum (fun m => ‖uncoordFun b c m‖ ^ 2) (‖c‖ ^ 2) := by
  have hn : ∀ m, ‖uncoordFun b c m‖ ^ 2 = ∑' k, ‖c (m, k)‖ ^ 2 := fun m => by
    rw [uncoordFun, LinearIsometryEquiv.norm_map, norm_fiber_sq]
  simp only [hn]
  have hout : Summable fun m => ∑' k, ‖c (m, k)‖ ^ 2 :=
    ((summable_prod_of_nonneg fun p => sq_nonneg _).1 (summable_sq c)).2
  convert hout.hasSum using 1
  have h1 := lp.norm_rpow_eq_tsum two_toReal_pos c
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
  rw [h1, (summable_sq c).tsum_prod' (summable_fiber c)]

/-- **The inverse coordinates** `ℓ²(M × ι) → ℓ²(M, Z)`, an isometry. -/
noncomputable def uncoordL : lp (fun _ : M × ι => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : M => Z) 2 where
  toFun c := ⟨uncoordFun b c, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (hasSum_uncoordFun_sq b c).summable)⟩
  map_add' c d := by
    ext m
    show b.repr.symm (fiber (c + d) m) = b.repr.symm (fiber c m) + b.repr.symm (fiber d m)
    rw [← map_add]; congr 1
  map_smul' r c := by
    ext m
    show b.repr.symm (fiber (r • c) m) = r • b.repr.symm (fiber c m)
    rw [← map_smul]; congr 1
  norm_map' c := by
    have h1 := lp.norm_rpow_eq_tsum two_toReal_pos
      (⟨uncoordFun b c, memℓp_gen (by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using (hasSum_uncoordFun_sq b c).summable)⟩ :
        lp (fun _ : M => Z) 2)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (h1.trans (hasSum_uncoordFun_sq b c).tsum_eq)

/-- **`h ⊗ 1` in coordinates**, on `ℓ²(M × ι)`: `coordL ∘ slotMap h ∘ uncoordL`. -/
noncomputable def slotC (h : Z →L[ℂ] Z) : lp (fun _ : M × ι => ℂ) 2 →L[ℂ] lp (fun _ : M × ι => ℂ) 2 :=
  (coordL b).toContinuousLinearMap ∘L slotMap h ∘L (uncoordL b).toContinuousLinearMap

/-- **`‖h ⊗ 1‖ ≤ ‖h‖` in coordinates.** -/
theorem norm_slotC_le (h : Z →L[ℂ] Z) : ‖(slotC b h : lp (fun _ : M × ι => ℂ) 2 →L[ℂ] _)‖ ≤ ‖h‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _) (ContinuousLinearMap.opNorm_comp_le _ _)
    (norm_nonneg _) zero_le_one).trans ?_
  rw [one_mul]
  exact (mul_le_mul (norm_slotMap_le h) (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)
    (norm_nonneg _)).trans (by rw [mul_one])

omit [CompleteSpace Z] in
lemma summable_reindex {α β : Type*} (e : α ≃ β) (f : lp (fun _ : β => ℂ) 2) :
    Summable fun a => ‖f (e a)‖ ^ (2 : ℝ≥0∞).toReal :=
  (e.summable_iff (f := fun b => ‖f b‖ ^ (2 : ℝ≥0∞).toReal)).2 ((lp.memℓp f).summable two_toReal_pos)

/-- **Reindexing `ℓ²`** along an equivalence `e : α ≃ β`, `f ↦ f ∘ e`, an isometric isomorphism. -/
noncomputable def reindexL {α β : Type*} (e : α ≃ β) : lp (fun _ : β => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : α => ℂ) 2 where
  toFun f := ⟨fun a => f (e a), memℓp_gen (summable_reindex e f)⟩
  invFun g := ⟨fun b => g (e.symm b), memℓp_gen (summable_reindex e.symm g)⟩
  map_add' f g := by ext a; rfl
  map_smul' c f := by ext a; rfl
  left_inv f := by ext b; show f (e (e.symm b)) = f b; rw [e.apply_symm_apply]
  right_inv g := by ext a; show g (e.symm (e a)) = g a; rw [e.symm_apply_apply]
  norm_map' f := by
    have h1 := lp.norm_rpow_eq_tsum two_toReal_pos
      (⟨fun a => f (e a), memℓp_gen (summable_reindex e f)⟩ : lp (fun _ : α => ℂ) 2)
    have h2 := lp.norm_rpow_eq_tsum two_toReal_pos f
    have h3 : ∑' a, ‖f (e a)‖ ^ (2 : ℝ≥0∞).toReal = ∑' b, ‖f b‖ ^ (2 : ℝ≥0∞).toReal :=
      e.tsum_eq (fun b => ‖f b‖ ^ (2 : ℝ≥0∞).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2 h3
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by
      show ‖(⟨fun a => f (e a), memℓp_gen (summable_reindex e f)⟩ : lp (fun _ : α => ℂ) 2)‖ ^ 2 = ‖f‖ ^ 2
      rw [h1, h2, h3])

variable {n : ℕ}

/-- The equivalence `(Fin (n+1) → ι) ≃ (Fin n → ι) × ι` that takes out slot `j`. -/
def slotEquiv (j : Fin (n + 1)) : (Fin (n + 1) → ι) ≃ (Fin n → ι) × ι :=
  (Fin.insertNthEquiv (fun _ => ι) j).symm.trans (Equiv.prodComm _ _)

/-- **`h` acting on slot `j`** of `ℓ²(Fin (n+1) → ι)`, the coordinate model of `Z^{⊗(n+1)}`. -/
noncomputable def slotOp (j : Fin (n + 1)) (h : Z →L[ℂ] Z) :
    lp (fun _ : Fin (n + 1) → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin (n + 1) → ι => ℂ) 2 :=
  (reindexL (slotEquiv j)).toLinearIsometry.toContinuousLinearMap ∘L slotC b h ∘L
    (reindexL (slotEquiv j)).symm.toLinearIsometry.toContinuousLinearMap

theorem norm_slotOp_le (j : Fin (n + 1)) (h : Z →L[ℂ] Z) : ‖slotOp b j h‖ ≤ ‖h‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul (LinearIsometry.norm_toContinuousLinearMap_le _) (ContinuousLinearMap.opNorm_comp_le _ _)
    (norm_nonneg _) zero_le_one).trans ?_
  rw [one_mul]
  exact (mul_le_mul (norm_slotC_le b h) (LinearIsometry.norm_toContinuousLinearMap_le _) (norm_nonneg _)
    (norm_nonneg _)).trans (by rw [mul_one])

/-- **`dΓₙ₊₁(h) = ∑ⱼ 1 ⊗ ⋯ ⊗ h ⊗ ⋯ ⊗ 1`** on the coordinate model `ℓ²(Fin (n+1) → ι)` of `Z^{⊗(n+1)}`
(Dereziński, Section 5.2, p. 19). -/
noncomputable def dGammaTensor (n : ℕ) (h : Z →L[ℂ] Z) :
    lp (fun _ : Fin (n + 1) → ι => ℂ) 2 →L[ℂ] lp (fun _ : Fin (n + 1) → ι => ℂ) 2 :=
  ∑ j, slotOp b j h

/-- **`‖dΓₙ₊₁(h)‖ ≤ (n + 1) ‖h‖`.** -/
theorem norm_dGammaTensor_le (n : ℕ) (h : Z →L[ℂ] Z) : ‖dGammaTensor b n h‖ ≤ (n + 1) * ‖h‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin (n + 1), ‖slotOp b j h‖ ≤ ∑ _j : Fin (n + 1), ‖h‖ :=
        Finset.sum_le_sum fun j _ => norm_slotOp_le b j h
    _ = (n + 1) * ‖h‖ := by simp

end Lightlike.OperatorAlgebras.SecondQuantSlot
