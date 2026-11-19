import Lightlike.Spacetime.PoincareKilling

/-!
# All Killing fields of Minkowski space (GE12)

* `eq_affine_of_skew_deriv`: a `C²` field `X` on a normed space whose derivative is everywhere skew for a symmetric
  nondegenerate form `B` is affine, `X y = A y + c` with `A` `B`-skew (the second derivative is symmetric in its first two
  slots and skew in its last two, so it vanishes);
* `killing_eq_affField`: every `C²` Killing field of Minkowski space `ℝⁿ` is `affField A c` with `A` `η`-skew; with
  `affField_killing_iff` the Killing fields are exactly these;
* `finrank_skewEta`: the `η`-skew endomorphisms (the Lorentz algebra) have dimension `n (n - 1) / 2` (`skewEtaEquiv`: the
  lowered matrices are the antisymmetric matrices, `finrank_antisymmMatrices`);
* `finrank_killingFields`: **the Killing fields of Minkowski space form a vector space of dimension `n (n + 1) / 2`**
  (`killingFieldsEquiv`: they are the pairs `(A, c)`), the count of the GE12 check.

**Limits.** Killing fields are the `C²` fields with `L_X g = 0` in the form `IsKillingAt` (for the flat connection); flows
and isometries are not treated here.
-/

open Module
open scoped ContDiff Manifold

noncomputable section
namespace Lightlike

section Affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A trilinear expression symmetric in its first two arguments and antisymmetric in its last two vanishes. -/
theorem trilinear_symm_antisymm_eq_zero {T : E → E → E → ℝ} (hs : ∀ u v w, T u v w = T v u w)
    (ha : ∀ u v w, T u v w = - T u w v) (u v w : E) : T u v w = 0 := by
  have h1 := ha u v w
  have h2 := hs u w v
  have h3 := ha w u v
  have h4 := hs w v u
  have h5 := ha v w u
  have h6 := hs v u w
  linarith

/-- **A field whose derivative is everywhere `B`-skew is affine** (the Killing fields of a flat metric): if `X` is `C²` and
`B(DX(x) v, w) + B(v, DX(x) w) = 0` for all `x, v, w`, with `B` symmetric and nondegenerate, then `X y = A y + c` with `A` `B`-skew. -/
theorem eq_affine_of_skew_deriv (B : E →L[ℝ] E →L[ℝ] ℝ) (hBs : ∀ v w, B v w = B w v)
    (hBn : ∀ v, (∀ w, B v w = 0) → v = 0) {X : E → E} (hX : ContDiff ℝ 2 X)
    (hK : ∀ x v w, B (fderiv ℝ X x v) w + B v (fderiv ℝ X x w) = 0) :
    ∃ (A : E →L[ℝ] E) (c : E), (∀ v w, B (A v) w + B v (A w) = 0) ∧ ∀ y, X y = A y + c := by
  have hX1 : ContDiff ℝ 1 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
  have hdX : Differentiable ℝ (fderiv ℝ X) := hX1.differentiable (by norm_num)
  -- the second derivative vanishes
  have hD2 : ∀ x, fderiv ℝ (fderiv ℝ X) x = 0 := by
    intro x
    have hsym : ∀ u v, fderiv ℝ (fderiv ℝ X) x u v = fderiv ℝ (fderiv ℝ X) x v u := by
      intro u v
      exact (hX.contDiffAt.isSymmSndFDerivAt (by simp)) u v
    have hskew : ∀ u v w, B (fderiv ℝ (fderiv ℝ X) x u v) w + B v (fderiv ℝ (fderiv ℝ X) x u w) = 0 := by
      intro u v w
      let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
        (B.flip w).comp (ContinuousLinearMap.apply ℝ E v) + (B v).comp (ContinuousLinearMap.apply ℝ E w)
      have hL : ∀ y, L (fderiv ℝ X y) = 0 := fun y => by
        simpa [L] using hK y v w
      have hzero : (fun y => L (fderiv ℝ X y)) = fun _ => 0 := funext hL
      have hd : HasFDerivAt (fun y => L (fderiv ℝ X y)) (L.comp (fderiv ℝ (fderiv ℝ X) x)) x :=
        L.hasFDerivAt.comp x (hdX x).hasFDerivAt
      rw [hzero] at hd
      have := congrArg (fun f => f u) ((hasFDerivAt_const (0 : ℝ) x).unique hd)
      simpa [L] using this.symm
    ext u v
    refine hBn _ fun w => ?_
    let T : E → E → E → ℝ := fun u v w => B (fderiv ℝ (fderiv ℝ X) x u v) w
    have hs : ∀ u v w, T u v w = T v u w := fun u v w => by simp only [T, hsym u v]
    have ha : ∀ u v w, T u v w = - T u w v := fun u v w => by
      have := hskew u v w
      simp only [T]
      rw [hBs v] at this
      linarith
    simpa [T] using trilinear_symm_antisymm_eq_zero hs ha u v w
  -- the derivative is constant
  have hconst : ∀ x, fderiv ℝ X x = fderiv ℝ X 0 := fun x => is_const_of_fderiv_eq_zero hdX hD2 x 0
  set A := fderiv ℝ X 0
  have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
  have hg : Differentiable ℝ (fun y => A y + X 0) := A.differentiable.add_const _
  have heq : X = fun y => A y + X 0 := by
    refine eq_of_fderiv_eq hXd hg (fun y => ?_) 0 (by simp)
    rw [hconst y, (A.hasFDerivAt.add_const (X 0)).fderiv]
  exact ⟨A, X 0, fun v w => hK 0 v w, fun y => congrFun heq y⟩

end Affine

variable {n : ℕ}

/-- The antisymmetric `n × n` matrices. -/
def antisymmMatrices (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {M | ∀ i j, M i j = - M j i}
  add_mem' := by
    intro a b ha hb i j; simp only [Set.mem_ofPred_eq, Matrix.add_apply] at *; rw [ha i j, hb i j]; ring
  zero_mem' := by intro i j; simp
  smul_mem' := by
    intro c a ha i j; simp only [Set.mem_ofPred_eq, Matrix.smul_apply, smul_eq_mul] at *; rw [ha i j]; ring

/-- Antisymmetric matrices are their entries above the diagonal. -/
def antisymmEquiv (n : ℕ) : antisymmMatrices n ≃ₗ[ℝ] ({p : Fin n × Fin n // p.1 < p.2} → ℝ) where
  toFun M := fun p => M.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then - f ⟨(j, i), h'⟩ else 0, by
    intro i j
    simp only [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst h; simp
    · simp [h, not_lt_of_gt h]⟩
  map_add' a b := rfl
  map_smul' c a := rfl
  left_inv M := by
    obtain ⟨M, hM⟩ := M
    ext i j
    simp only [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h
      have := hM i i
      simp only [lt_irrefl, dite_false]
      linarith
    · simp [h, not_lt_of_gt h, hM i j]
  right_inv f := by
    funext p
    simp [p.2]

/-- The number of pairs `i < j` in `Fin n` is `n (n - 1) / 2`. -/
theorem card_pairs_lt (n : ℕ) : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun a b : Fin n => a < b), Fintype.card_sigma]
  have h : ∀ a : Fin n, Fintype.card {b : Fin n // a < b} = n - 1 - a := fun a => by
    rw [Fintype.card_subtype, ← Fin.card_Ioi]; congr 1; ext b; simp
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun a => n - 1 - a) n, Finset.sum_range_reflect (fun a => a) n, Finset.sum_range_id]

/-- **The antisymmetric `n × n` matrices have dimension `n (n - 1) / 2`.** -/
theorem finrank_antisymmMatrices (n : ℕ) : finrank ℝ (antisymmMatrices n) = n * (n - 1) / 2 := by
  rw [(antisymmEquiv n).finrank_eq, Module.finrank_fintype_fun_eq_card, card_pairs_lt]

/-- `η(v, eᵢ) = ηᵢᵢ vᵢ`. -/
theorem minkowskiForm_single_right (v : Fin n → ℝ) (i : Fin n) :
    minkowskiForm n v (Pi.single i 1) = etaDiag i * v i := by
  simp only [minkowskiForm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

/-- **The `η`-skew endomorphisms** of `ℝⁿ`, `η(A v, w) + η(v, A w) = 0` (the Lorentz algebra). -/
def skewEta (n : ℕ) : Submodule ℝ ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) where
  carrier := {A | ∀ v w, minkowskiForm n (A v) w + minkowskiForm n v (A w) = 0}
  add_mem' := by
    intro a b ha hb v w
    simp only [Set.mem_ofPred_eq, add_apply, map_add] at *
    have := ha v w; have := hb v w
    linarith
  zero_mem' := by intro v w; simp
  smul_mem' := by
    intro c a ha v w
    simp only [Set.mem_ofPred_eq, smul_apply, map_smul, smul_eq_mul] at *
    rw [← mul_add, ha v w, mul_zero]

/-- The matrix `η(A eⱼ, eᵢ)` of an endomorphism. -/
def lowerMat (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => minkowskiForm n (A (Pi.single j 1)) (Pi.single i 1)

/-- The endomorphism with lowered matrix `S`: `(A v)ᵢ = ηᵢᵢ Σⱼ Sᵢⱼ vⱼ`. -/
def raiseMat (S : Matrix (Fin n) (Fin n) ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.of fun i j => etaDiag i * S i j))

theorem raiseMat_apply (S : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    raiseMat S v i = etaDiag i * ∑ j, S i j * v j := by
  simp [raiseMat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- The `η`-skew endomorphisms are the antisymmetric lowered matrices. -/
def skewEtaEquiv (n : ℕ) : skewEta n ≃ₗ[ℝ] antisymmMatrices n where
  toFun A := ⟨lowerMat A.1, by
    intro i j
    have h := A.2 (Pi.single j 1) (Pi.single i 1)
    have hs : minkowskiForm n (Pi.single j 1) (A.1 (Pi.single i 1)) =
        minkowskiForm n (A.1 (Pi.single i 1)) (Pi.single j 1) := (minkowskiForm_isLorentzian n).symm _ _
    simp only [lowerMat, Matrix.of_apply]
    linarith⟩
  invFun S := ⟨raiseMat S.1, by
    intro v w
    simp only [minkowskiForm_apply, raiseMat_apply]
    have e1 : ∀ i, etaDiag i * (etaDiag i * ∑ j, S.1 i j * v j) * w i = ∑ j, S.1 i j * v j * w i := fun i => by
      rw [← mul_assoc, etaDiag_mul_self, one_mul, Finset.sum_mul]
    have e2 : ∀ i, etaDiag i * v i * (etaDiag i * ∑ j, S.1 i j * w j) = ∑ j, S.1 i j * w j * v i := fun i => by
      calc etaDiag i * v i * (etaDiag i * ∑ j, S.1 i j * w j) = (etaDiag i * etaDiag i) * ((∑ j, S.1 i j * w j) * v i) := by ring
        _ = _ := by rw [etaDiag_mul_self, one_mul, Finset.sum_mul]
    simp only [e1, e2]
    rw [← Finset.sum_add_distrib]
    conv_lhs => arg 2; ext i; rw [← Finset.sum_add_distrib]
    have h2 : ∑ i, ∑ j, S.1 i j * w j * v i = ∑ i, ∑ j, S.1 j i * w i * v j := Finset.sum_comm
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [S.2 j i]; ring⟩
  map_add' a b := by
    ext i j; simp [lowerMat]
  map_smul' c a := by
    ext i j; simp [lowerMat]
  left_inv A := by
    ext v i
    have hv : v = ∑ j, v j • (Pi.single j 1 : Fin n → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    show raiseMat (lowerMat A.1) v i = A.1 v i
    conv_rhs => rw [hv]
    simp only [raiseMat_apply, lowerMat, Matrix.of_apply, minkowskiForm_single_right, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    calc etaDiag i * (etaDiag i * A.1 (Pi.single j 1) i * v j)
        = (etaDiag i * etaDiag i) * (v j * A.1 (Pi.single j 1) i) := by ring
      _ = _ := by rw [etaDiag_mul_self, one_mul]
  right_inv S := by
    ext i j
    simp only [lowerMat, Matrix.of_apply, minkowskiForm_single_right, raiseMat_apply]
    rw [Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same, mul_one]; rw [← mul_assoc, etaDiag_mul_self, one_mul]
    · intro k _ hk; simp [hk]
    · simp

/-- **The Lorentz algebra of `ℝⁿ` has dimension `n (n - 1) / 2`.** -/
theorem finrank_skewEta (n : ℕ) : finrank ℝ (skewEta n) = n * (n - 1) / 2 := by
  rw [(skewEtaEquiv n).finrank_eq, finrank_antisymmMatrices]

/-- **The Poincaré parameters `(A, c)` form a space of dimension `n (n + 1) / 2`.** -/
theorem finrank_skewEta_prod (n : ℕ) : finrank ℝ (skewEta n × (Fin n → ℝ)) = n * (n + 1) / 2 := by
  have := Module.Free.of_divisionRing ℝ (skewEta n)
  rw [Module.finrank_prod, finrank_skewEta, Module.finrank_fin_fun]
  rcases n with _ | m
  · simp
  · have : (m + 1) * (m + 1 - 1) / 2 + (m + 1) = (m + 1) * (m + 1 + 1) / 2 := by
      simp only [Nat.add_sub_cancel]
      have h2 : (m + 1) * (m + 1 + 1) = (m + 1) * m + 2 * (m + 1) := by ring
      rw [h2, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    exact this


/-! ## The Killing fields of Minkowski space -/

/-- `IsKillingAt` for the flat connection is the `η`-skewness of the derivative. -/
theorem isKillingAt_flat_iff (X : Π y : Fin n → ℝ, TangentSpace 𝓘(ℝ, Fin n → ℝ) y) (x : Fin n → ℝ) :
    IsKillingAt (flatConnection (Fin n → ℝ)) (minkowskiMetric n) X x ↔
      ∀ v w : Fin n → ℝ, minkowskiForm n (fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x v) w +
        minkowskiForm n v (fderiv ℝ (X : (Fin n → ℝ) → (Fin n → ℝ)) x w) = 0 := Iff.rfl

/-- **Every `C²` Killing field of Minkowski space is affine with an `η`-skew linear part.** -/
theorem killing_eq_affField {X : Π y : Fin n → ℝ, TangentSpace 𝓘(ℝ, Fin n → ℝ) y}
    (hX : ContDiff ℝ 2 (X : (Fin n → ℝ) → (Fin n → ℝ)))
    (hK : ∀ x, IsKillingAt (flatConnection (Fin n → ℝ)) (minkowskiMetric n) X x) :
    ∃ (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (c : Fin n → ℝ),
      (∀ v w, minkowskiForm n (A v) w + minkowskiForm n v (A w) = 0) ∧ X = affField A c := by
  obtain ⟨A, c, hA, hXA⟩ := eq_affine_of_skew_deriv (minkowskiForm n) (minkowskiForm_isLorentzian n).symm
    (minkowskiForm_isLorentzian n).nondegenerate hX fun x v w => (isKillingAt_flat_iff X x).1 (hK x) v w
  exact ⟨A, c, hA, funext hXA⟩

/-- **The Killing fields of Minkowski space**: the `C²` fields that are Killing at every point. -/
def killingFields (n : ℕ) : Submodule ℝ ((Fin n → ℝ) → (Fin n → ℝ)) where
  carrier := {X | ContDiff ℝ 2 X ∧ ∀ x, IsKillingAt (flatConnection (Fin n → ℝ)) (minkowskiMetric n) X x}
  add_mem' := by
    rintro X Y ⟨hX, hKX⟩ ⟨hY, hKY⟩
    refine ⟨hX.add hY, fun x => (isKillingAt_flat_iff _ x).2 fun v w => ?_⟩
    have h1 := (isKillingAt_flat_iff X x).1 (hKX x) v w
    have h2 := (isKillingAt_flat_iff Y x).1 (hKY x) v w
    have hd : fderiv ℝ (X + Y) x = fderiv ℝ X x + fderiv ℝ Y x :=
      fderiv_add (hX.differentiable (by norm_num) x) (hY.differentiable (by norm_num) x)
    show minkowskiForm n (fderiv ℝ (X + Y) x v) w + minkowskiForm n v (fderiv ℝ (X + Y) x w) = 0
    rw [hd]
    simp only [add_apply, map_add]
    linarith
  zero_mem' := ⟨contDiff_const, fun x => (isKillingAt_flat_iff _ x).2 fun v w => by
    show minkowskiForm n (fderiv ℝ (fun _ => (0 : Fin n → ℝ)) x v) w + _ = 0
    simp⟩
  smul_mem' := by
    rintro a X ⟨hX, hKX⟩
    refine ⟨hX.const_smul a, fun x => (isKillingAt_flat_iff _ x).2 fun v w => ?_⟩
    have h1 := (isKillingAt_flat_iff X x).1 (hKX x) v w
    have hd : fderiv ℝ (a • X) x = a • fderiv ℝ X x := fderiv_const_smul (hX.differentiable (by norm_num) x) a
    show minkowskiForm n (fderiv ℝ (a • X) x v) w + minkowskiForm n v (fderiv ℝ (a • X) x w) = 0
    rw [hd]
    simp only [smul_apply, map_smul, smul_eq_mul]
    rw [← mul_add, h1, mul_zero]

/-- The Killing field of a Poincaré parameter `(A, c)`. -/
def minkowskiPoincareMap (n : ℕ) : (skewEta n × (Fin n → ℝ)) →ₗ[ℝ] killingFields n where
  toFun p := ⟨fun y => p.1.1 y + p.2, (p.1.1.contDiff.add contDiff_const), fun x =>
    (affField_killing_iff p.1.1 p.2 x).2 p.1.2⟩
  map_add' p q := by
    ext y; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_apply, Pi.add_apply]; abel
  map_smul' a p := by
    ext y i; simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Pi.add_apply]; ring

/-- **The Killing fields of Minkowski space are the Poincaré parameters `(A, c)`.** -/
theorem minkowskiPoincareMap_bijective (n : ℕ) : Function.Bijective (minkowskiPoincareMap n) := by
  constructor
  · intro p q h
    have hy : ∀ y, p.1.1 y + p.2 = q.1.1 y + q.2 := fun y => congrFun (congrArg Subtype.val h) y
    have hc : p.2 = q.2 := by simpa using hy 0
    refine Prod.ext (Subtype.ext (ContinuousLinearMap.ext fun y => ?_)) hc
    have := hy y; rw [hc] at this; exact add_right_cancel this
  · rintro ⟨X, hX, hK⟩
    obtain ⟨A, c, hA, hXA⟩ := killing_eq_affField (X := X) hX hK
    refine ⟨(⟨A, hA⟩, c), Subtype.ext (funext fun y => ?_)⟩
    show A y + c = X y
    rw [hXA]; rfl

/-- **The Killing fields of Minkowski space `ℝⁿ` form a vector space of dimension `n (n + 1) / 2`** (GE12 check). -/
theorem finrank_killingFields (n : ℕ) : finrank ℝ (killingFields n) = n * (n + 1) / 2 := by
  rw [← (LinearEquiv.ofBijective (minkowskiPoincareMap n) (minkowskiPoincareMap_bijective n)).finrank_eq, finrank_skewEta_prod]

end Lightlike
