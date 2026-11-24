import Mathlib

/-!
# The quantum group `U_q(sl₂)` as a Hopf algebra

For a field `k` and a unit `q : kˣ`, `UqSl2 k q` is the `k`-algebra with generators `E, F, K, K⁻¹`
and relations
`K K⁻¹ = K⁻¹ K = 1`, `K E = q² E K`, `K F = q⁻² F K`, `(q - q⁻¹) (E F - F E) = K - K⁻¹`.
The commutation relation is written without division, so it makes sense for every `q`.

Source: Turaev, *Quantum invariants of knots and 3-manifolds*, Chapter XI (the algebra `U_q(sl₂)`),
and Kassel, *Quantum Groups*, Chapter VI.
-/

open TensorProduct

namespace Lightlike.QuantumGroups

/-- The four generators of `U_q(sl₂)`. -/
inductive Gen
  | E | F | K | Ki

variable (k : Type*) [Field k] (q : kˣ)

/-- The defining relations of `U_q(sl₂)`, as relations on the free algebra. -/
inductive Rel : FreeAlgebra k Gen → FreeAlgebra k Gen → Prop
  | kki : Rel (FreeAlgebra.ι k Gen.K * FreeAlgebra.ι k Gen.Ki) 1
  | kik : Rel (FreeAlgebra.ι k Gen.Ki * FreeAlgebra.ι k Gen.K) 1
  | ke : Rel (FreeAlgebra.ι k Gen.K * FreeAlgebra.ι k Gen.E)
      (algebraMap k _ ((q : k) ^ 2) * (FreeAlgebra.ι k Gen.E * FreeAlgebra.ι k Gen.K))
  | kf : Rel (FreeAlgebra.ι k Gen.K * FreeAlgebra.ι k Gen.F)
      (algebraMap k _ ((↑q⁻¹ : k) ^ 2) * (FreeAlgebra.ι k Gen.F * FreeAlgebra.ι k Gen.K))
  | ef : Rel (algebraMap k _ ((q : k) - ↑q⁻¹) *
        (FreeAlgebra.ι k Gen.E * FreeAlgebra.ι k Gen.F - FreeAlgebra.ι k Gen.F * FreeAlgebra.ι k Gen.E))
      (FreeAlgebra.ι k Gen.K - FreeAlgebra.ι k Gen.Ki)

/-- The quantum group `U_q(sl₂)`. -/
abbrev UqSl2 := RingQuot (Rel k q)

namespace UqSl2

variable {k q}

/-- The generator `E`. -/
def E : UqSl2 k q := RingQuot.mkAlgHom k _ (FreeAlgebra.ι k Gen.E)
/-- The generator `F`. -/
def F : UqSl2 k q := RingQuot.mkAlgHom k _ (FreeAlgebra.ι k Gen.F)
/-- The generator `K`. -/
def K : UqSl2 k q := RingQuot.mkAlgHom k _ (FreeAlgebra.ι k Gen.K)
/-- The generator `K⁻¹`. -/
def Ki : UqSl2 k q := RingQuot.mkAlgHom k _ (FreeAlgebra.ι k Gen.Ki)

/-- The relation `K K⁻¹ = 1`. -/
theorem K_mul_Ki : (K : UqSl2 k q) * Ki = 1 := by
  simpa [E, F, K, Ki] using RingQuot.mkAlgHom_rel k (Rel.kki (k := k) (q := q))

/-- The relation `K⁻¹ K = 1`. -/
theorem Ki_mul_K : (Ki : UqSl2 k q) * K = 1 := by
  simpa [E, F, K, Ki] using RingQuot.mkAlgHom_rel k (Rel.kik (k := k) (q := q))

/-- The relation `K E = q² E K`. -/
theorem K_mul_E : (K : UqSl2 k q) * E = algebraMap k _ ((q : k) ^ 2) * (E * K) := by
  simpa [E, F, K, Ki] using RingQuot.mkAlgHom_rel k (Rel.ke (k := k) (q := q))

/-- The relation `K F = q⁻² F K`. -/
theorem K_mul_F : (K : UqSl2 k q) * F = algebraMap k _ ((↑q⁻¹ : k) ^ 2) * (F * K) := by
  simpa [E, F, K, Ki] using RingQuot.mkAlgHom_rel k (Rel.kf (k := k) (q := q))

/-- The relation `(q - q⁻¹)(E F - F E) = K - K⁻¹`. -/
theorem E_mul_F_sub : algebraMap k (UqSl2 k q) ((q : k) - ↑q⁻¹) * (E * F - F * E) = K - Ki := by
  simpa [E, F, K, Ki] using RingQuot.mkAlgHom_rel k (Rel.ef (k := k) (q := q))

theorem E_mul_Ki : (E : UqSl2 k q) * Ki = ((q : k) ^ 2) • (Ki * E) := by
  have h : (E : UqSl2 k q) = ((q : k) ^ 2) • (Ki * E * K) := by
    have := congrArg (fun x => Ki * x) (K_mul_E (k := k) (q := q))
    simp only [← mul_assoc, Ki_mul_K, one_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul] at this
    exact this.trans (by simp [mul_assoc])
  calc (E : UqSl2 k q) * Ki = (((q : k) ^ 2) • (Ki * E * K)) * Ki := by rw [← h]
    _ = ((q : k) ^ 2) • (Ki * E) := by simp [mul_assoc, K_mul_Ki]

theorem F_mul_K : (F : UqSl2 k q) * K = ((q : k) ^ 2) • (K * F) := by
  have h := K_mul_F (k := k) (q := q)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  calc (F : UqSl2 k q) * K = ((q : k) ^ 2) • (((↑q⁻¹ : k) ^ 2) • (F * K)) := by
        rw [smul_smul, ← mul_pow]; simp
    _ = ((q : k) ^ 2) • (K * F) := by rw [← h]

/-- The images of the generators under the comultiplication
`Δ E = E ⊗ K + 1 ⊗ E`, `Δ F = F ⊗ 1 + K⁻¹ ⊗ F`, `Δ K = K ⊗ K`, `Δ K⁻¹ = K⁻¹ ⊗ K⁻¹`. -/
def comulGen : Gen → UqSl2 k q ⊗[k] UqSl2 k q
  | .E => E ⊗ₜ K + 1 ⊗ₜ E
  | .F => F ⊗ₜ 1 + Ki ⊗ₜ F
  | .K => K ⊗ₜ K
  | .Ki => Ki ⊗ₜ Ki

theorem comul_commutator :
    (E ⊗ₜ K + 1 ⊗ₜ E : UqSl2 k q ⊗[k] UqSl2 k q) * (F ⊗ₜ 1 + Ki ⊗ₜ F)
      - (F ⊗ₜ 1 + Ki ⊗ₜ F) * (E ⊗ₜ K + 1 ⊗ₜ E)
    = (E * F - F * E) ⊗ₜ K + Ki ⊗ₜ (E * F - F * E) := by
  have h1 : ((E * Ki) ⊗ₜ[k] (K * F) : UqSl2 k q ⊗[k] UqSl2 k q) = (Ki * E) ⊗ₜ[k] (F * K) := by
    rw [E_mul_Ki, F_mul_K, TensorProduct.smul_tmul]
  simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub, h1]
  abel

theorem comul_ef :
    (algebraMap k (UqSl2 k q ⊗[k] UqSl2 k q) (q : k) -
        algebraMap k (UqSl2 k q ⊗[k] UqSl2 k q) (↑q⁻¹ : k)) *
      ((E ⊗ₜ K + 1 ⊗ₜ E : UqSl2 k q ⊗[k] UqSl2 k q) * (F ⊗ₜ 1 + Ki ⊗ₜ F)
        - (F ⊗ₜ 1 + Ki ⊗ₜ F) * (E ⊗ₜ K + 1 ⊗ₜ E)) = K ⊗ₜ K - Ki ⊗ₜ Ki := by
  rw [← map_sub (algebraMap k (UqSl2 k q ⊗[k] UqSl2 k q)), comul_commutator, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_add,
    TensorProduct.smul_tmul', ← TensorProduct.tmul_smul]
  have := E_mul_F_sub (k := k) (q := q)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at this
  rw [this]
  simp only [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

theorem comul_rel : ∀ ⦃x y⦄, Rel k q x y →
    FreeAlgebra.lift k (comulGen (k := k) (q := q)) x = FreeAlgebra.lift k comulGen y := by
  intro x y h
  cases h
  · simp [comulGen, Algebra.TensorProduct.tmul_mul_tmul, K_mul_Ki, Algebra.TensorProduct.one_def]
  · simp [comulGen, Algebra.TensorProduct.tmul_mul_tmul, Ki_mul_K, Algebra.TensorProduct.one_def]
  · simp only [map_mul, FreeAlgebra.lift_ι_apply, comulGen, mul_add, add_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, K_mul_E, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    simp [TensorProduct.smul_tmul', smul_add, mul_assoc]
  · simp only [map_mul, FreeAlgebra.lift_ι_apply, comulGen, mul_add, add_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, K_mul_F, K_mul_Ki, Ki_mul_K, AlgHom.commutes,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    simp [TensorProduct.smul_tmul', smul_add, mul_assoc]
  · simp only [map_mul, map_sub, FreeAlgebra.lift_ι_apply, comulGen, AlgHom.commutes]
    exact comul_ef (k := k) (q := q)

/-- The generator as an element of `UqSl2`. -/
def gen : Gen → UqSl2 k q
  | .E => E
  | .F => F
  | .K => K
  | .Ki => Ki

/-- Two algebra maps out of `U_q(sl₂)` agree when they agree on the generators. -/
theorem algHom_ext {B : Type*} [Semiring B] [Algebra k B] {f g : UqSl2 k q →ₐ[k] B}
    (h : ∀ x, f (gen x) = g (gen x)) : f = g := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext x
  show f (RingQuot.mkAlgHom k _ (FreeAlgebra.ι k x)) = g (RingQuot.mkAlgHom k _ (FreeAlgebra.ι k x))
  cases x
  · simpa [gen, E] using h Gen.E
  · simpa [gen, F] using h Gen.F
  · simpa [gen, K] using h Gen.K
  · simpa [gen, Ki] using h Gen.Ki

/-- The comultiplication. -/
noncomputable def comul : UqSl2 k q →ₐ[k] UqSl2 k q ⊗[k] UqSl2 k q :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k comulGen, comul_rel⟩

theorem comul_gen (x : Gen) : comul (gen x) = comulGen (k := k) (q := q) x := by
  cases x <;> simp [comul, gen, E, F, K, Ki]

/-- The images of the generators under the counit. -/
def counitGen : Gen → k
  | .E => 0
  | .F => 0
  | .K => 1
  | .Ki => 1

theorem counit_rel : ∀ ⦃x y⦄, Rel k q x y →
    FreeAlgebra.lift k (counitGen (k := k)) x = FreeAlgebra.lift k (counitGen (k := k)) y := by
  intro x y h
  cases h <;> simp [counitGen]

/-- The counit. -/
noncomputable def counit : UqSl2 k q →ₐ[k] k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k (counitGen (k := k)), counit_rel⟩

theorem counit_gen (x : Gen) : counit (gen x : UqSl2 k q) = counitGen (k := k) x := by
  cases x <;> simp [counit, gen, E, F, K, Ki]

/-- The coproduct of `E`: `ΔE = E ⊗ K + 1 ⊗ E`. -/
@[simp] theorem comul_E : comul (E : UqSl2 k q) = E ⊗ₜ K + 1 ⊗ₜ E := comul_gen Gen.E
/-- The coproduct of `F`: `ΔF = F ⊗ 1 + K⁻¹ ⊗ F`. -/
@[simp] theorem comul_F : comul (F : UqSl2 k q) = F ⊗ₜ 1 + Ki ⊗ₜ F := comul_gen Gen.F
/-- The coproduct of `K`: `ΔK = K ⊗ K`. -/
@[simp] theorem comul_K : comul (K : UqSl2 k q) = K ⊗ₜ K := comul_gen Gen.K
/-- The coproduct of `K⁻¹`: `ΔK⁻¹ = K⁻¹ ⊗ K⁻¹`. -/
@[simp] theorem comul_Ki : comul (Ki : UqSl2 k q) = Ki ⊗ₜ Ki := comul_gen Gen.Ki
/-- The counit of `E` is `0`. -/
@[simp] theorem counit_E : counit (E : UqSl2 k q) = 0 := counit_gen Gen.E
/-- The counit of `F` is `0`. -/
@[simp] theorem counit_F : counit (F : UqSl2 k q) = 0 := counit_gen Gen.F
/-- The counit of `K` is `1`. -/
@[simp] theorem counit_K : counit (K : UqSl2 k q) = 1 := counit_gen Gen.K
/-- The counit of `K⁻¹` is `1`. -/
@[simp] theorem counit_Ki : counit (Ki : UqSl2 k q) = 1 := counit_gen Gen.Ki

theorem coassoc_aux :
    (Algebra.TensorProduct.assoc k k k (UqSl2 k q) (UqSl2 k q) (UqSl2 k q)).toAlgHom.comp
      ((Algebra.TensorProduct.map comul (AlgHom.id k (UqSl2 k q))).comp comul)
      = (Algebra.TensorProduct.map (AlgHom.id k (UqSl2 k q)) comul).comp comul := by
  apply algHom_ext
  intro x
  cases x <;> simp [gen, add_tmul, tmul_add, Algebra.TensorProduct.one_def] <;> abel

theorem rTensor_aux :
    (Algebra.TensorProduct.map counit (AlgHom.id k (UqSl2 k q))).comp comul
      = (Algebra.TensorProduct.lid k (UqSl2 k q)).symm := by
  apply algHom_ext
  intro x
  cases x <;> simp [gen]

theorem lTensor_aux :
    (Algebra.TensorProduct.map (AlgHom.id k (UqSl2 k q)) counit).comp comul
      = (Algebra.TensorProduct.rid k k (UqSl2 k q)).symm := by
  apply algHom_ext
  intro x
  cases x <;> simp [gen]

/-- `U_q(sl₂)` is a bialgebra. -/
noncomputable instance : Bialgebra k (UqSl2 k q) :=
  Bialgebra.ofAlgHom comul counit coassoc_aux rTensor_aux lTensor_aux

theorem K_mul_FE : (K : UqSl2 k q) * (F * E) = (F * E) * K := by
  have h1 := K_mul_F (k := k) (q := q)
  have h2 := K_mul_E (k := k) (q := q)
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h1 h2
  calc (K : UqSl2 k q) * (F * E) = (K * F) * E := by rw [mul_assoc]
    _ = ((↑q⁻¹ : k) ^ 2) • (F * K) * E := by rw [h1]
    _ = ((↑q⁻¹ : k) ^ 2) • (F * (K * E)) := by rw [smul_mul_assoc, mul_assoc]
    _ = ((↑q⁻¹ : k) ^ 2) • (F * (((q : k) ^ 2) • (E * K))) := by rw [h2]
    _ = (F * E) * K := by
      rw [mul_smul_comm, smul_smul, ← mul_pow]; simp [mul_assoc]

/-- The images of the generators under the antipode (an algebra map to the opposite algebra):
`S E = -E K⁻¹`, `S F = -K F`, `S K = K⁻¹`, `S K⁻¹ = K`. -/
def antipodeGen : Gen → (UqSl2 k q)ᵐᵒᵖ
  | .E => MulOpposite.op ((-1 : k) • (E * Ki))
  | .F => MulOpposite.op ((-1 : k) • (K * F))
  | .K => MulOpposite.op Ki
  | .Ki => MulOpposite.op K

theorem antipode_rel : ∀ ⦃x y⦄, Rel k q x y →
    FreeAlgebra.lift k (antipodeGen (k := k) (q := q)) x
      = FreeAlgebra.lift k (antipodeGen (k := k) (q := q)) y := by
  intro x y h
  apply MulOpposite.unop_injective
  cases h
  · simp [antipodeGen, K_mul_Ki (k := k) (q := q)]
  · simp [antipodeGen, Ki_mul_K (k := k) (q := q)]
  · have aux : ((E : UqSl2 k q) * Ki) * Ki = ((q : k) ^ 2) • (Ki * (E * Ki)) := by
      conv_lhs => rw [E_mul_Ki]
      rw [smul_mul_assoc, mul_assoc]
    simp only [map_mul, map_sub, map_smul, map_one, FreeAlgebra.lift_ι_apply, antipodeGen,
      AlgHom.commutes, MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      MulOpposite.unop_sub, MulOpposite.unop_one]
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, MulOpposite.unop_smul,
      MulOpposite.unop_one, smul_mul_assoc, mul_smul_comm, mul_one, aux]
    module
  · have a1 : ((K : UqSl2 k q) * F) * Ki = ((q : k) ^ 2)⁻¹ • F := by
      rw [K_mul_F, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc,
        mul_assoc, K_mul_Ki, mul_one]
      simp [inv_pow]
    have a2 : (Ki : UqSl2 k q) * (K * F) = F := by rw [← mul_assoc, Ki_mul_K, one_mul]
    simp only [map_mul, map_sub, map_smul, map_one, FreeAlgebra.lift_ι_apply, antipodeGen,
      AlgHom.commutes, MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      MulOpposite.unop_sub, MulOpposite.unop_one]
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, MulOpposite.unop_smul,
      MulOpposite.unop_one, smul_mul_assoc, mul_smul_comm, mul_one, a1, a2]
    simp only [Units.val_inv_eq_inv_val, inv_pow]
    module
  · have h1 : (K : UqSl2 k q) * F * (E * Ki) = F * E := by
      calc (K : UqSl2 k q) * F * (E * Ki) = K * (F * E) * Ki := by simp [mul_assoc]
        _ = (F * E) * K * Ki := by rw [K_mul_FE]
        _ = F * E := by rw [mul_assoc, K_mul_Ki, mul_one]
    have h2 : (E : UqSl2 k q) * Ki * (K * F) = E * F := by
      rw [mul_assoc, ← mul_assoc Ki K F, Ki_mul_K, one_mul]
    have h3 := E_mul_F_sub (k := k) (q := q)
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h3
    simp only [Units.val_inv_eq_inv_val] at h3
    simp only [map_mul, map_sub, map_smul, map_one, FreeAlgebra.lift_ι_apply, antipodeGen,
      AlgHom.commutes, MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
      MulOpposite.unop_sub, MulOpposite.unop_one]
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, MulOpposite.unop_smul,
      MulOpposite.unop_one, smul_mul_smul_comm, h1, h2, mul_sub, smul_mul_assoc,
      mul_smul_comm, mul_one, Units.val_inv_eq_inv_val]
    linear_combination (norm := module) (-1 : k) • h3

/-- The antipode, as an algebra map to the opposite algebra. -/
noncomputable def antipodeOp : UqSl2 k q →ₐ[k] (UqSl2 k q)ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k antipodeGen, antipode_rel⟩

theorem antipodeOp_gen (x : Gen) :
    antipodeOp (gen x : UqSl2 k q) = antipodeGen (k := k) (q := q) x := by
  cases x <;> simp [antipodeOp, gen, E, F, K, Ki]

/-- The four generators `E, F, K, K⁻¹` generate `U_q(sl₂)` as a `k`-algebra. -/
theorem adjoin_gen : Algebra.adjoin k (Set.range (gen : Gen → UqSl2 k q)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, rfl⟩ := RingQuot.mkAlgHom_surjective k (Rel k q) y
  induction z using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 x =>
    cases x
    · exact Algebra.subset_adjoin ⟨Gen.E, rfl⟩
    · exact Algebra.subset_adjoin ⟨Gen.F, rfl⟩
    · exact Algebra.subset_adjoin ⟨Gen.K, rfl⟩
    · exact Algebra.subset_adjoin ⟨Gen.Ki, rfl⟩
  | mul a b ha hb => simpa using Subalgebra.mul_mem _ (ha trivial) (hb trivial)
  | add a b ha hb => simpa using Subalgebra.add_mem _ (ha trivial) (hb trivial)

/-- The antipode as a linear endomorphism. -/
noncomputable def antipodeLin : UqSl2 k q →ₗ[k] UqSl2 k q :=
  (MulOpposite.opLinearEquiv k).symm.toLinearMap ∘ₗ (antipodeOp (k := k) (q := q)).toLinearMap

/-- The antipode of `E`: `S E = -E K⁻¹`. -/
@[simp] theorem antipodeLin_E : antipodeLin (E : UqSl2 k q) = (-1 : k) • (E * Ki) :=
  congrArg MulOpposite.unop (antipodeOp_gen (k := k) (q := q) Gen.E)
/-- The antipode of `F`: `S F = -K F`. -/
@[simp] theorem antipodeLin_F : antipodeLin (F : UqSl2 k q) = (-1 : k) • (K * F) :=
  congrArg MulOpposite.unop (antipodeOp_gen (k := k) (q := q) Gen.F)
/-- The antipode of `K`: `S K = K⁻¹`. -/
@[simp] theorem antipodeLin_K : antipodeLin (K : UqSl2 k q) = Ki :=
  congrArg MulOpposite.unop (antipodeOp_gen (k := k) (q := q) Gen.K)
/-- The antipode of `K⁻¹`: `S K⁻¹ = K`. -/
@[simp] theorem antipodeLin_Ki : antipodeLin (Ki : UqSl2 k q) = K :=
  congrArg MulOpposite.unop (antipodeOp_gen (k := k) (q := q) Gen.Ki)
@[simp] theorem antipodeLin_one : antipodeLin (1 : UqSl2 k q) = 1 := by
  simp [antipodeLin]

open Coalgebra LinearMap in
/-- `U_q(sl₂)` is a Hopf algebra. -/
noncomputable instance : HopfAlgebra k (UqSl2 k q) :=
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp (k := k) (q := q)) adjoin_gen
    (by
      rintro _ ⟨x, rfl⟩
      cases x
      · show mul' k (UqSl2 k q) (rTensor _ (antipodeLin (k := k) (q := q)) (comul (E : UqSl2 k q)))
          = algebraMap k _ (counit (E : UqSl2 k q))
        simp [mul_assoc, Ki_mul_K (k := k) (q := q)]
        module
      · show mul' k (UqSl2 k q) (rTensor _ (antipodeLin (k := k) (q := q)) (comul (F : UqSl2 k q)))
          = algebraMap k _ (counit (F : UqSl2 k q))
        simp
        module
      · show mul' k (UqSl2 k q) (rTensor _ (antipodeLin (k := k) (q := q)) (comul (K : UqSl2 k q)))
          = algebraMap k _ (counit (K : UqSl2 k q))
        simp [Ki_mul_K (k := k) (q := q)]
      · show mul' k (UqSl2 k q) (rTensor _ (antipodeLin (k := k) (q := q)) (comul (Ki : UqSl2 k q)))
          = algebraMap k _ (counit (Ki : UqSl2 k q))
        simp [K_mul_Ki (k := k) (q := q)])
    (by
      rintro _ ⟨x, rfl⟩
      cases x
      · show mul' k (UqSl2 k q) (lTensor _ (antipodeLin (k := k) (q := q)) (comul (E : UqSl2 k q)))
          = algebraMap k _ (counit (E : UqSl2 k q))
        simp
        module
      · show mul' k (UqSl2 k q) (lTensor _ (antipodeLin (k := k) (q := q)) (comul (F : UqSl2 k q)))
          = algebraMap k _ (counit (F : UqSl2 k q))
        simp [← mul_assoc, Ki_mul_K (k := k) (q := q)]
        module
      · show mul' k (UqSl2 k q) (lTensor _ (antipodeLin (k := k) (q := q)) (comul (K : UqSl2 k q)))
          = algebraMap k _ (counit (K : UqSl2 k q))
        simp [K_mul_Ki (k := k) (q := q)]
      · show mul' k (UqSl2 k q) (lTensor _ (antipodeLin (k := k) (q := q)) (comul (Ki : UqSl2 k q)))
          = algebraMap k _ (counit (Ki : UqSl2 k q))
        simp [Ki_mul_K (k := k) (q := q)])

end UqSl2

end Lightlike.QuantumGroups
