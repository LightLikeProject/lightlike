module

public import Lightlike.Lorentz.LimitFormula
public import Lightlike.Lorentz.ParamIntegral
public import Lightlike.Lorentz.SpinVectors

/-!
# The average over SU(2) conjugation (milestone HA2)

For a function `F` on `2 × 2` complex matrices, the **SU(2) conjugation average**

    F♮(X) = ∫_{SU(2)} F(k⁻¹ X k) dk

is invariant under conjugation by `SU(2)`, so the limit formula (`limit_formula`) applies to it.
In the Plancherel formula it is applied to `F = f* ∗ f`, where `F(1) = ‖f‖²` and where the
`SU(2)` average does not change the integrals of the kernels over the diagonal.

## Construction

Instead of the Haar measure of `SU(2)` the average is taken over `ℂ²` with a radial weight. For
`v = (a, b) ∈ ℂ²` let `K_v = [[a, -b̄], [b, ā]]` (`kv`). Then `K_v* K_v = K_v K_v* = |v|²`, so
`K_v / |v| ∈ SU(2)` for `v ≠ 0`, and `X ↦ |v|⁻² K_v* X K_v` (`conjV`) is conjugation by it. With a
smooth bump `ψ` on `ℝ`, equal to `1` near `1` and supported in `(1/2, 3/2)` (`avgBump`),

    F♮(X) = (∫ ψ(|v|²) d⁴v)⁻¹ ∫_{ℂ²} ψ(|v|²) F(|v|⁻² K_v* X K_v) d⁴v      (`su2Avg`).

Since `k K_v = K_{k v}` for `k ∈ SU(2)` (`mul_kv`) and `v ↦ k v` preserves Lebesgue measure on
`ℂ²` (`measurePreserving_mulVec`), the substitution `v ↦ k* v` gives the invariance
(`isSU2ConjInvariant_su2Avg`). The push-forward of `ψ(|v|²) d⁴v` to `SU(2) ≅ S³` is a multiple of
the Haar measure, so `su2Avg` is the Haar average; this identification is not needed, because
only the properties below are used.

## Main results

- `contDiff_su2Avg`: `F♮` is smooth if `F` is (differentiation under the integral sign,
  `contDiff_parametric_integral_infty`).
- `hasCompactSupport_su2Avg`: `F♮` has compact support if `F` has, since
  `‖X‖ ≤ 32 ‖|v|⁻² K_v* X K_v‖` on the support of the weight.
- `su2Avg_one`: `F♮(1) = F(1)`.
- `isSU2ConjInvariant_su2Avg`: `F♮` is invariant under `SU(2)` conjugation.
- `su2Avg_eq_self`: if `F` is already invariant, then `F♮ = F`.

## Conventions

As in `LimitFormula.lean`, functions live on the arrays `Fin 2 → Fin 2 → ℂ` (written `P2`),
which carry the sup norm, and matrix products are taken in `Matrix (Fin 2) (Fin 2) ℂ` through
`Matrix.of`. The scalar `|v|⁻²` in `conjV` is real, so that the parameter of the integral is a
measurable map into a real normed space.

## References

- I. M. Gel'fand, M. A. Naimark, *Unitary representations of the Lorentz group*, Izv. Akad. Nauk
  SSSR 11 (1947); M. A. Naimark, *Linear representations of the Lorentz group* (1964), ch. III.
- Harish-Chandra, *The Plancherel formula for complex semisimple Lie groups*, Trans. AMS 76
  (1954).
-/

@[expose] public section

open MeasureTheory Complex Metric
open scoped Matrix ComplexConjugate ContDiff

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "P2" => Fin 2 → Fin 2 → ℂ

namespace Lightlike.Lorentz

/-! ### Triple products of arrays -/

/-- The matrix product `A X B` of three arrays. -/
noncomputable def mm3 (A X B : P2) : P2 := Matrix.of A * Matrix.of X * Matrix.of B

/-- The entries of a triple product. -/
lemma mm3_apply (A X B : P2) (i j : Fin 2) :
    mm3 A X B i j = ∑ k, ∑ l, A i l * X l k * B k j := by
  simp only [mm3, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]

/-- A triple product of smooth arrays is smooth. -/
lemma _root_.ContDiff.mm3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {f g h : E → P2} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (hh : ContDiff ℝ n h) : ContDiff ℝ n (fun x => mm3 (f x) (g x) (h x)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [mm3_apply]
  refine ContDiff.sum fun k _ => ContDiff.sum fun l _ => ?_
  refine (ContDiff.mul ?_ ?_).mul ?_
  · exact (contDiff_apply_apply (𝕜 := ℝ) i l).comp hf
  · exact (contDiff_apply_apply (𝕜 := ℝ) l k).comp hg
  · exact (contDiff_apply_apply (𝕜 := ℝ) k j).comp hh

/-- `‖A X B‖ ≤ 4 ‖A‖ ‖X‖ ‖B‖` in the sup norm. -/
lemma norm_mm3_le (A X B : P2) : ‖mm3 A X B‖ ≤ 4 * ‖A‖ * ‖X‖ * ‖B‖ := by
  have h0 : 0 ≤ 4 * ‖A‖ * ‖X‖ * ‖B‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  rw [mm3_apply]
  calc ‖∑ k, ∑ l, A i l * X l k * B k j‖
      ≤ ∑ k : Fin 2, ∑ l : Fin 2, ‖A‖ * ‖X‖ * ‖B‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (norm_apply_le A i l) (norm_apply_le X l k)
          (norm_nonneg _) (norm_nonneg _)) (norm_apply_le B k j) (norm_nonneg _) (by positivity)
    _ = 4 * ‖A‖ * ‖X‖ * ‖B‖ := by simp only [Fin.sum_univ_two]; ring

/-- An array whose entries are bounded by `R` has norm at most `R`. -/
lemma norm_mat2_le {a b c d : ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R)
    (hc : ‖c‖ ≤ R) (hd : ‖d‖ ≤ R) : ‖mat2 a b c d‖ ≤ R := by
  refine (pi_norm_le_iff_of_nonneg hR).2 fun i => (pi_norm_le_iff_of_nonneg hR).2 fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [ha, hb, hc, hd]

/-! ### The matrices `K_v` -/

/-! `|v|² = |v₀|² + |v₁|²` is `nsq` from `Lightlike.Lorentz.SpinVectors`. -/

lemma continuous_nsq : Continuous nsq := by unfold nsq; fun_prop

/-- `|v|² = v₀ v̄₀ + v₁ v̄₁` in `ℂ`. -/
lemma nsq_ofReal (v : Fin 2 → ℂ) :
    ((nsq v : ℝ) : ℂ) = v 0 * conj (v 0) + v 1 * conj (v 1) := by
  simp only [nsq, ofReal_add, ofReal_pow, mul_conj']

/-- `K_v = [[v₀, -v̄₁], [v₁, v̄₀]]`, which is `|v|` times an element of `SU(2)`. -/
noncomputable def kv (v : Fin 2 → ℂ) : P2 := mat2 (v 0) (-conj (v 1)) (v 1) (conj (v 0))

/-- `K_v* = [[v̄₀, v̄₁], [-v₁, v₀]]`. -/
noncomputable def kvs (v : Fin 2 → ℂ) : P2 := mat2 (conj (v 0)) (conj (v 1)) (-(v 1)) (v 0)

lemma continuous_kv : Continuous kv := by
  refine continuous_mat2 ?_ ?_ ?_ ?_ <;> fun_prop

lemma continuous_kvs : Continuous kvs := by
  refine continuous_mat2 ?_ ?_ ?_ ?_ <;> fun_prop

/-- `kvs v` is the adjoint of `kv v`. -/
lemma kvs_eq_star (v : Fin 2 → ℂ) : Matrix.of (kvs v) = star (Matrix.of (kv v)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kvs, kv, Matrix.of_apply, Matrix.star_apply]

/-- `K_v* K_v = |v|²`. -/
lemma kvs_mul_kv (v : Fin 2 → ℂ) : Matrix.of (kvs v) * Matrix.of (kv v) = nsq v • (1 : M2) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, real_smul, nsq_ofReal]
  fin_cases i <;> fin_cases j <;> simp [kvs, kv, Matrix.of_apply] <;> ring

/-- `K_v K_v* = |v|²`. -/
lemma kv_mul_kvs (v : Fin 2 → ℂ) : Matrix.of (kv v) * Matrix.of (kvs v) = nsq v • (1 : M2) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, real_smul, nsq_ofReal]
  fin_cases i <;> fin_cases j <;> simp [kvs, kv, Matrix.of_apply] <;> ring

/-- `det K_v = |v|²`. -/
lemma det_kvs (v : Fin 2 → ℂ) : (Matrix.of (kvs v)).det = (nsq v : ℂ) := by
  rw [Matrix.det_fin_two, nsq_ofReal]
  simp [kvs, Matrix.of_apply]
  ring

/-- A real multiple of a complex matrix is the same as the complex multiple. -/
lemma real_smul_M2 (r : ℝ) (A : M2) : r • A = (r : ℂ) • A := by
  ext i j
  simp only [Matrix.smul_apply, real_smul, smul_eq_mul]

/-- The entries of an element of `SU(2)`:`U = [[a, b], [-b̄, ā]]` with `|a|² + |b|² = 1`. -/
lemma SU2_entries {U : M2} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    U 1 1 = conj (U 0 0) ∧ U 1 0 = -conj (U 0 1) ∧
      U 0 0 * conj (U 0 0) + U 0 1 * conj (U 0 1) = 1 := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff] at hU
  obtain ⟨h1, hdet⟩ := hU
  have e : ∀ i j, (U * star U) i j = (1 : M2) i j := fun i j => by rw [h1]
  have h00 : U 0 0 * conj (U 0 0) + U 0 1 * conj (U 0 1) = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using e 0 0
  have h10 : U 1 0 * conj (U 0 0) + U 1 1 * conj (U 0 1) = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using e 1 0
  have hd := hdet
  rw [Matrix.det_fin_two] at hd
  refine ⟨?_, ?_, h00⟩
  · linear_combination (-(U 1 1)) * h00 + U 0 1 * h10 + conj (U 0 0) * hd
  · linear_combination (-(U 1 0)) * h00 + U 0 0 * h10 - conj (U 0 1) * hd

/-- `U K_v = K_{U v}` for `U ∈ SU(2)`. -/
lemma mul_kv {U : M2} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    U * Matrix.of (kv v) = Matrix.of (kv (U *ᵥ v)) := by
  obtain ⟨hd, hc, -⟩ := SU2_entries hU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, kv, Matrix.of_apply, Matrix.mulVec, dotProduct,
      hd, hc]
  ring

/-- `|U v| = |v|` for `U ∈ SU(2)`. -/
lemma nsq_mulVec {U : M2} (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    nsq (U *ᵥ v) = nsq v := by
  obtain ⟨hd, hc, h00⟩ := SU2_entries hU
  apply ofReal_injective
  rw [nsq_ofReal, nsq_ofReal]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd, hc, map_add, map_mul, map_neg,
    conj_conj]
  linear_combination (v 0 * conj (v 0) + v 1 * conj (v 1)) * h00

/-- A complex matrix of determinant one preserves Lebesgue measure on `ℂ²`: its real
determinant is `|det U|² = 1`. -/
lemma measurePreserving_mulVec {U : M2} (hU : U.det = 1) :
    MeasurePreserving (fun v : Fin 2 → ℂ => U *ᵥ v) volume volume := by
  set L : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) := (Matrix.toLin' U).restrictScalars ℝ
  have hdet : LinearMap.det L = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', hU, map_one]
  have hL : MeasurePreserving L volume volume := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
    simp
  convert hL using 1
  funext v
  simp [L, Matrix.toLin'_apply]

/-- Substitution `v ↦ U v` in an integral over `ℂ²`, for `det U = 1`. -/
lemma integral_comp_mulVec {U : M2} (hU : U.det = 1) {g : (Fin 2 → ℂ) → ℂ}
    (hg : AEStronglyMeasurable g volume) : ∫ v, g (U *ᵥ v) = ∫ v, g v := by
  have hmp := measurePreserving_mulVec hU
  have h2 : AEStronglyMeasurable g (Measure.map (fun v => U *ᵥ v) volume) := by
    rw [hmp.map_eq]; exact hg
  calc ∫ v, g (U *ᵥ v) = ∫ v, g v ∂(Measure.map (fun v => U *ᵥ v) volume) :=
        (integral_map hmp.measurable.aemeasurable h2).symm
    _ = ∫ v, g v := by rw [hmp.map_eq]

/-! ### Conjugation by `K_v / |v|` -/

/-- `|v|⁻² K_v* X K_v`: conjugation of `X` by `K_v / |v| ∈ SU(2)`. -/
noncomputable def conjV (v : Fin 2 → ℂ) (X : P2) : P2 := (nsq v)⁻¹ • mm3 (kvs v) X (kv v)

/-- `conjV v` undone: `X = |v|⁻² K_v (conjV v X) K_v*` for `v ≠ 0`. -/
lemma conjV_inv {v : Fin 2 → ℂ} (h : nsq v ≠ 0) (X : P2) :
    (nsq v)⁻¹ • mm3 (kv v) (conjV v X) (kvs v) = X := by
  have e : Matrix.of ((nsq v)⁻¹ • mm3 (kv v) (conjV v X) (kvs v)) = Matrix.of X := by
    show (nsq v)⁻¹ • (Matrix.of (kv v) * ((nsq v)⁻¹ • (Matrix.of (kvs v) * Matrix.of X *
      Matrix.of (kv v))) * Matrix.of (kvs v)) = Matrix.of X
    rw [show Matrix.of (kv v) * ((nsq v)⁻¹ • (Matrix.of (kvs v) * Matrix.of X *
        Matrix.of (kv v))) * Matrix.of (kvs v) = (nsq v)⁻¹ • ((Matrix.of (kv v) *
        Matrix.of (kvs v)) * Matrix.of X * (Matrix.of (kv v) * Matrix.of (kvs v))) by
      rw [Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]]
    rw [kv_mul_kvs, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, smul_smul, smul_smul]
    rw [show (nsq v)⁻¹ * (nsq v)⁻¹ * nsq v * nsq v = 1 by field_simp, one_smul]
  exact e

/-- `conjV v` fixes the identity matrix for `v ≠ 0`. -/
lemma conjV_one {v : Fin 2 → ℂ} (h : nsq v ≠ 0) : conjV v (mat2 1 0 0 1) = mat2 1 0 0 1 := by
  have h1 : Matrix.of (mat2 1 0 0 1) = (1 : M2) := by rw [Matrix.one_fin_two]; rfl
  have h2 : Matrix.of (conjV v (mat2 1 0 0 1)) = (1 : M2) := by
    show (nsq v)⁻¹ • (Matrix.of (kvs v) * Matrix.of (mat2 1 0 0 1) * Matrix.of (kv v)) = (1 : M2)
    rw [h1, Matrix.mul_one, kvs_mul_kv, smul_smul, inv_mul_cancel₀ h, one_smul]
  exact h2.trans h1.symm

/-- **Equivariance.** For `k ∈ SU(2)`, conjugating `X` by `k` first is the same as replacing
`v` by `k* v`: `conjV v (k X k*) = conjV (k* v) X`. -/
lemma conjV_conj {k : M2} (hk : k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (v : Fin 2 → ℂ)
    (X : M2) : conjV v (k * X * star k) = conjV (star k *ᵥ v) X := by
  have hk' : star k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    (star (⟨k, hk⟩ : Matrix.specialUnitaryGroup (Fin 2) ℂ)).2
  have h1 := mul_kv hk' v
  have h2 : Matrix.of (kvs v) * k = Matrix.of (kvs (star k *ᵥ v)) := by
    rw [kvs_eq_star, kvs_eq_star, ← h1, star_mul, star_star]
  have h3 : Matrix.of (conjV v (k * X * star k)) = Matrix.of (conjV (star k *ᵥ v) X) := by
    show (nsq v)⁻¹ • (Matrix.of (kvs v) * (k * X * star k) * Matrix.of (kv v)) =
      (nsq (star k *ᵥ v))⁻¹ • (Matrix.of (kvs (star k *ᵥ v)) * X *
        Matrix.of (kv (star k *ᵥ v)))
    rw [nsq_mulVec hk', ← h1, ← h2]
    simp only [Matrix.mul_assoc]
  exact h3

/-! ### The weight -/

/-- The bump `ψ` on `ℝ`: `1` on `[3/4, 5/4]`, supported in `(1/2, 3/2)`. -/
noncomputable def avgBump : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The weight `ψ(|v|²)` on `ℂ²`. -/
noncomputable def avgWeight (v : Fin 2 → ℂ) : ℝ := avgBump (nsq v)

lemma continuous_avgWeight : Continuous avgWeight := avgBump.continuous.comp continuous_nsq

lemma avgWeight_nonneg (v : Fin 2 → ℂ) : 0 ≤ avgWeight v := avgBump.nonneg

lemma avgWeight_le_one (v : Fin 2 → ℂ) : avgWeight v ≤ 1 := avgBump.le_one

/-- On the support of the weight, `1/2 < |v|² < 3/2`. -/
lemma nsq_mem_of_avgWeight_ne_zero {v : Fin 2 → ℂ} (h : avgWeight v ≠ 0) :
    1 / 2 < nsq v ∧ nsq v < 3 / 2 := by
  have h1 : nsq v ∈ Function.support ⇑avgBump := h
  have hr : avgBump.rOut = 1 / 2 := rfl
  rw [avgBump.support_eq, hr, mem_ball, Real.dist_eq] at h1
  obtain ⟨h2, h3⟩ := abs_lt.1 h1
  constructor <;> linarith

/-- On the support of the weight, `|v₀|, |v₁| ≤ 2`. -/
lemma norm_apply_le_two {v : Fin 2 → ℂ} (h : avgWeight v ≠ 0) : ‖v 0‖ ≤ 2 ∧ ‖v 1‖ ≤ 2 := by
  have h1 := (nsq_mem_of_avgWeight_ne_zero h).2
  unfold nsq at h1
  constructor
  · nlinarith [norm_nonneg (v 0), sq_nonneg ‖v 1‖]
  · nlinarith [norm_nonneg (v 1), sq_nonneg ‖v 0‖]

/-- The support of the weight lies in the ball `|v| ≤ 2`. -/
lemma support_avgWeight_subset : Function.support avgWeight ⊆ closedBall 0 2 := by
  intro v hv
  obtain ⟨h0, h1⟩ := norm_apply_le_two hv
  rw [mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  fin_cases i
  exacts [h0, h1]

lemma hasCompactSupport_avgWeight : HasCompactSupport avgWeight :=
  HasCompactSupport.intro (isCompact_closedBall 0 2) fun _ hv =>
    Function.notMem_support.1 fun h => hv (support_avgWeight_subset h)

lemma integrable_avgWeight : Integrable avgWeight :=
  continuous_avgWeight.integrable_of_hasCompactSupport hasCompactSupport_avgWeight

/-- The weight is `1` at `v = (1, 0)`. -/
lemma avgWeight_e0 : avgWeight ![1, 0] = 1 := by
  have h : nsq ![1, 0] = 1 := by simp [nsq]
  unfold avgWeight
  rw [h]
  exact avgBump.one_of_mem_closedBall (mem_closedBall_self avgBump.rIn_pos.le)

/-- The normalisation `∫ ψ(|v|²) d⁴v`. -/
noncomputable def avgNorm : ℝ := ∫ v : Fin 2 → ℂ, avgWeight v

/-- The normalisation is positive. -/
lemma avgNorm_pos : 0 < avgNorm := by
  unfold avgNorm
  rw [integral_pos_iff_support_of_nonneg avgWeight_nonneg integrable_avgWeight]
  refine continuous_avgWeight.isOpen_support.measure_pos volume ⟨![1, 0], ?_⟩
  rw [Function.mem_support, avgWeight_e0]
  exact one_ne_zero

/-! ### The average -/

/-- **The SU(2) conjugation average** `F♮(X) = ∫ F(k⁻¹ X k) dk`, as the normalised integral
`(∫ ψ(|v|²))⁻¹ ∫ ψ(|v|²) F(|v|⁻² K_v* X K_v) d⁴v` over `ℂ²`. -/
noncomputable def su2Avg (F : P2 → ℂ) (X : P2) : ℂ :=
  (avgNorm : ℂ)⁻¹ * ∫ v : Fin 2 → ℂ, (avgWeight v : ℂ) * F (conjV v X)

/-- The parameter `(ψ(|v|²), |v|⁻², K_v*, K_v)` of the integrand. -/
noncomputable def avgParam (v : Fin 2 → ℂ) : ℝ × ℝ × P2 × P2 :=
  (avgWeight v, (nsq v)⁻¹, kvs v, kv v)

/-- The integrand of `su2Avg` as a function of the parameter `q = (w, s, A, B)` and of `X`. -/
noncomputable def avgIntegrand (F : P2 → ℂ) (q : ℝ × ℝ × P2 × P2) (X : P2) : ℂ :=
  (q.1 : ℂ) * F (q.2.1 • mm3 q.2.2.1 X q.2.2.2)

lemma avgIntegrand_avgParam (F : P2 → ℂ) (v : Fin 2 → ℂ) (X : P2) :
    avgIntegrand F (avgParam v) X = (avgWeight v : ℂ) * F (conjV v X) := rfl

lemma measurable_avgParam : Measurable avgParam :=
  continuous_avgWeight.measurable.prodMk (continuous_nsq.measurable.inv.prodMk
    (continuous_kvs.measurable.prodMk continuous_kv.measurable))

/-- The integrand is jointly smooth if `F` is. -/
lemma contDiff_avgIntegrand {F : P2 → ℂ} {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (Function.uncurry (avgIntegrand F)) := by
  have hm : ContDiff ℝ n fun y : (ℝ × ℝ × P2 × P2) × P2 => mm3 y.1.2.2.1 y.2 y.1.2.2.2 :=
    ContDiff.mm3 contDiff_fst.snd.snd.fst contDiff_snd contDiff_fst.snd.snd.snd
  have h1 : ContDiff ℝ n fun y : (ℝ × ℝ × P2 × P2) × P2 => ((y.1.1 : ℝ) : ℂ) :=
    ofRealCLM.contDiff.comp contDiff_fst.fst
  have h2 : ContDiff ℝ n fun y : (ℝ × ℝ × P2 × P2) × P2 =>
      y.1.2.1 • mm3 y.1.2.2.1 y.2 y.1.2.2.2 :=
    contDiff_fst.snd.fst.smul hm
  have h3 := h1.mul (hF.comp h2)
  exact h3

/-- The parameter is bounded by `2` on the support of the weight. -/
lemma norm_avgParam_le {v : Fin 2 → ℂ} (h : avgWeight v ≠ 0) : ‖avgParam v‖ ≤ 2 := by
  obtain ⟨h0, h1⟩ := norm_apply_le_two h
  have hn := (nsq_mem_of_avgWeight_ne_zero h).1
  have hc0 : ‖conj (v 0)‖ ≤ 2 := by rwa [Complex.norm_conj]
  have hc1 : ‖conj (v 1)‖ ≤ 2 := by rwa [Complex.norm_conj]
  have hn0 : ‖-(v 1)‖ ≤ 2 := by rwa [norm_neg]
  have hn1 : ‖-conj (v 1)‖ ≤ 2 := by rwa [norm_neg]
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩⟩
  · show ‖avgWeight v‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (avgWeight_nonneg v)]
    linarith [avgWeight_le_one v]
  · show ‖(nsq v)⁻¹‖ ≤ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (nsq_nonneg v))]
    exact (inv_anti₀ (by norm_num) hn.le).trans_eq (by norm_num)
  · exact norm_mat2_le (by norm_num) hc0 hc1 hn0 h0
  · exact norm_mat2_le (by norm_num) h0 hn1 h1 hc0

/-- The integrand vanishes off the support of the weight. -/
lemma avgIntegrand_eq_zero (F : P2 → ℂ) {v : Fin 2 → ℂ} (h : avgWeight v = 0) (X : P2) :
    avgIntegrand F (avgParam v) X = 0 := by
  rw [avgIntegrand_avgParam, h, ofReal_zero, zero_mul]

/-- `su2Avg F` as a parametric integral. -/
lemma su2Avg_eq (F : P2 → ℂ) :
    su2Avg F = fun X => (avgNorm : ℂ)⁻¹ * ∫ v, avgIntegrand F (avgParam v) X := rfl

/-- **Smoothness.** `F♮` is smooth if `F` is. -/
theorem contDiff_su2Avg {F : P2 → ℂ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (su2Avg F) := by
  rw [su2Avg_eq]
  refine contDiff_const.mul (contDiff_parametric_integral_infty (contDiff_avgIntegrand hF)
    measurable_avgParam.aestronglyMeasurable
    continuous_avgWeight.isOpen_support.measurableSet ?_ (R := 2) ?_ ?_)
  · exact ((measure_mono support_avgWeight_subset).trans_lt measure_closedBall_lt_top).ne
  · exact Filter.Eventually.of_forall fun v hv => norm_avgParam_le hv
  · exact Filter.Eventually.of_forall fun v hv X =>
      avgIntegrand_eq_zero F (Function.notMem_support.1 hv) X

/-- `‖X‖ ≤ 32 ‖conjV v X‖` on the support of the weight. -/
lemma norm_le_conjV {v : Fin 2 → ℂ} (h : avgWeight v ≠ 0) (X : P2) :
    ‖X‖ ≤ 32 * ‖conjV v X‖ := by
  obtain ⟨h0, h1⟩ := norm_apply_le_two h
  have hn := (nsq_mem_of_avgWeight_ne_zero h).1
  have hpos : 0 < nsq v := by linarith
  have hk : ‖kv v‖ ≤ 2 := norm_mat2_le (by norm_num) h0 (by rwa [norm_neg, Complex.norm_conj])
    h1 (by rwa [Complex.norm_conj])
  have hks : ‖kvs v‖ ≤ 2 := norm_mat2_le (by norm_num) (by rwa [Complex.norm_conj])
    (by rwa [Complex.norm_conj]) (by rwa [norm_neg]) h0
  have hinv : ‖(nsq v)⁻¹‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
    exact (inv_anti₀ (by norm_num) hn.le).trans_eq (by norm_num)
  calc ‖X‖ = ‖(nsq v)⁻¹ • mm3 (kv v) (conjV v X) (kvs v)‖ := by rw [conjV_inv hpos.ne']
    _ = ‖(nsq v)⁻¹‖ * ‖mm3 (kv v) (conjV v X) (kvs v)‖ := norm_smul _ _
    _ ≤ 2 * (4 * 2 * ‖conjV v X‖ * 2) := by
        gcongr
        refine (norm_mm3_le _ _ _).trans ?_
        gcongr
    _ = 32 * ‖conjV v X‖ := by ring

/-- **Compact support.** `F♮` has compact support if `F` has. -/
theorem hasCompactSupport_su2Avg {F : P2 → ℂ} (hF : HasCompactSupport F) :
    HasCompactSupport (su2Avg F) := by
  obtain ⟨C, hC, hCF⟩ := exists_bound_support hF
  refine HasCompactSupport.intro (isCompact_closedBall (0 : P2) (32 * C)) fun X hX => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hX
  have h : ∀ v, (avgWeight v : ℂ) * F (conjV v X) = 0 := fun v => by
    by_cases hv : avgWeight v = 0
    · rw [hv, ofReal_zero, zero_mul]
    · rw [hCF _ (by linarith [norm_le_conjV hv X]), mul_zero]
  simp only [su2Avg, h, integral_zero, mul_zero]

/-- **Value at the identity.** `F♮(1) = F(1)`. -/
theorem su2Avg_one (F : P2 → ℂ) : su2Avg F (mat2 1 0 0 1) = F (mat2 1 0 0 1) := by
  have h : ∀ v, (avgWeight v : ℂ) * F (conjV v (mat2 1 0 0 1)) =
      (avgWeight v : ℂ) * F (mat2 1 0 0 1) := fun v => by
    by_cases hv : avgWeight v = 0
    · rw [hv, ofReal_zero, zero_mul, zero_mul]
    · have hn := (nsq_mem_of_avgWeight_ne_zero hv).1
      rw [conjV_one (by linarith)]
  have hN : (avgNorm : ℂ) ≠ 0 := ofReal_ne_zero.2 avgNorm_pos.ne'
  simp only [su2Avg, h]
  rw [integral_mul_const, integral_complex_ofReal, ← avgNorm, ← mul_assoc, inv_mul_cancel₀ hN,
    one_mul]

/-- The integrand of `su2Avg F X` is measurable in `v` if `F` is continuous. -/
lemma aestronglyMeasurable_avgIntegrand {F : P2 → ℂ} (hF : Continuous F) (X : P2) :
    AEStronglyMeasurable (fun v => (avgWeight v : ℂ) * F (conjV v X)) volume := by
  have hc : Continuous fun q : ℝ × ℝ × P2 × P2 => avgIntegrand F q X :=
    (contDiff_avgIntegrand (n := 0) (contDiff_zero.2 hF)).continuous.comp
      (continuous_id.prodMk continuous_const)
  exact (hc.measurable.comp measurable_avgParam).aestronglyMeasurable

/-- **Invariance.** `F♮` is invariant under conjugation by `SU(2)`. -/
theorem isSU2ConjInvariant_su2Avg {F : P2 → ℂ} (hF : Continuous F) :
    IsSU2ConjInvariant (su2Avg F) := by
  intro k hk X
  have hk' : star k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    (star (⟨k, hk⟩ : Matrix.specialUnitaryGroup (Fin 2) ℂ)).2
  have hw : ∀ v, avgWeight (star k *ᵥ v) = avgWeight v := fun v => by
    unfold avgWeight; rw [nsq_mulVec hk']
  unfold su2Avg
  congr 1
  calc ∫ v, (avgWeight v : ℂ) * F (conjV v (k * X * star k))
      = ∫ v, (fun u => (avgWeight u : ℂ) * F (conjV u X)) (star k *ᵥ v) := by
        congr 1; funext v; rw [conjV_conj hk v X]; beta_reduce; rw [hw]
    _ = ∫ v, (avgWeight v : ℂ) * F (conjV v X) :=
        integral_comp_mulVec (Matrix.mem_specialUnitaryGroup_iff.1 hk').2
          (aestronglyMeasurable_avgIntegrand hF X)

/-- `conjV v` is a conjugation by a multiple of an element of `SU(2)`, so an `SU(2)`-invariant
function does not see it. -/
lemma IsSU2ConjInvariant.apply_conjV {F : P2 → ℂ} (hK : IsSU2ConjInvariant F)
    {v : Fin 2 → ℂ} (h : nsq v ≠ 0) (X : P2) : F (conjV v X) = F X := by
  have hpos : 0 < nsq v := lt_of_le_of_ne (nsq_nonneg v) (Ne.symm h)
  have hU : star (Matrix.of (kvs v)) * Matrix.of (kvs v) = ((nsq v : ℝ) : ℂ) • (1 : M2) := by
    rw [kvs_eq_star, star_star, ← kvs_eq_star, kv_mul_kvs, real_smul_M2]
  have e := hK.conj_scaled hpos hU (det_kvs v) X
  rw [← e]
  congr 1
  show (nsq v)⁻¹ • (Matrix.of (kvs v) * Matrix.of X * Matrix.of (kv v)) =
    Matrix.of (kvs v) * Matrix.of X * (((nsq v : ℝ) : ℂ)⁻¹ • star (Matrix.of (kvs v)))
  rw [kvs_eq_star, star_star, Matrix.mul_smul, ← ofReal_inv, ← real_smul_M2]

/-- **Trust check.** Averaging an `SU(2)`-invariant function changes nothing: `F♮ = F`. -/
theorem su2Avg_eq_self {F : P2 → ℂ} (hK : IsSU2ConjInvariant F) : su2Avg F = F := by
  funext X
  have h : ∀ v, (avgWeight v : ℂ) * F (conjV v X) = (avgWeight v : ℂ) * F X := fun v => by
    by_cases hv : avgWeight v = 0
    · rw [hv, ofReal_zero, zero_mul, zero_mul]
    · have hn := (nsq_mem_of_avgWeight_ne_zero hv).1
      rw [hK.apply_conjV (by linarith)]
  have hN : (avgNorm : ℂ) ≠ 0 := ofReal_ne_zero.2 avgNorm_pos.ne'
  simp only [su2Avg, h]
  rw [integral_mul_const, integral_complex_ofReal, ← avgNorm, ← mul_assoc, inv_mul_cancel₀ hN,
    one_mul]

end Lightlike.Lorentz
