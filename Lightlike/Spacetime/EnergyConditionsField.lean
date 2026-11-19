import Lightlike.Spacetime.EnergyConditions
import Lightlike.Spacetime.EinsteinEquations
import Lightlike.Spacetime.FlatConnection

/-!
# Energy conditions for a stress-energy field on a Lorentzian manifold (GE14, stage 2)

A stress-energy field on a Lorentzian 4-manifold `(M, g)` is a field `T x` of continuous bilinear forms on the tangent
spaces. The four energy conditions hold for `T` if they hold at every point (`NullECField`, `WeakECField`,
`StrongECField`, `DominantECField`, from the pointwise conditions of `EnergyConditions.lean`).

* The fields of a perfect fluid (`fluidField`), dust, a Klein–Gordon field (`scalarField`) and an electromagnetic field
  (`emField`) on `M`; the effective forms of the four conditions for a perfect fluid with a unit timelike velocity field
  (`fluidField_nullEC_iff`, ..., `fluidField_dominantEC_iff`); a constant Klein–Gordon field with a negative potential
  violates the weak condition (`scalarField_const_violates_weak`); the electromagnetic field satisfies the null condition
  (`emField_nullEC`).
* **Geometric forms** (Curiel, *A Primer on Energy Conditions*, arXiv 1405.0403v1, §2, p. 5: "the physical formulation is
  logically equivalent to the geometric formulation if the Einstein field equation is assumed to hold"; the geometric
  forms of §2.1, p. 6): if `G = κ T` with `κ > 0` (`EinsteinEq` with `Λ = 0`), then NEC ⇔ `Ric(k, k) ≥ 0` for null `k`
  (`nullECField_iff_ricci`), WEC ⇔ `G(ξ, ξ) ≥ 0` for timelike `ξ` (`weakECField_iff_einstein`), SEC ⇔ `Ric(ξ, ξ) ≥ 0`
  for timelike `ξ` (`strongECField_iff_ricci`), DEC ⇔ the dominant condition for `G` (`dominantECField_iff_einstein`).
  A cosmological constant is moved into the source by `einsteinEq_iff_absorb`.
* `traceG_eq_gram`: the `g`-trace in any basis, `tr_g T = Σᵢⱼ (G⁻¹)ⱼᵢ T(bᵢ, bⱼ)`.

**Limits.** The fields are not required to be smooth or symmetric (the conditions are pointwise); no time orientation
(co-oriented is `g(ξ, η) < 0`, as in `EnergyConditions.lean`); the geometric forms are stated for the Einstein equations
on a boundaryless manifold modelled on `E` (the setting of `EinsteinEquations.lean`). For the electromagnetic field only
the null condition, for the scalar field only the violation by a constant field (both as in stage 1).
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

noncomputable section
namespace Lightlike

section Gram
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- **The `g`-trace in any basis**: `tr_g T = Σᵢⱼ (G⁻¹)ⱼᵢ T(bᵢ, bⱼ)` with `G = (g(bᵢ, bⱼ))` the Gram matrix of `g`. -/
theorem traceG_eq_gram [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g T : V →L[ℝ] V →L[ℝ] ℝ) (hg : g.toBilinForm.Nondegenerate) (b : Module.Basis ι ℝ V) :
    traceG g T hg = ∑ i, ∑ j, (Matrix.of fun i j => g (b i) (b j))⁻¹ j i * T (b i) (b j) := by
  set G : Matrix ι ι ℝ := Matrix.of fun i j => g (b i) (b j) with hGdef
  have hdet : IsUnit G.det := by
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hg
    have hm : LinearMap.BilinForm.toMatrix b g.toBilinForm = G := by
      ext i j; simp [hGdef, LinearMap.BilinForm.toMatrix_apply]
    rw [hm] at h; exact isUnit_iff_ne_zero.mpr h
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  unfold traceG
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  have key : ∀ i, (((g.toBilinForm).toDual hg).symm.toLinearMap ∘ₗ T.toBilinForm) (b i) =
      ∑ k, (∑ l, T (b i) (b l) * G⁻¹ l k) • b k := by
    intro i
    show ((g.toBilinForm).toDual hg).symm (T.toBilinForm (b i)) = _
    rw [LinearEquiv.symm_apply_eq]
    refine b.ext fun m => ?_
    simp only [LinearMap.BilinForm.toDual_def, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    have hGm : ∀ k, g (b k) (b m) = G k m := fun k => rfl
    show T (b i) (b m) = ∑ k, (∑ l, T (b i) (b l) * G⁻¹ l k) * g (b k) (b m)
    simp only [hGm]
    have h1 : T (b i) (b m) = ∑ l, T (b i) (b l) * (G⁻¹ * G) l m := by
      rw [hGG, Finset.sum_eq_single m]
      · simp
      · intro l _ hl; simp [hl]
      · simp
    rw [h1]
    simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, key]
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The `g`-trace of the zero form vanishes. -/
@[simp] theorem traceG_zero [FiniteDimensional ℝ V] (g : V →L[ℝ] V →L[ℝ] ℝ) (hg : g.toBilinForm.Nondegenerate) :
    traceG g 0 hg = 0 := by
  have h0 : (0 : V →L[ℝ] V →L[ℝ] ℝ).toBilinForm = 0 := by
    ext v w; simp [ContinuousLinearMap.toBilinForm_apply]
  simp [traceG, h0]

end Gram

/-! ## The conditions for a field -/

section Field
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace LorentzianMetric
variable (g : LorentzianMetric I M 4) (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)

/-- **Null energy condition for a stress-energy field**: `T(k, k) ≥ 0` for every null `k` at every point. -/
def NullECField : Prop := ∀ x, NullEC (g.g x) (T x)

/-- **Weak energy condition for a stress-energy field**: `T(ξ, ξ) ≥ 0` for every timelike `ξ` at every point. -/
def WeakECField : Prop := ∀ x, WeakEC (g.g x) (T x)

/-- **Strong energy condition for a stress-energy field**: `(T − ½ tr_g T · g)(ξ, ξ) ≥ 0` for every timelike `ξ` at
every point. -/
def StrongECField : Prop := ∀ x, StrongEC (g.g x) (T x) (g.lorentzian x)

/-- **Dominant energy condition for a stress-energy field**: Curiel's physical form at every point. -/
def DominantECField : Prop := ∀ x, DominantEC (g.g x) (T x) (g.lorentzian x)

/-- **The stress-energy field of a perfect fluid** with velocity field `u`, density `ρ` and pressure `p`:
`(ρ + p) u ⊗ u + p g` at every point (`fluidT`; Carroll, gr-qc/9712019, eq. (1.110), p. 30). -/
def fluidField (u : Π x : M, TangentSpace I x) (ρ p : M → ℝ) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  fun x => fluidT (g.g x) (u x) (ρ x) (p x)

/-- **The stress-energy field of a Klein–Gordon field** `φ` with potential `V`: `dφ ⊗ dφ − (½ |dφ|² + V(φ)) g`
(`scalarT`; Carroll, eq. (1.112), p. 30, with `V = ½ m² φ²`). -/
def scalarField (φ : M → ℝ) (Vpot : ℝ → ℝ) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  fun x => scalarT (g.g x) (g.lorentzian x) (mfderiv I 𝓘(ℝ, ℝ) φ x) (Vpot (φ x))

/-- **The stress-energy of an electromagnetic field** `F` (a field of bilinear forms): `F_ac F_b^c − ¼ F² g`
(`emT`; Carroll, eq. (8.25), p. 222, without the Gaussian factor `1/4π`). -/
def emField (F : Π x : M, LinearMap.BilinForm ℝ (TangentSpace I x)) (x : M) (v w : TangentSpace I x) : ℝ :=
  emT (g.g x) (g.lorentzian x).bilinForm_nondegenerate (F x) v w

omit [FiniteDimensional ℝ E] in
/-- The model space of a Lorentzian 4-manifold has dimension four. -/
theorem finrank_eq_four (g : LorentzianMetric I M 4) (x : M) : Module.finrank ℝ E = 4 := by
  obtain ⟨e, -⟩ := g.lorentzian x
  have := Module.finrank_eq_card_basis e
  simp only [Fintype.card_fin] at this
  exact this

variable {g} {u : Π x : M, TangentSpace I x} {ρ p : M → ℝ}

/-- **NEC for a perfect fluid field** with unit timelike velocity: `ρ + p ≥ 0` everywhere. -/
theorem fluidField_nullEC_iff (hu : ∀ x, g.g x (u x) (u x) = -1) :
    g.NullECField (g.fluidField u ρ p) ↔ ∀ x, 0 ≤ ρ x + p x :=
  forall_congr' fun x => fluid_nullEC_iff (g.lorentzian x) (hu x)

/-- **WEC for a perfect fluid field**: `ρ ≥ 0` and `ρ + p ≥ 0` everywhere. -/
theorem fluidField_weakEC_iff (hu : ∀ x, g.g x (u x) (u x) = -1) :
    g.WeakECField (g.fluidField u ρ p) ↔ ∀ x, 0 ≤ ρ x ∧ 0 ≤ ρ x + p x :=
  forall_congr' fun x => fluid_weakEC_iff (g.lorentzian x) (hu x)

/-- **SEC for a perfect fluid field**: `ρ + p ≥ 0` and `ρ + 3p ≥ 0` everywhere. -/
theorem fluidField_strongEC_iff (hu : ∀ x, g.g x (u x) (u x) = -1) :
    g.StrongECField (g.fluidField u ρ p) ↔ ∀ x, 0 ≤ ρ x + p x ∧ 0 ≤ ρ x + 3 * p x :=
  forall_congr' fun x => fluid_strongEC_iff (g.lorentzian x) (hu x)

/-- **DEC for a perfect fluid field**: `|p| ≤ ρ` everywhere. -/
theorem fluidField_dominantEC_iff (hu : ∀ x, g.g x (u x) (u x) = -1) :
    g.DominantECField (g.fluidField u ρ p) ↔ ∀ x, |p x| ≤ ρ x :=
  forall_congr' fun x => fluid_dominantEC_iff (g.lorentzian x) (hu x)

/-- **Dust with `ρ ≥ 0` satisfies all four conditions** (trust check): the fluid field with `p = 0`. -/
theorem fluidField_dust (hu : ∀ x, g.g x (u x) (u x) = -1) (hρ : ∀ x, 0 ≤ ρ x) :
    g.NullECField (g.fluidField u ρ 0) ∧ g.WeakECField (g.fluidField u ρ 0) ∧
      g.StrongECField (g.fluidField u ρ 0) ∧ g.DominantECField (g.fluidField u ρ 0) := by
  refine ⟨(fluidField_nullEC_iff hu).2 fun x => ?_, (fluidField_weakEC_iff hu).2 fun x => ?_,
    (fluidField_strongEC_iff hu).2 fun x => ?_, (fluidField_dominantEC_iff hu).2 fun x => ?_⟩ <;>
    simp [hρ x]

/-- **A constant Klein–Gordon field with a negative potential value violates the weak condition** (trust check; on a
nonempty manifold). -/
theorem scalarField_const_violates_weak [Nonempty M] {c : ℝ} {Vpot : ℝ → ℝ} (hV : Vpot c < 0) :
    ¬ g.WeakECField (g.scalarField (fun _ => c) Vpot) := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty M›
  have h0 : mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => c) x = 0 := mfderiv_const
  have := h x
  simp only [scalarField, h0] at this
  exact scalar_negative_potential_violates_weak (g.lorentzian x) hV this

/-- **The electromagnetic field satisfies the null condition** at every point, for antisymmetric `F`. -/
theorem emField_nullEC {F : Π x : M, LinearMap.BilinForm ℝ (TangentSpace I x)}
    (hF : ∀ x v w, F x v w = -F x w v) (x : M) (k : TangentSpace I x) (hk : g.g x k k = 0) :
    0 ≤ g.emField F x k k :=
  em_nullEC (g.lorentzian x) (hF x) k hk

end LorentzianMetric
end Field

/-! ## Geometric forms under the Einstein equations -/

section Geometric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) 2 M] [CompleteSpace E]
  {g : LorentzianMetric 𝓘(ℝ, E) M 4} {cov : Connection 𝓘(ℝ, E) M} {κ Λ : ℝ}
  {T : Π x : M, TangentSpace 𝓘(ℝ, E) x →L[ℝ] TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ}

namespace LorentzianMetric

/-- **A cosmological constant moved into the source**: `G + Λ g = κ T` iff `G = κ (T − (Λ/κ) g)`, for `κ ≠ 0`. -/
theorem einsteinEq_iff_absorb (hκ : κ ≠ 0) :
    g.EinsteinEq cov Λ κ (fun x v w => T x v w) ↔
      g.EinsteinEq cov 0 κ (fun x v w => (T x + cosmoT (g.g x) (Λ / κ)) v w) := by
  unfold EinsteinEq
  refine and_congr_right fun _ => forall_congr' fun x => forall_congr' fun v => forall_congr' fun w => ?_
  simp only [cosmoT, add_apply, smul_apply, smul_eq_mul, zero_mul, add_zero]
  constructor <;> intro h
  · rw [mul_add, ← h]; field_simp; ring
  · rw [h, mul_add]; field_simp; ring

/-- Under `G = κ T`, `Ric = κ T + (R/2) g` pointwise. -/
theorem ricciAt_of_einsteinEq (h : g.EinsteinEq cov 0 κ (fun x v w => T x v w)) (x : M)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    cov.ricciAt x v w = κ * T x v w + cov.scalarCurvatureAt g x / 2 * g.g x v w := by
  have := h.2 x v w
  simp only [Connection.einsteinField, zero_mul, add_zero] at this
  linarith

/-- **The trace of the Einstein equations**: under `G = κ T` in dimension four, `R = −κ tr_g T`. -/
theorem scalarCurvatureAt_of_einsteinEq [T2Space M] (h : g.EinsteinEq cov 0 κ (fun x v w => T x v w)) (x : M) :
    cov.scalarCurvatureAt g x = -κ * traceG (g.g x) (T x) (g.lorentzian x).bilinForm_nondegenerate := by
  set b := tb (E := E) x
  set Gm := metricGram g x
  have hsym : Gm.transpose = Gm := by ext i j; exact g.symm x _ _
  have hinvT : (Gm⁻¹).transpose = Gm⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym]
  have htr : traceG (g.g x) (T x) (g.lorentzian x).bilinForm_nondegenerate =
      ∑ i, ∑ j, Gm⁻¹ i j * T x (b i) (b j) := by
    rw [traceG_eq_gram _ _ _ b]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := congrFun (congrFun hinvT i) j
    simp only [Matrix.transpose_apply] at this
    rw [← this]; rfl
  have hGG : ∑ i, ∑ j, Gm⁻¹ i j * g.g x (b i) (b j) = 4 := by
    have hG : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ (metricGram_isUnit g x)
    have h1 : ∀ i, ∑ j, Gm⁻¹ i j * g.g x (b i) (b j) = (Gm⁻¹ * Gm) i i := by
      intro i
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := congrFun (congrFun hsym j) i
      simp only [Matrix.transpose_apply] at this
      show _ = Gm⁻¹ i j * Gm j i
      rw [← this]; rfl
    simp only [h1, hG, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [g.finrank_eq_four x]; norm_num
  have hR : cov.scalarCurvatureAt g x = ∑ i, ∑ j, Gm⁻¹ i j * cov.ricciAt x (b i) (b j) := rfl
  have hR' : cov.scalarCurvatureAt g x = κ * traceG (g.g x) (T x) (g.lorentzian x).bilinForm_nondegenerate +
      cov.scalarCurvatureAt g x / 2 * 4 := by
    conv_lhs => rw [hR]
    simp only [ricciAt_of_einsteinEq h x, mul_add, Finset.sum_add_distrib]
    rw [htr, ← hGG, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  linarith

variable (hκ : 0 < κ)
include hκ

/-- **The null energy condition, geometric form** (Curiel, p. 6): under `G = κ T` with `κ > 0`, the null condition for
`T` is `Ric(k, k) ≥ 0` for every null `k`. -/
theorem nullECField_iff_ricci (h : g.EinsteinEq cov 0 κ (fun x v w => T x v w)) :
    g.NullECField T ↔ ∀ x (k : TangentSpace 𝓘(ℝ, E) x), g.g x k k = 0 → 0 ≤ cov.ricciAt x k k := by
  refine forall_congr' fun x => forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [ricciAt_of_einsteinEq h x, hk, mul_zero, add_zero]
  exact (mul_nonneg_iff_of_pos_left hκ).symm

/-- **The weak energy condition, geometric form** (Curiel, p. 6): under `G = κ T` with `κ > 0`, the weak condition for
`T` is `G(ξ, ξ) ≥ 0` for every timelike `ξ`. -/
theorem weakECField_iff_einstein (h : g.EinsteinEq cov 0 κ (fun x v w => T x v w)) :
    g.WeakECField T ↔ ∀ x (ξ : TangentSpace 𝓘(ℝ, E) x), g.g x ξ ξ < 0 → 0 ≤ cov.einsteinField g x ξ ξ := by
  refine forall_congr' fun x => forall_congr' fun ξ => imp_congr_right fun _ => ?_
  have := h.2 x ξ ξ
  simp only [zero_mul, add_zero] at this
  rw [this]
  exact (mul_nonneg_iff_of_pos_left hκ).symm

/-- **The strong energy condition, geometric form** (Curiel, p. 6): under `G = κ T` with `κ > 0` in dimension four, the
strong condition for `T` is `Ric(ξ, ξ) ≥ 0` for every timelike `ξ` (the timelike convergence condition). -/
theorem strongECField_iff_ricci [T2Space M] (h : g.EinsteinEq cov 0 κ (fun x v w => T x v w)) :
    g.StrongECField T ↔ ∀ x (ξ : TangentSpace 𝓘(ℝ, E) x), g.g x ξ ξ < 0 → 0 ≤ cov.ricciAt x ξ ξ := by
  refine forall_congr' fun x => forall_congr' fun ξ => imp_congr_right fun _ => ?_
  rw [ricciAt_of_einsteinEq h x, scalarCurvatureAt_of_einsteinEq h x]
  have e : κ * T x ξ ξ + -κ * traceG (g.g x) (T x) (g.lorentzian x).bilinForm_nondegenerate / 2 * g.g x ξ ξ =
      κ * (T x ξ ξ - 1 / 2 * traceG (g.g x) (T x) (g.lorentzian x).bilinForm_nondegenerate * g.g x ξ ξ) := by ring
  rw [e]
  exact (mul_nonneg_iff_of_pos_left hκ).symm

/-- **The dominant energy condition, geometric form** (Curiel, p. 6): under `G = κ T` with `κ > 0`, the dominant condition
for `T` is: for timelike `ξ`, `G(ξ, ξ) ≥ 0` and the vector `G^a_n ξ^n` (the `w` with `g(w, ·) = G(ξ, ·)`) is causal; for
co-oriented timelike `ξ, η`, `G(ξ, η) ≥ 0`. -/
theorem dominantECField_iff_einstein (h : g.EinsteinEq cov 0 κ (fun x v w => T x v w)) :
    g.DominantECField T ↔ ∀ x : M,
      (∀ ξ : TangentSpace 𝓘(ℝ, E) x, g.g x ξ ξ < 0 → 0 ≤ cov.einsteinField g x ξ ξ ∧
        ∃ w : TangentSpace 𝓘(ℝ, E) x, (∀ v, g.g x w v = cov.einsteinField g x ξ v) ∧ g.g x w w ≤ 0) ∧
      ∀ ξ η : TangentSpace 𝓘(ℝ, E) x, g.g x ξ ξ < 0 → g.g x η η < 0 → g.g x ξ η < 0 →
        0 ≤ cov.einsteinField g x ξ η := by
  have hG : ∀ x (v w : TangentSpace 𝓘(ℝ, E) x), cov.einsteinField g x v w = κ * T x v w := fun x v w => by
    have := h.2 x v w
    simpa only [zero_mul, add_zero] using this
  refine forall_congr' fun x => ?_
  have hnd := (g.lorentzian x).bilinForm_nondegenerate
  set r := raiseT (g.g x) (T x) hnd with hr
  have hraise : ∀ ξ v, g.g x (r ξ) v = T x ξ v := fun ξ v => by
    have e := ((g.g x).toBilinForm.toDual hnd).apply_symm_apply ((T x).toBilinForm ξ)
    have := LinearMap.congr_fun e v
    rw [LinearMap.BilinForm.toDual_def] at this
    exact this
  have hκ0 : κ ≠ 0 := hκ.ne'
  unfold DominantEC
  simp only [hG]
  refine and_congr (forall_congr' fun ξ => imp_congr_right fun _ => and_congr ?_ ?_)
    (forall_congr' fun ξ => forall_congr' fun η => imp_congr_right fun _ => imp_congr_right fun _ =>
      imp_congr_right fun _ => (mul_nonneg_iff_of_pos_left hκ).symm)
  · exact (mul_nonneg_iff_of_pos_left hκ).symm
  · constructor
    · intro hc
      change g.g x (r ξ) (r ξ) ≤ 0 at hc
      refine ⟨κ • r ξ, fun v => ?_, ?_⟩
      · simp only [map_smul, smul_apply, smul_eq_mul, hraise]
      · simp only [map_smul, smul_apply, smul_eq_mul]
        nlinarith [sq_nonneg κ]
    · rintro ⟨w, hw, hww⟩
      have hwr : w = κ • r ξ := by
        refine sub_eq_zero.1 (g.nondegenerate x _ fun v => ?_)
        simp only [map_sub, sub_apply, hw, map_smul, smul_apply, smul_eq_mul, hraise, sub_self]
      show g.g x (r ξ) (r ξ) ≤ 0
      rw [hwr] at hww
      simp only [map_smul, smul_apply, smul_eq_mul] at hww
      have hk2 : 0 < κ * κ := mul_pos hκ hκ
      nlinarith

end LorentzianMetric

/-! ## Non-vacuity: Minkowski space -/

/-- **Minkowski space with no source solves `G = κ T`** (non-vacuity of the geometric forms): the flat connection, `T = 0`. -/
theorem minkowski_einsteinEq_zero (κ : ℝ) :
    (minkowskiMetric 4).EinsteinEq (flatConnection (Fin 4 → ℝ)) 0 κ
      (fun x v w => (0 : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] ℝ) v w) := by
  have h := (satisfiesEinstein_iff_einsteinEq_zero (minkowskiMetric 4) (flatConnection (Fin 4 → ℝ)) 0).1
    (minkowski_satisfiesEinstein_flat 4)
  refine ⟨h.1, fun x v w => ?_⟩
  have := h.2 x v w
  simpa using this

/-- **The four conditions hold on Minkowski space with no source**, and by the geometric forms its Ricci tensor is
nonnegative on null and timelike vectors (trust check: `Ric = 0`). -/
theorem minkowski_ricci_nonneg (x : Fin 4 → ℝ) (ξ : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x)
    (hξ : (minkowskiMetric 4).g x ξ ξ < 0) : 0 ≤ (flatConnection (Fin 4 → ℝ)).ricciAt x ξ ξ := by
  have hS : (minkowskiMetric 4).StrongECField
      (fun x => (0 : TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] TangentSpace 𝓘(ℝ, Fin 4 → ℝ) x →L[ℝ] ℝ)) := by
    intro y v _
    simp
  exact (LorentzianMetric.strongECField_iff_ricci one_pos (minkowski_einsteinEq_zero 1)).1 hS x ξ hξ

end Geometric

end Lightlike
