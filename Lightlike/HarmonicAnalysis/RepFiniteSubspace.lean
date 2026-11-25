import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Lightlike.OperatorAlgebras.Spectral.Compact

/-!
# A continuous unitary representation of a compact group has a finite-dimensional invariant subspace

Let `K` be a compact group with Haar probability measure `μ`, `U` a strongly continuous unitary representation on a
Hilbert space `H` and `v ≠ 0`. The operator `S : L²(μ) → H`, `S f = ∫ f(k) U(k) v dμ(k)` is compact (a norm limit of
finite-rank operators, from the uniform continuity of `k ↦ U(k) v` on `K`), and `S` intertwines the left translations
with `U`. Then `A = S S†` is a compact self-adjoint operator commuting with `U(K)`, nonzero because
`⟨v, S \bar c⟩ = ∫ |c|² > 0` for the matrix coefficient `c(k) = ⟨v, U(k) v⟩`; a nonzero eigenspace of `A` is a nonzero
finite-dimensional `U(K)`-invariant subspace contained in the closed span of the `U(k) v`.

Supporting results for the converse of the Wigner classification; no catalogue entry.
-/

open scoped InnerProductSpace
open MeasureTheory

namespace Lightlike.HarmonicAnalysis

noncomputable section

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
  [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {μ : Measure K} [IsProbabilityMeasure μ] [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Orbit

variable {w : K → H} (hw : Continuous w)
include hw

lemma exists_bound_orbit : ∃ C, ∀ k, ‖w k‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hw).isBounded.exists_norm_le
  exact ⟨C, fun k => hC _ ⟨k, Set.mem_univ k, rfl⟩⟩

lemma integrable_smul_orbit (f : Lp ℂ 2 μ) : Integrable (fun k => f k • w k) μ := by
  have hf : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  obtain ⟨C, hC⟩ := exists_bound_orbit hw
  refine Integrable.mono' (hf.norm.mul_const C) ((Lp.aestronglyMeasurable f).smul hw.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun k => ?_
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC k) (norm_nonneg _)

lemma integral_norm_le_norm (f : Lp ℂ 2 μ) : ∫ k, ‖f k‖ ∂μ ≤ ‖f‖ := by
  have h1 : eLpNorm f 1 μ ≤ eLpNorm f 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hf : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def]
  rw [eLpNorm_one_eq_lintegral_enorm] at h1
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top h1
  exact Lp.aestronglyMeasurable f

/-- **The operator `f ↦ ∫ f(k) w(k) dμ(k)`** from `L²(μ)` to `H`. -/
def orbitOp : Lp ℂ 2 μ →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ k, f k • w k ∂μ
      map_add' := fun f g => by
        have h1 := integrable_smul_orbit (μ := μ) hw f
        have h2 := integrable_smul_orbit (μ := μ) hw g
        rw [← integral_add h1 h2]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add f g] with k hk
        rw [hk, Pi.add_apply, add_smul]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with k hk
        rw [hk, Pi.smul_apply]
        exact smul_assoc c _ _ }
    (max (Classical.choose (exists_bound_orbit hw)) 0) (fun f => by
      have hC := Classical.choose_spec (exists_bound_orbit hw)
      set C := max (Classical.choose (exists_bound_orbit hw)) 0 with hCdef
      have hC' : ∀ k, ‖w k‖ ≤ C := fun k => (hC k).trans (le_max_left _ _)
      have hf : Integrable (fun k => ‖f k‖) μ := ((Lp.memLp f).integrable (by norm_num)).norm
      calc ‖∫ k, f k • w k ∂μ‖ ≤ ∫ k, ‖f k • w k‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ k, ‖f k‖ * C ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => norm_nonneg _)
            (hf.mul_const C) (Filter.Eventually.of_forall fun k => ?_)
          show ‖f k • w k‖ ≤ ‖f k‖ * C
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hC' k) (norm_nonneg _)
        _ = (∫ k, ‖f k‖ ∂μ) * C := integral_mul_const _ _
        _ ≤ ‖f‖ * C := mul_le_mul_of_nonneg_right (integral_norm_le_norm hw f) (le_max_right _ _)
        _ = C * ‖f‖ := mul_comm _ _)

lemma orbitOp_apply (f : Lp ℂ 2 μ) : orbitOp hw f = ∫ k, f k • w k ∂μ := rfl

/-- A finite measurable partition of `K` on whose pieces `w` varies by less than `ε`. -/
lemma exists_partition (ε : ℝ) (hε : 0 < ε) : ∃ (N : ℕ) (A : Fin N → Set K) (x : Fin N → K),
    (∀ i, MeasurableSet (A i)) ∧ (Pairwise (Function.onFun Disjoint A)) ∧ (⋃ i, A i) = Set.univ ∧
      ∀ i, ∀ k ∈ A i, ‖w k - w (x i)‖ < ε := by
  have hcov : (Set.univ : Set K) ⊆ ⋃ x : K, {k | ‖w k - w x‖ < ε} := fun k _ =>
    Set.mem_iUnion.2 ⟨k, by simpa using hε⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : K => {k | ‖w k - w x‖ < ε})
    (fun x => isOpen_lt (by fun_prop) continuous_const) hcov
  set x : Fin t.card → K := fun i => ((t.equivFin.symm i : t) : K) with hx
  set B : Fin t.card → Set K := fun i => {k | ‖w k - w (x i)‖ < ε} with hB
  have hBm : ∀ i, MeasurableSet (B i) := fun i =>
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  set A : Fin t.card → Set K := fun i => B i \ ⋃ j ∈ {j | j < i}, B j with hA
  have hAm : ∀ i, MeasurableSet (A i) := fun i =>
    (hBm i).diff (MeasurableSet.biUnion (Set.to_countable _) fun j _ => hBm j)
  refine ⟨t.card, A, x, hAm, ?_, ?_, fun i k hk => hk.1⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · refine Set.disjoint_left.2 fun k hki hkj => hkj.2 ?_
      exact Set.mem_biUnion (show i ∈ {j' | j' < j} from h) hki.1
    · refine Set.disjoint_left.2 fun k hki hkj => hki.2 ?_
      exact Set.mem_biUnion (show j ∈ {j' | j' < i} from h) hkj.1
  · refine Set.eq_univ_of_forall fun k => ?_
    have hk := ht (Set.mem_univ k)
    simp only [Set.mem_iUnion] at hk
    obtain ⟨y, hy, hky⟩ := hk
    have hex : ∃ i, k ∈ B i := ⟨t.equivFin ⟨y, hy⟩, by simpa [hB, hx] using hky⟩
    obtain ⟨i0, hi0, hmin⟩ := (wellFounded_lt (α := Fin t.card)).has_min {i | k ∈ B i} hex
    refine Set.mem_iUnion.2 ⟨i0, hi0, ?_⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    intro j hj hkj
    exact hmin j hkj hj

/-- The finite-rank approximation of `orbitOp` along a partition. -/
def orbitApprox {N : ℕ} (A : Fin N → Set K) (hA : ∀ i, MeasurableSet (A i)) (x : Fin N → K) :
    Lp ℂ 2 μ →L[ℂ] H :=
  ∑ i, (innerSL ℂ (indicatorConstLp 2 (hA i) (measure_ne_top μ (A i)) (1 : ℂ))).smulRight (w (x i))

lemma orbitApprox_apply {N : ℕ} (A : Fin N → Set K) (hA : ∀ i, MeasurableSet (A i)) (x : Fin N → K)
    (f : Lp ℂ 2 μ) : orbitApprox (w := w) A hA x f = ∑ i, (∫ k in A i, f k ∂μ) • w (x i) := by
  simp only [orbitApprox, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [L2.inner_indicatorConstLp_one (𝕜 := ℂ) (hA i) (measure_ne_top μ (A i)) f]

lemma norm_orbitOp_sub_approx {ε : ℝ} (hε : 0 ≤ ε) {N : ℕ} (A : Fin N → Set K) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Function.onFun Disjoint A)) (hU : (⋃ i, A i) = Set.univ) (x : Fin N → K)
    (hx : ∀ i, ∀ k ∈ A i, ‖w k - w (x i)‖ < ε) (f : Lp ℂ 2 μ) :
    ‖orbitOp (μ := μ) hw f - orbitApprox (w := w) A hA x f‖ ≤ ε * ‖f‖ := by
  have hf1 : Integrable f μ := (Lp.memLp f).integrable (by norm_num)
  have hint : Integrable (fun k => f k • w k) μ := integrable_smul_orbit hw f
  have h1 : orbitOp (μ := μ) hw f = ∑ i, ∫ k in A i, f k • w k ∂μ := by
    rw [orbitOp_apply, ← integral_iUnion_fintype hA hd (fun i => hint.integrableOn)]
    rw [hU, Measure.restrict_univ]
  have h2 : ∀ i, (∫ k in A i, f k ∂μ) • w (x i) = ∫ k in A i, f k • w (x i) ∂μ := fun i =>
    (integral_smul_const _ _).symm
  rw [orbitApprox_apply hw, h1]
  simp_rw [h2]
  rw [← Finset.sum_sub_distrib]
  have h3 : ∀ i, ‖(∫ k in A i, f k • w k ∂μ) - ∫ k in A i, f k • w (x i) ∂μ‖ ≤ ∫ k in A i, ε * ‖f k‖ ∂μ := by
    intro i
    have hi1 : IntegrableOn (fun k => f k • w k) (A i) μ := hint.integrableOn
    have hi2 : IntegrableOn (fun k => f k • w (x i)) (A i) μ := hf1.integrableOn.smul_const _
    rw [← integral_sub hi1 hi2]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine setIntegral_mono_on (hi1.sub hi2).norm (hf1.norm.const_mul ε).integrableOn (hA i) fun k hk => ?_
    rw [← smul_sub, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hx i k hk).le (norm_nonneg _)
  calc ‖∑ i, ((∫ k in A i, f k • w k ∂μ) - ∫ k in A i, f k • w (x i) ∂μ)‖
      ≤ ∑ i, ‖(∫ k in A i, f k • w k ∂μ) - ∫ k in A i, f k • w (x i) ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∫ k in A i, ε * ‖f k‖ ∂μ := Finset.sum_le_sum fun i _ => h3 i
    _ = ∫ k, ε * ‖f k‖ ∂μ := by
        rw [← integral_iUnion_fintype hA hd (fun i => (hf1.norm.const_mul ε).integrableOn), hU,
          Measure.restrict_univ]
    _ = ε * ∫ k, ‖f k‖ ∂μ := integral_const_mul _ _
    _ ≤ ε * ‖f‖ := mul_le_mul_of_nonneg_left (integral_norm_le_norm hw f) hε

lemma isCompactOperator_orbitApprox {N : ℕ} (A : Fin N → Set K) (hA : ∀ i, MeasurableSet (A i))
    (x : Fin N → K) : IsCompactOperator (orbitApprox (μ := μ) (w := w) A hA x) := by
  unfold orbitApprox
  have key : ∀ (φ : Lp ℂ 2 μ →L[ℂ] ℂ) (u : H), IsCompactOperator (φ.smulRight u) := fun φ u => by
    have h1 : IsCompactOperator (ContinuousLinearMap.toSpanSingleton ℂ u) :=
      isCompactOperator_of_locallyCompactSpace_rng _
    exact h1.comp_clm φ
  have hsum : ∀ s : Finset (Fin N), IsCompactOperator ⇑(∑ i ∈ s,
      (innerSL ℂ (indicatorConstLp 2 (μ := μ) (hA i) (measure_ne_top μ (A i)) (1 : ℂ))).smulRight (w (x i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isCompactOperator_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ContinuousLinearMap.coe_add']
      exact (key _ _).add ih
  exact hsum Finset.univ

lemma isCompactOperator_orbitOp : IsCompactOperator (orbitOp (μ := μ) hw) := by
  have hn : ∀ n : ℕ, ∃ F : Lp ℂ 2 μ →L[ℂ] H, IsCompactOperator F ∧ ‖orbitOp (μ := μ) hw - F‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, A, x, hA, hd, hU, hx⟩ := exists_partition hw (1 / ((n : ℝ) + 1)) (by positivity)
    refine ⟨orbitApprox (μ := μ) (w := w) A hA x, isCompactOperator_orbitApprox hw A hA x, ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    rw [sub_apply]
    exact norm_orbitOp_sub_approx hw (by positivity) A hA hd hU x hx f
  choose F hF hFn using hn
  refine isCompactOperator_of_tendsto (l := Filter.atTop) (F := F) ?_ (Filter.Eventually.of_forall hF)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact hFn n

/-- The matrix-coefficient map `x ↦ (k ↦ ⟪w k, x⟫)` into continuous functions. -/
def coeffMap : H →L[ℂ] C(K, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun k => ⟪w k, x⟫_ℂ, by fun_prop⟩
      map_add' := fun x y => by ext k; simp [inner_add_right]
      map_smul' := fun c x => by ext k; simp [inner_smul_right] }
    (max (Classical.choose (exists_bound_orbit hw)) 0) (fun x => by
      have hC := Classical.choose_spec (exists_bound_orbit hw)
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun k => ?_
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul_of_nonneg_right ((hC k).trans (le_max_left _ _)) (norm_nonneg _))

lemma coeffMap_apply (x : H) (k : K) : coeffMap hw x k = ⟪w k, x⟫_ℂ := rfl

/-- **The averaging operator** `A x = ∫ ⟪w k, x⟫ w k dμ(k)`, the composite of the compact operator `orbitOp` with
the bounded operator `x ↦ ⟪w ·, x⟫`. -/
def avgOp : H →L[ℂ] H :=
  (orbitOp (μ := μ) hw).comp ((ContinuousMap.toLp (E := ℂ) 2 μ ℂ).comp (coeffMap hw))

lemma avgOp_apply (x : H) : avgOp (μ := μ) hw x = ∫ k, ⟪w k, x⟫_ℂ • w k ∂μ := by
  show orbitOp (μ := μ) hw (ContinuousMap.toLp (E := ℂ) 2 μ ℂ (coeffMap hw x)) = _
  rw [orbitOp_apply]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) μ (coeffMap hw x)] with k hk
  rw [hk]
  rfl

lemma isCompactOperator_avgOp : IsCompactOperator (avgOp (μ := μ) hw) :=
  (isCompactOperator_orbitOp (μ := μ) hw).comp_clm _

lemma integrable_avg (x : H) : Integrable (fun k => ⟪w k, x⟫_ℂ • w k) μ := by
  obtain ⟨C, hC⟩ := exists_bound_orbit hw
  refine Integrable.mono' (integrable_const (C * ‖x‖ * C))
    ((by fun_prop : Continuous fun k => ⟪w k, x⟫_ℂ • w k).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun k => ?_
  rw [norm_smul]
  have h1 : ‖⟪w k, x⟫_ℂ‖ ≤ C * ‖x‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _))
  exact mul_le_mul h1 (hC k) (norm_nonneg _) ((norm_nonneg _).trans h1)

lemma inner_avgOp (x y : H) : ⟪y, avgOp (μ := μ) hw x⟫_ℂ = ∫ k, ⟪w k, x⟫_ℂ * ⟪y, w k⟫_ℂ ∂μ := by
  rw [avgOp_apply, ← integral_inner (integrable_avg (μ := μ) hw x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [inner_smul_right]

lemma avgOp_isSymmetric : ∀ x y : H, ⟪avgOp (μ := μ) hw x, y⟫_ℂ = ⟪x, avgOp (μ := μ) hw y⟫_ℂ := by
  intro x y
  rw [← inner_conj_symm, inner_avgOp (μ := μ) hw x y, ← integral_conj, inner_avgOp (μ := μ) hw y x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_comm]

lemma avgOp_ne_zero (k₀ : K) (x : H) (h : ⟪w k₀, x⟫_ℂ ≠ 0) : avgOp (μ := μ) hw ≠ 0 := by
  intro h0
  have h1 := inner_avgOp (μ := μ) hw x x
  rw [h0, ContinuousLinearMap.zero_apply, inner_zero_right] at h1
  have hpos : 0 < ∫ k, ((‖⟪w k, x⟫_ℂ‖ ^ 2 : ℝ)) ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := k₀) (by fun_prop)
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_
    simpa using h
  have h2 : ∫ k, ⟪w k, x⟫_ℂ * ⟪x, w k⟫_ℂ ∂μ = ((∫ k, (‖⟪w k, x⟫_ℂ‖ ^ 2 : ℝ) ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← inner_conj_symm x (w k), mul_comm, Complex.conj_mul']
    push_cast; ring_nf
  rw [h2] at h1
  have := Complex.ofReal_eq_zero.1 h1.symm
  linarith

end Orbit

section Rep

variable (ρ : K →* (H ≃ₗᵢ[ℂ] H)) (hρ : ∀ x, Continuous fun k => ρ k x) (v : H)

/-- The averaging operator of the orbit `k ↦ ρ(k) v` commutes with `ρ`. -/
lemma avgOp_comm (g : K) (x : H) :
    ρ g (avgOp (μ := μ) (w := fun k => ρ k v) (hρ v) x) = avgOp (μ := μ) (w := fun k => ρ k v) (hρ v) (ρ g x) := by
  rw [avgOp_apply, avgOp_apply]
  have h1 : ρ g (∫ k, ⟪ρ k v, x⟫_ℂ • ρ k v ∂μ) = ∫ k, ρ g (⟪ρ k v, x⟫_ℂ • ρ k v) ∂μ :=
    ((ρ g).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (integrable_avg (μ := μ) (hρ v) x)).symm
  rw [h1]
  have h2 : ∀ k, ρ g (⟪ρ k v, x⟫_ℂ • ρ k v) = ⟪ρ (g * k) v, ρ g x⟫_ℂ • ρ (g * k) v := fun k => by
    rw [map_smul, map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    simp [LinearIsometryEquiv.inner_map_map]
  simp_rw [h2]
  exact integral_mul_left_eq_self (fun k => ⟪ρ k v, ρ g x⟫_ℂ • ρ k v) g

include μ hρ in
open Lightlike.OperatorAlgebras.CompactSpectral in
/-- **A continuous unitary representation of a compact group has a nonzero finite-dimensional invariant
subspace inside every closed subspace containing an orbit.** -/
theorem exists_finiteDim_invariant (hv : v ≠ 0) (M : Submodule ℂ H) (hM : IsClosed (M : Set H))
    (hvM : ∀ k, ρ k v ∈ M) :
    ∃ W : Submodule ℂ H, W ≠ ⊥ ∧ FiniteDimensional ℂ W ∧ W ≤ M ∧ ∀ g, ∀ x ∈ W, ρ g x ∈ W := by
  set A := avgOp (μ := μ) (w := fun k => ρ k v) (hρ v) with hA
  have hcomp : IsCompactOperator A := isCompactOperator_avgOp (μ := μ) (hρ v)
  have hsymm : (A : H →ₗ[ℂ] H).IsSymmetric := fun x y => avgOp_isSymmetric (μ := μ) (hρ v) x y
  have hne : A ≠ 0 :=
    avgOp_ne_zero (μ := μ) (hρ v) 1 v (by simpa using hv)
  obtain ⟨s, b, ev, hb, hev⟩ := exists_hilbertBasis_eigenvectors hcomp hsymm
  -- some eigenvalue is nonzero
  have hex : ∃ i, ev i ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    ext x
    have := hasSum_eigen b (fun i => (ev i : ℂ)) hev x
    have h0 : (fun i => ((ev i : ℂ) * ⟪b i, x⟫_ℂ) • b i) = fun _ => (0 : H) := by
      funext i; simp [hall i]
    rw [h0] at this
    exact this.unique hasSum_zero
  obtain ⟨i, hi⟩ := hex
  have hμ : (ev i : ℂ) ≠ 0 := by exact_mod_cast hi
  refine ⟨Module.End.eigenspace (A : Module.End ℂ H) (ev i), ?_, ?_, ?_, ?_⟩
  · intro h
    have hmem : b i ∈ Module.End.eigenspace (A : Module.End ℂ H) (ev i) := by
      rw [Module.End.mem_eigenspace_iff]; exact hev i
    rw [h] at hmem
    have : b i = 0 := by simpa using hmem
    have h1 := b.orthonormal.1 i
    rw [this] at h1; simp at h1
  · exact finiteDimensional_eigenspace hcomp hμ
  · intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have hAx : A x ∈ M := by
      rw [← (hM.submodule_topologicalClosure_eq : M.topologicalClosure = M), ← Submodule.orthogonal_orthogonal_eq_closure]
      rw [Submodule.mem_orthogonal']
      intro z hz
      rw [← inner_conj_symm, inner_avgOp (μ := μ) (hρ v) x z]
      have : ∀ k, ⟪z, ρ k v⟫_ℂ = 0 := fun k => by
        rw [← inner_conj_symm]; simp [(Submodule.mem_orthogonal _ _).1 hz _ (hvM k)]
      simp [this]
    have : x = (ev i : ℂ)⁻¹ • A x := by
      have : (A : Module.End ℂ H) x = (ev i : ℂ) • x := hx
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, smul_smul, inv_mul_cancel₀ hμ, one_smul]
    rw [this]
    exact M.smul_mem _ hAx
  · intro g x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have h1 : A (ρ g x) = ρ g (A x) := (avgOp_comm (μ := μ) ρ hρ v g x).symm
    have h2 : (A : Module.End ℂ H) x = (ev i : ℂ) • x := hx
    simp only [ContinuousLinearMap.coe_coe] at h2 ⊢
    rw [h1, h2, map_smul]

end Rep

end

end Lightlike.HarmonicAnalysis