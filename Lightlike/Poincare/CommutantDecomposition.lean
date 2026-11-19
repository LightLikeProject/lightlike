import Lightlike.Poincare.CommutantPVM

/-!
# Operators commuting with the multiplications are matrix multiplications

On `L²(μ; ℂ^{n+1})` over the mass shell (`μ` σ-finite), a bounded operator `B` that commutes with the
multiplication by the indicator of every Borel set (`indOp`) is the multiplication by a measurable field of matrices
`M(Q)` (`ae_eq_matAct_of_commute`, `exists_matField_of_commute_transl`): with a strictly positive weight `w ∈ L²`, `M(Q) e_j = (B (w e_j))(Q) / w(Q)`;
then `B` and `M` agree on the vectors `1_S w e_j`, whose span is dense (`span_genSet_dense`), and the vectors on
which they agree form a closed subspace (`isClosed_goodSub`: an `L²`-convergent sequence has an almost everywhere
convergent subsequence).

Supporting results for the irreducibility of the one-particle representations; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace Lightlike.Poincare

noncomputable section

variable {m : ℝ} {μ : Measure (MassShell m)} {n : ℕ}

/-- Every Borel set of the shell is the momentum preimage of a Borel set of `ℝ⁴`. -/
lemma exists_momPreimage (hm : 0 < m) {S : Set (MassShell m)} (hS : MeasurableSet S) :
    ∃ T : Set (Fin 4 → ℝ), MeasurableSet T ∧ mom ⁻¹' T = S := by
  have hc : Continuous fun p : Fin 4 → ℝ => chartInv hm ![p 1, p 2, p 3] := by
    refine (continuous_chartInv hm).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> exact continuous_apply _
  refine ⟨(fun p : Fin 4 → ℝ => chartInv hm ![p 1, p 2, p 3]) ⁻¹' S, hc.measurable hS, ?_⟩
  ext Q
  simp only [Set.mem_preimage]
  have : (![mom Q 1, mom Q 2, mom Q 3] : Fin 3 → ℝ) = coordV Q.1 := by
    funext i; fin_cases i <;> rfl
  rw [this, chartInv_coordV]

/-- **`B` commutes with the multiplication by the indicator of every Borel set of the shell.** -/
lemma commute_indOp (hm : 0 < m) [SFinite μ] (B : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ)
    (hB : ∀ a f, B (translL2 n a f) = translL2 n a (B f)) {S : Set (MassShell m)} (hS : MeasurableSet S)
    (v : Lp (Spinor n) 2 μ) : B (indOp S hS v) = indOp S hS (B v) := by
  obtain ⟨T, hT, rfl⟩ := exists_momPreimage hm hS
  have h := commute_momOp B hB hT v
  change B (momOp T v) = momOp T (B v) at h
  rw [momOp_of_measurable hT] at h
  exact h

/-! ## The weight -/

/-- A strictly positive weight with `∫ w² < ∞`. -/
structure PosWeight (μ : Measure (MassShell m)) where
  /-- The weight. -/
  w : MassShell m → ℝ
  pos : ∀ Q, 0 < w Q
  meas : Measurable w
  memLp : MemLp (fun Q => (w Q : ℂ)) 2 μ

lemma exists_posWeight [SigmaFinite μ] : Nonempty (PosWeight μ) := by
  obtain ⟨g, hgpos, hgm, hgint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
  have hwm : Measurable fun Q => Real.sqrt (g Q) := (NNReal.continuous_coe.measurable.comp hgm).sqrt
  have hae : AEStronglyMeasurable (fun Q => ((Real.sqrt (g Q) : ℝ) : ℂ)) μ :=
    (Complex.continuous_ofReal.measurable.comp hwm).aestronglyMeasurable
  refine ⟨⟨fun Q => Real.sqrt (g Q), fun Q => Real.sqrt_pos.2 (by exact_mod_cast hgpos Q), hwm, ?_⟩⟩
  change eLpNorm _ 2 μ < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hae]
  have hint : ∫⁻ Q, ‖((Real.sqrt (g Q) : ℝ) : ℂ)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun Q => ?_)) (hgint.trans ENNReal.one_lt_top)
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hint.ne

variable (W : PosWeight μ)

/-- The vector `w e_j`. -/
def wvecFun (j : Fin (n + 1)) : MassShell m → Spinor n :=
  fun Q => (W.w Q : ℂ) • EuclideanSpace.single j 1

lemma memLp_wvecFun (j : Fin (n + 1)) : MemLp (wvecFun (n := n) W j) 2 μ := by
  refine W.memLp.of_le ?_ (Filter.Eventually.of_forall fun Q => ?_)
  · exact ((Complex.continuous_ofReal.measurable.comp W.meas).smul_const _).aestronglyMeasurable
  · simp [wvecFun, norm_smul]

/-- The vector `w e_j` of `L²`. -/
def wvec (j : Fin (n + 1)) : Lp (Spinor n) 2 μ := (memLp_wvecFun W j).toLp _

lemma coeFn_wvec (j : Fin (n + 1)) : (wvec W j : MassShell m → Spinor n) =ᵐ[μ] wvecFun W j :=
  (memLp_wvecFun W j).coeFn_toLp

/-- `⟪1_S w e_j, u⟫ = ∫_S w u_j`. -/
lemma inner_indOp_wvec {S : Set (MassShell m)} (hS : MeasurableSet S) (j : Fin (n + 1)) (u : Lp (Spinor n) 2 μ) :
    ⟪indOp S hS (wvec W j), u⟫_ℂ = ∫ Q in S, (W.w Q : ℂ) * (u Q).ofLp j ∂μ := by
  rw [MeasureTheory.L2.inner_def, ← integral_indicator hS]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_indOp (μ := μ) hS (wvec W j), coeFn_wvec W j] with Q h1 h2
  rw [h1]
  by_cases hQ : Q ∈ S
  · rw [Set.indicator_of_mem hQ, Set.indicator_of_mem hQ, h2]
    simp only [wvecFun]
    rw [inner_smul_left, EuclideanSpace.inner_single_left, Complex.conj_ofReal, map_one, one_mul]
  · rw [Set.indicator_of_notMem hQ, Set.indicator_of_notMem hQ, inner_zero_left]

/-- The vectors `1_S w e_j`. -/
def genSet : Set (Lp (Spinor n) 2 μ) :=
  {f | ∃ (S : Set (MassShell m)) (hS : MeasurableSet S) (j : Fin (n + 1)), f = indOp S hS (wvec W j)}

/-- **The vectors `1_S w e_j` span a dense subspace.** -/
lemma span_genSet_dense [SigmaFinite μ] : (Submodule.span ℂ (genSet (n := n) W)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu
  have hj : ∀ j : Fin (n + 1), (fun Q => (W.w Q : ℂ) * (u Q).ofLp j) =ᵐ[μ] 0 := by
    intro j
    have hint : Integrable (fun Q => (W.w Q : ℂ) * (u Q).ofLp j) μ := by
      have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (wvec (n := n) W j) u
      refine h.congr ?_
      filter_upwards [coeFn_wvec W j] with Q h2
      rw [h2]
      simp only [wvecFun]
      rw [inner_smul_left, EuclideanSpace.inner_single_left, Complex.conj_ofReal, map_one, one_mul]
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => hint.integrableOn)
      (fun s hs _ => ?_)
    rw [← inner_indOp_wvec W hs j u]
    exact hu _ (Submodule.subset_span ⟨s, hs, j, rfl⟩)
  apply Lp.ext
  filter_upwards [ae_all_iff.2 hj, Lp.coeFn_zero (Spinor n) 2 μ] with Q hQ h0
  rw [h0]
  ext j
  have h := hQ j
  simp only [Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero, (W.pos Q).ne', false_or] at h
  simpa using h

/-! ## The matrix field -/

/-- A matrix acting on spinors. -/
def matAct (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (v : Spinor n) : Spinor n :=
  WithLp.toLp 2 (N *ᵥ WithLp.ofLp v)

lemma matAct_add (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (v v' : Spinor n) :
    matAct N (v + v') = matAct N v + matAct N v' := by
  simp [matAct, Matrix.mulVec_add]

lemma matAct_smul (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (c : ℂ) (v : Spinor n) :
    matAct N (c • v) = c • matAct N v := by
  simp [matAct, Matrix.mulVec_smul]

lemma matAct_zero (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : matAct N (0 : Spinor n) = 0 := by
  simp [matAct]

lemma continuous_matAct (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Continuous (matAct (n := n) N) := by
  unfold matAct
  exact (PiLp.continuous_toLp 2 _).comp ((Continuous.matrix_mulVec continuous_const
    (PiLp.continuous_ofLp 2 _)))

variable (B : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ)

/-- `M(Q)_{ij} = (B (w e_j))(Q)_i / w(Q)`. -/
def matField (Q : MassShell m) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun i j => ((W.w Q : ℂ))⁻¹ * (B (wvec W j) Q).ofLp i

lemma stronglyMeasurable_matField : StronglyMeasurable (matField (n := n) W B) := by
  have hw : StronglyMeasurable fun Q => ((W.w Q : ℂ))⁻¹ :=
    (Complex.continuous_ofReal.measurable.comp W.meas).inv.stronglyMeasurable
  have hij : ∀ i j : Fin (n + 1), StronglyMeasurable fun Q => matField W B Q i j := by
    intro i j
    have hg : StronglyMeasurable fun Q => (B (wvec W j) Q).ofLp i :=
      ((PiLp.continuous_apply 2 _ i).comp_stronglyMeasurable (Lp.stronglyMeasurable (B (wvec W j))))
    exact hw.mul hg
  have e : matField (n := n) W B = fun Q => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      Matrix.single i j (matField W B Q i j) := funext fun Q => Matrix.matrix_eq_sum_single _
  rw [e]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_
  have h1 : (fun Q => Matrix.single i j (matField W B Q i j)) =
      fun Q => matField W B Q i j • Matrix.single i j (1 : ℂ) := by
    funext Q; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h1]
  exact (hij i j).smul_const _

lemma matAct_matField_wvec (Q : MassShell m) (j : Fin (n + 1)) :
    matAct (matField W B Q) (wvecFun W j Q) = B (wvec W j) Q := by
  ext i
  simp only [matAct, matField, wvecFun, WithLp.ofLp_smul, Matrix.mulVec_smul, EuclideanSpace.single,
    PiLp.ofLp_single, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul]
  rw [Matrix.mulVec_single_one]
  simp only [Matrix.col_apply, Matrix.of_apply]
  field_simp [(W.pos Q).ne']

/-- The vectors on which `B` is the multiplication by `M`. -/
def goodSub : Submodule ℂ (Lp (Spinor n) 2 μ) where
  carrier := {f | (B f : MassShell m → Spinor n) =ᵐ[μ] fun Q => matAct (matField W B Q) (f Q)}
  add_mem' := fun {f g} hf hg => by
    change (⇑(B (f + g)) : MassShell m → Spinor n) =ᵐ[μ] _
    rw [map_add]
    filter_upwards [hf, hg, Lp.coeFn_add (B f) (B g), Lp.coeFn_add f g] with Q h1 h2 h3 h4
    rw [h3, Pi.add_apply, h1, h2, h4, Pi.add_apply, matAct_add]
  zero_mem' := by
    change (⇑(B 0) : MassShell m → Spinor n) =ᵐ[μ] _
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero (Spinor n) 2 μ] with Q h
    rw [h, Pi.zero_apply, matAct_zero]
  smul_mem' := fun c f hf => by
    change (⇑(B (c • f)) : MassShell m → Spinor n) =ᵐ[μ] _
    rw [map_smul]
    filter_upwards [hf, Lp.coeFn_smul c (B f), Lp.coeFn_smul c f] with Q h1 h2 h3
    rw [h2, Pi.smul_apply, h1, h3, Pi.smul_apply, matAct_smul]

lemma isClosed_goodSub : IsClosed (goodSub (n := n) W B : Set (Lp (Spinor n) 2 μ)) := by
  refine IsSeqClosed.isClosed fun f g hf hlim => ?_
  obtain ⟨ns, hns, hns_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hB : Tendsto (fun i => B (f (ns i))) atTop (𝓝 (B g)) :=
    (B.continuous.tendsto g).comp (hlim.comp hns.tendsto_atTop)
  obtain ⟨ns', hns', hns'_ae⟩ := (tendstoInMeasure_of_tendsto_Lp hB).exists_seq_tendsto_ae
  have hall : ∀ᵐ Q ∂μ, ∀ k, (B (f k) : MassShell m → Spinor n) Q = matAct (matField W B Q) (f k Q) :=
    ae_all_iff.2 fun k => hf k
  change (⇑(B g) : MassShell m → Spinor n) =ᵐ[μ] _
  filter_upwards [hns_ae, hns'_ae, hall] with Q h1 h2 h3
  have h1' : Tendsto (fun i => f (ns (ns' i)) Q) atTop (𝓝 (g Q)) := h1.comp hns'.tendsto_atTop
  have h4 := ((continuous_matAct (matField W B Q)).tendsto _).comp h1'
  refine tendsto_nhds_unique h2 (h4.congr fun i => ?_)
  exact (h3 _).symm

/-- **An operator commuting with the indicator multiplications is a matrix multiplication**:
`(B f)(Q) = M(Q) f(Q)` almost everywhere, for every `f`. -/
theorem ae_eq_matAct_of_commute [SigmaFinite μ]
    (hI : ∀ (S : Set (MassShell m)) (hS : MeasurableSet S) v, B (indOp S hS v) = indOp S hS (B v))
    (f : Lp (Spinor n) 2 μ) :
    (B f : MassShell m → Spinor n) =ᵐ[μ] fun Q => matAct (matField W B Q) (f Q) := by
  have hgen : genSet W ⊆ (goodSub (n := n) W B : Set (Lp (Spinor n) 2 μ)) := by
    rintro _ ⟨S, hS, j, rfl⟩
    change (⇑(B (indOp S hS (wvec W j))) : MassShell m → Spinor n) =ᵐ[μ] _
    rw [hI]
    filter_upwards [coeFn_indOp (μ := μ) hS (B (wvec W j)), coeFn_indOp (μ := μ) hS (wvec W j),
      coeFn_wvec W j] with Q h1 h2 h3
    rw [h1, h2]
    by_cases hQ : Q ∈ S
    · rw [Set.indicator_of_mem hQ, Set.indicator_of_mem hQ, h3, matAct_matField_wvec]
    · rw [Set.indicator_of_notMem hQ, Set.indicator_of_notMem hQ, matAct_zero]
  have hle : (Submodule.span ℂ (genSet (n := n) W)).topologicalClosure ≤ goodSub W B :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 hgen) (isClosed_goodSub W B)
  rw [span_genSet_dense W] at hle
  exact hle Submodule.mem_top

/-- **An operator commuting with the translations is a matrix multiplication** (massive shell, `μ` σ-finite):
`(B f)(Q) = M(Q) f(Q)` almost everywhere, with `M` strongly measurable. -/
theorem exists_matField_of_commute_transl (hm : 0 < m) [SigmaFinite μ]
    (hB : ∀ a f, B (translL2 n a f) = translL2 n a (B f)) :
    ∃ M : MassShell m → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, StronglyMeasurable M ∧
      ∀ f : Lp (Spinor n) 2 μ, (B f : MassShell m → Spinor n) =ᵐ[μ] fun Q => matAct (M Q) (f Q) := by
  obtain ⟨W⟩ := exists_posWeight (μ := μ)
  exact ⟨matField W B, stronglyMeasurable_matField W B,
    ae_eq_matAct_of_commute W B (fun S hS v => commute_indOp hm B hB hS v)⟩

end

end Lightlike.Poincare
