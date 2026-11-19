import Lightlike.Poincare.OneParticleContinuity
import Lightlike.OperatorAlgebras.Spectral.OperatorIntegral

/-!
# The spectral condition for the one-particle space

The translations of the one-particle space `L²(μ; ℂ^{n+1})` over the mass shell have the joint spectral measure
`E(B) = 1_{p ∈ B}` (multiplication by the indicator of the momenta in `B ⊆ ℝ⁴`, `momPVM`): it is a
projection-valued measure on momentum space, and `T(a) = ∫ e^{i p·a} dE(p)` for every translation `a`
(`translL2_eq_integral`). Its support lies in the closed forward cone `p⁰ ≥ 0, p² ≥ 0`: `E(B) = 0` for every `B`
disjoint from the cone (`momPVM_eq_zero_of_disjoint`). This is the positive-energy (spectral) condition.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1 (page 9 of v2: the translations act on the momentum eigenstates by phases, so the
  momenta are the joint eigenvalues of the translation generators), §3.2 (page 11: the momenta of a massive or
  massless representation lie on the mass shell or light cone with `Θ(p⁰)`, the forward sheet).
-/

open MeasureTheory Matrix Lightlike.Lorentz Filter Topology Lightlike.OperatorAlgebras.Spectral
open scoped InnerProductSpace

namespace Lightlike.Poincare

noncomputable section

/-! ## Momentum coordinates -/

/-- The momentum four-vector `(p⁰, p¹, p², p³)` of a point of the shell. -/
def mom {m : ℝ} (Q : MassShell m) : Fin 4 → ℝ := ![coord0 Q.1, coordV Q.1 0, coordV Q.1 1, coordV Q.1 2]

lemma continuous_coord0_shell {m : ℝ} : Continuous fun P : MassShell m => coord0 P.1 := by
  have h : ∀ i j : Fin 2, Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j =>
    (continuous_subtype_val : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ)).matrix_elem i j
  exact Complex.continuous_re.comp (((h 0 0).add (h 1 1)).div_const 2)

lemma continuous_mom {m : ℝ} : Continuous (mom (m := m)) := by
  refine continuous_pi fun i => ?_
  have hV : ∀ k, Continuous fun P : MassShell m => coordV P.1 k := fun k =>
    (continuous_apply k).comp continuous_coordV_shell
  fin_cases i
  · exact continuous_coord0_shell
  · exact hV 0
  · exact hV 1
  · exact hV 2

lemma measurable_mom {m : ℝ} : Measurable (mom (m := m)) := continuous_mom.measurable

/-- The Minkowski product `p⁰ a⁰ − p·a` (signature `(+,−,−,−)`). -/
def minkowski (p a : Fin 4 → ℝ) : ℝ := p 0 * a 0 - p 1 * a 1 - p 2 * a 2 - p 3 * a 3

/-- The coordinates of a translation. -/
def tcoords (a : Transl) : Fin 4 → ℝ := ![coord0 a.1, coordV a.1 0, coordV a.1 1, coordV a.1 2]

lemma mink_momH (p0 q0 : ℝ) (p q : Fin 3 → ℝ) :
    mink (momH p0 p) (momH q0 q) = ((p0 * q0 - p 0 * q 0 - p 1 * q 1 - p 2 * q 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [mink, momH, Matrix.det_fin_two] <;> ring

lemma pairing_eq_minkowski {m : ℝ} (Q : MassShell m) (a : Transl) :
    pairing Q.1 a.1 = minkowski (mom Q) (tcoords a) := by
  have ha : (a.1 : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]; exact a.2
  have h := mink_momH (coord0 Q.1) (coord0 a.1) (coordV Q.1) (coordV a.1)
  rw [momH_coords_shell, momH_coords ha] at h
  rw [pairing, h, Complex.ofReal_re]
  simp [minkowski, mom, tcoords]

/-- The closed forward cone `p⁰ ≥ 0, p⁰² ≥ |p|²`. -/
def forwardCone : Set (Fin 4 → ℝ) := {p | 0 ≤ p 0 ∧ p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ p 0 ^ 2}

lemma mom_mem_forwardCone {m : ℝ} (Q : MassShell m) : mom Q ∈ forwardCone := by
  have h0 := coord0_pos Q
  have h := coords_sq Q
  refine ⟨h0.le, ?_⟩
  simp only [mom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg m]

/-! ## Multiplication by an indicator -/

variable {m : ℝ} {μ : Measure (MassShell m)} {n : ℕ}

/-- Multiplication by the indicator of a measurable set, on `L²`. -/
def indOp (S : Set (MassShell m)) (hS : MeasurableSet S) : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).indicator hS.nullMeasurableSet).toLp (S.indicator f)
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (f + g)).indicator hS.nullMeasurableSet).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add (((Lp.memLp f).indicator hS.nullMeasurableSet).toLp (S.indicator f))
            (((Lp.memLp g).indicator hS.nullMeasurableSet).toLp (S.indicator g)),
          ((Lp.memLp f).indicator hS.nullMeasurableSet).coeFn_toLp,
          ((Lp.memLp g).indicator hS.nullMeasurableSet).coeFn_toLp] with x h1 h2 h3 h4 h5
        rw [h1, h3, Pi.add_apply, h4, h5]
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx, h2, Pi.add_apply]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • f)).indicator hS.nullMeasurableSet).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).indicator hS.nullMeasurableSet).toLp (S.indicator f)),
          ((Lp.memLp f).indicator hS.nullMeasurableSet).coeFn_toLp] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h4]
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h2, Pi.smul_apply]
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, smul_zero] }
    1 (fun f => by
      rw [one_mul]
      change ‖((Lp.memLp f).indicator hS.nullMeasurableSet).toLp (S.indicator f)‖ ≤ ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _ hS.nullMeasurableSet))

lemma coeFn_indOp {S : Set (MassShell m)} (hS : MeasurableSet S) (f : Lp (Spinor n) 2 μ) :
    (indOp (μ := μ) S hS f : MassShell m → Spinor n) =ᵐ[μ] S.indicator f :=
  ((Lp.memLp f).indicator hS.nullMeasurableSet).coeFn_toLp

lemma inner_indOp {S : Set (MassShell m)} (hS : MeasurableSet S) (f g : Lp (Spinor n) 2 μ) :
    ⟪indOp (μ := μ) S hS f, g⟫_ℂ = ⟪f, indOp (μ := μ) S hS g⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_indOp (μ := μ) hS f, coeFn_indOp (μ := μ) hS g] with x h1 h2
  rw [h1, h2]
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx]

lemma indOp_comp {S T : Set (MassShell m)} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (indOp (μ := μ) (n := n) (S ∩ T) (hS.inter hT)) = indOp S hS * indOp T hT := by
  ext f : 1
  apply Lp.ext
  filter_upwards [coeFn_indOp (μ := μ) (hS.inter hT) f, coeFn_indOp (μ := μ) hS (indOp T hT f),
    coeFn_indOp (μ := μ) hT f] with x h1 h2 h3
  rw [ContinuousLinearMap.mul_apply, h1, h2]
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;> simp [Set.indicator, hxS, hxT, h3]

lemma indOp_univ : indOp (μ := μ) (n := n) Set.univ MeasurableSet.univ = 1 := by
  ext f : 1
  apply Lp.ext
  filter_upwards [coeFn_indOp (μ := μ) MeasurableSet.univ f] with x h
  rw [h, ContinuousLinearMap.one_apply]
  simp

/-! ## The momentum projection-valued measure -/

open Classical in
/-- The operator `E(B)`: multiplication by the indicator of the momenta in `B`. -/
def momOp (B : Set (Fin 4 → ℝ)) : Lp (Spinor n) 2 μ →L[ℂ] Lp (Spinor n) 2 μ :=
  if hB : MeasurableSet B then indOp (mom ⁻¹' B) (measurable_mom hB) else 0

lemma momOp_of_measurable {B : Set (Fin 4 → ℝ)} (hB : MeasurableSet B) :
    momOp (μ := μ) (n := n) B = indOp (mom ⁻¹' B) (measurable_mom hB) := by
  simp [momOp, hB]

lemma hasSum_momOp (E : ℕ → Set (Fin 4 → ℝ)) (hE : ∀ j, MeasurableSet (E j))
    (hd : Pairwise fun i j => Disjoint (E i) (E j)) (v : Lp (Spinor n) 2 μ) :
    HasSum (fun j => momOp (μ := μ) (E j) v) (momOp (⋃ j, E j) v) := by
  have hU : MeasurableSet (⋃ j, E j) := MeasurableSet.iUnion hE
  simp only [momOp_of_measurable (hE _), momOp_of_measurable hU]
  -- finite sums are indicators of finite unions
  have hfin : ∀ s : Finset ℕ, ∑ j ∈ s, indOp (μ := μ) (n := n) (mom ⁻¹' E j) (measurable_mom (hE j)) v =
      indOp (mom ⁻¹' (⋃ j ∈ s, E j)) (measurable_mom (Finset.measurableSet_biUnion s fun j _ => hE j)) v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      apply Lp.ext
      filter_upwards [coeFn_indOp (μ := μ) (measurable_mom (Finset.measurableSet_biUnion (∅ : Finset ℕ)
        fun j _ => hE j)) v, Lp.coeFn_zero (E := Spinor n) (p := 2) (μ := μ)] with x h1 h2
      rw [h1, h2]
      simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ih]
      apply Lp.ext
      filter_upwards [Lp.coeFn_add (indOp (μ := μ) (n := n) (mom ⁻¹' E a) (measurable_mom (hE a)) v)
          (indOp (mom ⁻¹' (⋃ j ∈ s, E j)) (measurable_mom (Finset.measurableSet_biUnion s fun j _ => hE j)) v),
        coeFn_indOp (μ := μ) (measurable_mom (hE a)) v,
        coeFn_indOp (μ := μ) (measurable_mom (Finset.measurableSet_biUnion s fun j _ => hE j)) v,
        coeFn_indOp (μ := μ) (measurable_mom (Finset.measurableSet_biUnion (insert a s) fun j _ => hE j)) v]
        with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, h3, h4]
      by_cases hxa : mom x ∈ E a
      · have hnot : mom x ∉ ⋃ j ∈ s, E j := by
          intro h
          obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 h
          exact Set.disjoint_left.1 (hd (show a ≠ j from fun h => ha (h ▸ hj))) hxa hxj
        have hin : mom x ∈ ⋃ j ∈ insert a s, E j := Set.mem_biUnion (Finset.mem_insert_self a s) hxa
        rw [Set.indicator_of_mem (show x ∈ mom ⁻¹' E a from hxa),
          Set.indicator_of_notMem (show x ∉ mom ⁻¹' (⋃ j ∈ s, E j) from hnot),
          Set.indicator_of_mem (show x ∈ mom ⁻¹' (⋃ j ∈ insert a s, E j) from hin), add_zero]
      · by_cases hxs : mom x ∈ ⋃ j ∈ s, E j
        · have hin : mom x ∈ ⋃ j ∈ insert a s, E j := by
            obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hxs
            exact Set.mem_biUnion (Finset.mem_insert_of_mem hj) hxj
          rw [Set.indicator_of_notMem (show x ∉ mom ⁻¹' E a from hxa),
            Set.indicator_of_mem (show x ∈ mom ⁻¹' (⋃ j ∈ s, E j) from hxs),
            Set.indicator_of_mem (show x ∈ mom ⁻¹' (⋃ j ∈ insert a s, E j) from hin), zero_add]
        · have hnot : mom x ∉ ⋃ j ∈ insert a s, E j := by
            intro h
            obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 h
            rcases Finset.mem_insert.1 hj with rfl | hj
            · exact hxa hxj
            · exact hxs (Set.mem_biUnion hj hxj)
          rw [Set.indicator_of_notMem (show x ∉ mom ⁻¹' E a from hxa),
            Set.indicator_of_notMem (show x ∉ mom ⁻¹' (⋃ j ∈ s, E j) from hxs),
            Set.indicator_of_notMem (show x ∉ mom ⁻¹' (⋃ j ∈ insert a s, E j) from hnot), add_zero]
  unfold HasSum
  simp only [hfin]
  -- dominated convergence along the finsets
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hcongr : ∀ s : Finset ℕ, eLpNorm (⇑(indOp (μ := μ) (n := n) (mom ⁻¹' (⋃ j ∈ s, E j))
      (measurable_mom (Finset.measurableSet_biUnion s fun j _ => hE j)) v) -
      ⇑(indOp (mom ⁻¹' (⋃ j, E j)) (measurable_mom hU) v)) 2 μ =
      eLpNorm (fun x => (mom ⁻¹' (⋃ j ∈ s, E j)).indicator v x - (mom ⁻¹' (⋃ j, E j)).indicator v x) 2 μ :=
    fun s => eLpNorm_congr_ae ((coeFn_indOp _ v).sub (coeFn_indOp _ v))
  simp only [hcongr]
  have hvm : AEStronglyMeasurable (fun x => v x) μ := Lp.aestronglyMeasurable v
  have hmeas : ∀ s : Finset ℕ, AEStronglyMeasurable
      (fun x => (mom ⁻¹' (⋃ j ∈ s, E j)).indicator v x - (mom ⁻¹' (⋃ j, E j)).indicator v x) μ := by
    intro s
    exact ((Lp.aestronglyMeasurable v).indicator
      (measurable_mom (Finset.measurableSet_biUnion s fun j _ => hE j))).sub
      ((Lp.aestronglyMeasurable v).indicator (measurable_mom hU))
  have hlim : Tendsto (fun s : Finset ℕ => ∫⁻ x, ‖(mom ⁻¹' (⋃ j ∈ s, E j)).indicator v x -
      (mom ⁻¹' (⋃ j, E j)).indicator v x‖ₑ ^ (2 : ℝ) ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun x => ‖v x‖ₑ ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun s => ((hmeas s).enorm.pow_const _)
    · refine Filter.Eventually.of_forall fun s => Filter.Eventually.of_forall fun x => ?_
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      by_cases h1 : x ∈ mom ⁻¹' (⋃ j ∈ s, E j) <;> by_cases h2 : x ∈ mom ⁻¹' (⋃ j, E j)
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, sub_self, enorm_zero]; exact zero_le'
      · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem h2, sub_zero]
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, zero_sub, enorm_neg]
      · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, sub_zero, enorm_zero]; exact zero_le'
    · have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (two_ne_zero) ENNReal.ofNat_ne_top
        (Lp.memLp v).eLpNorm_lt_top
      simpa using h.ne
    · refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : mom x ∈ ⋃ j, E j
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop ({j} : Finset ℕ)] with s hs
        have h1 : mom x ∈ ⋃ i ∈ s, E i := Set.mem_biUnion (hs (Finset.mem_singleton_self j)) hj
        rw [Set.indicator_of_mem (show x ∈ mom ⁻¹' (⋃ i ∈ s, E i) from h1),
          Set.indicator_of_mem (show x ∈ mom ⁻¹' (⋃ i, E i) from hx), sub_self, enorm_zero,
          ENNReal.zero_rpow_of_pos (by norm_num)]
      · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun s => ?_)
        have h1 : mom x ∉ ⋃ i ∈ s, E i := fun h => by
          obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.1 h
          exact hx (Set.mem_iUnion.2 ⟨i, hi⟩)
        dsimp only
        rw [Set.indicator_of_notMem (show x ∉ mom ⁻¹' (⋃ i ∈ s, E i) from h1),
          Set.indicator_of_notMem (show x ∉ mom ⁻¹' (⋃ i, E i) from hx), sub_self, enorm_zero,
          ENNReal.zero_rpow_of_pos (by norm_num)]
  rw [lintegral_zero] at hlim
  have hlim2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hlim2
  refine hlim2.congr' (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hmeas s)]
  norm_num

/-- **The momentum projection-valued measure** `E(B) = 1_{p ∈ B}` on `L²(μ; ℂ^{n+1})`. -/
def momPVM : ProjectionValuedMeasure (Fin 4 → ℝ) (Lp (Spinor n) 2 μ) where
  toFun := momOp
  isStarProjection' B := by
    by_cases hB : MeasurableSet B
    · rw [momOp_of_measurable hB]
      refine ⟨?_, ?_⟩
      · change indOp _ _ * indOp _ _ = indOp _ _
        rw [← indOp_comp]
        congr 1
        exact Set.inter_self _
      · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
        intro f g
        exact inner_indOp _ f g
    · simp only [momOp, hB, dite_false]
      exact IsStarProjection.zero _
  notMeasurable' B hB := by simp [momOp, hB]
  univ' := by
    rw [momOp_of_measurable MeasurableSet.univ]
    exact indOp_univ
  hasSum' E hE hd v := hasSum_momOp E hE hd v
  inter' E F hE hF := by
    rw [momOp_of_measurable (hE.inter hF), momOp_of_measurable hE, momOp_of_measurable hF, ← indOp_comp]
    rfl

/-- **The spectral condition**: `E(B) = 0` for every `B` disjoint from the closed forward cone. -/
theorem momPVM_eq_zero_of_disjoint {B : Set (Fin 4 → ℝ)} (hB : Disjoint B forwardCone) :
    momPVM (μ := μ) (n := n) B = 0 := by
  by_cases hBm : MeasurableSet B
  · change momOp B = 0
    rw [momOp_of_measurable hBm]
    ext f : 1
    apply Lp.ext
    filter_upwards [coeFn_indOp (μ := μ) (measurable_mom hBm) f,
      Lp.coeFn_zero (E := Spinor n) (p := 2) (μ := μ)] with x h1 h2
    rw [ContinuousLinearMap.zero_apply, h1, h2]
    have hx : mom x ∉ B := fun h => Set.disjoint_left.1 hB h (mom_mem_forwardCone x)
    simp [Set.indicator, hx]
  · exact momPVM.notMeasurable' B hBm

/-! ## The translations are the Fourier transform of the momentum measure -/

lemma bddMeasurable_phase (a : Transl) :
    (fun p => Complex.exp (Complex.I * minkowski p (tcoords a))) ∈ BddMeasurable (Fin 4 → ℝ) := by
  refine ⟨?_, 1, fun p => ?_⟩
  · have : Continuous fun p : Fin 4 → ℝ => minkowski p (tcoords a) := by unfold minkowski; fun_prop
    exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp this))).measurable
  · show ‖Complex.exp (Complex.I * (minkowski p (tcoords a) : ℂ))‖ ≤ 1
    rw [show Complex.I * (minkowski p (tcoords a) : ℂ) = (minkowski p (tcoords a) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I]

/-- The momentum distribution of `ψ`: the image of `‖ψ‖² dμ` under the momentum map. -/
def momDist (ψ : Lp (Spinor n) 2 μ) : Measure (Fin 4 → ℝ) :=
  (μ.withDensity fun Q => ((‖ψ Q‖₊ ^ 2 : NNReal) : ENNReal)).map mom

lemma aemeasurable_densSq (ψ : Lp (Spinor n) 2 μ) : AEMeasurable (fun Q => ‖ψ Q‖₊ ^ 2) μ :=
  ((Lp.aestronglyMeasurable ψ).nnnorm.aemeasurable).pow_const 2

lemma momDist_apply (ψ : Lp (Spinor n) 2 μ) {B : Set (Fin 4 → ℝ)} (hB : MeasurableSet B) :
    momDist ψ B = ∫⁻ Q in mom ⁻¹' B, ((‖ψ Q‖₊ ^ 2 : NNReal) : ENNReal) ∂μ := by
  rw [momDist, Measure.map_apply measurable_mom hB, withDensity_apply _ (measurable_mom hB)]

lemma coe_nnnorm_sq (v : Spinor n) : ((‖v‖₊ ^ 2 : NNReal) : ENNReal) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.coe_pow, enorm_eq_nnnorm]

instance (ψ : Lp (Spinor n) 2 μ) : IsFiniteMeasure (momDist ψ) := by
  refine ⟨?_⟩
  rw [momDist_apply ψ MeasurableSet.univ, Set.preimage_univ, Measure.restrict_univ]
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    (Lp.memLp ψ).eLpNorm_lt_top
  refine lt_of_eq_of_lt (lintegral_congr fun Q => ?_) h
  rw [ENNReal.coe_pow, ← enorm_eq_nnnorm]
  norm_num

lemma momDist_toReal (ψ : Lp (Spinor n) 2 μ) {B : Set (Fin 4 → ℝ)} (hB : MeasurableSet B) :
    (momDist ψ B).toReal = ∫ Q in mom ⁻¹' B, ‖ψ Q‖ ^ 2 ∂μ := by
  rw [momDist_apply ψ hB, integral_eq_lintegral_of_nonneg_ae (f := fun Q => ‖ψ Q‖ ^ 2)
    (Filter.Eventually.of_forall fun _ => by positivity) (((Lp.aestronglyMeasurable ψ).norm.pow 2).restrict)]
  congr 1
  exact lintegral_congr fun Q => coe_nnnorm_sq _

lemma inner_momPVM (ψ : Lp (Spinor n) 2 μ) {B : Set (Fin 4 → ℝ)} (hB : MeasurableSet B) :
    (⟪ψ, momPVM B ψ⟫_ℂ).re = ∫ Q in mom ⁻¹' B, ‖ψ Q‖ ^ 2 ∂μ := by
  change (⟪ψ, momOp B ψ⟫_ℂ).re = _
  rw [momOp_of_measurable hB, MeasureTheory.L2.inner_def]
  have h : ∫ Q, ⟪ψ Q, indOp (μ := μ) (mom ⁻¹' B) (measurable_mom hB) ψ Q⟫_ℂ ∂μ =
      ∫ Q, (mom ⁻¹' B).indicator (fun Q => ((‖ψ Q‖ ^ 2 : ℝ) : ℂ)) Q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_indOp (μ := μ) (measurable_mom hB) ψ] with Q hQ
    rw [hQ]
    by_cases hm : Q ∈ mom ⁻¹' B
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm, inner_zero_right]
  rw [h, integral_indicator (measurable_mom hB), integral_complex_ofReal, Complex.ofReal_re]

lemma assoc_momPVM (ψ : Lp (Spinor n) 2 μ) : momPVM.assoc ψ = momDist ψ := by
  have h := (ProjectionValuedMeasure.existsUnique_assoc (momPVM (μ := μ) (n := n)) ψ).choose_spec.2 (momDist ψ)
    ⟨inferInstance, fun B hB => by rw [momDist_toReal ψ hB, inner_momPVM ψ hB]⟩
  exact h.symm

lemma integral_momDist (ψ : Lp (Spinor n) 2 μ) {f : (Fin 4 → ℝ) → ℂ} (hf : Measurable f) :
    ∫ p, f p ∂(momDist ψ) = ∫ Q, ((‖ψ Q‖ ^ 2 : ℝ) : ℂ) * f (mom Q) ∂μ := by
  rw [momDist, integral_map measurable_mom.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul₀ (aemeasurable_densSq ψ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Q => ?_)
  simp only [NNReal.smul_def, NNReal.coe_pow, coe_nnnorm, Complex.real_smul]

/-- **The translations are the Fourier transform of the momentum measure**:
`T(a) = ∫ e^{i p·a} dE(p)`, so `E` is the joint spectral measure of the translation generators. -/
theorem translL2_eq_integral (a : Transl) :
    (translL2 (μ := μ) n a).toContinuousLinearMap =
      (momPVM (μ := μ) (n := n)).integral (fun p => Complex.exp (Complex.I * minkowski p (tcoords a))) := by
  have hq : ∀ ψ : Lp (Spinor n) 2 μ, ⟪ψ, translL2 n a ψ⟫_ℂ =
      ⟪ψ, (momPVM (μ := μ) (n := n)).integral (fun p => Complex.exp (Complex.I * minkowski p (tcoords a))) ψ⟫_ℂ := by
    intro ψ
    rw [ProjectionValuedMeasure.inner_integral _ (bddMeasurable_phase a), assoc_momPVM,
      integral_momDist ψ (bddMeasurable_phase a).1, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_translL2 n a ψ] with Q h
    rw [h, inner_smul_right, inner_self_eq_norm_sq_to_K, pairing_eq_minkowski, mul_comm]
    congr 1
    norm_cast
  apply ContinuousLinearMap.coe_injective
  refine (ext_inner_map _ _).1 fun ψ => ?_
  change ⟪translL2 n a ψ, ψ⟫_ℂ = ⟪(momPVM (μ := μ) (n := n)).integral
    (fun p => Complex.exp (Complex.I * minkowski p (tcoords a))) ψ, ψ⟫_ℂ
  rw [← inner_conj_symm, hq ψ, inner_conj_symm]

end

end Lightlike.Poincare
