import Lightlike.Poincare.InducedL2
import Lightlike.Poincare.ShellChart

/-!
# The generators of the massive induced representation on `L²`

Let `φ : ℝ³ → ℂ^{n+1}` be continuously differentiable with compact support (`ChartTest`) and `ψ(Q) = φ(q)` the wave
function on the mass shell. For a Lorentz generator `M_{νρ}` with its one-parameter subgroup `γ(t) = lorCurve ν ρ t`,
the difference quotients `t⁻¹ (U(γ(t)) ψ − ψ)` converge in `L²(μ)`, for every invariant measure finite on compacts,
to the pointwise generator `M_{νρ} ψ` of `hasDerivAt_inducedAct_curve` (`tendsto_diffQuot_L2`): the pointwise
generators are the `L²` derivatives of the one-parameter unitary groups on these wave functions.

The proof is by dominated convergence: the derivative of `t ↦ (U(γ(t)) ψ)(Q)` at every `t` is a unitary matrix times
the generator at `γ(t)⁻¹ Q`, which is continuous with compact support, so the mean value theorem bounds the
difference quotients uniformly, and they vanish off a compact set.

Supporting results for the Pauli–Lubanski operator on `L²`; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2 Filter Topology

namespace Lightlike.Poincare

noncomputable section

/-- A test wave function in the chart: `φ` continuously differentiable with compact support. -/
structure ChartTest (n : ℕ) where
  /-- The function of the spatial momentum. -/
  φ : (Fin 3 → ℝ) → Fin (n + 1) → ℂ
  contDiff : ContDiff ℝ 1 φ
  hasCompactSupport : HasCompactSupport φ

namespace ChartTest

variable {m : ℝ} {n : ℕ} (F : ChartTest n)

/-- The wave function on the mass shell. -/
def ψ (m : ℝ) : MassShell m → Fin (n + 1) → ℂ := fun Q => F.φ (coordV Q.1)

lemma differentiable : Differentiable ℝ F.φ := F.contDiff.differentiable (by norm_num)

lemma chartSmoothAt (P : MassShell m) : ChartSmoothAt (F.ψ m) P F.φ (fderiv ℝ F.φ (coordV P.1)) :=
  ⟨fun _ => rfl, (F.differentiable _).hasFDerivAt⟩

lemma continuous_ψ : Continuous (F.ψ m) := F.contDiff.continuous.comp continuous_coordV_shell

/-- The points of the shell over the support of `φ`. -/
def supp (m : ℝ) : Set (MassShell m) := {P | coordV P.1 ∈ tsupport F.φ}

lemma isCompact_supp (hm : 0 < m) : IsCompact (F.supp m) :=
  isCompact_coordV_preimage hm F.hasCompactSupport

lemma ψ_eq_zero {P : MassShell m} (hP : P ∉ F.supp m) : F.ψ m P = 0 :=
  image_eq_zero_of_notMem_tsupport (f := F.φ) (x := coordV P.1) hP

lemma fderiv_eq_zero {P : MassShell m} (hP : P ∉ F.supp m) : fderiv ℝ F.φ (coordV P.1) = 0 := by
  by_contra h
  exact hP (support_fderiv_subset ℝ h)

end ChartTest

/-! ## Continuity of the generator -/

lemma continuous_trN_shell {m : ℝ} : Continuous fun P : MassShell m => trN m P.1 := by
  unfold trN normP
  have h00 : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
    (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)
  have h11 : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) 1 1 :=
    (continuous_apply 1).comp ((continuous_apply 1).comp continuous_subtype_val)
  simp only [Matrix.trace_fin_two, Matrix.smul_apply, smul_eq_mul]
  exact Complex.continuous_re.comp ((continuous_const.mul h00).add (continuous_const.mul h11))

lemma continuous_dStdLift {m : ℝ} (hm : 0 < m) {c : MassShell m → Matrix (Fin 2) (Fin 2) ℂ} (hc : Continuous c) :
    Continuous fun P : MassShell m => dStdLift m P.1 (c P) := by
  have hpos : ∀ P : MassShell m, 0 < trN m P.1 + 2 := fun P => by
    have := (trace_normP hm P.2).2; linarith
  have hsq : Continuous fun P : MassShell m => Real.sqrt (trN m P.1 + 2) :=
    (continuous_trN_shell.add continuous_const).sqrt
  have hsqne : ∀ P : MassShell m, Real.sqrt (trN m P.1 + 2) ≠ 0 := fun P => (Real.sqrt_pos.2 (hpos P)).ne'
  have hden : ∀ P : MassShell m, 2 * (trN m P.1 + 2) * Real.sqrt (trN m P.1 + 2) ≠ 0 := fun P =>
    mul_ne_zero (mul_ne_zero two_ne_zero (hpos P).ne') (hsqne P)
  have htv : Continuous fun P : MassShell m => trVel m (c P) := by
    unfold trVel normP
    simp only [Matrix.trace_fin_two, Matrix.smul_apply, smul_eq_mul]
    have h00 : Continuous fun P => c P 0 0 := (continuous_apply 0).comp ((continuous_apply 0).comp hc)
    have h11 : Continuous fun P => c P 1 1 := (continuous_apply 1).comp ((continuous_apply 1).comp hc)
    exact Complex.continuous_re.comp ((continuous_const.mul h00).add (continuous_const.mul h11))
  have hP : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  unfold dStdLift normP
  refine Continuous.add ?_ ?_
  · have hA : Continuous fun P : MassShell m => ((1 / m : ℝ) : ℂ) • (P.1 : Matrix (Fin 2) (Fin 2) ℂ) + 1 :=
      (hP.const_smul ((1 / m : ℝ) : ℂ)).add (continuous_const (y := (1 : Matrix (Fin 2) (Fin 2) ℂ)))
    refine Continuous.smul (Complex.continuous_ofReal.comp ?_) hA
    exact htv.neg.div ((continuous_const.mul (continuous_trN_shell.add continuous_const)).mul hsq) hden
  · have hB : Continuous fun P : MassShell m => ((1 / m : ℝ) : ℂ) • c P := hc.const_smul ((1 / m : ℝ) : ℂ)
    exact (Complex.continuous_ofReal.comp (continuous_const.div hsq hsqne)).smul hB

lemma continuous_moveVel {m : ℝ} (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun P : MassShell m => moveVel P.1 X := by
  unfold moveVel
  have hP : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  exact ((continuous_const.matrix_mul hP).add (hP.matrix_mul continuous_const)).neg

lemma continuous_wigVel {m : ℝ} (hm : 0 < m) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun P : MassShell m => wigVel hm P X := by
  have hL : Continuous fun P : MassShell m => ((stdLift hm P : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp (continuous_stdLift hm)
  have hN : Continuous fun P : MassShell m => (((stdLift hm P)⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp (continuous_stdLift hm).inv
  unfold wigVel
  exact ((hN.matrix_mul continuous_const).matrix_mul hL).add
    (hN.matrix_mul (continuous_dStdLift hm (continuous_moveVel X)))

lemma continuous_dSpin (n : ℕ) : Continuous (dSpin n) := (dSpinL n).continuous_of_finiteDimensional

namespace ChartTest

variable {m : ℝ} {n : ℕ} (F : ChartTest n)

/-- The generator `X` applied to `ψ`, as a function on the shell. -/
def genFun (hm : 0 < m) (X : Matrix (Fin 2) (Fin 2) ℂ) : MassShell m → Fin (n + 1) → ℂ :=
  fun P => genVal hm n P (F.ψ m) (fderiv ℝ F.φ (coordV P.1)) X

lemma continuous_genFun (hm : 0 < m) (X : Matrix (Fin 2) (Fin 2) ℂ) : Continuous (F.genFun hm X) := by
  unfold genFun genVal
  refine Continuous.add ?_ ?_
  · exact ((continuous_dSpin n).comp (continuous_wigVel hm X)).matrix_mulVec F.continuous_ψ
  · exact ((F.contDiff.continuous_fderiv (by norm_num)).comp continuous_coordV_shell).clm_apply
      (continuous_coordV.comp (continuous_moveVel X))

lemma genFun_eq_zero (hm : 0 < m) (X : Matrix (Fin 2) (Fin 2) ℂ) {P : MassShell m} (hP : P ∉ F.supp m) :
    F.genFun hm X P = 0 := by
  simp [genFun, genVal, F.ψ_eq_zero hP, F.fderiv_eq_zero hP]

end ChartTest

/-! ## Spinor values -/

/-- The Euclidean structure on `ℂ^{n+1}`, as a real continuous linear map. -/
def toSp (n : ℕ) : (Fin (n + 1) → ℂ) →L[ℝ] Spinor n :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (n + 1) => ℂ)).symm.toContinuousLinearMap).restrictScalars ℝ

lemma toSp_apply (n : ℕ) (v : Fin (n + 1) → ℂ) : toSp n v = WithLp.toLp 2 v := rfl

lemma norm_toSp_unitary (n : ℕ) (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (v : Fin (n + 1) → ℂ) :
    ‖toSp n ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v)‖ = ‖toSp n v‖ := by
  have := norm_uAct U (WithLp.toLp 2 v)
  simpa [uAct, toSp_apply] using this

namespace ChartTest

variable {m : ℝ} {n : ℕ} (F : ChartTest n)

lemma exists_bound (hm : 0 < m) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ C, ∀ P : MassShell m, ‖toSp n (F.genFun hm X P)‖ ≤ C := by
  refine ((toSp n).continuous.comp (F.continuous_genFun hm X)).bounded_above_of_compact_support ?_
  exact HasCompactSupport.intro (F.isCompact_supp hm) fun P hP => by
    simp [F.genFun_eq_zero hm X hP]

end ChartTest

/-! ## The curves -/

lemma continuous_curveOf (Y : Matrix (Fin 2) (Fin 2) ℂ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hdet : ∀ t, ((f t : ℂ)) ^ 2 + (g t : ℂ) ^ 2 * Y.det = 1) (htr : Y.trace = 0) :
    Continuous (curveOf Y f g hdet htr) :=
  Continuous.subtype_mk (((Complex.continuous_ofReal.comp hf).smul continuous_const).add
    ((Complex.continuous_ofReal.comp hg).smul continuous_const)) _

lemma continuous_lorCurve (ν ρ : Fin 4) : Continuous (lorCurve ν ρ) := by
  unfold lorCurve
  split_ifs
  · exact continuous_curveOf _ (by fun_prop) (by fun_prop) _ _
  · exact continuous_curveOf _ (by fun_prop) (by fun_prop) _ _
  · exact continuous_const

lemma continuous_shellAct_lorCurve {m : ℝ} (ν ρ : Fin 4) :
    Continuous fun q : ℝ × MassShell m => shellAct (lorCurve ν ρ q.1) q.2 := by
  refine Continuous.subtype_mk ?_ _
  have hA : Continuous fun q : ℝ × MassShell m => ((lorCurve ν ρ q.1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp ((continuous_lorCurve ν ρ).comp continuous_fst)
  have hP : Continuous fun q : ℝ × MassShell m => (q.2.1 : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val.comp continuous_snd
  exact (hA.matrix_mul hP).matrix_mul hA.matrix_conjTranspose

namespace ChartTest

variable {m : ℝ} {n : ℕ} (F : ChartTest n)

/-- The compact set outside of which `U(γ(t)) ψ` vanishes for `|t| ≤ 1`. -/
def bigSupp (m : ℝ) (ν ρ : Fin 4) : Set (MassShell m) :=
  (fun q : ℝ × MassShell m => shellAct (lorCurve ν ρ q.1) q.2) '' (Set.Icc (-1) 1 ×ˢ F.supp m)

lemma isCompact_bigSupp (hm : 0 < m) (ν ρ : Fin 4) : IsCompact (F.bigSupp m ν ρ) :=
  (isCompact_Icc.prod (F.isCompact_supp hm)).image (continuous_shellAct_lorCurve ν ρ)

lemma supp_subset_bigSupp (ν ρ : Fin 4) : F.supp m ⊆ F.bigSupp m ν ρ := fun P hP =>
  ⟨(0, P), ⟨⟨by norm_num, by norm_num⟩, hP⟩, by simp [lorCurve_zero, shellAct_one]⟩

/-- The induced action along the curve, at the point `Q`. -/
def curveVal (hm : 0 < m) (ν ρ : Fin 4) (t : ℝ) (Q : MassShell m) : Fin (n + 1) → ℂ :=
  inducedAct hm (spinRep n) (lorCurve ν ρ t) (F.ψ m) Q

lemma curveVal_zero (hm : 0 < m) (ν ρ : Fin 4) (Q : MassShell m) : F.curveVal hm ν ρ 0 Q = F.ψ m Q := by
  simp [curveVal, lorCurve_zero, inducedAct_one]

lemma curveVal_eq_zero (hm : 0 < m) (ν ρ : Fin 4) {t : ℝ} (ht : |t| ≤ 1) {Q : MassShell m}
    (hQ : Q ∉ F.bigSupp m ν ρ) : F.curveVal hm ν ρ t Q = 0 := by
  have hnot : shellAct (lorCurve ν ρ t)⁻¹ Q ∉ F.supp m := fun h => hQ
    ⟨(t, shellAct (lorCurve ν ρ t)⁻¹ Q), ⟨⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩, h⟩, by
      simp only; rw [← shellAct_mul, mul_inv_cancel, shellAct_one]⟩
  simp [curveVal, inducedAct, F.ψ_eq_zero hnot]

/-- **The derivative along the curve at every time** `s`: `D(W(γ(s), γ(s)⁻¹ Q)) (M ψ)(γ(s)⁻¹ Q)`. -/
lemma hasDerivAt_curveVal (hm : 0 < m) (ν ρ : Fin 4) (Q : MassShell m) (s : ℝ) :
    HasDerivAt (fun t => F.curveVal hm ν ρ t Q)
      (((spinRep n (wignerSU2 hm (lorCurve ν ρ s) (shellAct (lorCurve ν ρ s)⁻¹ Q)) :
          Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ
        F.genFun hm (lorGen ν ρ) (shellAct (lorCurve ν ρ s)⁻¹ Q)) s := by
  set Q' := shellAct (lorCurve ν ρ s)⁻¹ Q
  set Ms := ((spinRep n (wignerSU2 hm (lorCurve ν ρ s) Q') : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  have h0 := hasDerivAt_inducedAct_curve hm n (isCurveAt_lorCurve ν ρ) Q' (F.chartSmoothAt Q')
  have e : (fun t => F.curveVal hm ν ρ t Q) =
      fun t => Ms *ᵥ inducedAct hm (spinRep n) (lorCurve ν ρ (t - s)) (F.ψ m) Q' := by
    funext t
    have ht : lorCurve ν ρ t = lorCurve ν ρ s * lorCurve ν ρ (t - s) := by
      rw [← lorCurve_add]; congr 1; ring
    simp only [curveVal]
    rw [ht, inducedAct_mul]
    rfl
  rw [e]
  have h1 : HasDerivAt (fun t => inducedAct hm (spinRep n) (lorCurve ν ρ (t - s)) (F.ψ m) Q')
      (genVal hm n Q' (F.ψ m) (fderiv ℝ F.φ (coordV Q'.1)) (lorGen ν ρ)) s := by
    have h0' : HasDerivAt (fun t => inducedAct hm (spinRep n) (lorCurve ν ρ t) (F.ψ m) Q')
        (genVal hm n Q' (F.ψ m) (fderiv ℝ F.φ (coordV Q'.1)) (lorGen ν ρ)) (s - s) := by
      rw [sub_self]; exact h0
    exact h0'.comp_sub_const s s
  rw [hasDerivAt_pi] at h1 ⊢
  intro k
  simp only [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum fun l _ => (h1 l).const_mul _

lemma hasDerivAt_toSp_curveVal (hm : 0 < m) (ν ρ : Fin 4) (Q : MassShell m) (s : ℝ) :
    HasDerivAt (fun t => toSp n (F.curveVal hm ν ρ t Q))
      (toSp n (((spinRep n (wignerSU2 hm (lorCurve ν ρ s) (shellAct (lorCurve ν ρ s)⁻¹ Q)) :
          Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ
        F.genFun hm (lorGen ν ρ) (shellAct (lorCurve ν ρ s)⁻¹ Q))) s :=
  (toSp n).hasFDerivAt.comp_hasDerivAt s (F.hasDerivAt_curveVal hm ν ρ Q s)

/-- **The mean value bound**: `‖U(γ(t)) ψ(Q) − ψ(Q)‖ ≤ C |t|`. -/
lemma norm_curveVal_sub_le (hm : 0 < m) (ν ρ : Fin 4) {C : ℝ}
    (hC : ∀ P : MassShell m, ‖toSp n (F.genFun hm (lorGen ν ρ) P)‖ ≤ C) (t : ℝ) (Q : MassShell m) :
    ‖toSp n (F.curveVal hm ν ρ t Q) - toSp n (F.curveVal hm ν ρ 0 Q)‖ ≤ C * ‖t - 0‖ := by
  refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (F.hasDerivAt_toSp_curveVal hm ν ρ Q s).hasDerivWithinAt) (fun s _ => ?_) convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  rw [norm_toSp_unitary]
  exact hC _

/-- **The difference quotients at a point converge to the generator.** -/
lemma tendsto_slope_curveVal (hm : 0 < m) (ν ρ : Fin 4) (Q : MassShell m) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (toSp n (F.curveVal hm ν ρ t Q) - toSp n (F.ψ m Q)))
      (𝓝[≠] 0) (𝓝 (toSp n (F.genFun hm (lorGen ν ρ) Q))) := by
  have h := F.hasDerivAt_toSp_curveVal hm ν ρ Q 0
  simp only [lorCurve_zero, inv_one, shellAct_one] at h
  have hw : wignerSU2 hm 1 Q = 1 := by
    apply Subtype.ext
    simp [wignerSU2, wigner, shellAct_one]
  rw [hw, map_one] at h
  simp only [OneMemClass.coe_one, Matrix.one_mulVec] at h
  have hs := hasDerivAt_iff_tendsto_slope.1 h
  refine hs.congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [slope_def_module, F.curveVal_zero hm ν ρ Q, sub_zero]
  rw [← Complex.ofReal_inv, Complex.coe_smul]

end ChartTest

/-! ## Convergence in `L²` -/

variable {m : ℝ} {μ : Measure (MassShell m)}

namespace ChartTest

variable {n : ℕ} (F : ChartTest n)

lemma memLp_toSp {f : MassShell m → Fin (n + 1) → ℂ} [IsFiniteMeasureOnCompacts μ] (hf : Continuous f)
    (hcs : HasCompactSupport f) : MemLp (fun Q => toSp n (f Q)) 2 μ :=
  ((toSp n).continuous.comp hf).memLp_of_hasCompactSupport (hcs.comp_left (by simp))

lemma hasCompactSupport_ψ (hm : 0 < m) : HasCompactSupport (F.ψ m) :=
  HasCompactSupport.intro (F.isCompact_supp hm) fun _ hP => F.ψ_eq_zero hP

lemma hasCompactSupport_genFun (hm : 0 < m) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    HasCompactSupport (F.genFun hm X) :=
  HasCompactSupport.intro (F.isCompact_supp hm) fun _ hP => F.genFun_eq_zero hm X hP

/-- The wave function as an element of `L²`. -/
def toL2 (hm : 0 < m) (μ : Measure (MassShell m)) [IsFiniteMeasureOnCompacts μ] : Lp (Spinor n) 2 μ :=
  (memLp_toSp F.continuous_ψ (F.hasCompactSupport_ψ hm)).toLp _

/-- The generator applied to the wave function, as an element of `L²`. -/
def genL2 (hm : 0 < m) (μ : Measure (MassShell m)) [IsFiniteMeasureOnCompacts μ] (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Lp (Spinor n) 2 μ :=
  (memLp_toSp (F.continuous_genFun hm X) (F.hasCompactSupport_genFun hm X)).toLp _

lemma continuous_curveVal (hm : 0 < m) (ν ρ : Fin 4) (t : ℝ) : Continuous (F.curveVal (n := n) hm ν ρ t) := by
  have h := (continuous_subtype_val.comp (continuous_wigField hm n (lorCurve ν ρ t))).matrix_mulVec
    (F.continuous_ψ.comp (continuous_shellAct (lorCurve ν ρ t)⁻¹))
  exact h

/-- **The difference quotients converge in `L²`** to the generator, for every invariant measure finite on compacts. -/
theorem tendsto_diffQuot_L2 (hm : 0 < m) [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (ν ρ : Fin 4) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (inducedL2 hm n hμ (lorCurve ν ρ t) (F.toL2 hm μ) - F.toL2 hm μ))
      (𝓝[≠] 0) (𝓝 (F.genL2 hm μ (lorGen ν ρ))) := by
  obtain ⟨C, hC⟩ := F.exists_bound hm (lorGen ν ρ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (restShell hm))
  set K := F.bigSupp m ν ρ
  have hK := F.isCompact_bigSupp hm ν ρ
  -- the explicit difference
  set Ft : ℝ → MassShell m → Spinor n := fun t Q =>
    (t : ℂ)⁻¹ • (toSp n (F.curveVal hm ν ρ t Q) - toSp n (F.ψ m Q)) - toSp n (F.genFun hm (lorGen ν ρ) Q)
  -- the representatives
  have hrep : ∀ t : ℝ, (⇑((t : ℂ)⁻¹ • (inducedL2 hm n hμ (lorCurve ν ρ t) (F.toL2 hm μ) - F.toL2 hm μ)) -
      ⇑(F.genL2 hm μ (lorGen ν ρ))) =ᵐ[μ] Ft t := by
    intro t
    have h1 := coeFn_inducedL2 hm n hμ (lorCurve ν ρ t) (F.toL2 hm μ)
    have h2 : ⇑(F.toL2 hm μ) =ᵐ[μ] fun Q => toSp n (F.ψ m Q) :=
      (memLp_toSp (μ := μ) F.continuous_ψ (F.hasCompactSupport_ψ hm)).coeFn_toLp
    have h3 := (hμ (lorCurve ν ρ t)⁻¹).quasiMeasurePreserving.ae_eq_comp h2
    have h4 : ⇑(F.genL2 hm μ (lorGen ν ρ)) =ᵐ[μ] fun Q => toSp n (F.genFun hm (lorGen ν ρ) Q) :=
      (memLp_toSp (μ := μ) (F.continuous_genFun hm (lorGen ν ρ))
        (F.hasCompactSupport_genFun hm (lorGen ν ρ))).coeFn_toLp
    filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (inducedL2 hm n hμ (lorCurve ν ρ t) (F.toL2 hm μ) - F.toL2 hm μ),
      Lp.coeFn_sub (inducedL2 hm n hμ (lorCurve ν ρ t) (F.toL2 hm μ)) (F.toL2 hm μ), h1, h2, h3, h4]
      with Q e2 e3 e4 e5 e6 e7
    simp only [Function.comp_apply] at e6
    rw [Pi.sub_apply, e2, Pi.smul_apply, e3, Pi.sub_apply, e4, e5, e6, e7]
    simp only [Ft, ChartTest.curveVal, inducedAct, toSp_apply, uAct, WithLp.ofLp_toLp, wigField]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hcongr : ∀ t : ℝ, eLpNorm (⇑((t : ℂ)⁻¹ • (inducedL2 hm n hμ (lorCurve ν ρ t) (F.toL2 hm μ) -
      F.toL2 hm μ)) - ⇑(F.genL2 hm μ (lorGen ν ρ))) 2 μ = eLpNorm (Ft t) 2 μ :=
    fun t => eLpNorm_congr_ae (hrep t)
  simp only [hcongr]
  -- continuity of the explicit difference
  have hFt_cont : ∀ t, Continuous (Ft t) := fun t =>
    (((((toSp n).continuous.comp (F.continuous_curveVal hm ν ρ t)).sub
      ((toSp n).continuous.comp F.continuous_ψ)).const_smul ((t : ℂ)⁻¹)).sub
        ((toSp n).continuous.comp (F.continuous_genFun hm (lorGen ν ρ))))
  -- the bound
  have hbound : ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 → ∀ Q, ‖Ft t Q‖ ≤ K.indicator (fun _ => 2 * C) Q := by
    intro t ht0 ht1 Q
    by_cases hQ : Q ∈ K
    · rw [Set.indicator_of_mem hQ]
      have hmv := F.norm_curveVal_sub_le hm ν ρ hC t Q
      rw [F.curveVal_zero hm ν ρ Q, sub_zero] at hmv
      have h1 : ‖(t : ℂ)⁻¹ • (toSp n (F.curveVal hm ν ρ t Q) - toSp n (F.ψ m Q))‖ ≤ C := by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
        calc |t|⁻¹ * ‖toSp n (F.curveVal hm ν ρ t Q) - toSp n (F.ψ m Q)‖ ≤ |t|⁻¹ * (C * |t|) := by
              gcongr; simpa [Real.norm_eq_abs] using hmv
          _ = C := by field_simp
      calc ‖Ft t Q‖ ≤ ‖(t : ℂ)⁻¹ • (toSp n (F.curveVal hm ν ρ t Q) - toSp n (F.ψ m Q))‖ +
            ‖toSp n (F.genFun hm (lorGen ν ρ) Q)‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add h1 (hC Q)
        _ = 2 * C := by ring
    · rw [Set.indicator_of_notMem hQ]
      have hQs : Q ∉ F.supp m := fun h => hQ (F.supp_subset_bigSupp ν ρ h)
      simp [Ft, F.curveVal_eq_zero hm ν ρ ht1 hQ, F.ψ_eq_zero hQs, F.genFun_eq_zero hm _ hQs]
  -- dominated convergence for `∫⁻ ‖Ft t‖ₑ²`
  have hK_meas : MeasurableSet K := hK.isClosed.measurableSet
  have hlim : Tendsto (fun t => ∫⁻ Q, ‖Ft t Q‖ₑ ^ (2 : ℝ) ∂μ) (𝓝[≠] 0) (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence'
      (K.indicator fun _ => (ENNReal.ofReal (2 * C)) ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun t =>
        ((hFt_cont t).measurable.enorm.pow_const _).aemeasurable
    · have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 ∧ |t| ≤ 1 := by
        have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
        have h2 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| ≤ 1 := nhdsWithin_le_nhds (by
          filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
          simpa [Real.dist_eq] using ht)
        filter_upwards [h1, h2] with t a b using ⟨a, b⟩
      filter_upwards [hev] with t ht
      refine Filter.Eventually.of_forall fun Q => ?_
      have hb := hbound t ht.1 ht.2 Q
      by_cases hQ : Q ∈ K
      · rw [Set.indicator_of_mem hQ]
        rw [Set.indicator_of_mem hQ] at hb
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal hb
      · rw [Set.indicator_of_notMem hQ] at hb ⊢
        have : Ft t Q = 0 := norm_le_zero_iff.1 hb
        simp [this]
    · rw [lintegral_indicator_const hK_meas]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
        hK.measure_lt_top.ne
    · refine Filter.Eventually.of_forall fun Q => ?_
      have h := ((F.tendsto_slope_curveVal hm ν ρ Q).sub_const (toSp n (F.genFun hm (lorGen ν ρ) Q)))
      rw [sub_self] at h
      have h' := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto _).comp h)
      rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h'
      exact h'
  rw [lintegral_zero] at hlim
  have hlim2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hlim2
  refine hlim2.congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hFt_cont t).aestronglyMeasurable]
  norm_num

end ChartTest

end

end Lightlike.Poincare
