import Lightlike.Poincare.InducedUnitary
import Lightlike.Poincare.ShellMeasureFinite

/-!
# The induced massive representation on `L²`

For a measure `μ` on the mass shell invariant under `SL(2,ℂ)`, the induced representation acts on
`L²(μ; ℂ^{n+1})` (spinors with the Euclidean norm) by linear isometries:
`(U(A) f)(Q) = D(W(A, A⁻¹ Q)) f(A⁻¹ Q)` (`inducedL2`), the composition with the measure-preserving map `Q ↦ A⁻¹ • Q`
(Mathlib's `Lp.compMeasurePreservingₗᵢ`) followed by the multiplication by a continuous field of unitary matrices
(`mulL2`). Its representatives are the pointwise induced action (`coeFn_inducedL2`).

Supporting construction for the generators on `L²`; no catalogue entry.
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2

namespace Lightlike.Poincare

noncomputable section

local instance (k : ℕ) : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin k → Fin k → ℂ))

local instance (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))

local instance (k : ℕ) : TopologicalSpace.PseudoMetrizableSpace (Matrix.unitaryGroup (Fin k) ℂ) :=
  Topology.IsInducing.subtypeVal.pseudoMetrizableSpace

/-- Spinors: `ℂ^{n+1}` with the Euclidean norm. -/
abbrev Spinor (n : ℕ) := EuclideanSpace ℂ (Fin (n + 1))

/-- A unitary matrix acting on spinors. -/
def uAct {n : ℕ} (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (v : Spinor n) : Spinor n :=
  WithLp.toLp 2 ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ WithLp.ofLp v)

lemma norm_uAct {n : ℕ} (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (v : Spinor n) : ‖uAct U v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  have := normSqV_unitary_mulVec U (WithLp.ofLp v)
  simpa [normSqV, uAct] using this

lemma uAct_add {n : ℕ} (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (v w : Spinor n) :
    uAct U (v + w) = uAct U v + uAct U w := by
  simp only [uAct, WithLp.ofLp_add, Matrix.mulVec_add, WithLp.toLp_add]

lemma uAct_smul {n : ℕ} (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (c : ℂ) (v : Spinor n) :
    uAct U (c • v) = c • uAct U v := by
  simp only [uAct, WithLp.ofLp_smul, Matrix.mulVec_smul, WithLp.toLp_smul]

lemma continuous_uAct {n : ℕ} :
    Continuous fun p : Matrix.unitaryGroup (Fin (n + 1)) ℂ × Spinor n => uAct p.1 p.2 := by
  unfold uAct
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact (continuous_subtype_val.comp continuous_fst).matrix_mulVec
    ((PiLp.continuous_ofLp 2 _).comp continuous_snd)

variable {m : ℝ} {μ : Measure (MassShell m)}

/-- `U v` as a combination of the columns of `U`. -/
lemma uAct_eq_sum {n : ℕ} (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (v : Spinor n) :
    uAct U v = ∑ j, (WithLp.ofLp v j) • WithLp.toLp 2 (fun i => (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j) := by
  apply (WithLp.equiv 2 (Fin (n + 1) → ℂ)).injective
  funext i
  simp [uAct, Matrix.mulVec, dotProduct, mul_comm]

lemma aestronglyMeasurable_uAct {n : ℕ} {M : MassShell m → Matrix.unitaryGroup (Fin (n + 1)) ℂ}
    (hM : Continuous M) (f : Lp (Spinor n) 2 μ) :
    AEStronglyMeasurable (fun Q => uAct (M Q) (f Q)) μ := by
  have hcol : ∀ j, AEStronglyMeasurable (fun Q => (WithLp.toLp 2
      (fun i => ((M Q : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j) :
        Spinor n)) μ := fun j => by
    refine Continuous.aestronglyMeasurable ?_
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    exact (continuous_apply j).comp ((continuous_apply i).comp hM.subtype_val)
  have hcoef : ∀ j, AEStronglyMeasurable (fun Q => WithLp.ofLp ((f : MassShell m → Spinor n) Q) j) μ :=
    fun j => ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)
  have hsum : AEStronglyMeasurable (fun Q => ∑ j, (WithLp.ofLp ((f : MassShell m → Spinor n) Q) j) •
      (WithLp.toLp 2 (fun i => ((M Q : Matrix.unitaryGroup (Fin (n + 1)) ℂ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j) : Spinor n)) μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hcoef j).smul (hcol j)
  exact hsum.congr (Filter.Eventually.of_forall fun Q => (uAct_eq_sum _ _).symm)

lemma memLp_uAct {n : ℕ} {M : MassShell m → Matrix.unitaryGroup (Fin (n + 1)) ℂ} (hM : Continuous M)
    (f : Lp (Spinor n) 2 μ) : MemLp (fun Q => uAct (M Q) (f Q)) 2 μ := by
  have hf : MemLp (f : MassShell m → Spinor n) 2 μ := Lp.memLp f
  refine hf.of_le (aestronglyMeasurable_uAct hM f) ?_
  exact Filter.Eventually.of_forall fun Q => (norm_uAct (M Q) _).le

/-- **Multiplication by a continuous field of unitary matrices**, a linear isometry of `L²`. -/
def mulL2 {n : ℕ} (M : MassShell m → Matrix.unitaryGroup (Fin (n + 1)) ℂ) (hM : Continuous M) :
    Lp (Spinor n) 2 μ →ₗᵢ[ℂ] Lp (Spinor n) 2 μ where
  toFun f := (memLp_uAct hM f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_uAct hM (f + g)).coeFn_toLp, Lp.coeFn_add f g,
      Lp.coeFn_add ((memLp_uAct hM f).toLp _) ((memLp_uAct hM g).toLp _),
      (memLp_uAct hM f).coeFn_toLp, (memLp_uAct hM g).coeFn_toLp] with Q h1 h2 h3 h4 h5
    rw [h1, h3, Pi.add_apply, h4, h5, h2, Pi.add_apply, uAct_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_uAct hM (c • f)).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((memLp_uAct hM f).toLp _), (memLp_uAct hM f).coeFn_toLp] with Q h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h4, h2, Pi.smul_apply, uAct_smul]
  norm_map' f := by
    change ‖(memLp_uAct hM f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae (aestronglyMeasurable_uAct hM f) (Lp.aestronglyMeasurable f)
      (Filter.Eventually.of_forall fun Q => norm_uAct _ _)

lemma coeFn_mulL2 {n : ℕ} {M : MassShell m → Matrix.unitaryGroup (Fin (n + 1)) ℂ} (hM : Continuous M)
    (f : Lp (Spinor n) 2 μ) : (mulL2 M hM f : MassShell m → Spinor n) =ᵐ[μ] fun Q => uAct (M Q) (f Q) :=
  (memLp_uAct hM f).coeFn_toLp

variable (hm : 0 < m)

/-- The spin matrix of the Wigner rotation of `A` at `A⁻¹ • Q`. -/
def wigField (n : ℕ) (A : SL2C) (Q : MassShell m) : Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
  spinRep n (wignerSU2 hm A (shellAct A⁻¹ Q))

lemma continuous_wigField (n : ℕ) (A : SL2C) : Continuous (wigField (m := m) hm n A) := by
  have hw : Continuous fun Q : MassShell m => wignerSU2 hm A (shellAct A⁻¹ Q) := by
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun Q : MassShell m => ((stdLift hm (shellAct A (shellAct A⁻¹ Q)))⁻¹ : SL2C) :=
      ((continuous_stdLift hm).comp ((continuous_shellAct A).comp (continuous_shellAct A⁻¹))).inv
    have h2 : Continuous fun Q : MassShell m => stdLift hm (shellAct A⁻¹ Q) :=
      (continuous_stdLift hm).comp (continuous_shellAct A⁻¹)
    exact continuous_subtype_val.comp ((h1.mul continuous_const).mul h2)
  exact continuous_induced_rng.2 ((continuous_spinRep (n := n)).comp hw)

/-- **The induced representation on `L²`**: `(U(A) f)(Q) = D(W(A, A⁻¹ Q)) f(A⁻¹ Q)`, for an invariant measure. -/
def inducedL2 (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (A : SL2C) :
    Lp (Spinor n) 2 μ →ₗᵢ[ℂ] Lp (Spinor n) 2 μ :=
  (mulL2 (wigField hm n A) (continuous_wigField hm n A)).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (shellAct A⁻¹) (hμ A⁻¹))

/-- The representatives of `U(A) f` are the pointwise induced action. -/
lemma coeFn_inducedL2 (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (A : SL2C)
    (f : Lp (Spinor n) 2 μ) :
    (inducedL2 hm n hμ A f : MassShell m → Spinor n) =ᵐ[μ]
      fun Q => uAct (wigField hm n A Q) (f (shellAct A⁻¹ Q)) := by
  have h1 := coeFn_mulL2 (continuous_wigField hm n A) (Lp.compMeasurePreservingₗᵢ ℂ (shellAct A⁻¹) (hμ A⁻¹) f)
  have h2 := Lp.coeFn_compMeasurePreserving f (hμ A⁻¹)
  filter_upwards [h1, h2] with Q hQ1 hQ2
  rw [show inducedL2 hm n hμ A f = mulL2 (wigField hm n A) (continuous_wigField hm n A)
    (Lp.compMeasurePreservingₗᵢ ℂ (shellAct A⁻¹) (hμ A⁻¹) f) from rfl, hQ1]
  congr 1

/-! ## The group law -/

lemma uAct_mul {n : ℕ} (U V : Matrix.unitaryGroup (Fin (n + 1)) ℂ) (v : Spinor n) :
    uAct (U * V) v = uAct U (uAct V v) := by
  unfold uAct
  rw [WithLp.ofLp_toLp, Matrix.mulVec_mulVec]
  rfl

lemma uAct_one {n : ℕ} (v : Spinor n) : uAct (1 : Matrix.unitaryGroup (Fin (n + 1)) ℂ) v = v := by
  simp [uAct]

lemma wigField_mul (n : ℕ) (A B : SL2C) (Q : MassShell m) :
    wigField hm n (A * B) Q = wigField hm n A Q * wigField hm n B (shellAct A⁻¹ Q) := by
  simp only [wigField]
  have hBB : shellAct B (shellAct B⁻¹ (shellAct A⁻¹ Q)) = shellAct A⁻¹ Q := by
    rw [← shellAct_mul, mul_inv_cancel, shellAct_one]
  rw [← map_mul, _root_.mul_inv_rev, shellAct_mul, wignerSU2_mul, hBB]

lemma wigField_one (n : ℕ) (Q : MassShell m) : wigField hm n 1 Q = 1 := by
  have h : wignerSU2 hm 1 (shellAct 1⁻¹ Q) = 1 := by
    apply Subtype.ext
    simp [wignerSU2, wigner, shellAct_one]
  simp only [wigField, h, map_one]

variable {hm} in
/-- **The group law on `L²`**: `U(A B) = U(A) U(B)`. -/
lemma inducedL2_mul (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (A B : SL2C)
    (f : Lp (Spinor n) 2 μ) : inducedL2 hm n hμ (A * B) f = inducedL2 hm n hμ A (inducedL2 hm n hμ B f) := by
  apply Lp.ext
  have h3 := (hμ A⁻¹).quasiMeasurePreserving.ae_eq_comp (coeFn_inducedL2 hm n hμ B f)
  filter_upwards [coeFn_inducedL2 hm n hμ (A * B) f, coeFn_inducedL2 hm n hμ A (inducedL2 hm n hμ B f), h3]
    with Q hQ1 hQ2 hQ3
  rw [hQ1, hQ2]
  simp only [Function.comp_apply] at hQ3
  rw [hQ3, ← uAct_mul, ← wigField_mul, _root_.mul_inv_rev, shellAct_mul]

variable {hm} in
lemma inducedL2_one (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (f : Lp (Spinor n) 2 μ) :
    inducedL2 hm n hμ 1 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_inducedL2 hm n hμ 1 f] with Q hQ
  rw [hQ, wigField_one, uAct_one, inv_one, shellAct_one]

/-- `U(A)` as a unitary operator of `L²`. -/
def inducedL2E (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (A : SL2C) :
    Lp (Spinor n) 2 μ ≃ₗᵢ[ℂ] Lp (Spinor n) 2 μ :=
  LinearIsometryEquiv.ofSurjective (inducedL2 hm n hμ A) fun f =>
    ⟨inducedL2 hm n hμ A⁻¹ f, by rw [← inducedL2_mul, mul_inv_cancel, inducedL2_one]⟩

lemma inducedL2E_apply (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (A : SL2C)
    (f : Lp (Spinor n) 2 μ) : inducedL2E hm n hμ A f = inducedL2 hm n hμ A f := rfl

end

end Lightlike.Poincare
