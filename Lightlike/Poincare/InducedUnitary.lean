module

public import Lightlike.Poincare.InducedMassive

/-!
# Unitarity of the induced massive representations

The mass shell `MassShell m` (`m > 0`) is the orbit of the rest momentum `m · 1` under `SL(2,ℂ)`. The image of the
Haar measure of `SL(2,ℂ)` under the orbit map `g ↦ g • (m · 1)` is an `SL(2,ℂ)`-invariant measure on the mass shell
(`shellMeasure`, `shellMeasure_map_shellAct`): invariance is the left invariance of the Haar measure. For a unitary
representation `D` of `SU(2)` the induced action preserves `∫ ‖ψ(P)‖² dμ(P)` (`lintegral_normSq_inducedAct`), and so do
the translations (`lintegral_normSq_transAct`, for real pairings): the induced representations are unitary.

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.2 (the Poincaré-invariant scalar product on the orbit, page 11 of v2).
-/

@[expose] public section

noncomputable section

open Matrix MeasureTheory Lightlike.Lorentz
open scoped ENNReal ComplexOrder

namespace Lightlike.Poincare

/-- The Borel σ-algebra on the mass shell. -/
instance instMeasurableSpaceMassShell (m : ℝ) : MeasurableSpace (MassShell m) := borel _

instance instBorelSpaceMassShell (m : ℝ) : BorelSpace (MassShell m) := ⟨rfl⟩

/-- The rest momentum `m · 1` as a point of the mass shell. -/
def restShell {m : ℝ} (hm : 0 < m) : MassShell m :=
  ⟨(m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ), by
    refine ⟨Matrix.PosDef.one.smul (Complex.zero_lt_real.2 hm), ?_⟩
    rw [Matrix.det_smul, Matrix.det_one]
    simp⟩

lemma continuous_actP (P : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun A : SL2C => actP A P := by
  unfold actP
  have h : Continuous fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  exact (h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose

lemma continuous_shellAct {m : ℝ} (A : SL2C) : Continuous (shellAct (m := m) A) := by
  refine Continuous.subtype_mk ?_ _
  unfold actP
  have h : Continuous fun P : MassShell m => (P.1 : Matrix (Fin 2) (Fin 2) ℂ) := continuous_subtype_val
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

/-- The orbit map `g ↦ g • (m · 1)`. -/
def orbitMap {m : ℝ} (hm : 0 < m) (g : SL2C) : MassShell m := shellAct g (restShell hm)

lemma continuous_orbitMap {m : ℝ} (hm : 0 < m) : Continuous (orbitMap hm) :=
  (continuous_actP _).subtype_mk _

/-- **The invariant measure on the mass shell**: the image of the Haar measure of `SL(2,ℂ)`. -/
def shellMeasure {m : ℝ} (hm : 0 < m) : Measure (MassShell m) := Measure.map (orbitMap hm) SL2C.haar

/-- The action of `A` on the mass shell as a measurable equivalence. -/
def shellActEquiv {m : ℝ} (A : SL2C) : MassShell m ≃ᵐ MassShell m where
  toFun := shellAct A
  invFun := shellAct A⁻¹
  left_inv P := by rw [← shellAct_mul, inv_mul_cancel, shellAct_one]
  right_inv P := by rw [← shellAct_mul, mul_inv_cancel, shellAct_one]
  measurable_toFun := (continuous_shellAct A).measurable
  measurable_invFun := (continuous_shellAct A⁻¹).measurable

/-- **Invariance of the mass-shell measure.** -/
theorem shellMeasure_map_shellAct {m : ℝ} (hm : 0 < m) (A : SL2C) :
    Measure.map (shellAct A) (shellMeasure hm) = shellMeasure hm := by
  rw [shellMeasure, Measure.map_map (continuous_shellAct A).measurable (continuous_orbitMap hm).measurable]
  have h : shellAct A ∘ orbitMap hm = orbitMap hm ∘ (fun g => A * g) := by
    funext g; simp [orbitMap, shellAct_mul]
  rw [h, ← Measure.map_map (continuous_orbitMap hm).measurable (measurable_const_mul A),
    map_mul_left_eq_self SL2C.haar A]

lemma measurePreserving_shellAct {m : ℝ} (hm : 0 < m) (A : SL2C) :
    MeasurePreserving (shellAct A) (shellMeasure hm) (shellMeasure hm) :=
  ⟨(continuous_shellAct A).measurable, shellMeasure_map_shellAct hm A⟩

/-- The squared Euclidean norm `Σ |vᵢ|²` of a vector. -/
def normSqV {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma normSqV_eq {ι : Type} [Fintype ι] (v : ι → ℂ) : (normSqV v : ℂ) = star v ⬝ᵥ v := by
  simp only [normSqV, dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.star_def, Complex.conj_mul']

/-- Unitary matrices preserve the squared Euclidean norm. -/
lemma normSqV_unitary_mulVec {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix.unitaryGroup ι ℂ)
    (v : ι → ℂ) : normSqV ((U : Matrix ι ι ℂ) *ᵥ v) = normSqV v := by
  have h : star ((U : Matrix ι ι ℂ) *ᵥ v) ⬝ᵥ ((U : Matrix ι ι ℂ) *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, Matrix.UnitaryGroup.star_mul_self, Matrix.vecMul_one]
  have h1 : ((normSqV ((U : Matrix ι ι ℂ) *ᵥ v) : ℝ) : ℂ) = ((normSqV v : ℝ) : ℂ) := by
    rw [normSqV_eq, normSqV_eq, h]
  exact_mod_cast h1

/-- **Unitarity of the induced massive action** for the invariant measure. -/
theorem lintegral_normSq_inducedAct {m : ℝ} (hm : 0 < m) {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : Lightlike.SU2 →* Matrix.unitaryGroup ι ℂ) (A : SL2C) (ψ : MassShell m → ι → ℂ) :
    ∫⁻ P, ENNReal.ofReal (normSqV (inducedAct hm D A ψ P)) ∂shellMeasure hm =
      ∫⁻ P, ENNReal.ofReal (normSqV (ψ P)) ∂shellMeasure hm := by
  simp only [inducedAct, normSqV_unitary_mulVec]
  exact (measurePreserving_shellAct hm A⁻¹).lintegral_comp_emb (shellActEquiv A⁻¹).measurableEmbedding
    (fun P => ENNReal.ofReal (normSqV (ψ P)))

/-- The translations preserve the squared norm when the pairing is real (`X` Hermitian). -/
theorem normSqV_transAct {m : ℝ} {ι : Type} [Fintype ι] (X : Matrix (Fin 2) (Fin 2) ℂ)
    (hX : ∀ P : MassShell m, (mink P.1 X).im = 0) (ψ : MassShell m → ι → ℂ) (P : MassShell m) :
    normSqV (transAct X ψ P) = normSqV (ψ P) := by
  simp only [normSqV, transAct, Pi.smul_apply, smul_eq_mul, norm_mul]
  have : ‖Complex.exp (Complex.I * mink P.1 X)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, hX P]
  simp [this]

end Lightlike.Poincare
