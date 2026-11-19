import Lightlike.Poincare.PauliLubanskiStone
import Lightlike.Poincare.ConeMeasure
import Lightlike.Poincare.LightConeUnitary
import Physlib.Relativity.SL2C.Cover

/-!
# The one-particle space of a massive free field

The momenta are Hermitian matrices `P = p⁰ + p·σ`, on which `SL(2,ℂ)` acts by `P ↦ A P Aᴴ`; this action is the
restricted Lorentz group acting on four-vectors through Physlib's covering homomorphism
`Lorentz.SL2C.toRestrictedLorentzGroup`, which is surjective.

* **Invariant measures.** The mass shell `p² = m², p⁰ > 0` (`m > 0`) and the forward light cone carry nonzero
  measures, finite on compacts, invariant under the restricted Lorentz group (`exists_invariant_measure_massShell`,
  `exists_invariant_measure_lightCone`).
* **The Poincaré representation.** On `L²(μ; ℂ^{n+1})`, for an invariant measure `μ` on the mass shell, the
  translations act by the phases `(T(a) ψ)(p) = e^{i p·a} ψ(p)` (`translL2`) and `SL(2,ℂ)` by the induced
  spinor action `U(A)` (`inducedL2E`); `V(a, A) = T(a) U(A)` (`poincareL2`) is a unitary representation of the
  inhomogeneous group `ℝ⁴ ⋊ SL(2,ℂ)`: `V(a, A) V(b, B) = V(a + Λ(A) b, A B)` (`poincareL2_mul`).

## References

* X. Bekaert, N. Boulanger, *The unitary representations of the Poincaré group in any spacetime dimension*,
  arXiv:hep-th/0611263v2, §3.1 (page 9 of v2: translations act on the momentum eigenstates by `e^{−i q·a}`, signature
  `(−,+,+,+)`; equation (13), page 10: the induced action), §3.2, Remarks (page 11: the Poincaré-invariant scalar
  product `⟨Ψ|Φ⟩ = ∫ dᴰp δ(p² + m²) Θ(p⁰) Σ_σ Ψ*_{p,σ} Φ_{p,σ}`).
-/

open MeasureTheory Matrix Lightlike.Lorentz Lightlike.SU2

namespace Lightlike.Poincare

noncomputable section

/-! ## Invariant measures -/

/-- The action of `A ∈ SL(2,ℂ)` on momenta is the action of the restricted Lorentz transformation
`toRestrictedLorentzGroup A`, and every restricted Lorentz transformation arises this way. -/
lemma exists_lift_restricted (Λ : LorentzGroup.restricted 3) :
    ∃ A : SL2C, _root_.Lorentz.SL2C.toRestrictedLorentzGroup A = Λ :=
  _root_.Lorentz.SL2C.toRestrictedLorentzGroup_surjective Λ

/-- **A Lorentz-invariant measure on the mass shell** `p² = m²`, `p⁰ > 0`: nonzero, finite on compacts, and preserved
by every restricted Lorentz transformation (through each of its two lifts to `SL(2,ℂ)`). -/
theorem exists_invariant_measure_massShell {m : ℝ} (hm : 0 < m) :
    ∃ μ : Measure (MassShell m), μ ≠ 0 ∧ IsFiniteMeasureOnCompacts μ ∧
      ∀ Λ : LorentzGroup.restricted 3, ∀ A : SL2C, _root_.Lorentz.SL2C.toRestrictedLorentzGroup A = Λ →
        MeasurePreserving (shellAct A) μ μ :=
  ⟨shellMeasure hm, shellMeasure_ne_zero hm, inferInstance, fun _ A _ => measurePreserving_shellAct hm A⟩

/-- **A Lorentz-invariant measure on the forward light cone** `p² = 0`, `p ≠ 0`, `p⁰ ≥ 0`: nonzero, finite on
compacts, and preserved by every restricted Lorentz transformation. -/
theorem exists_invariant_measure_lightCone :
    ∃ μ : Measure LightCone, μ ≠ 0 ∧ IsFiniteMeasureOnCompacts μ ∧
      ∀ Λ : LorentzGroup.restricted 3, ∀ A : SL2C, _root_.Lorentz.SL2C.toRestrictedLorentzGroup A = Λ →
        MeasurePreserving (fun P : LightCone => A • P) μ μ :=
  ⟨coneMeasure, coneMeasure_ne_zero, inferInstance, fun _ A _ =>
    ⟨(continuous_smul_lightCone A).measurable, coneMeasure_map_smul A⟩⟩

/-! ## Translations -/

/-- The translations: Hermitian matrices `a = a⁰ + a·σ`. -/
abbrev Transl := selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)

/-- `SL(2,ℂ)` acts on translations by `a ↦ A a Aᴴ`. -/
def translAct (A : SL2C) (a : Transl) : Transl :=
  ⟨actP A a.1, by
    rw [selfAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
    have ha : a.1ᴴ = a.1 := by rw [← Matrix.star_eq_conjTranspose]; exact a.2
    simp only [actP, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ha, Matrix.mul_assoc]⟩

lemma translAct_add (A : SL2C) (a b : Transl) : translAct A (a + b) = translAct A a + translAct A b :=
  Subtype.ext (actP_add A a.1 b.1)

lemma translAct_mul (A B : SL2C) (a : Transl) : translAct (A * B) a = translAct A (translAct B a) :=
  Subtype.ext (actP_mul A B a.1)

/-- The Minkowski pairing `p·a` of a momentum and a translation (real for Hermitian matrices). -/
def pairing (P a : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (mink P a).re

lemma pairing_actP (A : SL2C) (P a : Matrix (Fin 2) (Fin 2) ℂ) : pairing (actP A P) (actP A a) = pairing P a := by
  rw [pairing, pairing, mink_actP]

lemma mink_add_right (P a b : Matrix (Fin 2) (Fin 2) ℂ) : mink P (a + b) = mink P a + mink P b := by
  simp only [mink, Matrix.det_fin_two, Matrix.add_apply]
  ring

lemma pairing_add (P a b : Matrix (Fin 2) (Fin 2) ℂ) : pairing P (a + b) = pairing P a + pairing P b := by
  rw [pairing, pairing, pairing, mink_add_right, Complex.add_re]

/-- The phase `e^{i p·a}`, a unitary scalar matrix. -/
def phaseMat {m : ℝ} (n : ℕ) (a : Transl) (Q : MassShell m) : Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
  ⟨Complex.exp (Complex.I * pairing Q.1 a.1) • 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, smul_mul_smul_comm, Matrix.one_mul]
    have he : Complex.exp (Complex.I * (pairing Q.1 a.1 : ℂ)) *
        star (Complex.exp (Complex.I * (pairing Q.1 a.1 : ℂ))) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp [Complex.conj_ofReal]
    rw [he, one_smul]⟩

lemma continuous_mink_left (a : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous fun P : Matrix (Fin 2) (Fin 2) ℂ => mink P a := by
  unfold mink
  simp only [Matrix.det_fin_two, Matrix.add_apply]
  have h : ∀ i j : Fin 2, Continuous fun P : Matrix (Fin 2) (Fin 2) ℂ => P i j :=
    fun i j => (continuous_id : Continuous (id : Matrix (Fin 2) (Fin 2) ℂ → _)).matrix_elem i j
  fun_prop

lemma continuous_phaseMat {m : ℝ} (n : ℕ) (a : Transl) : Continuous (phaseMat (m := m) n a) := by
  have hp : Continuous fun Q : MassShell m => ((pairing Q.1 a.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp
      ((continuous_mink_left a.1).comp continuous_subtype_val))
  have h : Continuous fun Q : MassShell m =>
      Complex.exp (Complex.I * (pairing Q.1 a.1 : ℂ)) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :=
    (Complex.continuous_exp.comp (continuous_const.mul hp)).smul continuous_const
  exact continuous_induced_rng.2 h

variable {m : ℝ} {μ : Measure (MassShell m)}

/-- **The translations on `L²`**: `(T(a) ψ)(p) = e^{i p·a} ψ(p)`. -/
def translL2 (n : ℕ) (a : Transl) : Lp (Spinor n) 2 μ →ₗᵢ[ℂ] Lp (Spinor n) 2 μ :=
  mulL2 (phaseMat n a) (continuous_phaseMat n a)

lemma coeFn_translL2 (n : ℕ) (a : Transl) (f : Lp (Spinor n) 2 μ) :
    (translL2 n a f : MassShell m → Spinor n) =ᵐ[μ] fun Q => Complex.exp (Complex.I * pairing Q.1 a.1) • f Q := by
  filter_upwards [coeFn_mulL2 (continuous_phaseMat n a) f] with Q hQ
  rw [translL2, hQ]
  simp only [uAct, phaseMat, Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.toLp_smul, WithLp.toLp_ofLp]

lemma translL2_add (n : ℕ) (a b : Transl) (f : Lp (Spinor n) 2 μ) :
    translL2 n (a + b) f = translL2 n a (translL2 n b f) := by
  apply Lp.ext
  filter_upwards [coeFn_translL2 n (a + b) f, coeFn_translL2 n a (translL2 n b f), coeFn_translL2 n b f]
    with Q h1 h2 h3
  rw [h1, h2, h3, smul_smul, ← Complex.exp_add]
  congr 2
  simp only [AddSubgroup.coe_add, pairing_add]
  push_cast
  ring

lemma translL2_zero (n : ℕ) (f : Lp (Spinor n) 2 μ) : translL2 n 0 f = f := by
  apply Lp.ext
  filter_upwards [coeFn_translL2 n 0 f] with Q h
  rw [h]
  simp [pairing, mink]

/-- **The covariance of the translations**: `U(A) T(b) = T(Λ(A) b) U(A)`. -/
lemma inducedL2_translL2 (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (A : SL2C)
    (b : Transl) (f : Lp (Spinor n) 2 μ) :
    inducedL2 hm n hμ A (translL2 n b f) = translL2 n (translAct A b) (inducedL2 hm n hμ A f) := by
  apply Lp.ext
  have h3 := (hμ A⁻¹).quasiMeasurePreserving.ae_eq_comp (coeFn_translL2 n b f)
  filter_upwards [coeFn_inducedL2 hm n hμ A (translL2 n b f), coeFn_translL2 n (translAct A b) (inducedL2 hm n hμ A f),
    coeFn_inducedL2 hm n hμ A f, h3] with Q h1 h2 h4 h5
  simp only [Function.comp_apply] at h5
  rw [h1, h2, h4, h5, uAct_smul]
  congr 3
  have : pairing (shellAct A⁻¹ Q).1 b.1 = pairing Q.1 (translAct A b).1 := by
    have h := pairing_actP A (shellAct A⁻¹ Q).1 b.1
    have hQ : actP A (shellAct A⁻¹ Q).1 = Q.1 := by
      change (shellAct A (shellAct A⁻¹ Q)).1 = Q.1
      rw [← shellAct_mul, mul_inv_cancel, shellAct_one]
    rw [hQ] at h
    exact h.symm
  rw [this]

/-- **The unitary representation of the inhomogeneous group** `V(a, A) = T(a) U(A)`. -/
def poincareL2 (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (a : Transl) (A : SL2C) :
    Lp (Spinor n) 2 μ →ₗᵢ[ℂ] Lp (Spinor n) 2 μ :=
  (translL2 n a).comp (inducedL2 hm n hμ A)

/-- **The group law** of `ℝ⁴ ⋊ SL(2,ℂ)`: `V(a, A) V(b, B) = V(a + Λ(A) b, A B)`. -/
theorem poincareL2_mul (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ) (a b : Transl)
    (A B : SL2C) (f : Lp (Spinor n) 2 μ) :
    poincareL2 hm n hμ a A (poincareL2 hm n hμ b B f) = poincareL2 hm n hμ (a + translAct A b) (A * B) f := by
  simp only [poincareL2, LinearIsometry.coe_comp, Function.comp_apply]
  rw [inducedL2_translL2, translL2_add, inducedL2_mul]

theorem poincareL2_one (hm : 0 < m) (n : ℕ) (hμ : ∀ A : SL2C, MeasurePreserving (shellAct A) μ μ)
    (f : Lp (Spinor n) 2 μ) : poincareL2 hm n hμ 0 1 f = f := by
  simp only [poincareL2, LinearIsometry.coe_comp, Function.comp_apply, inducedL2_one, translL2_zero]

end

end Lightlike.Poincare
