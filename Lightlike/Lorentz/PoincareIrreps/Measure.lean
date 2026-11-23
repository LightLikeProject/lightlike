module

public import Mathlib
public import Lightlike.Lorentz.HaarChart
public import Lightlike.Lorentz.PoincareIrreps.Wigner

/-!
# The invariant measure on the mass shell and unitarity of the induced representation

HA6 (Wigner's classification), fifth piece. For `m > 0` the mass shell `massShell m` is the orbit
`SL(2,ℂ) · (m·1)`. We define

* `shellMeasure hm`: the push-forward of the Haar measure `haarC` of `SL(2,ℂ)` under the orbit map
  `A ↦ A · (m·1)`; it is `SL(2,ℂ)`-invariant (`map_shellSMul_shellMeasure`), because the orbit map
  is equivariant and `haarC` is left invariant;
* `lintegral_shellSMul`: `∫⁻ g(A P) dμ(P) = ∫⁻ g(P) dμ(P)`;
* `fibreNormSq`: the squared norm on the fibre `ℂ^{n+1}`, preserved by the unitary spin matrices;
* `lintegral_inducedRep_normSq`: **`inducedRep hm n A` preserves the `L²(μ; ℂ^{n+1})` norm**
  (as an identity of lower integrals, for measurable `ψ`), i.e. the induced representation is
  isometric, hence unitary on `L²` (it is invertible with inverse `inducedRep hm n A⁻¹`).

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the
statements proved here are claimed.
-/

@[expose] public section

open Matrix MeasureTheory

namespace Lightlike.Lorentz.Poincare

open Lightlike.Lorentz

variable {m : ℝ} (hm : 0 < m)

/-- The matrix measurable space is the Borel one (it is that of `Fin 2 → Fin 2 → ℂ`). -/
instance instBorelMatrix22 : BorelSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → ℂ))

include hm in
lemma restMom_mem_massShell : restMom m ∈ massShell m := by
  refine ⟨?_, ?_⟩
  · simp [restMom, sq]
  · simp [restMom, hm]

/-- The rest momentum as a point of the mass shell. -/
def restShell : massShell m := ⟨restMom m, restMom_mem_massShell hm⟩

/-- The orbit map `A ↦ A · (m·1)`. -/
def orbitMap (A : SL2C) : massShell m := shellSMul hm A (restShell hm)

lemma orbitMap_mul (A B : SL2C) :
    orbitMap hm (A * B) = shellSMul hm A (orbitMap hm B) := by
  simp [orbitMap, shellSMul_mul hm]

lemma continuous_orbitMap : Continuous (orbitMap hm) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  change Continuous fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ) * (restMom m).1 *
    (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
  have h : Continuous fun A : SL2C => (A : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_subtype_val
  exact (h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose

lemma continuous_shellSMul (A : SL2C) : Continuous (shellSMul hm A) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  change Continuous fun P : massShell m => (A : Matrix (Fin 2) (Fin 2) ℂ) * P.1.1 *
    (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
  have h : Continuous fun P : massShell m => P.1.1 :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

lemma measurable_orbitMap : Measurable (orbitMap hm) := (continuous_orbitMap hm).measurable

lemma measurable_shellSMul (A : SL2C) : Measurable (shellSMul hm A) :=
  (continuous_shellSMul hm A).measurable

/-- **The invariant measure on the mass shell**: the push-forward of the Haar measure of
`SL(2,ℂ)` under `A ↦ A · (m·1)`. -/
noncomputable def shellMeasure : Measure (massShell m) := haarC.map (orbitMap hm)

/-- **Invariance**: `SL(2,ℂ)` acts on the mass shell preserving `shellMeasure`. -/
theorem map_shellSMul_shellMeasure (A : SL2C) :
    (shellMeasure hm).map (shellSMul hm A) = shellMeasure hm := by
  unfold shellMeasure
  rw [Measure.map_map (measurable_shellSMul hm A) (measurable_orbitMap hm)]
  have h : shellSMul hm A ∘ orbitMap hm = orbitMap hm ∘ (fun g => A * g) := by
    funext g; exact (orbitMap_mul hm A g).symm
  rw [h, ← Measure.map_map (measurable_orbitMap hm) (measurable_const_mul A),
    map_mul_left_eq_self haarC A]

/-- Invariance of the lower integral. -/
theorem lintegral_shellSMul (A : SL2C) {g : massShell m → ENNReal} (hg : Measurable g) :
    ∫⁻ P, g (shellSMul hm A P) ∂shellMeasure hm = ∫⁻ P, g P ∂shellMeasure hm := by
  conv_rhs => rw [← map_shellSMul_shellMeasure hm A]
  rw [lintegral_map hg (measurable_shellSMul hm A)]

/-- The squared norm on the fibre `ℂ^{n+1}`. -/
noncomputable def fibreNormSq {n : ℕ} (v : Fin (n + 1) → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma ofReal_fibreNormSq {n : ℕ} (v : Fin (n + 1) → ℂ) :
    (fibreNormSq v : ℂ) = star v ⬝ᵥ v := by
  simp only [fibreNormSq, dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (v i) = starRingEnd ℂ (v i) from rfl, Complex.conj_mul']
  simp

/-- Unitary matrices preserve the fibre norm. -/
lemma fibreNormSq_mulVec {n : ℕ} (U : Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (v : Fin (n + 1) → ℂ) :
    fibreNormSq ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) *ᵥ v) = fibreNormSq v := by
  apply Complex.ofReal_injective
  rw [ofReal_fibreNormSq, ofReal_fibreNormSq, star_mulVec, dotProduct_mulVec,
    vecMul_vecMul, show (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ *
      (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 from Matrix.mem_unitaryGroup_iff'.mp U.2,
    vecMul_one]

/-- **The induced representation preserves the `L²(shellMeasure; ℂ^{n+1})` norm**: for measurable
`ψ`, `∫ ‖(U(A) ψ)(P)‖² dμ(P) = ∫ ‖ψ(P)‖² dμ(P)` (lower integrals). -/
theorem lintegral_inducedRep_normSq (n : ℕ) (A : SL2C) (ψ : massShell m → Fin (n + 1) → ℂ)
    (hψ : Measurable fun P => ENNReal.ofReal (fibreNormSq (ψ P))) :
    ∫⁻ P, ENNReal.ofReal (fibreNormSq (inducedRep hm n A ψ P)) ∂shellMeasure hm =
      ∫⁻ P, ENNReal.ofReal (fibreNormSq (ψ P)) ∂shellMeasure hm := by
  simp only [inducedRep_apply, fibreNormSq_mulVec]
  exact lintegral_shellSMul hm A⁻¹ hψ

end Lightlike.Lorentz.Poincare
