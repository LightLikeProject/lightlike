module

public import Lightlike.Upstream.SU2Spin.Brackets
public import Lightlike.Upstream.SU2Spin.Sl2Standard
public import Lightlike.Upstream.SU2Spin.SpinRep

/-!
# Completeness of the spin representations: the Lie-algebra part

For a continuous representation `ρ` of `SU(2)` on `ℂᵈ`, the complexified differential gives matrices
`opH ρ`, `opE ρ`, `opF ρ` with the `sl₂` relations (`sl2_rel`), hence (when `opH ρ ≠ 0`) an
`sl₂`-triple in the sense of Mathlib (`isSl2Triple_ops`). A subspace stable under `opH, opE, opF`
is stable under `ρ` (`invariant_of_ops`).

Two `sl₂`-triples of matrices with primitive vectors of the same weight `n` whose `F`-orbits span
are intertwined by a linear equivalence (`exists_intertwiner`).
-/

@[expose] public section

open Matrix Filter Topology Module

namespace SU2Spin

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ## Algebra of `su(2)` -/

/-- Every `X ∈ su(2)` is a real combination of `suZ, suY, suX`. -/
lemma IsSu2.decomp {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : IsSu2 X) :
    X = (X 0 0).im • suZ + (-(X 0 1).re) • suY + (X 0 1).im • suX := by
  have h11 := hX.trace_eq
  have h10 := hX.entry10
  have hre := hX.re00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suZ, suY, suX, Complex.ext_iff, h11, h10, hre]

/-! ## The complexified differential -/

variable {d : ℕ} [NeZero d] {ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ}

/-- `H = -i dρ(Z)`. -/
noncomputable def opH (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (-Complex.I) • dρ ρ suZ

/-- `E = (-dρ(Y) - i dρ(X)) / 2`. -/
noncomputable def opE (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (-dρ ρ suY - Complex.I • dρ ρ suX)

/-- `F = (dρ(Y) - i dρ(X)) / 2`. -/
noncomputable def opF (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (1 / 2 : ℂ) • (dρ ρ suY - Complex.I • dρ ρ suX)

omit [NeZero d] in
lemma dρZ_eq (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    dρ ρ suZ = Complex.I • opH ρ := by
  rw [opH, smul_smul, show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg],
    one_smul]

omit [NeZero d] in
lemma dρY_eq (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    dρ ρ suY = opF ρ - opE ρ := by
  rw [opF, opE, ← smul_sub]; module

omit [NeZero d] in
lemma dρX_eq (ρ : specialUnitaryGroup (Fin 2) ℂ →* Matrix (Fin d) (Fin d) ℂ) :
    dρ ρ suX = Complex.I • (opE ρ + opF ρ) := by
  rw [opE, opF, ← smul_add, smul_smul]
  rw [show -dρ ρ suY - Complex.I • dρ ρ suX + (dρ ρ suY - Complex.I • dρ ρ suX) =
    (-2 * Complex.I) • dρ ρ suX by module, smul_smul]
  rw [show Complex.I * (1 / 2) * (-2 * Complex.I) = 1 by
    ring_nf; rw [Complex.I_sq]; ring, one_smul]

/-- **The `sl₂` relations** `[H,E] = 2E`, `[H,F] = -2F`, `[E,F] = H` for the complexified
differential of a continuous representation. -/
theorem sl2_rel (hρ : Continuous ρ) :
    opH ρ * opE ρ - opE ρ * opH ρ = (2 : ℂ) • opE ρ ∧
    opH ρ * opF ρ - opF ρ * opH ρ = (-2 : ℂ) • opF ρ ∧
    opE ρ * opF ρ - opF ρ * opE ρ = opH ρ := by
  obtain ⟨b1, b2, b3⟩ := brackets hρ
  unfold opH opE opF
  generalize dρ ρ suZ = z at b1 b2 b3 ⊢
  generalize dρ ρ suY = y at b1 b2 b3 ⊢
  generalize dρ ρ suX = x at b1 b2 b3 ⊢
  have r : ∀ (r : ℝ) (m : Matrix (Fin d) (Fin d) ℂ), r • m = (r : ℂ) • m := fun r m => rfl
  rw [r] at b1 b2 b3
  push_cast at b1 b2 b3
  have h1 : y * z = z * y + (2 : ℂ) • x := by rw [← sub_eq_iff_eq_add', ← neg_sub, b1]; module
  have h2 : x * z = z * x - (2 : ℂ) • y := by
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', b2]
  have h3 : x * y = y * x + (2 : ℂ) • z := by rw [← sub_eq_iff_eq_add', ← neg_sub, b3]; module
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, neg_mul, mul_neg,
      smul_sub, smul_neg, smul_smul, h1, h2, smul_add]
    match_scalars <;> first | ring1 | (ring_nf; simp only [Complex.I_sq])
  · simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, neg_mul, mul_neg,
      smul_sub, smul_smul, h1, h2, smul_add]
    match_scalars <;> first | ring1 | (ring_nf; simp only [Complex.I_sq])
  · simp only [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, neg_mul,
      mul_neg, smul_sub, smul_neg, smul_smul, h3, smul_add, neg_sub]
    match_scalars <;> ring1

section Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **`(H, E, F)` is an `sl₂`-triple** of matrices (when `H ≠ 0`). -/
theorem isSl2Triple_ops (hρ : Continuous ρ) (hH : opH ρ ≠ 0) :
    IsSl2Triple (opH ρ) (opE ρ) (opF ρ) where
  h_ne_zero := hH
  lie_e_f := by rw [LieRing.of_associative_ring_bracket]; exact (sl2_rel hρ).2.2
  lie_h_e_nsmul := by
    rw [LieRing.of_associative_ring_bracket, (sl2_rel hρ).1]; module
  lie_h_f_nsmul := by
    rw [LieRing.of_associative_ring_bracket, (sl2_rel hρ).2.1]; module

end Lie

end SU2Spin
