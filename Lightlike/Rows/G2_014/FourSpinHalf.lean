import Lightlike.Rows.G2_014.SpinHalf

/-!
# Four spin-`1/2` edges: explicit singlet-pair vectors

Seventh piece of row G2-014 (milestone CA4). We work on the node with four edges of spin `1/2`
(`n4`). `psi0` is the product of two singlets (edges `01` and `23`); it is gauge invariant
(`psi0_invariant`). With `phi`, the vector `q_{012} ψ₀` (`q_psi0`), we prove `phi_invariant` and
`q_phi : q_{012} φ = (3/16) ψ₀`, hence `q_{012}² ψ₀ = (3/16) ψ₀`.
-/

open Matrix

namespace Lightlike.Rows.G2_014

/-- Four edges, each of spin `1/2`. -/
abbrev n4 : Fin 4 → ℕ := fun _ => 1

/-- The singlet coefficients `ε(0,1) = 1`, `ε(1,0) = -1`. -/
def eps : Fin 2 → Fin 2 → ℂ := ![![0, 1], ![-1, 0]]

/-- Product of the singlets on edges `01` and `23`. -/
def psi0 : Idx n4 → ℂ := fun m => eps (m 0) (m 1) * eps (m 2) (m 3)

lemma n4_apply (e : Fin 4) (a : Fin 3) (ψ : Idx n4 → ℂ) (m : Idx n4) :
    (edgeOp n4 e a *ᵥ ψ) m =
      Lightlike.Poincare.spinOp 1 a (m e) 0 * ψ (Function.update m e 0)
        + Lightlike.Poincare.spinOp 1 a (m e) 1 * ψ (Function.update m e 1) := by
  rw [edgeOp_mulVec_apply]
  exact Fin.sum_univ_two _

lemma totalOp_apply (a : Fin 3) (ψ : Idx n4 → ℂ) (m : Idx n4) :
    (totalOp n4 a *ᵥ ψ) m = ∑ e, (edgeOp n4 e a *ᵥ ψ) m := by
  simp [totalOp, Matrix.sum_mulVec, Finset.sum_apply]

lemma psi0_invariant : IsInvariant n4 psi0 := by
  intro a
  funext m
  rw [totalOp_apply, Fin.sum_univ_four, n4_apply, n4_apply, n4_apply, n4_apply]
  fin_cases a
  all_goals
    simp [spinOp_one_zero, spinOp_one_one, spinOp_one_two, psi0]
  all_goals
    generalize m 0 = x0
    generalize m 1 = x1
    generalize m 2 = x2
    generalize m 3 = x3
    fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> simp [eps]
    all_goals norm_num

/-- Expected value of `q_{012} ψ₀` (a swap of edges `0` and `2` applied to `ψ₀`, up to constants). -/
noncomputable def phi : Idx n4 → ℂ := fun m =>
  -(Complex.I / 4) * (2 * eps (m 2) (m 1) * eps (m 0) (m 3) - eps (m 0) (m 1) * eps (m 2) (m 3))

lemma qOp_apply (i j k : Fin 4) (ψ : Idx n4 → ℂ) (m : Idx n4) :
    (qOp n4 i j k *ᵥ ψ) m =
      (edgeOp n4 i 0 *ᵥ (edgeOp n4 j 1 *ᵥ (edgeOp n4 k 2 *ᵥ ψ))) m
      + (edgeOp n4 i 1 *ᵥ (edgeOp n4 j 2 *ᵥ (edgeOp n4 k 0 *ᵥ ψ))) m
      + (edgeOp n4 i 2 *ᵥ (edgeOp n4 j 0 *ᵥ (edgeOp n4 k 1 *ᵥ ψ))) m
      - (edgeOp n4 i 0 *ᵥ (edgeOp n4 j 2 *ᵥ (edgeOp n4 k 1 *ᵥ ψ))) m
      - (edgeOp n4 i 2 *ᵥ (edgeOp n4 j 1 *ᵥ (edgeOp n4 k 0 *ᵥ ψ))) m
      - (edgeOp n4 i 1 *ᵥ (edgeOp n4 j 0 *ᵥ (edgeOp n4 k 2 *ᵥ ψ))) m := by
  simp only [qOp, add_mulVec, sub_mulVec, ← mulVec_mulVec, Pi.add_apply, Pi.sub_apply]

lemma q_psi0 : qOp n4 0 1 2 *ᵥ psi0 = phi := by
  funext m
  rw [qOp_apply]
  simp only [n4_apply]
  simp [spinOp_one_zero, spinOp_one_one, spinOp_one_two, psi0, phi]
  generalize m 0 = x0
  generalize m 1 = x1
  generalize m 2 = x2
  generalize m 3 = x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> simp [eps]
  all_goals ring

lemma phi_invariant : IsInvariant n4 phi := by
  intro a
  funext m
  rw [totalOp_apply, Fin.sum_univ_four, n4_apply, n4_apply, n4_apply, n4_apply]
  fin_cases a
  all_goals
    simp [spinOp_one_zero, spinOp_one_one, spinOp_one_two, phi]
    generalize m 0 = x0
    generalize m 1 = x1
    generalize m 2 = x2
    generalize m 3 = x3
    fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> simp [eps]
    all_goals ring

lemma q_phi : qOp n4 0 1 2 *ᵥ phi = (3 / 16 : ℂ) • psi0 := by
  funext m
  rw [qOp_apply]
  simp only [n4_apply]
  simp [spinOp_one_zero, spinOp_one_one, spinOp_one_two, psi0, phi]
  generalize m 0 = x0
  generalize m 1 = x1
  generalize m 2 = x2
  generalize m 3 = x3
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> simp [eps]
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

end Lightlike.Rows.G2_014
