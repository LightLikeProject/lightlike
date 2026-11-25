import Lightlike.Canonical.VolumeOperator.SpinHalf
import Lightlike.Canonical.VolumeOperator.FourValent

/-!
# Four spin-`1/2` edges: explicit singlet-pair vectors

Seventh piece of row G2-014 (milestone CA4). We work on the node with four edges of spin `1/2`
(`n4`). `psi0` is the product of two singlets (edges `01` and `23`); it is gauge invariant
(`psi0_invariant`). With `phi`, the vector `q_{012} ψ₀` (`q_psi0`), we prove `phi_invariant` and
`q_phi : q_{012} φ = (3/16) ψ₀`, hence `q_{012}² ψ₀ = (3/16) ψ₀`. The vectors `ψ_± = φ ± (√3/4) ψ₀` (`psiS`) are gauge-invariant
eigenvectors of `q_{012}` (`q_psiS`) and of `Q` with eigenvalue `±√3` (`Qnode_psiS`), so the volume
operator acts on them as `κ · 3^{1/4}` (`volume_four_halves_eigen`), and two different
regularization constants give different results (`volume_four_halves_ne`).
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

/-- Gauge invariance is preserved by linear combinations. -/
lemma IsInvariant.add_smul {ψ χ : Idx n4 → ℂ} (hψ : IsInvariant n4 ψ) (hχ : IsInvariant n4 χ)
    (c : ℂ) : IsInvariant n4 (ψ + c • χ) := by
  intro a
  rw [mulVec_add, mulVec_smul, hψ a, hχ a]
  simp

/-- The combination `φ + r ψ₀`. -/
noncomputable def psiS (r : ℝ) : Idx n4 → ℂ := phi + (r : ℂ) • psi0

lemma psiS_invariant (r : ℝ) : IsInvariant n4 (psiS r) :=
  IsInvariant.add_smul phi_invariant psi0_invariant _

/-- If `r² = 3/16`, then `φ + r ψ₀` is an eigenvector of `q_{012}` with eigenvalue `r`. -/
lemma q_psiS {r : ℝ} (hr : r * r = 3 / 16) :
    qOp n4 0 1 2 *ᵥ psiS r = (r : ℂ) • psiS r := by
  have hr' : (r : ℂ) * r = 3 / 16 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hr
    push_cast at this
    exact this
  unfold psiS
  rw [mulVec_add, mulVec_smul, q_psi0, q_phi, smul_add, smul_smul, hr', add_comm]

lemma psiS_ne_zero (r : ℝ) : psiS r ≠ 0 := by
  intro h
  have := congrFun h (fun i => ![(0 : Fin 2), 1, 0, 1] i)
  simp [psiS, phi, psi0, eps] at this
  have h2 := congrArg Complex.im this
  norm_num at h2

/-- `Q = ∑ s_{IJK} q_{IJK}` (with the signs `sgn4`) has eigenvalue `4 r` on `φ + r ψ₀`
whenever `r² = 3/16`, i.e. `4r = ±√3`. -/
lemma Qnode_psiS {r : ℝ} (hr : r * r = 3 / 16) :
    Qnode n4 sgn4 *ᵥ psiS r = ((4 * r : ℝ) : ℂ) • psiS r := by
  rw [Qnode_four_mulVec (psiS_invariant r), q_psiS hr, smul_smul]
  simp

/-- **Volume eigenvalues at the four-valent node with four spins `1/2`.**
On the gauge-invariant vector `ψ_± = φ ± (√3/4) ψ₀` (edges `0,1,2,3`, all spin `1/2`), the operator
`Q` has eigenvalue `±√3` and the volume operator `κ √|Q|` acts as multiplication by `κ · 3^{1/4}`.
The normalisation of `Q` is that of the present definition (`qOp`, `sgn4`); matching with the
tabulated values of Brunnemann–Thiemann (`brunnemann-thiemann-2006`) is not checked here. -/
theorem volume_four_halves_eigen (κ : ℝ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    volumeOp κ n4 sgn4 *ᵥ psiS (σ * (Real.sqrt 3 / 4)) =
      ((κ * Real.sqrt |σ * Real.sqrt 3| : ℝ) : ℂ) • psiS (σ * (Real.sqrt 3 / 4)) := by
  have hr : (σ * (Real.sqrt 3 / 4)) * (σ * (Real.sqrt 3 / 4)) = 3 / 16 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have : σ * σ = 1 := by rcases hσ with h | h <;> simp [h]
    calc _ = (σ * σ) * (Real.sqrt 3 * Real.sqrt 3) / 16 := by ring
      _ = _ := by rw [this, h3]; ring
  have hQ := Qnode_psiS hr
  have e : 4 * (σ * (Real.sqrt 3 / 4)) = σ * Real.sqrt 3 := by ring
  rw [e] at hQ
  exact volumeOp_mulVec_of_eigenvector κ sgn4 _ _ hQ

/-- **A wrong regularization constant is detected on a four-valent node**: for `κ ≠ κ'` the
volume operators differ on the eigenvector `ψ_±` of `volume_four_halves_eigen`. -/
theorem volume_four_halves_ne {κ κ' : ℝ} (hκ : κ ≠ κ') (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    volumeOp κ n4 sgn4 *ᵥ psiS (σ * (Real.sqrt 3 / 4)) ≠
      volumeOp κ' n4 sgn4 *ᵥ psiS (σ * (Real.sqrt 3 / 4)) := by
  have hr : (σ * (Real.sqrt 3 / 4)) * (σ * (Real.sqrt 3 / 4)) = 3 / 16 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have : σ * σ = 1 := by rcases hσ with h | h <;> simp [h]
    calc _ = (σ * σ) * (Real.sqrt 3 * Real.sqrt 3) / 16 := by ring
      _ = _ := by rw [this, h3]; ring
  have hQ := Qnode_psiS hr
  have e : 4 * (σ * (Real.sqrt 3 / 4)) = σ * Real.sqrt 3 := by ring
  rw [e] at hQ
  refine volumeOp_ne_of_ne hκ sgn4 (psiS_ne_zero _) ?_ hQ
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rcases hσ with h | h <;> simp [h, h3.ne']

end Lightlike.Rows.G2_014
