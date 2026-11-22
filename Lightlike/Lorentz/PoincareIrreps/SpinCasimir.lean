module

public import Mathlib
public import Lightlike.Upstream.SU2Spin.Completeness

/-!
# The spin Casimir of the SU(2) representations

HA6 (Wigner's classification), eighth piece: the little-group Casimir `J² = s(s+1)` needed for the
Pauli–Lubanski square `W² = −m² s(s+1)`.

* `dρZ_spin`: the differential of `spinMat n` at `suZ` is `diag(i (n − 2k))`;
* `opH_spin`: `opH (σ n) = diag(n − 2k)`;
* `opE_spin_highest`: the raising operator kills the highest weight vector;
* `sl2Casimir H E F = H² + 2H + 4FE`, commuting with `H, E, F` when they satisfy the `sl₂`
  relations (`sl2Casimir_comm_H/E/F`);
* `spin_casimir`: in the spin-`n/2` representation the Casimir is the scalar `n(n+2) = 4 s(s+1)`,
  `s = n/2` (irreducibility plus the highest weight vector).

Reference: S. Weinberg, *The Quantum Theory of Fields I* (1995), Chapter 2, §2.5; only the
statements proved here are claimed, no equation numbers.
-/

@[expose] public section

open Matrix

namespace Lightlike.Lorentz.Poincare

open SU2Spin

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The differential of the spin-`n/2` representation at `suZ` is `diag(i (n − 2k))`. -/
lemma dρZ_spin (n : ℕ) :
    dρ (σ n) suZ = diagonal fun k : Fin (n + 1) => Complex.I * ((n : ℂ) - 2 * (k : ℕ)) := by
  apply exp_smul_injective
  intro t
  rw [← rho_expCurve (continuous_σ n) isSu2_Z t, σ_apply, expCurve_coe]
  have h1 : (t • suZ : Matrix (Fin 2) (Fin 2) ℂ) =
      diagonal ![(t : ℂ) * Complex.I, -((t : ℂ) * Complex.I)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [suZ]
  have h2 : (t • diagonal fun k : Fin (n + 1) => Complex.I * ((n : ℂ) - 2 * (k : ℕ)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      diagonal fun k : Fin (n + 1) => (t : ℂ) * (Complex.I * ((n : ℂ) - 2 * (k : ℕ))) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h1, h2, Matrix.exp_diagonal, Matrix.exp_diagonal, spinMat_diagonal]
  congr 1
  ext k
  have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.2
  rw [Pi.coe_exp, Pi.coe_exp, Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  rw [Nat.cast_sub hk]
  ring

/-- `opH (σ n) = diag(n − 2k)`. -/
lemma opH_spin (n : ℕ) :
    opH (σ n) = diagonal fun k : Fin (n + 1) => (n : ℂ) - 2 * (k : ℕ) := by
  rw [opH, dρZ_spin]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [← mul_assoc]
  · simp [hij]

/-- The highest weight vector `e₀` is killed by the raising operator `E`. -/
lemma opE_spin_highest (n : ℕ) :
    opE (σ n) *ᵥ (Pi.single (0 : Fin (n + 1)) (1 : ℂ)) = 0 := by
  set e0 : Fin (n + 1) → ℂ := Pi.single 0 1 with he0
  set w := opE (σ n) *ᵥ e0 with hw
  have hH0 : opH (σ n) *ᵥ e0 = (n : ℂ) • e0 := by
    rw [opH_spin, he0]
    ext k
    by_cases hk : k = 0
    · subst hk; simp [mulVec_diagonal]
    · simp [mulVec_diagonal, hk]
  have key := congrArg (fun M => M *ᵥ e0) (sl2_rel (continuous_σ n)).1
  simp only [sub_mulVec, ← mulVec_mulVec, hH0, smul_mulVec] at key
  rw [mulVec_smul, ← hw] at key
  have hHw : opH (σ n) *ᵥ w = ((n : ℂ) + 2) • w := by
    rw [sub_eq_iff_eq_add] at key
    rw [key]; module
  ext k
  have := congrFun hHw k
  rw [opH_spin, mulVec_diagonal] at this
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have h2 : w k * (2 * ((k : ℕ) : ℂ) + 2) = 0 := by linear_combination -this
  have h3 : (2 * ((k : ℕ) : ℂ) + 2) ≠ 0 := by
    have : ((2 * (k : ℕ) + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using this
  simpa [h3] using h2

section Casimir

variable {d : ℕ}

/-- The `sl₂` Casimir `H² + 2H + 4FE` (equal to `H² + 2EF + 2FE` when `[E,F] = H`); it equals
`4 s(s+1)` in the spin-`s` representation. -/
def sl2Casimir (H E F : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  H * H + (2 : ℂ) • H + (4 : ℂ) • (F * E)

variable {H E F : Matrix (Fin d) (Fin d) ℂ}

/-- The Casimir commutes with `H`. -/
lemma sl2Casimir_comm_H (h1 : H * E - E * H = (2 : ℂ) • E)
    (h2 : H * F - F * H = (-2 : ℂ) • F) :
    sl2Casimir H E F * H = H * sl2Casimir H E F := by
  have a := congrArg (· * E) h2
  have b := congrArg (F * ·) h1
  simp only [sl2Casimir, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc] at a b
  linear_combination (norm := module) (-4 : ℂ) • a - (4 : ℂ) • b

/-- The Casimir commutes with `E`. -/
lemma sl2Casimir_comm_E (h1 : H * E - E * H = (2 : ℂ) • E)
    (h3 : E * F - F * E = H) :
    sl2Casimir H E F * E = E * sl2Casimir H E F := by
  have e1 := congrArg (H * ·) h1
  have e2 := congrArg (· * H) h1
  have h3E := congrArg (· * E) h3
  simp only [sl2Casimir, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc] at e1 e2 h3E
  linear_combination (norm := module) e1 + e2 - (4 : ℂ) • h3E

/-- The Casimir commutes with `F`. -/
lemma sl2Casimir_comm_F (h2 : H * F - F * H = (-2 : ℂ) • F)
    (h3 : E * F - F * E = H) :
    sl2Casimir H E F * F = F * sl2Casimir H E F := by
  have e1 := congrArg (H * ·) h2
  have e2 := congrArg (· * H) h2
  have h3F := congrArg (F * ·) h3
  simp only [sl2Casimir, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc] at e1 e2 h3F
  linear_combination (norm := module) e1 + e2 + (4 : ℂ) • h3F

end Casimir

/-- **The Casimir of the spin-`n/2` representation is `n(n+2) = 4 s(s+1)` with `s = n/2`.** -/
theorem spin_casimir (n : ℕ) :
    sl2Casimir (opH (σ n)) (opE (σ n)) (opF (σ n)) = ((n : ℂ) * (n + 2)) • 1 := by
  set C := sl2Casimir (opH (σ n)) (opE (σ n)) (opF (σ n)) with hC
  set c : ℂ := (n : ℂ) * (n + 2) with hc
  obtain ⟨hr1, hr2, hr3⟩ := sl2_rel (continuous_σ n)
  have cH := sl2Casimir_comm_H hr1 hr2
  have cE := sl2Casimir_comm_E hr1 hr3
  have cF := sl2Casimir_comm_F hr2 hr3
  let W : Submodule ℂ (Fin (n + 1) → ℂ) := LinearMap.ker (Matrix.toLin' (C - c • 1))
  have hmem : ∀ v, v ∈ W ↔ C *ᵥ v = c • v := fun v => by
    simp [W, sub_eq_zero]
  have stable : ∀ (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), C * X = X * C →
      ∀ v ∈ W, X *ᵥ v ∈ W := by
    intro X hX v hv
    rw [hmem] at hv ⊢
    rw [mulVec_mulVec, hX, ← mulVec_mulVec, hv, mulVec_smul]
  have hinv := invariant_of_ops (continuous_σ n) W (stable _ cE) (stable _ cF)
    (stable _ cH)
  have hne : (Pi.single (0 : Fin (n + 1)) (1 : ℂ)) ∈ W := by
    rw [hmem]
    have hH0 : opH (σ n) *ᵥ (Pi.single (0 : Fin (n + 1)) (1 : ℂ)) =
        (n : ℂ) • Pi.single (0 : Fin (n + 1)) (1 : ℂ) := by
      rw [opH_spin]
      ext k
      by_cases hk : k = 0
      · subst hk; simp [mulVec_diagonal]
      · simp [mulVec_diagonal, hk]
    rw [hC, sl2Casimir]
    simp only [add_mulVec, smul_mulVec, ← mulVec_mulVec, opE_spin_highest, hH0, mulVec_smul,
      mulVec_zero, smul_zero, add_zero]
    rw [hc]
    module
  have htop : W = ⊤ := by
    rcases isInvariant_eq_bot_or_eq_top (n := n) (W := W) hinv with h | h
    · exfalso
      rw [h] at hne
      have := (Submodule.mem_bot ℂ).mp hne
      have h1 := congrFun this 0
      simp at h1
    · exact h
  ext i j
  have hv : ∀ v : Fin (n + 1) → ℂ, C *ᵥ v = c • v := fun v =>
    (hmem v).mp (htop ▸ Submodule.mem_top)
  have h := congrFun (hv (Pi.single j 1)) i
  rw [mulVec_single_one] at h
  rw [Matrix.smul_apply, Matrix.one_apply]
  simpa [Pi.single_apply] using h

end Lightlike.Lorentz.Poincare
