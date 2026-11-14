import Lightlike.Spin4.Intertwiner4

/-!
# The EPRL map on 4-valent intertwiners and the fusion coefficients

On a 4-valent node with links `a = 1, …, 4` carrying SU(2) spins `J_a = n_a + m_a` and EPRL labels
`(n_a, m_a)`, the EPRL map sends an SU(2) intertwiner `T : V_{J₃} ⊗ V_{J₄} → V_{J₁} ⊗ V_{J₂}` to the
Spin(4) intertwiner

`Φ(T) = P (Y₁ ⊗ Y₂) T (Y₃ ⊗ Y₄)ᴴ`,

where `Y_a = eprlMap n_a m_a` and `P` is the orthogonal projection onto the Spin(4) intertwiners
(Engle–Pereira–Rovelli–Livine). In the bases `ι_z` and `ι⁺_x ⊗ ι⁻_y` its matrix is given by the
**fusion coefficients** `f(z; x, y) = ⟨ι⁺_x ⊗ ι⁻_y, (Y₁ ⊗ Y₂) ι_z (Y₃ ⊗ Y₄)ᴴ⟩`.

## Main results

* `eprlIntertwiner_isSpin4Intertwiner`, `eprlIntertwiner_ivec`: `Φ` lands in the Spin(4)
  intertwiners, with `Φ(ι_z) = Σ f(z; x, y) ι⁺_x ⊗ ι⁻_y`.
* `projSpin4_eq_self`, `hsInner_sub_projSpin4`: `P` is the orthogonal projection.
* `hsInner_eprlIntertwiner_le`, `sum_normSq_fusion_le`: `‖Φ(T)‖ ≤ ‖T‖`, so
  `Σ_{x,y} |f(z; x, y)|² ≤ 1`; `eprlIntertwiner_not_isometric`: the inequality can be strict.
* `fusion_eq`: **factorisation** `f(z; x, y) = √(z+1)/√((x+1)(y+1)) · conj(λ₃₄) · λ₁₂` through
  the EPRL recoupling coefficients `λ` of the pairs of links (`eprlRecoupling`, the overlap of
  `((n₁ n₂) x, (m₁ m₂) y) z` with `(Y₁ ⊗ Y₂)((J₁ J₂) z)`, a 9j symbol up to dimension factors);
  `fusion_eq_zero`: the **selection rule** `f = 0` unless `(x y z)` is an admissible triad.
* `eprlRecoupling_stretched_pos`: **sign coherence**: the stretched coefficients `z = x + y` are
  positive.
* `eprlIntertwiner_injective`: **injectivity** for `0 < γ < 1` and `Σ_a 2j⁺_a` even, the
  hypotheses of Kamiński–Kisielowski–Lewandowski 2012, Theorem 2;
  `eprlIntertwiner_eq_zero_of_not_even`, `eprlIntertwiner_injective_iff`: when `Σ_a 2j⁺_a` is odd
  there are no Spin(4) intertwiners, so `Φ` is injective exactly when the parity holds or the
  SU(2) space is zero.
* `cgCoefficient_singlet`, `eprlRecoupling_singlet`, `fusion_zero_equal`, `fusion_two_valent`:
  exact values, e.g. `f(0; 0, 0) = (2j+1)/((2j₊+1)(2j₋+1))` on a node with four equal links.

The fusion coefficients are products of two 9j symbols (`fusion_eq_nineJSym` in
`Lightlike/Spin4/FusionNineJ.lean`). Alesci–Bianchi–Magliaro–Perini write the same 9j symbol with
rows and columns permuted, which changes it by the sign `(-1)^{j₁-j₂+j₃-j₄}`; that comparison of
conventions is checked numerically on 184 coefficients (`scripts/spin4/eprl_check.py`).

## References

* J. Engle, R. Pereira, C. Rovelli, E. Livine, *LQG vertex with finite Immirzi parameter*,
  Nucl. Phys. B 799 (2008) 136, arXiv:0711.0146.
* W. Kamiński, M. Kisielowski, J. Lewandowski, *The EPRL intertwiners and corrected partition
  function*, Class. Quantum Grav. 27 (2010) 165020, arXiv:0912.0540 (the map is not isometric).
* W. Kamiński, M. Kisielowski, J. Lewandowski, *The kernel and the injectivity of the EPRL map*,
  Class. Quantum Grav. 29 (2012) 085001, arXiv:1109.5023, Theorem 2 (injectivity for `|γ| < 1`
  under `j±_a ∈ ½ℕ` and `Σ_a j⁺_a ∈ ℕ`).
* E. Alesci, E. Bianchi, E. Magliaro, C. Perini, *Asymptotics of LQG fusion coefficients*,
  Class. Quantum Grav. 27 (2010) 095016, arXiv:0809.3718, eqs. (7)–(9) (the fusion coefficients
  as products of two 9j symbols, the selection rule).
-/

open Matrix Finset PhyslibAlpha.Sl2 Lightlike.Pentagon
open scoped Kronecker

namespace Lightlike.Spin4

open SU2

variable {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ}

/-! ## A. The EPRL map on a pair of links -/

/-- **The EPRL map on two links**,
`Y₁ ⊗ Y₂ : V_{J₁} ⊗ V_{J₂} → (V_{n₁} ⊗ V_{n₂}) ⊗ (V_{m₁} ⊗ V_{m₂})`, with the target regrouped by
`shuffle` (self-dual factors first). -/
noncomputable def eprlPair (n₁ m₁ n₂ m₂ : ℕ) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx (n₁ + m₁) (n₂ + m₂)) ℂ :=
  (eprlMap n₁ m₁ ⊗ₖ eprlMap n₂ m₂).submatrix (shuffle n₁ m₁ n₂ m₂).symm id

lemma eprlPair_apply (P : Idx n₁ n₂ × Idx m₁ m₂) (c : Idx (n₁ + m₁) (n₂ + m₂)) :
    eprlPair n₁ m₁ n₂ m₂ P c =
      eprlMap n₁ m₁ (P.1.1, P.2.1) c.1 * eprlMap n₂ m₂ (P.1.2, P.2.2) c.2 := rfl

/-- `Y₁ ⊗ Y₂` is an isometry. -/
theorem eprlPair_isometry : (eprlPair n₁ m₁ n₂ m₂)ᴴ * eprlPair n₁ m₁ n₂ m₂ = 1 := by
  rw [eprlPair, conjTranspose_submatrix, submatrix_mul_equiv, conjTranspose_kronecker,
    ← mul_kronecker_mul, eprlMap_isometry, eprlMap_isometry, one_kronecker_one]
  rfl

/-- `Y₁ ⊗ Y₂` is equivariant for the diagonal SU(2). -/
theorem eprlPair_equivariant (g : SU2) :
    (pairMat n₁ n₂ g ⊗ₖ pairMat m₁ m₂ g) * eprlPair n₁ m₁ n₂ m₂ =
      eprlPair n₁ m₁ n₂ m₂ * pairMat (n₁ + m₁) (n₂ + m₂) g := by
  have h := spin4Mat_kronecker n₁ n₂ m₁ m₂ (g, g)
  have h' : pairMat n₁ n₂ g ⊗ₖ pairMat m₁ m₂ g = (spin4Mat n₁ m₁ (g, g) ⊗ₖ
      spin4Mat n₂ m₂ (g, g)).submatrix (shuffle n₁ m₁ n₂ m₂).symm (shuffle n₁ m₁ n₂ m₂).symm := by
    rw [h, submatrix_submatrix]
    simp
  rw [h', eprlPair, submatrix_mul_equiv, ← mul_kronecker_mul]
  simp only [spin4Mat]
  rw [eprlMap_equivariant, eprlMap_equivariant, mul_kronecker_mul]
  ext P c
  simp [mul_apply, submatrix_apply]

/-- The adjoint `(Y₁ ⊗ Y₂)ᴴ` is equivariant for the diagonal SU(2). -/
theorem eprlPair_conjTranspose_equivariant (g : SU2) :
    (eprlPair n₁ m₁ n₂ m₂)ᴴ * (pairMat n₁ n₂ g ⊗ₖ pairMat m₁ m₂ g) =
      pairMat (n₁ + m₁) (n₂ + m₂) g * (eprlPair n₁ m₁ n₂ m₂)ᴴ := by
  have h := congrArg conjTranspose (eprlPair_equivariant (n₁ := n₁) (m₁ := m₁) (n₂ := n₂)
    (m₂ := m₂) (star g))
  simp only [conjTranspose_mul, pairMat, conjTranspose_kronecker, spinMat_conjTranspose,
    specialUnitaryGroup.coe_star, star_eq_conjTranspose, conjTranspose_conjTranspose] at h
  exact h

/-! ## B. The EPRL map on intertwiners -/

variable (n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄)

/-- The EPRL map before projection, `T ↦ (Y₁ ⊗ Y₂) T (Y₃ ⊗ Y₄)ᴴ`. -/
noncomputable def eprlLift (T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ :=
  eprlPair n₁ m₁ n₂ m₂ * T * (eprlPair n₃ m₃ n₄ m₄)ᴴ

/-- **The orthogonal projection onto the Spin(4) intertwiners**,
`P Q = Σ_{x,y} ⟨ι⁺_x ⊗ ι⁻_y, Q⟩ ι⁺_x ⊗ ι⁻_y`. -/
noncomputable def projSpin4 (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ :=
  ∑ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
    hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) Q • ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2

/-- **The EPRL map on 4-valent intertwiners**, `Φ(T) = P (Y₁ ⊗ Y₂) T (Y₃ ⊗ Y₄)ᴴ`. -/
noncomputable def eprlIntertwiner
    (T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ) :
    Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ :=
  projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T)

/-- **The fusion coefficients** `f(z; x, y) = ⟨ι⁺_x ⊗ ι⁻_y, (Y₁ ⊗ Y₂) ι_z (Y₃ ⊗ Y₄)ᴴ⟩`. -/
noncomputable def fusion (z x y : ℕ) : ℂ :=
  hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ x y)
    (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z))

variable {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄}

lemma isSpin4Intertwiner_sum {β : Type*} (s : Finset β) (c : β → ℂ)
    (Q : β → Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ)
    (hQ : ∀ b ∈ s, IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (Q b)) :
    IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (∑ b ∈ s, c b • Q b) := fun g => by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_congr rfl fun b hb => by rw [Matrix.mul_smul, Matrix.smul_mul, hQ b hb g]

/-- The projection lands in the Spin(4) intertwiners. -/
theorem projSpin4_isSpin4Intertwiner
    (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) :
    IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) :=
  isSpin4Intertwiner_sum _ _ _ fun _ hp => ivec4_isSpin4Intertwiner hp

/-- **The EPRL map lands in the Spin(4) intertwiners.** -/
theorem eprlIntertwiner_isSpin4Intertwiner
    (T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ) :
    IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T) :=
  projSpin4_isSpin4Intertwiner _

/-- The projection fixes the Spin(4) intertwiners. -/
theorem projSpin4_eq_self {Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ}
    (hQ : IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) :
    projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q = Q :=
  (eq_sum_ivec4 hQ).symm

/-- The basis coefficients of `P Q` are those of `Q`. -/
lemma hsInner_ivec4_projSpin4 {p : ℕ × ℕ} (hp : p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄)
    (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) :
    hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) (projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) =
      hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) Q := by
  rw [projSpin4, hsInner_sum_right]
  simp only [hsInner_smul_right]
  rw [Finset.sum_eq_single p (fun p' hp' hne => by
    rw [hsInner_ivec4 hp hp', ite_eq_right (Ne.symm hne), mul_zero]) (fun h => absurd hp h),
    hsInner_ivec4 hp hp, ite_eq_left rfl, mul_one]

lemma hsInner_sub_right {ι κ : Type*} [Fintype ι] [Fintype κ] (S T T' : Matrix ι κ ℂ) :
    hsInner S (T - T') = hsInner S T - hsInner S T' := by
  simp only [hsInner, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma hsInner_add_left {ι κ : Type*} [Fintype ι] [Fintype κ] (S S' T : Matrix ι κ ℂ) :
    hsInner (S + S') T = hsInner S T + hsInner S' T := by
  simp only [hsInner, Matrix.add_apply, star_add, add_mul, Finset.sum_add_distrib]

lemma hsInner_sum_left {ι κ β : Type*} [Fintype ι] [Fintype κ] (s : Finset β)
    (f : β → Matrix ι κ ℂ) (T : Matrix ι κ ℂ) :
    hsInner (∑ b ∈ s, f b) T = ∑ b ∈ s, hsInner (f b) T := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsInner]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hsInner_add_left, ih]

lemma star_hsInner {ι κ : Type*} [Fintype ι] [Fintype κ] (S T : Matrix ι κ ℂ) :
    star (hsInner S T) = hsInner T S := by
  simp only [hsInner, star_sum, star_mul', star_star]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **`P` is the orthogonal projection**: `Q - P Q` is orthogonal to every Spin(4) intertwiner. -/
theorem hsInner_sub_projSpin4 {R : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ}
    (hR : IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ R)
    (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) :
    hsInner R (Q - projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) = 0 := by
  rw [eq_sum_ivec4 hR, hsInner_sum_left]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [hsInner_smul_left, hsInner_sub_right, hsInner_ivec4_projSpin4 hp, sub_self, mul_zero]

/-- The image of a basis intertwiner: `Φ(ι_z) = Σ_{x,y} f(z; x, y) ι⁺_x ⊗ ι⁻_y`. -/
theorem eprlIntertwiner_ivec (z : ℕ) :
    eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z) =
      ∑ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
        fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z p.1 p.2 • ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2 :=
  rfl

/-- `(Y₁ ⊗ Y₂) T (Y₃ ⊗ Y₄)ᴴ` has the norm of `T`. -/
theorem hsInner_eprlLift (T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ) :
    hsInner (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T) (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T) =
      hsInner T T := by
  rw [hsInner_eq_trace, hsInner_eq_trace, eprlLift]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  have h1 := eprlPair_isometry (n₁ := n₁) (m₁ := m₁) (n₂ := n₂) (m₂ := m₂)
  have h3 := eprlPair_isometry (n₁ := n₃) (m₁ := m₃) (n₂ := n₄) (m₂ := m₄)
  calc trace (eprlPair n₃ m₃ n₄ m₄ * (Tᴴ * (eprlPair n₁ m₁ n₂ m₂)ᴴ) *
        (eprlPair n₁ m₁ n₂ m₂ * T * (eprlPair n₃ m₃ n₄ m₄)ᴴ))
      = trace (eprlPair n₃ m₃ n₄ m₄ * (Tᴴ * ((eprlPair n₁ m₁ n₂ m₂)ᴴ *
          eprlPair n₁ m₁ n₂ m₂) * T) * (eprlPair n₃ m₃ n₄ m₄)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = trace ((eprlPair n₃ m₃ n₄ m₄)ᴴ * eprlPair n₃ m₃ n₄ m₄ * (Tᴴ * T)) := by
        rw [h1, Matrix.mul_one, trace_mul_comm, ← Matrix.mul_assoc]
    _ = trace (Tᴴ * T) := by rw [h3, Matrix.one_mul]

/-- `⟨PQ, PQ⟩ + ⟨Q - PQ, Q - PQ⟩ = ⟨Q, Q⟩`. -/
lemma hsInner_projSpin4_add (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) :
    hsInner (projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) (projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) +
      hsInner (Q - projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) (Q - projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) =
        hsInner Q Q := by
  set P := projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q
  have h1 : hsInner P (Q - P) = 0 := hsInner_sub_projSpin4 (projSpin4_isSpin4Intertwiner Q) Q
  have h2 : hsInner (Q - P) P = 0 := by rw [← star_hsInner, h1, star_zero]
  have hQ : Q = P + (Q - P) := by abel
  conv_rhs => rw [hQ]
  rw [hsInner_add_left, hsInner_add_right, hsInner_add_right, h1, h2]
  ring

/-- **The EPRL map does not increase norms**: `‖Φ(T)‖² ≤ ‖T‖²`. -/
theorem hsInner_eprlIntertwiner_le
    (T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ) :
    (hsInner (eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T)
      (eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T)).re ≤ (hsInner T T).re := by
  have h := hsInner_projSpin4_add (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T)
  rw [hsInner_eprlLift] at h
  rw [eprlIntertwiner, ← h, Complex.add_re]
  have h0 := hsInner_self (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T -
    projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T))
  rw [h0, Complex.ofReal_re]
  have : 0 ≤ ∑ i, ∑ j, Complex.normSq ((eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T -
      projSpin4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T)) i j) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  linarith

/-- The squared norm of `Φ(ι_z)` is `Σ_{x,y} |f(z; x, y)|²`. -/
theorem hsInner_eprlIntertwiner_ivec (z : ℕ) :
    hsInner
      (eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z))
      (eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z)) =
      ((∑ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
        Complex.normSq (fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z p.1 p.2) : ℝ) : ℂ) := by
  rw [eprlIntertwiner_ivec, hsInner_sum_left]
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hsInner_smul_left, hsInner_sum_right]
  simp only [hsInner_smul_right]
  rw [Finset.sum_eq_single p (fun p' hp' hne => by
    rw [hsInner_ivec4 hp hp', ite_eq_right (Ne.symm hne), mul_zero]) (fun h => absurd hp h),
    hsInner_ivec4 hp hp, ite_eq_left rfl, mul_one, Complex.star_def, mul_comm,
    Complex.mul_conj]

/-- **Bessel bound for the fusion coefficients**: `Σ_{x,y} |f(z; x, y)|² ≤ 1` for every `z` in the
channel. -/
theorem sum_normSq_fusion_le {z : ℕ}
    (hz : z ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄)) :
    ∑ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
      Complex.normSq (fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z p.1 p.2) ≤ 1 := by
  have h := hsInner_eprlIntertwiner_le (n₁ := n₁) (n₂ := n₂) (n₃ := n₃) (n₄ := n₄) (m₁ := m₁)
    (m₂ := m₂) (m₃ := m₃) (m₄ := m₄) (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z)
  rw [hsInner_eprlIntertwiner_ivec, hsInner_ivec hz hz, ite_eq_left rfl, Complex.ofReal_re,
    Complex.one_re] at h
  exact h

/-! ## C. Factorisation and the selection rule -/

/-- **The EPRL recoupling matrix** of a pair of links,
`W = (C^{n₁n₂}_x ⊗ C^{m₁m₂}_y)ᴴ (Y₁ ⊗ Y₂) C^{J₁J₂}_z : V_{z/2} → V_{x/2} ⊗ V_{y/2}`. -/
noncomputable def recoupMat (n₁ m₁ n₂ m₂ x y z : ℕ) : Matrix (Idx x y) (Fin (z + 1)) ℂ :=
  (cgz n₁ n₂ x ⊗ₖ cgz m₁ m₂ y)ᴴ * eprlPair n₁ m₁ n₂ m₂ * cgz (n₁ + m₁) (n₂ + m₂) z

/-- **The EPRL recoupling coefficient** `λ = tr((C^{xy}_z)ᴴ W)/(z+1)`, so that `W = λ C^{xy}_z`
(`recoupMat_eq`): the overlap of the coupled state `((n₁ n₂)x (m₁ m₂)y) z` with the image under
`Y₁ ⊗ Y₂` of `(J₁ J₂) z`. -/
noncomputable def eprlRecoupling (n₁ m₁ n₂ m₂ x y z : ℕ) : ℂ :=
  trace ((cgz x y z)ᴴ * recoupMat n₁ m₁ n₂ m₂ x y z) / (z + 1 : ℂ)

variable {x y z : ℕ}

/-- The recoupling matrix is SU(2)-equivariant. -/
theorem recoupMat_equivariant (hx : Tri n₁ n₂ x) (hy : Tri m₁ m₂ y)
    (hz : Tri (n₁ + m₁) (n₂ + m₂) z) (g : SU2) :
    (spinMat x g ⊗ₖ spinMat y g) * recoupMat n₁ m₁ n₂ m₂ x y z =
      recoupMat n₁ m₁ n₂ m₂ x y z * spinMat z g := by
  have hA : (spinMat x g ⊗ₖ spinMat y g) * (cgz n₁ n₂ x ⊗ₖ cgz m₁ m₂ y)ᴴ =
      (cgz n₁ n₂ x ⊗ₖ cgz m₁ m₂ y)ᴴ * (pairMat n₁ n₂ g ⊗ₖ pairMat m₁ m₂ g) := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
      ← cgz_conjTranspose_equivariant hx, ← cgz_conjTranspose_equivariant hy]
  rw [recoupMat, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA,
    Matrix.mul_assoc _ _ (eprlPair _ _ _ _),
    eprlPair_equivariant, ← Matrix.mul_assoc, Matrix.mul_assoc _ (pairMat _ _ g),
    cgz_equivariant hz, ← Matrix.mul_assoc]

/-- `W = λ C^{xy}_z` for an admissible triad `(x y z)`. -/
theorem recoupMat_eq (hx : Tri n₁ n₂ x) (hy : Tri m₁ m₂ y) (hz : Tri (n₁ + m₁) (n₂ + m₂) z)
    (hxyz : Tri x y z) :
    recoupMat n₁ m₁ n₂ m₂ x y z = eprlRecoupling n₁ m₁ n₂ m₂ x y z • cgz x y z :=
  equivariant_eq_smul_cgz hxyz (recoupMat_equivariant hx hy hz)

/-- `W = 0` when `(x y z)` is not an admissible triad. -/
theorem recoupMat_eq_zero (hx : Tri n₁ n₂ x) (hy : Tri m₁ m₂ y) (hz : Tri (n₁ + m₁) (n₂ + m₂) z)
    (hxyz : ¬ Tri x y z) : recoupMat n₁ m₁ n₂ m₂ x y z = 0 :=
  equivariant_eq_zero hxyz (recoupMat_equivariant hx hy hz)

/-- The normalisation `√(z+1) / √((x+1)(y+1))` of the fusion coefficients. -/
noncomputable def fusionScale (x y z : ℕ) : ℝ :=
  Real.sqrt ((z : ℝ) + 1) / (Real.sqrt ((x : ℝ) + 1) * Real.sqrt ((y : ℝ) + 1))

lemma ivec4_eq (x y : ℕ) : ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ x y =
    (((Real.sqrt ((x : ℝ) + 1))⁻¹ : ℂ) * ((Real.sqrt ((y : ℝ) + 1))⁻¹ : ℂ)) •
      ((cgz n₁ n₂ x ⊗ₖ cgz m₁ m₂ y) * (cgz n₃ n₄ x ⊗ₖ cgz m₃ m₄ y)ᴴ) := by
  rw [ivec4, ivec, ivec, smul_kronecker, kronecker_smul, smul_smul, conjTranspose_kronecker,
    mul_kronecker_mul]

lemma fusion_scale_eq (x y z : ℕ) :
    star (((Real.sqrt ((x : ℝ) + 1))⁻¹ : ℂ) * ((Real.sqrt ((y : ℝ) + 1))⁻¹ : ℂ)) *
      (((Real.sqrt ((z : ℝ) + 1))⁻¹ : ℂ) * ((z : ℂ) + 1)) = (fusionScale x y z : ℂ) := by
  have hz : (0 : ℝ) < (z : ℝ) + 1 := by positivity
  have hsz : Real.sqrt ((z : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hz).ne'
  have hsx : Real.sqrt ((x : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsy : Real.sqrt ((y : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hss : Real.sqrt ((z : ℝ) + 1) * Real.sqrt ((z : ℝ) + 1) = (z : ℝ) + 1 :=
    Real.mul_self_sqrt hz.le
  have hc : (Real.sqrt ((z : ℝ) + 1) : ℂ) * (Real.sqrt ((z : ℝ) + 1) : ℂ) = (z : ℂ) + 1 := by
    rw [← Complex.ofReal_mul, hss]; push_cast; rfl
  have hsz' : (Real.sqrt ((z : ℝ) + 1) : ℂ) ≠ 0 := by exact_mod_cast hsz
  have hsx' : (Real.sqrt ((x : ℝ) + 1) : ℂ) ≠ 0 := by exact_mod_cast hsx
  have hsy' : (Real.sqrt ((y : ℝ) + 1) : ℂ) ≠ 0 := by exact_mod_cast hsy
  rw [fusionScale, Complex.star_def, map_mul, map_inv₀, map_inv₀, Complex.conj_ofReal,
    Complex.conj_ofReal, ← hc]
  push_cast
  field_simp

/-- **Factorisation of the fusion coefficients**: for `x, y, z` in their channels,
`f(z; x, y) = √(z+1)/√((x+1)(y+1)) · conj(λ₃₄) · λ₁₂` if `(x y z)` is admissible, and `0`
otherwise, where `λ₁₂`, `λ₃₄` are the EPRL recoupling coefficients of the two pairs of links. -/
theorem fusion_eq (hx : x ∈ channel n₁ n₂ n₃ n₄) (hy : y ∈ channel m₁ m₂ m₃ m₄)
    (hz : z ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄)) :
    fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z x y = if Tri x y z then
      (fusionScale x y z : ℂ) * star (eprlRecoupling n₃ m₃ n₄ m₄ x y z) *
        eprlRecoupling n₁ m₁ n₂ m₂ x y z else 0 := by
  rw [mem_channel] at hx hy hz
  have htr : fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z x y =
      star (((Real.sqrt ((x : ℝ) + 1))⁻¹ : ℂ) * ((Real.sqrt ((y : ℝ) + 1))⁻¹ : ℂ)) *
        (((Real.sqrt ((z : ℝ) + 1))⁻¹ : ℂ) *
          trace ((recoupMat n₃ m₃ n₄ m₄ x y z)ᴴ * recoupMat n₁ m₁ n₂ m₂ x y z)) := by
    rw [fusion, ivec4_eq, eprlLift, ivec, Matrix.mul_smul, Matrix.smul_mul, hsInner_smul_left,
      hsInner_smul_right, hsInner_mul_conjTranspose]
    congr 2
    simp only [recoupMat, conjTranspose_mul, conjTranspose_conjTranspose]
    conv_rhs => rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [htr]
  by_cases hxyz : Tri x y z
  · rw [ite_eq_left hxyz, recoupMat_eq hx.2 hy.2 hz.2 hxyz, recoupMat_eq hx.1 hy.1 hz.1 hxyz,
      conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, cgz_isometry hxyz, smul_smul,
      trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, ← fusion_scale_eq]
    push_cast
    ring
  · rw [ite_eq_right hxyz, recoupMat_eq_zero hx.1 hy.1 hz.1 hxyz, Matrix.mul_zero, trace_zero,
      mul_zero, mul_zero]

/-- **The selection rule**: `f(z; x, y) = 0` unless `(x y z)` is an admissible triad; in
particular unless `z ≤ x + y`. -/
theorem fusion_eq_zero (hx : x ∈ channel n₁ n₂ n₃ n₄) (hy : y ∈ channel m₁ m₂ m₃ m₄)
    (hz : z ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄)) (hxyz : ¬ Tri x y z) :
    fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z x y = 0 := by
  rw [fusion_eq hx hy hz, ite_eq_right hxyz]

/-! ## D. Sign coherence of the highest states -/

/-- The highest coupled state has alternating signs:
`(-1)^a ⟨n/2, n/2 - a; m/2, m/2 - b | J J⟩ ≥ 0`. -/
lemma neg_one_pow_mul_cgCoefficient_top_nonneg {n m k a b : ℕ} (hk : k ≤ n) (hk' : k ≤ m)
    (ha : a ≤ n) (hb : b ≤ m) : 0 ≤ (-1 : ℝ) ^ a * cgCoefficient n m k 0 a b := by
  by_cases h : a + b = k
  · obtain ⟨c, hc, he⟩ := cgCoefficient_top_sign hk hk' (show a ≤ k by omega)
    rw [show b = k - a by omega, he, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨a, rfl⟩, one_mul]
    exact hc.le
  · rcases Nat.eq_zero_or_pos (n + m) with h0 | hnm
    · exact absurd (by omega : a + b = k) h
    · rw [cgCoefficient_eq_zero_of_ne hnm hk hk' (by omega), mul_zero]

/-- The entries of the EPRL map, as real numbers. -/
noncomputable def eprlEntry (n m a b c : ℕ) : ℝ :=
  if a + b = c then Real.sqrt (((n.choose a * m.choose b : ℕ) : ℝ) / ((n + m).choose c : ℕ)) else 0

lemma eprlMap_eq_eprlEntry {n m : ℕ} (p : Idx n m) (c : Fin (n + m + 1)) :
    eprlMap n m p c = (eprlEntry n m p.1 p.2 c : ℂ) := by
  rw [eprlMap_apply, eprlEntry]
  split_ifs <;> simp

lemma eprlEntry_nonneg (n m a b c : ℕ) : 0 ≤ eprlEntry n m a b c := by
  unfold eprlEntry
  split_ifs
  · exact Real.sqrt_nonneg _
  · exact le_rfl

/-- **Sign coherence**: the stretched EPRL recoupling coefficient (`z = x + y`) is a positive real
number. All terms of the contraction of the highest states are nonnegative, since the
Condon–Shortley signs `(-1)^{a₁}`, `(-1)^{b₁}`, `(-1)^{a₁+b₁}` of the three highest states cancel
and the entries of `Y` are nonnegative. -/
theorem eprlRecoupling_stretched_pos (hx : Tri n₁ n₂ x) (hy : Tri m₁ m₂ y)
    (hz : Tri (n₁ + m₁) (n₂ + m₂) (x + y)) :
    ∃ r : ℝ, 0 < r ∧ eprlRecoupling n₁ m₁ n₂ m₂ x y (x + y) = r := by
  have hxyz : Tri x y (x + y) := by unfold Tri; omega
  have hW := congrFun (congrFun (recoupMat_eq hx hy hz hxyz) (0, 0)) 0
  have hG : cgz x y (x + y) (0, 0) 0 = 1 := by
    simp only [cgz, of_apply, Nat.sub_self, Nat.zero_div, Fin.val_zero]
    rw [cgCoefficient_stretched, Complex.ofReal_one]
  rw [Matrix.smul_apply, hG, smul_eq_mul, mul_one] at hW
  obtain ⟨kp, hkp1, hkp2, hxk⟩ := (tri_iff_exists _ _ _).mp hx
  obtain ⟨km, hkm1, hkm2, hyk⟩ := (tri_iff_exists _ _ _).mp hy
  have ekp : (n₁ + n₂ - x) / 2 = kp := by omega
  have ekm : (m₁ + m₂ - y) / 2 = km := by omega
  have ek : (n₁ + m₁ + (n₂ + m₂) - (x + y)) / 2 = kp + km := by unfold Tri at hz; omega
  -- the entry `W((0,0),0)` as a real sum
  set t : (Idx n₁ n₂ × Idx m₁ m₂) → Idx (n₁ + m₁) (n₂ + m₂) → ℝ := fun P c =>
    cgCoefficient n₁ n₂ kp 0 P.1.1 P.1.2 * cgCoefficient m₁ m₂ km 0 P.2.1 P.2.2 *
      eprlEntry n₁ m₁ P.1.1 P.2.1 c.1 * eprlEntry n₂ m₂ P.1.2 P.2.2 c.2 *
      cgCoefficient (n₁ + m₁) (n₂ + m₂) (kp + km) 0 c.1 c.2 with ht
  have hsum : recoupMat n₁ m₁ n₂ m₂ x y (x + y) (0, 0) 0 = ((∑ c, ∑ P, t P c : ℝ) : ℂ) := by
    rw [recoupMat, mul_apply]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [conjTranspose_apply, kroneckerMap_apply, cgz, of_apply, eprlPair_apply,
      eprlMap_eq_eprlEntry, ekp, ekm, ek, Fin.val_zero, ht, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    push_cast
    ring
  -- every term is nonnegative
  have hnn : ∀ P c, 0 ≤ t P c := by
    intro P c
    by_cases h1 : (P.1.1 : ℕ) + P.2.1 = c.1
    · by_cases h2 : (P.1.2 : ℕ) + P.2.2 = c.2
      · have hP1 := neg_one_pow_mul_cgCoefficient_top_nonneg (a := P.1.1) (b := P.1.2) hkp1 hkp2
          (Nat.lt_succ_iff.mp P.1.1.2) (Nat.lt_succ_iff.mp P.1.2.2)
        have hP2 := neg_one_pow_mul_cgCoefficient_top_nonneg (a := P.2.1) (b := P.2.2) hkm1 hkm2
          (Nat.lt_succ_iff.mp P.2.1.2) (Nat.lt_succ_iff.mp P.2.2.2)
        have hP3 := neg_one_pow_mul_cgCoefficient_top_nonneg (a := c.1) (b := c.2)
          (k := kp + km) (n := n₁ + m₁) (m := n₂ + m₂) (by omega) (by omega)
          (Nat.lt_succ_iff.mp c.1.2) (Nat.lt_succ_iff.mp c.2.2)
        have hsign : (-1 : ℝ) ^ (P.1.1 : ℕ) * (-1) ^ (P.2.1 : ℕ) * (-1) ^ (c.1 : ℕ) = 1 := by
          rw [← h1, ← pow_add, ← pow_add, Even.neg_one_pow ⟨(P.1.1 : ℕ) + P.2.1, by ring⟩]
        have heq : t P c = ((-1 : ℝ) ^ (P.1.1 : ℕ) * cgCoefficient n₁ n₂ kp 0 P.1.1 P.1.2) *
            ((-1 : ℝ) ^ (P.2.1 : ℕ) * cgCoefficient m₁ m₂ km 0 P.2.1 P.2.2) *
            eprlEntry n₁ m₁ P.1.1 P.2.1 c.1 * eprlEntry n₂ m₂ P.1.2 P.2.2 c.2 *
            ((-1 : ℝ) ^ (c.1 : ℕ) * cgCoefficient (n₁ + m₁) (n₂ + m₂) (kp + km) 0 c.1 c.2) := by
          rw [ht]
          linear_combination (-cgCoefficient n₁ n₂ kp 0 P.1.1 P.1.2 *
            cgCoefficient m₁ m₂ km 0 P.2.1 P.2.2 * eprlEntry n₁ m₁ P.1.1 P.2.1 c.1 *
            eprlEntry n₂ m₂ P.1.2 P.2.2 c.2 *
            cgCoefficient (n₁ + m₁) (n₂ + m₂) (kp + km) 0 c.1 c.2) * hsign
        rw [heq]
        have := eprlEntry_nonneg n₁ m₁ P.1.1 P.2.1 c.1
        have := eprlEntry_nonneg n₂ m₂ P.1.2 P.2.2 c.2
        positivity
      · have : eprlEntry n₂ m₂ P.1.2 P.2.2 c.2 = 0 := by rw [eprlEntry, ite_eq_right h2]
        rw [ht]; simp [this]
    · have : eprlEntry n₁ m₁ P.1.1 P.2.1 c.1 = 0 := by rw [eprlEntry, ite_eq_right h1]
      rw [ht]; simp [this]
  -- one term is positive
  let P₀ : Idx n₁ n₂ × Idx m₁ m₂ :=
    ((⟨0, by omega⟩, ⟨kp, by omega⟩), (⟨0, by omega⟩, ⟨km, by omega⟩))
  let c₀ : Idx (n₁ + m₁) (n₂ + m₂) := (⟨0, by omega⟩, ⟨kp + km, by omega⟩)
  have hpos : 0 < t P₀ c₀ := by
    obtain ⟨c1, hc1, he1⟩ := cgCoefficient_top_sign hkp1 hkp2 (Nat.zero_le kp)
    obtain ⟨c2, hc2, he2⟩ := cgCoefficient_top_sign hkm1 hkm2 (Nat.zero_le km)
    obtain ⟨c3, hc3, he3⟩ := cgCoefficient_top_sign (n := n₁ + m₁) (m := n₂ + m₂)
      (k := kp + km) (by omega) (by omega) (Nat.zero_le (kp + km))
    simp only [Nat.sub_zero, pow_zero, one_mul] at he1 he2 he3
    have hy1 : eprlEntry n₁ m₁ 0 0 0 = 1 := by simp [eprlEntry]
    have hy2 : 0 < eprlEntry n₂ m₂ kp km (kp + km) := by
      rw [eprlEntry, ite_eq_left rfl]
      apply Real.sqrt_pos.mpr
      have h1 := Nat.choose_pos (show kp ≤ n₂ by omega)
      have h2 := Nat.choose_pos (show km ≤ m₂ by omega)
      have h3 := Nat.choose_pos (show kp + km ≤ n₂ + m₂ by omega)
      positivity
    simp only [ht, P₀, c₀, he1, he2, he3, hy1, mul_one]
    positivity
  refine ⟨∑ c, ∑ P, t P c, ?_, by rw [← hW, hsum]⟩
  calc (0 : ℝ) < t P₀ c₀ := hpos
    _ ≤ ∑ P, t P c₀ := Finset.single_le_sum (fun P _ => hnn P c₀) (Finset.mem_univ P₀)
    _ ≤ ∑ c, ∑ P, t P c := Finset.single_le_sum (f := fun c => ∑ P, t P c)
        (fun c _ => Finset.sum_nonneg fun P _ => hnn P c) (Finset.mem_univ c₀)

/-! ## E. Injectivity under the parity condition -/

/-- **Stretched pairs**: for EPRL labels `n_a = (1+γ)J_a/2`, `m_a = (1-γ)J_a/2` with a common `γ`
and `Σ_a n_a` even, every spin `z` of the SU(2) channel is `z = x + y` with `x` in the channel of
the self-dual labels and `y` in that of the anti-self-dual labels. (Choose `x = n₁ + n₂ - 2⌊rk⌋`,
`r = (1+γ)/2`, for `z = J₁ + J₂ - 2k`.) -/
theorem exists_stretched {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (h₁ : (n₁ : ℝ) - m₁ = γ * (n₁ + m₁)) (h₂ : (n₂ : ℝ) - m₂ = γ * (n₂ + m₂))
    (h₃ : (n₃ : ℝ) - m₃ = γ * (n₃ + m₃)) (h₄ : (n₄ : ℝ) - m₄ = γ * (n₄ + m₄))
    (hpar : Even (n₁ + n₂ + n₃ + n₄)) {z : ℕ}
    (hz : z ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄)) :
    ∃ x y, x + y = z ∧ x ∈ channel n₁ n₂ n₃ n₄ ∧ y ∈ channel m₁ m₂ m₃ m₄ := by
  rw [mem_channel, tri_iff_exists, tri_iff_exists] at hz
  obtain ⟨⟨k, hk1, hk2, hzk⟩, ⟨k', hk3, hk4, hzk'⟩⟩ := hz
  obtain ⟨t, ht⟩ := hpar
  set r : ℝ := (1 + γ) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have e₁ : (n₁ : ℝ) = r * (n₁ + m₁) := by rw [hr]; linarith
  have e₂ : (n₂ : ℝ) = r * (n₂ + m₂) := by rw [hr]; linarith
  have e₃ : (n₃ : ℝ) = r * (n₃ + m₃) := by rw [hr]; linarith
  have e₄ : (n₄ : ℝ) = r * (n₄ + m₄) := by rw [hr]; linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk' : (0 : ℝ) ≤ k' := Nat.cast_nonneg k'
  set kp := ⌊r * k⌋₊ with hkp
  have hf1 : (kp : ℝ) ≤ r * k := Nat.floor_le (by positivity)
  have hf2 : r * k < kp + 1 := Nat.lt_floor_add_one _
  have c1 : (k : ℝ) ≤ n₁ + m₁ := by exact_mod_cast hk1
  have c2 : (k : ℝ) ≤ n₂ + m₂ := by exact_mod_cast hk2
  have c3 : (k' : ℝ) ≤ n₃ + m₃ := by exact_mod_cast hk3
  have c4 : (k' : ℝ) ≤ n₄ + m₄ := by exact_mod_cast hk4
  have p1 := mul_le_mul_of_nonneg_left c1 hr0.le
  have p2 := mul_le_mul_of_nonneg_left c2 hr0.le
  have p3 := mul_le_mul_of_nonneg_left c3 hr0.le
  have p4 := mul_le_mul_of_nonneg_left c4 hr0.le
  have p5 : r * k ≤ k := mul_le_of_le_one_left hk hr1.le
  have p6 : r * k' ≤ k' := mul_le_of_le_one_left hk' hr1.le
  have p7 : 0 ≤ r * k' := by positivity
  have hJ : ((n₃ + m₃ : ℕ) : ℝ) + (n₄ + m₄ : ℕ) - ((n₁ + m₁ : ℕ) + (n₂ + m₂ : ℕ)) =
      2 * k' - 2 * k := by
    have a : z + 2 * k = n₁ + m₁ + (n₂ + m₂) := by omega
    have b : z + 2 * k' = n₃ + m₃ + (n₄ + m₄) := by omega
    have a' : (z : ℝ) + 2 * k = n₁ + m₁ + (n₂ + m₂) := by exact_mod_cast a
    have b' : (z : ℝ) + 2 * k' = n₃ + m₃ + (n₄ + m₄) := by exact_mod_cast b
    push_cast
    linarith
  have hJr : r * ((n₃ + m₃ : ℕ) + (n₄ + m₄ : ℕ) - ((n₁ + m₁ : ℕ) + (n₂ + m₂ : ℕ)) : ℝ) =
      r * (2 * k' - 2 * k) := by rw [hJ]
  push_cast at hJr
  have ht' : (n₁ : ℝ) + n₂ + n₃ + n₄ = t + t := by exact_mod_cast ht
  -- the integer `K = kp + (n₃ + n₄ - n₁ - n₂)/2`
  set K : ℤ := (kp : ℤ) + ((n₃ : ℤ) + n₄ - t) with hK
  have hKr : (K : ℝ) = kp + r * k' - r * k := by
    rw [hK]; push_cast; linarith
  -- integer inequalities from the real ones
  have i1 : kp ≤ k := by exact_mod_cast hf1.trans p5
  have i2 : kp ≤ n₁ := by exact_mod_cast (show (kp : ℝ) ≤ n₁ by linarith)
  have i3 : kp ≤ n₂ := by exact_mod_cast (show (kp : ℝ) ≤ n₂ by linarith)
  have i4 : k < kp + m₁ + 1 := by
    have : (1 - r) * k ≤ (1 - r) * (n₁ + m₁) := mul_le_mul_of_nonneg_left c1 (by linarith)
    exact_mod_cast (show (k : ℝ) < kp + m₁ + 1 by linarith)
  have i5 : k < kp + m₂ + 1 := by
    have : (1 - r) * k ≤ (1 - r) * (n₂ + m₂) := mul_le_mul_of_nonneg_left c2 (by linarith)
    exact_mod_cast (show (k : ℝ) < kp + m₂ + 1 by linarith)
  have i6 : -1 < K := by exact_mod_cast (show (-1 : ℝ) < K by linarith)
  have i7 : K ≤ n₃ := by exact_mod_cast (show (K : ℝ) ≤ n₃ by linarith)
  have i8 : K ≤ n₄ := by exact_mod_cast (show (K : ℝ) ≤ n₄ by linarith)
  have i9 : K ≤ k' := by exact_mod_cast (show (K : ℝ) ≤ k' by linarith)
  have i10 : (k' : ℤ) < K + m₃ + 1 := by
    have : (1 - r) * k' ≤ (1 - r) * (n₃ + m₃) := mul_le_mul_of_nonneg_left c3 (by linarith)
    exact_mod_cast (show (k' : ℝ) < K + m₃ + 1 by linarith)
  have i11 : (k' : ℤ) < K + m₄ + 1 := by
    have : (1 - r) * k' ≤ (1 - r) * (n₄ + m₄) := mul_le_mul_of_nonneg_left c4 (by linarith)
    exact_mod_cast (show (k' : ℝ) < K + m₄ + 1 by linarith)
  refine ⟨n₁ + n₂ - 2 * kp, z - (n₁ + n₂ - 2 * kp), by omega, ?_, ?_⟩
  · rw [mem_channel]
    unfold Tri
    omega
  · rw [mem_channel]
    unfold Tri
    omega

lemma eprlLift_sum {β : Type*} (s : Finset β) (c : β → ℂ)
    (v : β → Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ) :
    eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (∑ b ∈ s, c b • v b) =
      ∑ b ∈ s, c b • eprlLift n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (v b) := by
  simp only [eprlLift, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The stretched fusion coefficients are nonzero (they are positive). -/
theorem fusion_stretched_ne_zero (hx : x ∈ channel n₁ n₂ n₃ n₄) (hy : y ∈ channel m₁ m₂ m₃ m₄)
    (hz : x + y ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄)) :
    fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (x + y) x y ≠ 0 := by
  have hxyz : Tri x y (x + y) := by unfold Tri; omega
  rw [fusion_eq hx hy hz, ite_eq_left hxyz]
  rw [mem_channel] at hx hy hz
  obtain ⟨r₁, hr₁, e₁⟩ := eprlRecoupling_stretched_pos hx.1 hy.1 hz.1
  obtain ⟨r₃, hr₃, e₃⟩ := eprlRecoupling_stretched_pos hx.2 hy.2 hz.2
  have hs : 0 < fusionScale x y (x + y) := by unfold fusionScale; positivity
  rw [e₁, e₃, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  exact_mod_cast (by positivity : (0 : ℝ) < fusionScale x y (x + y) * r₃ * r₁).ne'

/-- **Injectivity of the EPRL map on 4-valent intertwiners** (Kamiński–Kisielowski–Lewandowski
2012, Theorem 2): for `0 < γ < 1`, EPRL labels on the four links and `Σ_a n_a = Σ_a 2j⁺_a` even,
`Φ(T) = 0` forces `T = 0`. The fusion matrix is triangular in the stretched pairs `x + y = z`
(`exists_stretched`, selection rule `fusion_eq_zero`), with nonzero diagonal
(`fusion_stretched_ne_zero`). -/
theorem eprlIntertwiner_injective {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (h₁ : IsEPRLLabel γ (n₁ + m₁) n₁ m₁) (h₂ : IsEPRLLabel γ (n₂ + m₂) n₂ m₂)
    (h₃ : IsEPRLLabel γ (n₃ + m₃) n₃ m₃) (h₄ : IsEPRLLabel γ (n₄ + m₄) n₄ m₄)
    (hpar : Even (n₁ + n₂ + n₃ + n₄))
    {T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ}
    (hT : IsIntertwiner (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) T)
    (h0 : eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T = 0) : T = 0 := by
  have d₁ := ((isEPRLLabel_iff hγ hγ1).mp h₁).2
  have d₂ := ((isEPRLLabel_iff hγ hγ1).mp h₂).2
  have d₃ := ((isEPRLLabel_iff hγ hγ1).mp h₃).2
  have d₄ := ((isEPRLLabel_iff hγ hγ1).mp h₄).2
  push_cast at d₁ d₂ d₃ d₄
  have hexp := eq_sum_ivec hT
  have hrel : ∀ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
      ∑ z ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄),
        hsInner (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z) T *
          fusion n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ z p.1 p.2 = 0 := by
    intro p hp
    have h := congrArg (hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2)) h0
    rw [eprlIntertwiner, hsInner_ivec4_projSpin4 hp, hsInner_zero_right] at h
    conv_lhs at h => rw [hexp, eprlLift_sum, hsInner_sum_right]
    simp only [hsInner_smul_right] at h
    exact h
  have hc : ∀ z, z ∈ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) →
      hsInner (ivec (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) z) T = 0 := by
    intro z
    induction z using Nat.strong_induction_on with
    | _ z ih =>
      intro hz
      obtain ⟨x, y, hxy, hx, hy⟩ := exists_stretched hγ hγ1 d₁ d₂ d₃ d₄ hpar hz
      have hr := hrel (x, y) (mem_product.mpr ⟨hx, hy⟩)
      rw [Finset.sum_eq_single z (fun z' hz' hne => ?_) (fun h => absurd hz h)] at hr
      · have hf := fusion_stretched_ne_zero hx hy (hxy ▸ hz)
        rw [hxy] at hf
        exact (mul_eq_zero.mp hr).resolve_right hf
      · rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · rw [ih z' hlt hz', zero_mul]
        · rw [fusion_eq_zero hx hy hz' (fun h => by unfold Tri at h; omega), mul_zero]
  rw [hexp]
  exact Finset.sum_eq_zero fun z hz => by rw [hc z hz, zero_smul]

/-- Without the parity condition the self-dual channel is empty. -/
lemma channel_eq_empty_of_not_even (hodd : ¬ Even (n₁ + n₂ + n₃ + n₄)) :
    channel n₁ n₂ n₃ n₄ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => hodd ?_
  rw [mem_channel] at hx
  unfold Tri at hx
  exact Nat.even_iff.mpr (by omega)

/-- **The parity condition is needed**: if `Σ_a n_a` is odd, there are no Spin(4) intertwiners and
the EPRL map vanishes. -/
theorem eprlIntertwiner_eq_zero_of_not_even (hodd : ¬ Even (n₁ + n₂ + n₃ + n₄))
    (T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ) :
    eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T = 0 := by
  rw [eprlIntertwiner, projSpin4, channel4, channel_eq_empty_of_not_even hodd, Finset.empty_product,
    Finset.sum_empty]

/-- **When the EPRL map is injective**: for `0 < γ < 1` and EPRL labels, `Φ` is injective on the
SU(2) intertwiners exactly when `Σ_a n_a` is even or there are no SU(2) intertwiners. -/
theorem eprlIntertwiner_injective_iff {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (h₁ : IsEPRLLabel γ (n₁ + m₁) n₁ m₁) (h₂ : IsEPRLLabel γ (n₂ + m₂) n₂ m₂)
    (h₃ : IsEPRLLabel γ (n₃ + m₃) n₃ m₃) (h₄ : IsEPRLLabel γ (n₄ + m₄) n₄ m₄) :
    (∀ T : Matrix (Idx (n₁ + m₁) (n₂ + m₂)) (Idx (n₃ + m₃) (n₄ + m₄)) ℂ,
        IsIntertwiner (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) T →
          eprlIntertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ T = 0 → T = 0) ↔
      (Even (n₁ + n₂ + n₃ + n₄) ∨ channel (n₁ + m₁) (n₂ + m₂) (n₃ + m₃) (n₄ + m₄) = ∅) := by
  constructor
  · intro hinj
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hodd, hne⟩ := hcon
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h1 := hinj _ ((mem_channel.mp hz).elim fun a b => ivec_isIntertwiner a b)
      (eprlIntertwiner_eq_zero_of_not_even hodd _)
    have h2 := hsInner_ivec hz hz
    rw [h1, ite_eq_left rfl] at h2
    simp [hsInner] at h2
  · rintro (hpar | hempty) T hT h0
    · exact eprlIntertwiner_injective hγ hγ1 h₁ h₂ h₃ h₄ hpar hT h0
    · rw [eq_sum_ivec hT, hempty, Finset.sum_empty]

/-! ## F. Exact values -/

/-- **The singlet**: `⟨j, j - a; j, -(j - a) | 0 0⟩ = (-1)^a / √(2j+1)` (`n = 2j`,
Condon–Shortley). -/
theorem cgCoefficient_singlet {n a : ℕ} (ha : a ≤ n) :
    cgCoefficient n n n 0 a (n - a) = (-1) ^ a / Real.sqrt ((n : ℝ) + 1) := by
  rw [cgCoefficient_top le_rfl le_rfl ha, hwNormSq_closed le_rfl le_rfl, cgCoeff, hwNormNum, normSq,
    normSq]
  have e1 : n - n + a = a := by omega
  have e2 : n + n - 2 * n + 1 = 1 := by omega
  have e3 : n + n - n + 1 = n + 1 := by omega
  rw [e1, e2, e3, Nat.sub_self, Nat.factorial_zero, Nat.factorial_one, Nat.factorial_succ]
  have hA := Nat.choose_mul_factorial_mul_factorial ha
  have hB := Nat.factorial_mul_descFactorial ha
  have hC := Nat.factorial_mul_descFactorial (Nat.sub_le n a)
  rw [show n - (n - a) = a by omega] at hC
  have hF : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hA' : ((n.choose a * a.factorial * (n - a).factorial : ℕ) : ℝ) = n.factorial := by
    exact_mod_cast hA
  have hBC : ((a.factorial * n.descFactorial a : ℕ) : ℝ) *
      (((n - a).factorial * n.descFactorial (n - a) : ℕ) : ℝ) =
        (n.factorial : ℝ) * n.factorial := by
    have : (a.factorial * n.descFactorial a) * ((n - a).factorial * n.descFactorial (n - a)) =
        n.factorial * n.factorial := by
      calc _ = ((n - a).factorial * n.descFactorial a) *
            (a.factorial * n.descFactorial (n - a)) := by
            ring
        _ = _ := by rw [hB, hC]
    exact_mod_cast this
  have hD : ((n.factorial * n.factorial * n.factorial * ((n + 1) * n.factorial * 1 * 1) : ℕ) : ℝ) /
      ((1 : ℕ) : ℝ) = ((n.factorial : ℝ) * n.factorial) ^ 2 * ((n : ℝ) + 1) := by
    push_cast; ring
  rw [hA', mul_assoc _ (Real.sqrt _), ← Real.sqrt_mul (Nat.cast_nonneg _), hBC,
    Real.sqrt_mul_self (by positivity), hD, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- The singlet coefficients, all entries: `⟨a, b | 0 0⟩ = [a + b = n] (-1)^a / √(n+1)`. -/
lemma cgCoefficient_singlet_apply {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    cgCoefficient n n n 0 a b = if a + b = n then (-1) ^ a / Real.sqrt ((n : ℝ) + 1) else 0 := by
  split_ifs with h
  · rw [show b = n - a by omega, cgCoefficient_singlet ha]
  · rcases Nat.eq_zero_or_pos (n + n) with h0 | hpos
    · omega
    · exact cgCoefficient_eq_zero_of_ne hpos le_rfl le_rfl (by omega)

/-- The top entry `W((0,0),0)` of the recoupling matrix as a real sum. -/
lemma recoupMat_apply_zero (x y z : ℕ) :
    recoupMat n₁ m₁ n₂ m₂ x y z (0, 0) 0 =
      ((∑ c : Idx (n₁ + m₁) (n₂ + m₂), ∑ P : Idx n₁ n₂ × Idx m₁ m₂,
      cgCoefficient n₁ n₂ ((n₁ + n₂ - x) / 2) 0 P.1.1 P.1.2 *
        cgCoefficient m₁ m₂ ((m₁ + m₂ - y) / 2) 0 P.2.1 P.2.2 *
        eprlEntry n₁ m₁ P.1.1 P.2.1 c.1 * eprlEntry n₂ m₂ P.1.2 P.2.2 c.2 *
        cgCoefficient (n₁ + m₁) (n₂ + m₂) ((n₁ + m₁ + (n₂ + m₂) - z) / 2) 0 c.1 c.2 : ℝ) : ℂ) := by
  rw [recoupMat, mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_apply, Finset.sum_mul, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [conjTranspose_apply, kroneckerMap_apply, cgz, of_apply, eprlPair_apply,
    eprlMap_eq_eprlEntry, Fin.val_zero, star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- `Σ_{a ≤ n, b ≤ m} C(n,a) C(m,b) / C(n+m, a+b) = n + m + 1`. -/
lemma sum_choose_div_choose (n m : ℕ) :
    ∑ q : Idx n m, ((n.choose q.1 * m.choose q.2 : ℕ) : ℝ) / ((n + m).choose (q.1 + q.2) : ℕ) =
      (n + m + 1 : ℕ) := by
  have h1 : ∀ q : Idx n m,
      ((n.choose q.1 * m.choose q.2 : ℕ) : ℝ) / ((n + m).choose (q.1 + q.2) : ℕ) =
      ∑ c ∈ range (n + m + 1), if (q.1 : ℕ) + q.2 = c then
        ((n.choose q.1 * m.choose q.2 : ℕ) : ℝ) / ((n + m).choose c : ℕ) else 0 := fun q => by
    rw [Finset.sum_ite_eq]
    rw [ite_eq_left (by rw [mem_range]; omega)]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_comm]
  rw [show ((n + m + 1 : ℕ) : ℝ) = ∑ c ∈ range (n + m + 1), (1 : ℝ) by simp]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' : c ≤ n + m := Nat.lt_succ_iff.mp (mem_range.mp hc)
  have hch : (((n + m).choose c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hc').ne'
  have key := sum_idx_antidiagonal (n := n) (m := m) c (fun a b =>
    (((n.choose a * m.choose b : ℕ) : ℂ) / ((n + m).choose c : ℕ))) (fun a b h => by
      have h' : n.choose a * m.choose b ≠ 0 := fun h0 => h (by simp [h0])
      refine ⟨?_, ?_⟩
      · by_contra ha
        exact h' (by rw [Nat.choose_eq_zero_of_lt (by omega : n < a)]; simp)
      · by_contra hb
        exact h' (by rw [Nat.choose_eq_zero_of_lt (by omega : m < b)]; simp))
  have hV : ∑ ij ∈ antidiagonal c, (((n.choose ij.1 * m.choose ij.2 : ℕ) : ℂ) /
      ((n + m).choose c : ℕ)) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, ← Nat.add_choose_eq]
    exact div_self (by exact_mod_cast (Nat.choose_pos hc').ne')
  rw [hV] at key
  have key' : ((∑ q : Idx n m, if (q.1 : ℕ) + q.2 = c then
      ((n.choose q.1 * m.choose q.2 : ℕ) : ℝ) / ((n + m).choose c : ℕ) else 0 : ℝ) : ℂ) = 1 := by
    rw [← key]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  exact_mod_cast key'

/-- **The recoupling coefficient of two singlets**: on links `(n, m)` and `(n, m)` coupled to spin
`0` on both sides, `λ = √((n+m+1)/((n+1)(m+1))) = √((2j+1)/((2j₊+1)(2j₋+1)))`. -/
theorem eprlRecoupling_singlet (n m : ℕ) :
    eprlRecoupling n m n m 0 0 0 =
      (Real.sqrt (((n + m : ℕ) : ℝ) + 1) /
        (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) : ℝ) := by
  set K : ℝ := 1 / (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) *
    Real.sqrt (((n + m : ℕ) : ℝ) + 1)) with hK
  set g : ℕ → ℕ → ℝ := fun a b => ((n.choose a * m.choose b : ℕ) : ℝ) / ((n + m).choose (a + b) : ℕ)
    with hg
  -- the trace over the one-dimensional spin-0 space is the top entry
  have h00 : eprlRecoupling n m n m 0 0 0 = recoupMat n m n m 0 0 0 (0, 0) 0 := by
    rw [eprlRecoupling, trace, Fin.sum_univ_one, diag_apply, mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_one, Fin.sum_univ_one]
    simp [cgz, cgCoefficient_stretched]
  rw [h00, recoupMat_apply_zero]
  simp only [Nat.sub_zero, show (n + n) / 2 = n by omega, show (m + m) / 2 = m by omega,
    show (n + m + (n + m)) / 2 = n + m by omega]
  congr 1
  -- each term
  have hterm : ∀ (P : Idx n n × Idx m m) (c : Idx (n + m) (n + m)),
      cgCoefficient n n n 0 P.1.1 P.1.2 * cgCoefficient m m m 0 P.2.1 P.2.2 *
        eprlEntry n m P.1.1 P.2.1 c.1 * eprlEntry n m P.1.2 P.2.2 c.2 *
        cgCoefficient (n + m) (n + m) (n + m) 0 c.1 c.2 =
      if (P.1.1 : ℕ) + P.1.2 = n ∧ (P.2.1 : ℕ) + P.2.2 = m ∧ c = (⟨P.1.1 + P.2.1, by omega⟩,
        ⟨P.1.2 + P.2.2, by omega⟩) then K * g P.1.1 P.2.1 else 0 := by
    intro P c
    obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩, ⟨⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩⟩⟩ := P
    obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := c
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    rw [cgCoefficient_singlet_apply (by omega) (by omega),
      cgCoefficient_singlet_apply (by omega) (by omega),
      cgCoefficient_singlet_apply (by omega) (by omega)]
    by_cases h1 : a₁ + a₂ = n
    · by_cases h2 : b₁ + b₂ = m
      · by_cases h3 : c₁ = a₁ + b₁
        · by_cases h4 : c₂ = a₂ + b₂
          · rw [ite_eq_left (show a₁ + a₂ = n ∧ b₁ + b₂ = m ∧ c₁ = a₁ + b₁ ∧ c₂ = a₂ + b₂ from
              ⟨h1, h2, h3, h4⟩), ite_eq_left h1, ite_eq_left h2,
              ite_eq_left (show c₁ + c₂ = n + m by omega), eprlEntry, eprlEntry,
              ite_eq_left h3.symm, ite_eq_left h4.symm]
            subst h3
            have hsymm : ((n.choose a₂ * m.choose b₂ : ℕ) : ℝ) / ((n + m).choose c₂ : ℕ) =
                ((n.choose a₁ * m.choose b₁ : ℕ) : ℝ) / ((n + m).choose (a₁ + b₁) : ℕ) := by
              rw [show a₂ = n - a₁ by omega, show b₂ = m - b₁ by omega,
                show c₂ = n + m - (a₁ + b₁) by omega, Nat.choose_symm (by omega),
                Nat.choose_symm (by omega), Nat.choose_symm (by omega)]
            rw [hsymm]
            have hX : (0 : ℝ) ≤ ((n.choose a₁ * m.choose b₁ : ℕ) : ℝ) /
                ((n + m).choose (a₁ + b₁) : ℕ) := by positivity
            have hsign : (-1 : ℝ) ^ a₁ * (-1) ^ b₁ * (-1) ^ (a₁ + b₁) = 1 := by
              rw [← pow_add, ← pow_add, Even.neg_one_pow ⟨a₁ + b₁, by ring⟩]
            set X : ℝ := ((n.choose a₁ * m.choose b₁ : ℕ) : ℝ) / ((n + m).choose (a₁ + b₁) : ℕ)
              with hXdef
            calc (-1 : ℝ) ^ a₁ / Real.sqrt ((n : ℝ) + 1) * ((-1) ^ b₁ / Real.sqrt ((m : ℝ) + 1)) *
                  Real.sqrt X * Real.sqrt X * ((-1) ^ (a₁ + b₁) / Real.sqrt (((n + m : ℕ) : ℝ) + 1))
                = ((-1 : ℝ) ^ a₁ * (-1) ^ b₁ * (-1) ^ (a₁ + b₁)) *
                    (Real.sqrt X * Real.sqrt X) * K := by
                  rw [hK]; push_cast; ring
              _ = K * g a₁ b₁ := by rw [hsign, Real.mul_self_sqrt hX, hg, hXdef]; ring
          · have : eprlEntry n m a₂ b₂ c₂ = 0 := by
              rw [eprlEntry, ite_eq_right (fun h => h4 h.symm)]
            rw [this, ite_eq_right (show ¬(a₁ + a₂ = n ∧ b₁ + b₂ = m ∧ c₁ = a₁ + b₁ ∧
              c₂ = a₂ + b₂) from fun h => h4 h.2.2.2)]
            ring
        · have : eprlEntry n m a₁ b₁ c₁ = 0 := by
            rw [eprlEntry, ite_eq_right (fun h => h3 h.symm)]
          rw [this, ite_eq_right (show ¬(a₁ + a₂ = n ∧ b₁ + b₂ = m ∧ c₁ = a₁ + b₁ ∧
            c₂ = a₂ + b₂) from fun h => h3 h.2.2.1)]
          ring
      · rw [ite_eq_right h2, ite_eq_right (show ¬(a₁ + a₂ = n ∧ b₁ + b₂ = m ∧ c₁ = a₁ + b₁ ∧
          c₂ = a₂ + b₂) from fun h => h2 h.2.1)]
        ring
    · rw [ite_eq_right h1, ite_eq_right (show ¬(a₁ + a₂ = n ∧ b₁ + b₂ = m ∧ c₁ = a₁ + b₁ ∧
        c₂ = a₂ + b₂) from fun h => h1 h.1)]
      ring
  simp only [hterm]
  rw [Finset.sum_comm]
  have hin : ∀ y : Idx n n × Idx m m, (∑ x : Idx (n + m) (n + m),
      if (y.1.1 : ℕ) + y.1.2 = n ∧ (y.2.1 : ℕ) + y.2.2 = m ∧ x = (⟨y.1.1 + y.2.1, by omega⟩,
        ⟨y.1.2 + y.2.2, by omega⟩) then K * g y.1.1 y.2.1 else 0) =
      if (y.1.1 : ℕ) + y.1.2 = n ∧ (y.2.1 : ℕ) + y.2.2 = m then K * g y.1.1 y.2.1 else 0 := by
    intro y
    by_cases h : (y.1.1 : ℕ) + y.1.2 = n ∧ (y.2.1 : ℕ) + y.2.2 = m
    · rw [ite_eq_left h]
      simp only [h.1, h.2, true_and]
      rw [Finset.sum_ite_eq']
      simp
    · rw [ite_eq_right h]
      exact Finset.sum_eq_zero fun x _ => ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩
  simp only [hin]
  -- sum over a pair with fixed total
  have hpair : ∀ (N : ℕ) (f : Fin (N + 1) → ℝ),
      ∑ p : Fin (N + 1) × Fin (N + 1), (if (p.1 : ℕ) + p.2 = N then f p.1 else 0) = ∑ a, f a := by
    intro N f
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    dsimp only
    have ha := a.2
    rw [Finset.sum_eq_single (⟨N - a, by omega⟩ : Fin (N + 1))]
    · rw [ite_eq_left (show (a : ℕ) + (N - a) = N by omega)]
    · intro b _ hb
      refine ite_eq_right fun h => hb (Fin.ext ?_)
      show (b : ℕ) = N - a
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsplit : ∑ y : Idx n n × Idx m m,
      (if (y.1.1 : ℕ) + y.1.2 = n ∧ (y.2.1 : ℕ) + y.2.2 = m then K * g y.1.1 y.2.1 else 0) =
      ∑ q : Idx n m, K * g q.1 q.2 := by
    rw [Fintype.sum_prod_type]
    have : ∀ Y₁ : Idx n n, ∑ Y₂ : Idx m m,
        (if (Y₁.1 : ℕ) + Y₁.2 = n ∧ (Y₂.1 : ℕ) + Y₂.2 = m then K * g Y₁.1 Y₂.1 else 0) =
        if (Y₁.1 : ℕ) + Y₁.2 = n then ∑ b : Fin (m + 1), K * g Y₁.1 b else 0 := fun Y₁ => by
      by_cases h : (Y₁.1 : ℕ) + Y₁.2 = n
      · rw [ite_eq_left h]
        simp only [h, true_and]
        exact hpair m (fun b => K * g Y₁.1 b)
      · rw [ite_eq_right h]
        exact Finset.sum_eq_zero fun _ _ => ite_eq_right fun h' => h h'.1
    simp only [this]
    rw [hpair n (fun a => ∑ b : Fin (m + 1), K * g a b), Fintype.sum_prod_type]
  rw [hsplit, ← Finset.mul_sum]
  have hS := sum_choose_div_choose n m
  simp only [hg]
  rw [hS, hK]
  have hN : Real.sqrt (((n + m : ℕ) : ℝ) + 1) * Real.sqrt (((n + m : ℕ) : ℝ) + 1) =
      ((n + m : ℕ) : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  have h1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < Real.sqrt (((n + m : ℕ) : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  push_cast at hN h3 ⊢
  field_simp
  linarith

lemma tri_zero_left {n z : ℕ} : Tri n n z ∧ Tri 0 0 z ↔ z = 0 := by
  unfold Tri; omega

lemma channel_zero (n : ℕ) : channel n n 0 0 = {0} := by
  ext z
  rw [mem_channel, tri_zero_left, Finset.mem_singleton]

lemma zero_mem_channel (n m : ℕ) : 0 ∈ channel n n m m := by
  rw [mem_channel]; unfold Tri; omega

lemma fusionScale_zero : fusionScale 0 0 0 = 1 := by simp [fusionScale]

/-- **Fusion coefficient of an equal-spin node**: on four links with the same labels `(n, m)`,
`f(0; 0, 0) = (2j+1)/((2j₊+1)(2j₋+1))`, `j = j₊ + j₋`. -/
theorem fusion_zero_equal (n m : ℕ) :
    fusion n n n n m m m m 0 0 0 =
      ((((n + m : ℕ) : ℝ) + 1) / (((n : ℝ) + 1) * ((m : ℝ) + 1)) : ℝ) := by
  rw [fusion_eq (zero_mem_channel n n) (zero_mem_channel m m) (zero_mem_channel (n + m) (n + m)),
    ite_eq_left (by unfold Tri; omega), eprlRecoupling_singlet, fusionScale_zero, Complex.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [one_mul]
  have h1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity), mul_mul_mul_comm,
    Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity)]

/-- **The 2-valent fusion coefficient**: for a node with links `(n, m)`, `(n, m)` and two spin-`0`
links, `f(0; 0, 0) = √((2j+1)/((2j₊+1)(2j₋+1)))`. -/
theorem fusion_two_valent (n m : ℕ) :
    fusion n n 0 0 m m 0 0 0 0 0 =
      (Real.sqrt (((n + m : ℕ) : ℝ) + 1) /
        (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) : ℝ) := by
  rw [fusion_eq (zero_mem_channel n 0) (zero_mem_channel m 0) (zero_mem_channel (n + m) (0 + 0)),
    ite_eq_left (by unfold Tri; omega), eprlRecoupling_singlet, eprlRecoupling_singlet,
    fusionScale_zero]
  simp

/-- **The EPRL map is not isometric** (Kamiński–Kisielowski–Lewandowski): on the 2-valent node with
labels `n, m ≥ 1`, `‖Φ(ι_0)‖² = (2j+1)/((2j₊+1)(2j₋+1)) < 1 = ‖ι_0‖²`. -/
theorem eprlIntertwiner_two_valent_norm (n m : ℕ) :
    hsInner (eprlIntertwiner n n 0 0 m m 0 0 (ivec (n + m) (n + m) (0 + 0) (0 + 0) 0))
      (eprlIntertwiner n n 0 0 m m 0 0 (ivec (n + m) (n + m) (0 + 0) (0 + 0) 0)) =
      ((((n + m : ℕ) : ℝ) + 1) / (((n : ℝ) + 1) * ((m : ℝ) + 1)) : ℝ) := by
  rw [hsInner_eprlIntertwiner_ivec, channel4, channel_zero, channel_zero,
    Finset.singleton_product_singleton,
    Finset.sum_singleton, fusion_two_valent, Complex.normSq_ofReal]
  congr 1
  rw [div_mul_div_comm, Real.mul_self_sqrt (by positivity), mul_mul_mul_comm,
    Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity)]

/-- **The EPRL map is not isometric**: on a 2-valent node with `j₊, j₋ > 0`,
`‖Φ(ι₀)‖ < ‖ι₀‖`. -/
theorem eprlIntertwiner_not_isometric {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (hsInner (eprlIntertwiner n n 0 0 m m 0 0 (ivec (n + m) (n + m) (0 + 0) (0 + 0) 0))
      (eprlIntertwiner n n 0 0 m m 0 0 (ivec (n + m) (n + m) (0 + 0) (0 + 0) 0))).re <
    (hsInner (ivec (n + m) (n + m) (0 + 0) (0 + 0) 0)
      (ivec (n + m) (n + m) (0 + 0) (0 + 0) 0)).re := by
  rw [eprlIntertwiner_two_valent_norm, hsInner_ivec (zero_mem_channel _ _) (zero_mem_channel _ _),
    ite_eq_left rfl, Complex.ofReal_re, Complex.one_re, div_lt_one (by positivity)]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  nlinarith

end Lightlike.Spin4
