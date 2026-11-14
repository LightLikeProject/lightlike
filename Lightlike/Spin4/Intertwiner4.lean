import Lightlike.Spin4.EPRL
import Lightlike.Recoupling.Intertwiner

/-!
# 4-valent intertwiners of SU(2) and of Spin(4)

A 4-valent node of a spin network with two outgoing links of spins `J₁, J₂` and two incoming
links of spins `J₃, J₄` carries an intertwiner: an SU(2)-equivariant linear map
`T : V_{J₃/2} ⊗ V_{J₄/2} → V_{J₁/2} ⊗ V_{J₂/2}` (`IsIntertwiner`). This file gives the standard
orthonormal basis of these maps, labelled by the spin `z/2` of the channel `(J₁ J₂) → (J₃ J₄)`:

`ι_z = (z+1)^{-1/2} C^{J₁J₂}_z (C^{J₃J₄}_z)ᴴ`,

with the Clebsch–Gordan matrices `C^{nm}_z = cgz n m z` of Physlib's coefficients. Inner
products are Hilbert–Schmidt, `⟨S, T⟩ = tr(Sᴴ T)` (`hsInner`).

The same construction for each factor of Spin(4) = SU(2) × SU(2) gives the Spin(4) intertwiners:
the self-dual labels `n_a` and anti-self-dual labels `m_a` of the four links, with the products
`ι⁺_x ⊗ ι⁻_y` as orthonormal basis.

## Main results

* `equivariant_eq_smul_cgz`, `equivariant_eq_zero`: **Schur for coupled spins**: an equivariant
  map `V_{z/2} → V_{n/2} ⊗ V_{m/2}` is a multiple of `C^{nm}_z`, and zero when the triad
  `(n m z)` is not admissible.
* `ivec_isIntertwiner`, `hsInner_ivec`, `eq_sum_ivec`: the vectors `ι_z`, `z` in the channel set,
  form an orthonormal basis of the SU(2) intertwiners.
* `isSpin4Intertwiner_iff`: the Spin(4) intertwiners in the reordered form used here are exactly
  the equivariant maps for the representations `spin4Mat` of SF5a.
* `ivec4_isSpin4Intertwiner`, `hsInner_ivec4`, `eq_sum_ivec4`: the products `ι⁺_x ⊗ ι⁻_y` form
  an orthonormal basis of the Spin(4) intertwiners.
* `cgz_eq_threeJ`: the entries of `C^{nm}_z` are Physlib's 3j symbols.
* `fourJ_eq_ivec`: **the bridge to `Recoupling/`**: the all-outgoing intertwiners
  `Lightlike.Recoupling.fourJ` of SF4 are the `ι_z` with the two incoming links flipped by the invariant
  forms `ε`, up to a sign `(-1)^{J₂+J₄+a₁+a₂}` that does not depend on `z`.

## Conventions

Doubled spins throughout. The 4-valent intertwiners here are maps (two outgoing and two incoming
links); the all-outgoing intertwiners `Lightlike.Recoupling.fourJ` (milestone SF4) differ from them by
the SU(2) invariant forms on the incoming links (`fourJ_eq_ivec`).

## References

* P. Martin-Dussaud, *A primer of group theory for loop quantum gravity and spin-foams*,
  Gen. Relativ. Gravit. 51 (2019) 110, arXiv:1902.08439 (intertwiners and their bases).
* J. Engle, R. Pereira, C. Rovelli, E. Livine, *LQG vertex with finite Immirzi parameter*,
  Nucl. Phys. B 799 (2008) 136, arXiv:0711.0146 (SO(3) and SO(4) intertwiners).
-/

open Matrix Finset PhyslibAlpha.Sl2 Lightlike.Pentagon
open scoped Kronecker

namespace Lightlike.Spin4

open SU2

variable {n m z : ℕ}

/-! ## A. Clebsch–Gordan matrices labelled by the coupled spin -/

/-- An admissible triad `(n m z)` is a coupled spin `z = n + m - 2k`, `k ≤ n`, `k ≤ m`. -/
lemma tri_iff_exists (n m z : ℕ) : Tri n m z ↔ ∃ k, k ≤ n ∧ k ≤ m ∧ z = n + m - 2 * k := by
  unfold Tri
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨(n + m - z) / 2, by omega, by omega, by omega⟩
  · rintro ⟨k, hk, hk', rfl⟩
    omega

/-- **The Clebsch–Gordan matrix onto spin `z/2`**: rows the product states of
`V_{n/2} ⊗ V_{m/2}`, columns the states of spin `z/2`, entries Physlib's coefficients with
`k = (n + m - z)/2`. -/
noncomputable def cgz (n m z : ℕ) : Matrix (Idx n m) (Fin (z + 1)) ℂ :=
  Matrix.of fun p l => (cgCoefficient n m ((n + m - z) / 2) l p.1 p.2 : ℂ)

lemma cgz_sub {k : ℕ} (hk : 2 * k ≤ n + m) : cgz n m (n + m - 2 * k) = cgMatrix n m k := by
  ext p l
  simp only [cgz, cgMatrix, of_apply]
  rw [show (n + m - (n + m - 2 * k)) / 2 = k by omega]

/-- `C^{nm}_z` intertwines the SU(2) representations. -/
theorem cgz_equivariant (h : Tri n m z) (g : SU2) :
    (spinMat n g ⊗ₖ spinMat m g) * cgz n m z = cgz n m z * spinMat z g := by
  obtain ⟨k, hk, hk', rfl⟩ := (tri_iff_exists n m z).mp h
  rw [cgz_sub (by omega)]
  exact cgMatrix_equivariant hk hk' g

/-- The adjoint `(C^{nm}_z)ᴴ` intertwines the SU(2) representations. -/
theorem cgz_conjTranspose_equivariant (h : Tri n m z) (g : SU2) :
    (cgz n m z)ᴴ * (spinMat n g ⊗ₖ spinMat m g) = spinMat z g * (cgz n m z)ᴴ := by
  obtain ⟨k, hk, hk', rfl⟩ := (tri_iff_exists n m z).mp h
  rw [cgz_sub (by omega)]
  exact cgMatrix_conjTranspose_equivariant hk hk' g

/-- The columns of `C^{nm}_z` are orthonormal. -/
theorem cgz_isometry (h : Tri n m z) : (cgz n m z)ᴴ * cgz n m z = 1 := by
  obtain ⟨k, hk, hk', rfl⟩ := (tri_iff_exists n m z).mp h
  rw [cgz_sub (by omega)]
  exact cgMatrix_isometry hk hk'

/-- Different coupled spins are orthogonal. -/
theorem cgz_orth {z' : ℕ} (h : Tri n m z) (h' : Tri n m z') (hne : z ≠ z') :
    (cgz n m z)ᴴ * cgz n m z' = 0 := by
  obtain ⟨k, hk, hk', rfl⟩ := (tri_iff_exists n m z).mp h
  obtain ⟨k', hl, hl', rfl⟩ := (tri_iff_exists n m z').mp h'
  rw [cgz_sub (by omega), cgz_sub (by omega)]
  exact cgMatrix_orth hk hk' hl hl' (fun e => hne (by rw [e]))

/-- The admissible coupled spins of `n/2 ⊗ m/2`. -/
def triSet (n m : ℕ) : Finset ℕ := (range (n + m + 1)).filter (Tri n m)

lemma mem_triSet : z ∈ triSet n m ↔ Tri n m z := by
  simp only [triSet, mem_filter, mem_range, and_iff_right_iff_imp]
  intro h
  unfold Tri at h
  omega

/-- **Completeness**: `Σ_z C^{nm}_z (C^{nm}_z)ᴴ = 1` over the admissible coupled spins. -/
theorem cgz_complete : ∑ z ∈ triSet n m, cgz n m z * (cgz n m z)ᴴ = 1 := by
  rw [← cgMatrix_complete (n := n) (m := m)]
  symm
  refine Finset.sum_nbij' (fun k => n + m - 2 * k) (fun z => (n + m - z) / 2) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [mem_range, Nat.lt_succ_iff, le_min_iff] at hk
    rw [mem_triSet, tri_iff_exists]
    exact ⟨k, hk.1, hk.2, rfl⟩
  · intro z hz
    rw [mem_triSet, tri_iff_exists] at hz
    obtain ⟨k, hk, hk', rfl⟩ := hz
    rw [mem_range, Nat.lt_succ_iff, le_min_iff]
    omega
  · intro k hk
    rw [mem_range, Nat.lt_succ_iff, le_min_iff] at hk
    omega
  · intro z hz
    rw [mem_triSet, tri_iff_exists] at hz
    obtain ⟨k, hk, hk', rfl⟩ := hz
    omega
  · intro k hk
    rw [mem_range, Nat.lt_succ_iff, le_min_iff] at hk
    rw [cgz_sub (by omega)]

/-- **Schur for coupled spins, inadmissible case**: an equivariant map `V_{z/2} → V_{n/2} ⊗ V_{m/2}`
vanishes when `(n m z)` is not an admissible triad. -/
theorem equivariant_eq_zero (hz : ¬ Tri n m z) {W : Matrix (Idx n m) (Fin (z + 1)) ℂ}
    (hW : ∀ g : SU2, (spinMat n g ⊗ₖ spinMat m g) * W = W * spinMat z g) : W = 0 := by
  calc W = (∑ z' ∈ triSet n m, cgz n m z' * (cgz n m z')ᴴ) * W := by
        rw [cgz_complete, Matrix.one_mul]
    _ = ∑ z' ∈ triSet n m, cgz n m z' * ((cgz n m z')ᴴ * W) := by
        rw [Matrix.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Matrix.mul_assoc _ _ _
    _ = 0 := by
        refine Finset.sum_eq_zero fun z' hz' => ?_
        have hz'' := mem_triSet.mp hz'
        have hne : z ≠ z' := fun e => hz (e ▸ hz'')
        rw [spin_intertwiner_eq_zero (T := (cgz n m z')ᴴ * W) hne (fun g => by
          rw [← Matrix.mul_assoc, ← cgz_conjTranspose_equivariant hz'' g, Matrix.mul_assoc, hW g,
            Matrix.mul_assoc]), Matrix.mul_zero]

/-- **Schur for coupled spins**: an equivariant map `W : V_{z/2} → V_{n/2} ⊗ V_{m/2}` is
`c C^{nm}_z` with `c = tr((C^{nm}_z)ᴴ W)/(z+1)`. -/
theorem equivariant_eq_smul_cgz (h : Tri n m z) {W : Matrix (Idx n m) (Fin (z + 1)) ℂ}
    (hW : ∀ g : SU2, (spinMat n g ⊗ₖ spinMat m g) * W = W * spinMat z g) :
    W = (trace ((cgz n m z)ᴴ * W) / (z + 1 : ℂ)) • cgz n m z := by
  have hS : ∀ z' ∈ triSet n m, ∀ g : SU2,
      spinMat z' g * ((cgz n m z')ᴴ * W) = ((cgz n m z')ᴴ * W) * spinMat z g := fun z' hz' g => by
    rw [← Matrix.mul_assoc, ← cgz_conjTranspose_equivariant (mem_triSet.mp hz') g,
      Matrix.mul_assoc, hW g, Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := spin_intertwiner_eq_smul (hS z (mem_triSet.mpr h))
  have hW' : W = c • cgz n m z := by
    calc W = (∑ z' ∈ triSet n m, cgz n m z' * (cgz n m z')ᴴ) * W := by
          rw [cgz_complete, Matrix.one_mul]
      _ = ∑ z' ∈ triSet n m, cgz n m z' * ((cgz n m z')ᴴ * W) := by
          rw [Matrix.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => Matrix.mul_assoc _ _ _
      _ = cgz n m z * ((cgz n m z)ᴴ * W) := by
          refine Finset.sum_eq_single z (fun z' hz' hne => ?_) (fun hz => absurd
            (mem_triSet.mpr h) hz)
          rw [spin_intertwiner_eq_zero (Ne.symm hne) (hS z' hz'), Matrix.mul_zero]
      _ = c • cgz n m z := by rw [hc, Matrix.mul_smul, Matrix.mul_one]
  have htr : trace ((cgz n m z)ᴴ * W) = c * (z + 1 : ℂ) := by
    rw [hc, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    ring
  rw [htr, mul_div_assoc, div_self (by exact_mod_cast Nat.succ_ne_zero z), mul_one]
  exact hW'

/-! ## B. The Hilbert–Schmidt inner product -/

/-- **The Hilbert–Schmidt inner product** `⟨S, T⟩ = tr(Sᴴ T) = Σᵢⱼ conj(Sᵢⱼ) Tᵢⱼ`. -/
noncomputable def hsInner {ι κ : Type*} [Fintype ι] [Fintype κ] (S T : Matrix ι κ ℂ) : ℂ :=
  ∑ i, ∑ j, star (S i j) * T i j

section HS

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

lemma hsInner_eq_trace (S T : Matrix ι κ ℂ) : hsInner S T = trace (Sᴴ * T) := by
  simp only [hsInner, trace, Matrix.diag, mul_apply, conjTranspose_apply]
  exact Finset.sum_comm

lemma hsInner_add_right (S T T' : Matrix ι κ ℂ) :
    hsInner S (T + T') = hsInner S T + hsInner S T' := by
  simp only [hsInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma hsInner_smul_right (S T : Matrix ι κ ℂ) (c : ℂ) : hsInner S (c • T) = c * hsInner S T := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma hsInner_smul_left (S T : Matrix ι κ ℂ) (c : ℂ) :
    hsInner (c • S) T = star c * hsInner S T := by
  simp only [hsInner, Matrix.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma hsInner_sum_right {β : Type*} (S : Matrix ι κ ℂ) (s : Finset β) (f : β → Matrix ι κ ℂ) :
    hsInner S (∑ b ∈ s, f b) = ∑ b ∈ s, hsInner S (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hsInner]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hsInner_add_right, ih]

lemma hsInner_zero_right (S : Matrix ι κ ℂ) : hsInner S 0 = 0 := by simp [hsInner]

/-- `⟨A Bᴴ, M⟩ = tr(Aᴴ M B)`. -/
lemma hsInner_mul_conjTranspose (A : Matrix ι μ ℂ) (B : Matrix κ μ ℂ) (M : Matrix ι κ ℂ) :
    hsInner (A * Bᴴ) M = trace (Aᴴ * M * B) := by
  rw [hsInner_eq_trace, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    trace_mul_comm, Matrix.mul_assoc]

/-- The squared norm `⟨T, T⟩` is a nonnegative real. -/
lemma hsInner_self (T : Matrix ι κ ℂ) :
    hsInner T T = ((∑ i, ∑ j, Complex.normSq (T i j) : ℝ) : ℂ) := by
  simp only [hsInner, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj]

/-- Expansion in an orthonormal family: if `T = Σ a_b v_b` with `⟨v_b, v_b'⟩ = δ`, then
`a_b = ⟨v_b, T⟩`. -/
lemma eq_sum_hsInner_of_eq_sum {β : Type*} [DecidableEq β] {s : Finset β}
    {v : β → Matrix ι κ ℂ} (hv : ∀ b ∈ s, ∀ b' ∈ s, hsInner (v b) (v b') = if b = b' then 1 else 0)
    {T : Matrix ι κ ℂ} {a : β → ℂ} (hT : T = ∑ b ∈ s, a b • v b) :
    T = ∑ b ∈ s, hsInner (v b) T • v b := by
  have h : ∀ b ∈ s, hsInner (v b) T = a b := fun b hb => by
    rw [hT, hsInner_sum_right]
    simp only [hsInner_smul_right]
    rw [Finset.sum_eq_single b (fun b' hb' hne => by rw [hv b hb b' hb', ite_eq_right
      (Ne.symm hne), mul_zero]) (fun h => absurd hb h), hv b hb b hb, ite_eq_left rfl, mul_one]
  conv_lhs => rw [hT]
  exact Finset.sum_congr rfl fun b hb => by rw [h b hb]

end HS

/-! ## C. SU(2) intertwiners -/

/-- The diagonal action `D^{n/2}(g) ⊗ D^{m/2}(g)` on `V_{n/2} ⊗ V_{m/2}`. -/
noncomputable abbrev pairMat (n m : ℕ) (g : SU2) : Matrix (Idx n m) (Idx n m) ℂ :=
  spinMat n g ⊗ₖ spinMat m g

variable (J₁ J₂ J₃ J₄ : ℕ)

/-- **4-valent SU(2) intertwiners**: linear maps `T : V_{J₃/2} ⊗ V_{J₄/2} → V_{J₁/2} ⊗ V_{J₂/2}`
that commute with SU(2). -/
def IsIntertwiner (T : Matrix (Idx J₁ J₂) (Idx J₃ J₄) ℂ) : Prop :=
  ∀ g : SU2, pairMat J₁ J₂ g * T = T * pairMat J₃ J₄ g

/-- The spins `z` of the channel `(J₁ J₂) → (J₃ J₄)`: `(J₁ J₂ z)` and `(J₃ J₄ z)` admissible. -/
def channel : Finset ℕ := (range (J₁ + J₂ + 1)).filter fun z => Tri J₁ J₂ z ∧ Tri J₃ J₄ z

/-- **The intertwiner basis** `ι_z = (z+1)^{-1/2} C^{J₁J₂}_z (C^{J₃J₄}_z)ᴴ`. -/
noncomputable def ivec (z : ℕ) : Matrix (Idx J₁ J₂) (Idx J₃ J₄) ℂ :=
  ((Real.sqrt ((z : ℝ) + 1))⁻¹ : ℂ) • (cgz J₁ J₂ z * (cgz J₃ J₄ z)ᴴ)

variable {J₁ J₂ J₃ J₄}

lemma mem_channel : z ∈ channel J₁ J₂ J₃ J₄ ↔ Tri J₁ J₂ z ∧ Tri J₃ J₄ z := by
  simp only [channel, mem_filter, mem_range, and_iff_right_iff_imp]
  intro h
  unfold Tri at h
  omega

/-- The basis vectors are intertwiners. -/
theorem ivec_isIntertwiner (h12 : Tri J₁ J₂ z) (h34 : Tri J₃ J₄ z) :
    IsIntertwiner J₁ J₂ J₃ J₄ (ivec J₁ J₂ J₃ J₄ z) := fun g => by
  simp only [ivec, Matrix.mul_smul, Matrix.smul_mul]
  rw [← Matrix.mul_assoc, cgz_equivariant h12, Matrix.mul_assoc,
    ← cgz_conjTranspose_equivariant h34,
    Matrix.mul_assoc]

lemma sqrt_inv_sq (z : ℕ) :
    star ((Real.sqrt ((z : ℝ) + 1))⁻¹ : ℂ) * ((Real.sqrt ((z : ℝ) + 1))⁻¹ : ℂ) * ((z : ℂ) + 1) =
      1 := by
  have hpos : (0 : ℝ) < (z : ℝ) + 1 := by positivity
  rw [Complex.star_def, ← Complex.ofReal_inv, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← mul_inv, Real.mul_self_sqrt hpos.le]
  push_cast
  field_simp

/-- **Orthonormality**: `⟨ι_z, ι_z'⟩ = δ_{zz'}`. -/
theorem hsInner_ivec {z' : ℕ} (hz : z ∈ channel J₁ J₂ J₃ J₄) (hz' : z' ∈ channel J₁ J₂ J₃ J₄) :
    hsInner (ivec J₁ J₂ J₃ J₄ z) (ivec J₁ J₂ J₃ J₄ z') = if z = z' then 1 else 0 := by
  rw [mem_channel] at hz hz'
  simp only [ivec, hsInner_smul_left, hsInner_smul_right, hsInner_mul_conjTranspose]
  by_cases hzz : z = z'
  · subst hzz
    rw [ite_eq_left rfl, ← Matrix.mul_assoc (cgz J₁ J₂ z)ᴴ, cgz_isometry hz.1,
      Matrix.one_mul, cgz_isometry hz.2, trace_one, Fintype.card_fin]
    rw [← sqrt_inv_sq z]
    push_cast
    ring
  · rw [ite_eq_right hzz, ← Matrix.mul_assoc (cgz J₁ J₂ z)ᴴ, cgz_orth hz.1 hz'.1 hzz]
    simp

/-- **Completeness**: every SU(2) intertwiner expands in the basis,
`T = Σ_z ⟨ι_z, T⟩ ι_z`. -/
theorem eq_sum_ivec {T : Matrix (Idx J₁ J₂) (Idx J₃ J₄) ℂ} (hT : IsIntertwiner J₁ J₂ J₃ J₄ T) :
    T = ∑ z ∈ channel J₁ J₂ J₃ J₄, hsInner (ivec J₁ J₂ J₃ J₄ z) T • ivec J₁ J₂ J₃ J₄ z := by
  classical
  -- the blocks `C_zᴴ T C_z'` are intertwiners between spins `z'` and `z`
  have hB : ∀ z ∈ triSet J₁ J₂, ∀ z' ∈ triSet J₃ J₄, ∀ g : SU2,
      spinMat z g * ((cgz J₁ J₂ z)ᴴ * T * cgz J₃ J₄ z') =
        ((cgz J₁ J₂ z)ᴴ * T * cgz J₃ J₄ z') * spinMat z' g := fun z hz z' hz' g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cgz_conjTranspose_equivariant (mem_triSet.mp hz),
      Matrix.mul_assoc _ _ T, hT g, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (cgz J₃ J₄ z'),
      cgz_equivariant (mem_triSet.mp hz'), ← Matrix.mul_assoc]
  have hexp : T = ∑ z ∈ triSet J₁ J₂, ∑ z' ∈ triSet J₃ J₄,
      cgz J₁ J₂ z * ((cgz J₁ J₂ z)ᴴ * T * cgz J₃ J₄ z') * (cgz J₃ J₄ z')ᴴ := by
    calc T = (∑ z ∈ triSet J₁ J₂, cgz J₁ J₂ z * (cgz J₁ J₂ z)ᴴ) * T *
          (∑ z' ∈ triSet J₃ J₄, cgz J₃ J₄ z' * (cgz J₃ J₄ z')ᴴ) := by
          rw [cgz_complete, cgz_complete, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by
          rw [Matrix.sum_mul, Matrix.sum_mul]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Matrix.mul_sum]
          refine Finset.sum_congr rfl fun z' _ => ?_
          simp only [Matrix.mul_assoc]
  -- only the diagonal blocks survive, and they are scalars
  have hdiag : ∀ z ∈ triSet J₁ J₂, ∑ z' ∈ triSet J₃ J₄,
      cgz J₁ J₂ z * ((cgz J₁ J₂ z)ᴴ * T * cgz J₃ J₄ z') * (cgz J₃ J₄ z')ᴴ =
      if z ∈ channel J₁ J₂ J₃ J₄ then
        (trace ((cgz J₁ J₂ z)ᴴ * T * cgz J₃ J₄ z) / (z + 1 : ℂ)) •
          (cgz J₁ J₂ z * (cgz J₃ J₄ z)ᴴ) else 0 := by
    intro z hz
    have hz1 := mem_triSet.mp hz
    split_ifs with hzc
    · have hz2 := (mem_channel.mp hzc).2
      rw [Finset.sum_eq_single z (fun z' hz' hne => by
        rw [spin_intertwiner_eq_zero hne (hB z hz z' hz'), Matrix.mul_zero, Matrix.zero_mul])
        (fun h => absurd (mem_triSet.mpr hz2) h)]
      obtain ⟨c, hc⟩ := spin_intertwiner_eq_smul (hB z hz z (mem_triSet.mpr hz2))
      rw [hc, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, Nat.cast_add, Nat.cast_one, mul_div_assoc,
        div_self (by exact_mod_cast Nat.succ_ne_zero z), mul_one]
    · refine Finset.sum_eq_zero fun z' hz' => ?_
      have hne : z' ≠ z := fun e => hzc (mem_channel.mpr ⟨hz1, e ▸ mem_triSet.mp hz'⟩)
      rw [spin_intertwiner_eq_zero hne (hB z hz z' hz'), Matrix.mul_zero, Matrix.zero_mul]
  have hT' : T = ∑ z ∈ channel J₁ J₂ J₃ J₄,
      (trace ((cgz J₁ J₂ z)ᴴ * T * cgz J₃ J₄ z) / (z + 1 : ℂ) * (Real.sqrt ((z : ℝ) + 1) : ℂ)) •
        ivec J₁ J₂ J₃ J₄ z := by
    conv_lhs => rw [hexp]
    rw [Finset.sum_congr rfl hdiag, ← Finset.sum_filter]
    have hfilt : (triSet J₁ J₂).filter (· ∈ channel J₁ J₂ J₃ J₄) = channel J₁ J₂ J₃ J₄ := by
      ext z
      simp only [mem_filter, mem_triSet, mem_channel]
      tauto
    rw [hfilt]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hs : (Real.sqrt ((z : ℝ) + 1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (z : ℝ) + 1)).ne'
    rw [ivec, smul_smul]
    congr 1
    field_simp
  exact eq_sum_hsInner_of_eq_sum (fun b hb b' hb' => hsInner_ivec hb hb') hT'

/-! ## D. Spin(4) intertwiners -/

section Spin4Int

variable {α β γ' δ : Type*}

lemma kron_one_mul_apply [Fintype α] [Fintype γ'] [DecidableEq γ'] (R : Matrix α α ℂ)
    (Q : Matrix (α × γ') (β × δ) ℂ) (a : α) (c : γ') (q : β × δ) :
    ((R ⊗ₖ (1 : Matrix γ' γ' ℂ)) * Q) (a, c) q = ∑ a', R a a' * Q (a', c) q := by
  simp only [mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq]
  simp

lemma mul_kron_one_apply [Fintype β] [Fintype δ] [DecidableEq δ] (R : Matrix β β ℂ)
    (Q : Matrix (α × γ') (β × δ) ℂ) (p : α × γ') (b : β) (d : δ) :
    (Q * (R ⊗ₖ (1 : Matrix δ δ ℂ))) p (b, d) = ∑ b', Q p (b', d) * R b' b := by
  simp only [mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq']
  simp

lemma one_kron_mul_apply [Fintype α] [Fintype γ'] [DecidableEq α] (S : Matrix γ' γ' ℂ)
    (Q : Matrix (α × γ') (β × δ) ℂ) (a : α) (c : γ') (q : β × δ) :
    (((1 : Matrix α α ℂ) ⊗ₖ S) * Q) (a, c) q = ∑ c', S c c' * Q (a, c') q := by
  simp only [mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, ite_mul, one_mul,
    zero_mul]
  rw [Finset.sum_comm (β := ℂ)]
  simp

lemma mul_one_kron_apply [Fintype β] [Fintype δ] [DecidableEq β] (S : Matrix δ δ ℂ)
    (Q : Matrix (α × γ') (β × δ) ℂ) (p : α × γ') (b : β) (d : δ) :
    (Q * ((1 : Matrix β β ℂ) ⊗ₖ S)) p (b, d) = ∑ d', Q p (b, d') * S d' d := by
  simp only [mul_apply, Fintype.sum_prod_type, kroneckerMap_apply, one_apply, ite_mul, one_mul,
    zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm (β := ℂ)]
  simp

variable [Fintype α] [Fintype β] [Fintype γ'] [Fintype δ]

/-- `⟨A ⊗ B, C ⊗ D⟩ = ⟨A, C⟩ ⟨B, D⟩`. -/
lemma hsInner_kronecker (A C : Matrix α β ℂ) (B D : Matrix γ' δ ℂ) :
    hsInner (A ⊗ₖ B) (C ⊗ₖ D) = hsInner A C * hsInner B D := by
  rw [hsInner_eq_trace, hsInner_eq_trace, hsInner_eq_trace, conjTranspose_kronecker,
    ← mul_kronecker_mul, trace_kronecker]

omit [Fintype δ] in
lemma sum3_reorder (F : α → β → γ' → ℂ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm

lemma sum4_reorder (F : α → γ' → β → δ → ℂ) :
    ∑ a, ∑ c, ∑ b, ∑ d, F a c b d = ∑ c, ∑ d, ∑ a, ∑ b, F a c b d := by
  calc ∑ a, ∑ c, ∑ b, ∑ d, F a c b d = ∑ c, ∑ a, ∑ b, ∑ d, F a c b d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a c b d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a c b d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **Kronecker expansion**: if every slice `Q(·, c)(·, d)` expands in an orthonormal family
`u_i`, and every coefficient matrix `(c, d) ↦ ⟨u_i, Q(·, c)(·, d)⟩` expands in an orthonormal
family `v_k`, then `Q = Σ ⟨u_i ⊗ v_k, Q⟩ u_i ⊗ v_k`. -/
lemma eq_sum_kronecker {ι κ : Type*} (Q : Matrix (α × γ') (β × δ) ℂ) (s : Finset ι)
    (u : ι → Matrix α β ℂ) (t : Finset κ) (v : κ → Matrix γ' δ ℂ)
    (hu : ∀ c d, (Matrix.of fun a b => Q (a, c) (b, d)) =
      ∑ i ∈ s, hsInner (u i) (Matrix.of fun a b => Q (a, c) (b, d)) • u i)
    (hv : ∀ i ∈ s, (Matrix.of fun c d => hsInner (u i) (Matrix.of fun a b => Q (a, c) (b, d))) =
      ∑ k ∈ t, hsInner (v k)
        (Matrix.of fun c d => hsInner (u i) (Matrix.of fun a b => Q (a, c) (b, d))) • v k) :
    Q = ∑ p ∈ s ×ˢ t, hsInner (u p.1 ⊗ₖ v p.2) Q • (u p.1 ⊗ₖ v p.2) := by
  set B : ι → Matrix γ' δ ℂ :=
    fun i => Matrix.of fun c d => hsInner (u i) (Matrix.of fun a b => Q (a, c) (b, d)) with hB
  have hcoef : ∀ i k, hsInner (u i ⊗ₖ v k) Q = hsInner (v k) (B i) := fun i k => by
    simp only [hB, hsInner, Fintype.sum_prod_type, kroneckerMap_apply, of_apply, star_mul',
      Finset.mul_sum]
    refine (sum4_reorder _).trans ?_
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  ext ⟨a, c⟩ ⟨b, d⟩
  have h1 := congrFun (congrFun (hu c d) a) b
  simp only [of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h1
  rw [h1, Matrix.sum_apply, Finset.sum_product]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h2 := congrFun (congrFun (hv i hi) c) d
  simp only [of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h2
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, kroneckerMap_apply, hcoef]
  ring

end Spin4Int

variable (n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ)

/-- **4-valent Spin(4) intertwiners**, with the self-dual and anti-self-dual factors grouped: maps
`Q : (V_{n₃} ⊗ V_{n₄}) ⊗ (V_{m₃} ⊗ V_{m₄}) → (V_{n₁} ⊗ V_{n₂}) ⊗ (V_{m₁} ⊗ V_{m₂})` commuting
with `(g₊, g₋) ↦ (D(g₊) ⊗ D(g₊)) ⊗ (D(g₋) ⊗ D(g₋))` (`isSpin4Intertwiner_iff` relates this to the
representations `spin4Mat` link by link). -/
def IsSpin4Intertwiner (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) : Prop :=
  ∀ g : Spin4, (pairMat n₁ n₂ g.1 ⊗ₖ pairMat m₁ m₂ g.2) * Q =
    Q * (pairMat n₃ n₄ g.1 ⊗ₖ pairMat m₃ m₄ g.2)

/-- Regrouping two Spin(4) links: `(V_{n₁} ⊗ V_{m₁}) ⊗ (V_{n₂} ⊗ V_{m₂})` as
`(V_{n₁} ⊗ V_{n₂}) ⊗ (V_{m₁} ⊗ V_{m₂})`. -/
def shuffle (n₁ m₁ n₂ m₂ : ℕ) : Idx n₁ m₁ × Idx n₂ m₂ ≃ Idx n₁ n₂ × Idx m₁ m₂ where
  toFun P := ((P.1.1, P.2.1), (P.1.2, P.2.2))
  invFun P := ((P.1.1, P.2.1), (P.1.2, P.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The representation of Spin(4) on two links, regrouped. -/
lemma spin4Mat_kronecker (g : Spin4) : spin4Mat n₁ m₁ g ⊗ₖ spin4Mat n₂ m₂ g =
    (pairMat n₁ n₂ g.1 ⊗ₖ pairMat m₁ m₂ g.2).submatrix (shuffle n₁ m₁ n₂ m₂)
      (shuffle n₁ m₁ n₂ m₂) := by
  ext ⟨⟨a, b⟩, ⟨a', b'⟩⟩ ⟨⟨c, d⟩, ⟨c', d'⟩⟩
  simp only [spin4Mat, pairMat, shuffle, kroneckerMap_apply, submatrix_apply, Equiv.coe_fn_mk]
  ring

/-- **The Spin(4) intertwiners are the equivariant maps of SF5a's representations**: `Q` is a
Spin(4) intertwiner exactly when, regrouped link by link, it intertwines
`spin4Mat n₃ m₃ ⊗ spin4Mat n₄ m₄` with `spin4Mat n₁ m₁ ⊗ spin4Mat n₂ m₂`. -/
theorem isSpin4Intertwiner_iff (Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ) :
    IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q ↔ ∀ g : Spin4,
      (spin4Mat n₁ m₁ g ⊗ₖ spin4Mat n₂ m₂ g) *
          Q.submatrix (shuffle n₁ m₁ n₂ m₂) (shuffle n₃ m₃ n₄ m₄) =
        Q.submatrix (shuffle n₁ m₁ n₂ m₂) (shuffle n₃ m₃ n₄ m₄) *
          (spin4Mat n₃ m₃ g ⊗ₖ spin4Mat n₄ m₄ g) := by
  simp only [spin4Mat_kronecker, submatrix_mul_equiv]
  constructor
  · intro h g
    rw [h g]
  · intro h g
    have := congrArg (fun M => M.submatrix (shuffle n₁ m₁ n₂ m₂).symm (shuffle n₃ m₃ n₄ m₄).symm)
      (h g)
    simpa [submatrix_submatrix] using this

/-- **The Spin(4) intertwiner basis** `ι⁺_x ⊗ ι⁻_y`. -/
noncomputable def ivec4 (x y : ℕ) : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ :=
  ivec n₁ n₂ n₃ n₄ x ⊗ₖ ivec m₁ m₂ m₃ m₄ y

/-- The labels `(x, y)` of the Spin(4) intertwiner basis. -/
def channel4 : Finset (ℕ × ℕ) := channel n₁ n₂ n₃ n₄ ×ˢ channel m₁ m₂ m₃ m₄

variable {n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄}

/-- The products `ι⁺_x ⊗ ι⁻_y` are Spin(4) intertwiners. -/
theorem ivec4_isSpin4Intertwiner {p : ℕ × ℕ} (hp : p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄) :
    IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) := by
  rw [channel4, mem_product, mem_channel, mem_channel] at hp
  intro g
  rw [ivec4, ← mul_kronecker_mul, ← mul_kronecker_mul,
    ivec_isIntertwiner hp.1.1 hp.1.2 g.1, ivec_isIntertwiner hp.2.1 hp.2.2 g.2]

/-- **Orthonormality** of the Spin(4) intertwiner basis. -/
theorem hsInner_ivec4 {p p' : ℕ × ℕ} (hp : p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄)
    (hp' : p' ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄) :
    hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p'.1 p'.2) =
      if p = p' then 1 else 0 := by
  rw [channel4, mem_product] at hp hp'
  rw [ivec4, ivec4, hsInner_kronecker, hsInner_ivec hp.1 hp'.1, hsInner_ivec hp.2 hp'.2]
  by_cases h1 : p.1 = p'.1 <;> by_cases h2 : p.2 = p'.2 <;> simp [h1, h2, Prod.ext_iff]

lemma pairMat_one (n m : ℕ) : pairMat n m 1 = 1 := by
  simp [pairMat, spinMat_one]

/-- **Completeness**: every Spin(4) intertwiner expands in the basis `ι⁺_x ⊗ ι⁻_y`. -/
theorem eq_sum_ivec4 {Q : Matrix (Idx n₁ n₂ × Idx m₁ m₂) (Idx n₃ n₄ × Idx m₃ m₄) ℂ}
    (hQ : IsSpin4Intertwiner n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ Q) :
    Q = ∑ p ∈ channel4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄,
      hsInner (ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2) Q •
        ivec4 n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ p.1 p.2 := by
  refine eq_sum_kronecker Q _ (ivec n₁ n₂ n₃ n₄) _ (ivec m₁ m₂ m₃ m₄) (fun c d => ?_)
    (fun x _ => ?_)
  · -- every slice is an intertwiner of the self-dual factor
    refine eq_sum_ivec fun g => ?_
    have h := hQ (g, 1)
    simp only [pairMat_one] at h
    ext a b
    have := congrFun (congrFun h (a, c)) (b, d)
    rw [kron_one_mul_apply, mul_kron_one_apply] at this
    simpa [mul_apply] using this
  · -- every coefficient matrix is an intertwiner of the anti-self-dual factor
    refine eq_sum_ivec fun h => ?_
    have hh := hQ (1, h)
    simp only [pairMat_one] at hh
    ext c d
    have key : ∀ a b, ∑ c', pairMat m₁ m₂ h c c' * Q (a, c') (b, d) =
        ∑ d', Q (a, c) (b, d') * pairMat m₃ m₄ h d' d := fun a b => by
      have := congrFun (congrFun hh (a, c)) (b, d)
      rwa [one_kron_mul_apply, mul_one_kron_apply] at this
    set u := ivec n₁ n₂ n₃ n₄ x
    calc (pairMat m₁ m₂ h * Matrix.of fun c d => hsInner u (Matrix.of fun a b => Q (a, c) (b, d)))
          c d
        = ∑ c', ∑ a, ∑ b, pairMat m₁ m₂ h c c' * (star (u a b) * Q (a, c') (b, d)) := by
          simp only [mul_apply, of_apply, hsInner, Finset.mul_sum]
      _ = ∑ a, ∑ b, star (u a b) * ∑ c', pairMat m₁ m₂ h c c' * Q (a, c') (b, d) := by
          rw [← sum3_reorder]
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c' _ => by ring
      _ = ∑ a, ∑ b, star (u a b) * ∑ d', Q (a, c) (b, d') * pairMat m₃ m₄ h d' d := by
          simp only [key]
      _ = ∑ d', ∑ a, ∑ b, star (u a b) * Q (a, c) (b, d') * pairMat m₃ m₄ h d' d := by
          rw [← sum3_reorder]
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun d' _ => by ring
      _ = ((Matrix.of fun c d => hsInner u (Matrix.of fun a b => Q (a, c) (b, d))) *
          pairMat m₃ m₄ h) c d := by
          simp only [mul_apply, of_apply, hsInner, Finset.sum_mul]

/-! ## E. The 3j symbols and the 4-valent intertwiners `fourJ` -/

/-- The Clebsch–Gordan coefficients in Physlib's 3j symbols (real form of `cgMatrix_eq_threeJ`). -/
lemma cgCoefficient_eq_threeJ' {n m k l a b : ℕ} (hk : k ≤ n) (hk' : k ≤ m)
    (hl : l ≤ n + m - 2 * k) (ha : a ≤ n) (hb : b ≤ m) :
    cgCoefficient n m k l a b = (-1 : ℝ) ^ (n + k + l) * Real.sqrt ((n + m - 2 * k + 1 : ℕ) : ℝ) *
      threeJ n m (n + m - 2 * k) ((n : ℤ) - 2 * a) ((m : ℤ) - 2 * b)
        (-(((n + m - 2 * k : ℕ) : ℤ) - 2 * l)) := by
  have h := cgMatrix_eq_threeJ hk hk' ((⟨a, by omega⟩, ⟨b, by omega⟩) : Idx n m)
    (⟨l, by omega⟩ : Fin (n + m - 2 * k + 1))
  rw [cgMatrix_apply] at h
  exact_mod_cast h

/-- **The coupling matrices in 3j symbols**: `C^{nm}_z(a, b; l) = (-1)^{n+k+l} √(z+1)
(n m z; n - 2a, m - 2b, -(z - 2l))` with `k = (n + m - z)/2` (doubled units). -/
theorem cgz_eq_threeJ (h : Tri n m z) (p : Idx n m) (l : Fin (z + 1)) :
    cgz n m z p l = (((-1 : ℝ) ^ (n + (n + m - z) / 2 + (l : ℕ)) * Real.sqrt ((z + 1 : ℕ) : ℝ) *
      threeJ n m z ((n : ℤ) - 2 * (p.1 : ℕ)) ((m : ℤ) - 2 * (p.2 : ℕ))
        (-((z : ℤ) - 2 * (l : ℕ))) : ℝ) : ℂ) := by
  obtain ⟨k, hk, hk', rfl⟩ := (tri_iff_exists n m z).mp h
  rw [show (n + m - (n + m - 2 * k)) / 2 = k by omega, cgz_sub (by omega)]
  exact cgMatrix_eq_threeJ hk hk' p l

/-- A sum over doubled projections `μ ∈ [-z, z]` whose terms vanish unless `z + μ` is even is a
sum over the basis labels `l ∈ [0, z]`, `μ = 2l - z`. -/
lemma sum_Icc_eq_sum_range (z : ℕ) (g : ℤ → ℝ) (hg : ∀ μ : ℤ, ((z : ℤ) + μ) % 2 ≠ 0 → g μ = 0) :
    ∑ μ ∈ Icc (-(z : ℤ)) z, g μ = ∑ l ∈ range (z + 1), g (2 * l - z) := by
  symm
  refine Finset.sum_bij_ne_zero (fun l _ _ => 2 * (l : ℤ) - z) ?_ ?_ ?_ ?_
  · intro l hl _
    rw [mem_range] at hl
    rw [mem_Icc]
    omega
  · intro l₁ _ _ l₂ _ _ h
    omega
  · intro μ hμ hg0
    rw [mem_Icc] at hμ
    have hpar : ((z : ℤ) + μ) % 2 = 0 := by
      by_contra h
      exact hg0 (hg μ h)
    refine ⟨((z + μ) / 2).toNat, ?_, ?_, ?_⟩
    · rw [mem_range]; omega
    · rw [show 2 * (((z + μ) / 2).toNat : ℤ) - z = μ by omega]; exact hg0
    · omega
  · intro l _ _
    rfl

lemma neg_one_pow_eq_of_mod {X Y : ℕ} (h : X % 2 = Y % 2) : (-1 : ℝ) ^ X = (-1) ^ Y := by
  rw [← Nat.mod_add_div X 2, ← Nat.mod_add_div Y 2, pow_add, pow_add, pow_mul, pow_mul, h]
  simp

lemma fourJ_sign_parity {J₁ J₂ J₃ J₄ z k k' l a₁ a₂ : ℕ} (h1 : z + 2 * k = J₁ + J₂)
    (h2 : z + 2 * k' = J₃ + J₄) (h3 : a₁ + a₂ = k + l) (hl : l ≤ z) :
    (z - l + (J₃ + J₄ + z) / 2) % 2 = (J₂ + J₄ + a₁ + a₂ + (J₁ + k + l + (J₃ + k' + l))) % 2 := by
  omega

/-- **The 4-valent intertwiners `fourJ` are the basis `ι_z` with the incoming links flipped**:
the all-outgoing intertwiner `ι^{(z)}_{m₁ m₂ m₃ m₄}` of `Lightlike.Recoupling.fourJ`, at
`m₁ = J₁ - 2a₁`, `m₂ = J₂ - 2a₂`, `m₃ = -(J₃ - 2b₃)`, `m₄ = -(J₄ - 2b₄)`, is
`(-1)^{J₂+J₄+a₁+a₂} ι_z((a₁, a₂), (b₃, b₄))`. So `fourJ = ± ι_z (ε ⊗ ε)ᵀ` with the invariant forms
`ε(b, b') = (-1)^b [b + b' = J]` of the incoming links, and a sign independent of `z`. -/
theorem fourJ_eq_ivec (hz : z ∈ channel J₁ J₂ J₃ J₄) (p : Idx J₁ J₂) (q : Idx J₃ J₄) :
    ((Lightlike.Recoupling.fourJ J₁ J₂ J₃ J₄ z ((J₁ : ℤ) - 2 * (p.1 : ℕ)) ((J₂ : ℤ) - 2 * (p.2 : ℕ))
        (2 * (q.1 : ℕ) - J₃) (2 * (q.2 : ℕ) - J₄) : ℝ) : ℂ) =
      (-1 : ℂ) ^ (J₂ + J₄ + (p.1 : ℕ) + p.2) * ivec J₁ J₂ J₃ J₄ z p q := by
  rw [mem_channel] at hz
  obtain ⟨h12, h34⟩ := hz
  obtain ⟨k, hk1, hk2, hzk⟩ := (tri_iff_exists _ _ _).mp h12
  obtain ⟨k', hk3, hk4, hzk'⟩ := (tri_iff_exists _ _ _).mp h34
  obtain ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩ := p
  obtain ⟨⟨b₃, hb₃⟩, ⟨b₄, hb₄⟩⟩ := q
  simp only
  have ek : (J₁ + J₂ - z) / 2 = k := by omega
  have ek' : (J₃ + J₄ - z) / 2 = k' := by omega
  -- the right side as a real number
  have hR : ivec J₁ J₂ J₃ J₄ z (⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩) (⟨b₃, hb₃⟩, ⟨b₄, hb₄⟩) =
      (((Real.sqrt ((z : ℝ) + 1))⁻¹ * ∑ l ∈ range (z + 1),
        cgCoefficient J₁ J₂ k l a₁ a₂ * cgCoefficient J₃ J₄ k' l b₃ b₄ : ℝ) : ℂ) := by
    simp only [ivec, Matrix.smul_apply, mul_apply, conjTranspose_apply, cgz, of_apply, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, ek, ek']
    rw [Fin.sum_univ_eq_sum_range (fun l => ((cgCoefficient J₁ J₂ k l a₁ a₂ : ℝ) : ℂ) *
      (cgCoefficient J₃ J₄ k' l b₃ b₄ : ℂ))]
    push_cast
    rfl
  rw [hR, show (-1 : ℂ) ^ (J₂ + J₄ + a₁ + a₂) = (((-1 : ℝ) ^ (J₂ + J₄ + a₁ + a₂) : ℝ) : ℂ) by
    push_cast; rfl, ← Complex.ofReal_mul]
  congr 1
  rw [Lightlike.Recoupling.fourJ]
  rw [sum_Icc_eq_sum_range z _ (fun μ hμ => by
    rw [threeJ_of_not (fun h => hμ (by obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := h; omega)),
      mul_zero, zero_mul])]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  have hz1 : (0 : ℝ) < (z : ℝ) + 1 := by positivity
  have hs : Real.sqrt ((z : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hz1).ne'
  rw [cgCoefficient_eq_threeJ' hk1 hk2 (by omega) (by omega) (by omega),
    cgCoefficient_eq_threeJ' hk3 hk4 (by omega) (by omega) (by omega),
    show J₁ + J₂ - 2 * k = z by omega, show J₃ + J₄ - 2 * k' = z by omega]
  -- the second 3j symbol of `fourJ`, by a cyclic permutation and a sign flip
  have h3 : threeJ z J₃ J₄ (-(2 * (l : ℤ) - z)) (2 * (b₃ : ℤ) - J₃) (2 * (b₄ : ℤ) - J₄) =
      (-1 : ℝ) ^ ((J₃ + J₄ + z) / 2) *
        threeJ J₃ J₄ z ((J₃ : ℤ) - 2 * b₃) ((J₄ : ℤ) - 2 * b₄) (-((z : ℤ) - 2 * l)) := by
    rw [← threeJ_cycle, ← threeJ_neg]
    congr 1 <;> ring
  rw [h3, show (((z : ℤ) - (2 * (l : ℤ) - z)) / 2) = ((z - l : ℕ) : ℤ) by omega, zpow_natCast,
    show (2 * (l : ℤ) - z) = -((z : ℤ) - 2 * l) by ring]
  set A := threeJ J₁ J₂ z ((J₁ : ℤ) - 2 * a₁) ((J₂ : ℤ) - 2 * a₂) (-((z : ℤ) - 2 * l))
  set B := threeJ J₃ J₄ z ((J₃ : ℤ) - 2 * b₃) ((J₄ : ℤ) - 2 * b₄) (-((z : ℤ) - 2 * l))
  by_cases hA : A = 0
  · rw [hA]; ring
  have hadm := adm3_of_threeJ_ne_zero hA
  obtain ⟨hsum, -⟩ := hadm
  have h1 : z + 2 * k = J₁ + J₂ := by clear * - hzk hk1 hk2; omega
  have h2 : z + 2 * k' = J₃ + J₄ := by clear * - hzk' hk3 hk4; omega
  have h3 : a₁ + a₂ = k + l := by clear * - hsum h1; omega
  have hsign : (-1 : ℝ) ^ (z - l) * (-1) ^ ((J₃ + J₄ + z) / 2) =
      (-1) ^ (J₂ + J₄ + a₁ + a₂) * ((-1) ^ (J₁ + k + l) * (-1) ^ (J₃ + k' + l)) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact neg_one_pow_eq_of_mod (fourJ_sign_parity h1 h2 h3 (by omega))
  have hk : (Real.sqrt ((z : ℝ) + 1))⁻¹ * (Real.sqrt ((z : ℝ) + 1) * Real.sqrt ((z : ℝ) + 1)) =
      Real.sqrt ((z : ℝ) + 1) := by
    field_simp
  push_cast
  calc _ = ((-1 : ℝ) ^ (z - l) * (-1) ^ ((J₃ + J₄ + z) / 2)) * Real.sqrt ((z : ℝ) + 1) * A * B := by
        ring
    _ = ((-1) ^ (J₂ + J₄ + a₁ + a₂) * ((-1) ^ (J₁ + k + l) * (-1) ^ (J₃ + k' + l))) *
        ((Real.sqrt ((z : ℝ) + 1))⁻¹ * (Real.sqrt ((z : ℝ) + 1) * Real.sqrt ((z : ℝ) + 1))) *
          A * B := by
        rw [hsign, hk]
    _ = _ := by ring

end Lightlike.Spin4
