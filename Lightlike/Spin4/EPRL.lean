import Lightlike.Spin4.CGBridge
import Lightlike.Spin4.SpinSchur

/-!
# The EPRL map for Immirzi parameter `0 < γ < 1`

The Euclidean EPRL spin-foam model (Engle, Pereira, Rovelli, Livine) imposes the linear simplicity
constraint on Spin(4) = SU(2) × SU(2) data. For a Barbero–Immirzi parameter `0 < γ < 1` and an SU(2)
spin `j`, it uses the Spin(4) representation `(j₊, j₋)` with

`j± = |1 ± γ| j / 2`,

and embeds `V_j` into `V_{j₊} ⊗ V_{j₋}` as the highest spin `j = j₊ + j₋` in the decomposition along
the diagonal SU(2). This file defines the labels and the map and proves its basic properties.

Spins are doubled throughout: `J = 2j`, `n = 2j₊`, `m = 2j₋`, so the EPRL labels are
`n = (1 + γ) J / 2`, `m = (1 - γ) J / 2`, i.e. `n + m = J` and `n - m = γ J`. The label `j₊`
belongs to the first factor of `Spin4 = SU2 × SU2`, which is the self-dual one for the
orientation `(1, i, j, k)` of `ℝ⁴ = ℍ` (`Lightlike/Spin4/SelfDual.lean`).

## Main results

* `isEPRLLabel_iff`, `eprlAdmissible_iff`: `(n, m)` are the EPRL labels of `(γ, J)` exactly when
  `n + m = J` and `n - m = γ J`; the labels are half-integers exactly when `γ J` is a natural
  number `p` with `J + p` even.
* `eprlAdmissible_rat_iff`, `eprlAdmissible_irrational_iff`: for `γ = p/q` in lowest terms the
  admissible `J` are the multiples `J = q t` with `(p + q) t` even; for irrational `γ` only `J = 0`.
* `eprlMap n m = cgMatrix n m 0`, the EPRL map `Y : V_{(n+m)/2} → V_{n/2} ⊗ V_{m/2}`:
  `eprlMap_equivariant` (SU(2)-equivariant), `eprlMap_isometry` (`Yᴴ Y = 1`), the closed form
  `eprlMap_apply`, `Y e_c = Σ_{a+b=c} √(C(n,a) C(m,b) / C(n+m,c)) e_a ⊗ e_b`, `eprlMap_unique`
  (unique up to a scalar) and `mem_range_eprlMap_iff` (its image is the eigenspace of the diagonal
  Casimir with the highest eigenvalue `j(j+1)`).
* `eprlMap_compress_jPlus`: the projection theorem `(n+m) Yᴴ J₊ Y = n L`; hence
  `eprl_weak_simplicity`, `eprl_weak_simplicity_inner`: the linear simplicity constraint
  `K - γ L` vanishes between states of the image, and `weak_simplicity_iff`: on the highest
  component only the EPRL labels have this property.
* `eprl_master_constraint`: `Yᴴ M Y = (1 - γ²) j` for the master constraint
  `M = Σᵢ (Kⁱ - γ Lⁱ)²`; `eprl_not_strong_simplicity`: the constraint does not hold strongly.

## References

* J. Engle, R. Pereira, C. Rovelli, E. Livine, *LQG vertex with finite Immirzi parameter*,
  Nucl. Phys. B 799 (2008) 136, arXiv:0711.0146.
* W. Kamiński, M. Kisielowski, J. Lewandowski, *The EPRL intertwiners and corrected partition
  function*, Class. Quant. Grav. 27 (2010) 165020, arXiv:0912.0540.
-/

open Matrix Finset PhyslibAlpha.Sl2
open scoped Kronecker

namespace Lightlike.Spin4

open SU2

/-! ## A. The EPRL labels -/

/-- The self-dual EPRL spin `j₊ = |1 + γ| j / 2`. -/
noncomputable def jPlus (γ j : ℝ) : ℝ := |1 + γ| * j / 2

/-- The anti-self-dual EPRL spin `j₋ = |1 - γ| j / 2`. -/
noncomputable def jMinus (γ j : ℝ) : ℝ := |1 - γ| * j / 2

/-- A real number is a spin (a half-integer `k/2`, `k ∈ ℕ`). -/
def IsHalfInt (x : ℝ) : Prop := ∃ k : ℕ, x = k / 2

/-- `(n, m)` are the doubled EPRL labels of the doubled spin `J`: `n = 2 j₊`, `m = 2 j₋` for
`j = J/2`. -/
def IsEPRLLabel (γ : ℝ) (J n m : ℕ) : Prop :=
  (n : ℝ) = 2 * jPlus γ ((J : ℝ) / 2) ∧ (m : ℝ) = 2 * jMinus γ ((J : ℝ) / 2)

/-- `(γ, J)` is **EPRL-admissible** when both EPRL labels `j±` of `j = J/2` are spins. -/
def EPRLAdmissible (γ : ℝ) (J : ℕ) : Prop :=
  IsHalfInt (jPlus γ ((J : ℝ) / 2)) ∧ IsHalfInt (jMinus γ ((J : ℝ) / 2))

variable {γ : ℝ} {J n m : ℕ}

/-- **The EPRL labels**: for `0 < γ < 1`, `(n, m)` are the EPRL labels of `J` exactly when
`n + m = J` and `n - m = γ J`. -/
theorem isEPRLLabel_iff (hγ : 0 < γ) (hγ1 : γ < 1) :
    IsEPRLLabel γ J n m ↔ n + m = J ∧ (n : ℝ) - m = γ * J := by
  have h1 : |1 + γ| = 1 + γ := abs_of_pos (by linarith)
  have h2 : |1 - γ| = 1 - γ := abs_of_pos (by linarith)
  simp only [IsEPRLLabel, jPlus, jMinus, h1, h2]
  constructor
  · rintro ⟨hn, hm⟩
    refine ⟨?_, by rw [hn, hm]; ring⟩
    have : (n : ℝ) + m = J := by rw [hn, hm]; ring
    exact_mod_cast this
  · rintro ⟨hs, hd⟩
    have hs' : (n : ℝ) + m = J := by exact_mod_cast hs
    constructor
    · linear_combination (1 / 2 : ℝ) * hs' + (1 / 2 : ℝ) * hd
    · linear_combination (1 / 2 : ℝ) * hs' - (1 / 2 : ℝ) * hd

/-- The EPRL labels of `J` add up to `J`. -/
lemma IsEPRLLabel.add_eq (hγ : 0 < γ) (hγ1 : γ < 1) (h : IsEPRLLabel γ J n m) : n + m = J :=
  ((isEPRLLabel_iff hγ hγ1).mp h).1

/-- Admissibility means that EPRL labels exist. -/
lemma eprlAdmissible_iff_exists : EPRLAdmissible γ J ↔ ∃ n m, IsEPRLLabel γ J n m := by
  constructor
  · rintro ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
    exact ⟨n, m, by rw [hn]; ring, by rw [hm]; ring⟩
  · rintro ⟨n, m, hn, hm⟩
    exact ⟨⟨n, by rw [hn]; ring⟩, ⟨m, by rw [hm]; ring⟩⟩

/-- **The admissible spins**: for `0 < γ < 1`, the EPRL labels `j±` of `j = J/2` are spins exactly
when `γ J` is a natural number `p` with `J + p` even. -/
theorem eprlAdmissible_iff (hγ : 0 < γ) (hγ1 : γ < 1) :
    EPRLAdmissible γ J ↔ ∃ p : ℕ, γ * J = p ∧ Even (J + p) := by
  rw [eprlAdmissible_iff_exists]
  constructor
  · rintro ⟨n, m, h⟩
    obtain ⟨hs, hd⟩ := (isEPRLLabel_iff hγ hγ1).mp h
    have hmn : m ≤ n := by
      have : (0 : ℝ) ≤ γ * J := by positivity
      have : (m : ℝ) ≤ n := by linarith
      exact_mod_cast this
    refine ⟨n - m, by rw [← hd, Nat.cast_sub hmn], ⟨n, by omega⟩⟩
  · rintro ⟨p, hp, t, ht⟩
    have hpJ : p ≤ J := by
      have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      have : (p : ℝ) ≤ J := by rw [← hp]; nlinarith
      exact_mod_cast this
    refine ⟨t, J - t, (isEPRLLabel_iff hγ hγ1).mpr ⟨by omega, ?_⟩⟩
    rw [hp, Nat.cast_sub (by omega)]
    have : (J : ℝ) + p = t + t := by exact_mod_cast ht
    linarith

/-- **Admissible spins for rational `γ = p/q`** in lowest terms: `J` must be a multiple `q t`,
with `(p + q) t` even (so every multiple of `q` when `p` and `q` are both odd, and the even
multiples of `q` otherwise). -/
theorem eprlAdmissible_rat_iff {p q : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q) :
    EPRLAdmissible ((p : ℝ) / q) J ↔ ∃ t : ℕ, J = q * t ∧ Even ((p + q) * t) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast hp.trans hpq
  rw [eprlAdmissible_iff (by positivity) (by rw [div_lt_one hq]; exact_mod_cast hpq)]
  constructor
  · rintro ⟨r, hr, hev⟩
    have hnat : p * J = q * r := by
      have : (p : ℝ) * J = q * r := by rw [← hr]; field_simp
      exact_mod_cast this
    obtain ⟨t, rfl⟩ : q ∣ J := (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcop))
      ⟨r, by rw [hnat]⟩
    have hrt : r = p * t := by
      have hq0 : 0 < q := hp.trans hpq
      have : q * (p * t) = q * r := by rw [← hnat]; ring
      exact (Nat.eq_of_mul_eq_mul_left hq0 this).symm
    refine ⟨t, rfl, ?_⟩
    rw [hrt] at hev
    rwa [show (p + q) * t = q * t + p * t by ring]
  · rintro ⟨t, rfl, hev⟩
    refine ⟨p * t, ?_, by rwa [show q * t + p * t = (p + q) * t by ring]⟩
    push_cast
    field_simp

/-- **Irrational `γ`**: only `J = 0` is admissible. -/
theorem eprlAdmissible_irrational_iff (hγ : 0 < γ) (hγ1 : γ < 1) (hirr : Irrational γ) :
    EPRLAdmissible γ J ↔ J = 0 := by
  rw [eprlAdmissible_iff hγ hγ1]
  constructor
  · rintro ⟨p, hp, -⟩
    by_contra hJ
    have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
    exact hirr ⟨(p : ℚ) / J, by push_cast; field_simp; linarith⟩
  · rintro rfl
    exact ⟨0, by simp, by simp⟩

/-! ## B. The EPRL map -/

/-- **The EPRL map** `Y : V_{(n+m)/2} → V_{n/2} ⊗ V_{m/2}`: the embedding of the highest spin
`(n+m)/2 = j₊ + j₋` of the diagonal Clebsch–Gordan decomposition (`cgMatrix n m 0`). Rows are the
product states `e_a ⊗ e_b`, columns the states `e_c` of spin `(n+m)/2`. -/
noncomputable def eprlMap (n m : ℕ) : Matrix (Idx n m) (Fin (n + m + 1)) ℂ := cgMatrix n m 0

lemma eprlMap_eq_cgMatrix : eprlMap n m = cgMatrix n m 0 := rfl

/-- **The EPRL map is SU(2)-equivariant**: `(D^{j₊}(g) ⊗ D^{j₋}(g)) Y = Y D^{j}(g)`. -/
theorem eprlMap_equivariant (g : SU2) :
    (spinMat n g ⊗ₖ spinMat m g) * eprlMap n m = eprlMap n m * spinMat (n + m) g :=
  cgMatrix_equivariant (Nat.zero_le _) (Nat.zero_le _) g

/-- **The EPRL map is an isometry**: `Yᴴ Y = 1`. -/
theorem eprlMap_isometry : (eprlMap n m)ᴴ * eprlMap n m = 1 :=
  cgMatrix_isometry (Nat.zero_le _) (Nat.zero_le _)

/-- The EPRL map intertwines the diagonal Lie-algebra action. -/
theorem eprlMap_lie {X : Matrix (Fin 2) (Fin 2) ℂ} (h : X 1 1 = -X 0 0) :
    dDiag n m X * eprlMap n m = eprlMap n m * dSpin (n + m) X :=
  cgMatrix_lie (Nat.zero_le _) (Nat.zero_le _) h

/-! ## C. The closed form -/

/-- `cgSum` at `k = 0`. -/
lemma cgSum_zero (c a : ℕ) :
    cgSum n m 0 c a = (m.factorial * n.factorial * c.choose a : ℕ) := by
  simp [cgSum, cgCoeff]

/-- **The closed form of the EPRL map**:
`⟨e_a ⊗ e_b | Y e_c⟩ = √(C(n,a) C(m,b) / C(n+m,c))` if `a + b = c`, and `0` otherwise. -/
theorem eprlMap_apply (p : Idx n m) (c : Fin (n + m + 1)) :
    eprlMap n m p c = if (p.1 : ℕ) + p.2 = c then
      ((Real.sqrt (((n.choose p.1 * m.choose p.2 : ℕ) : ℝ) / ((n + m).choose c : ℕ)) : ℝ) : ℂ)
      else 0 := by
  rw [eprlMap, cgMatrix_apply]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  obtain ⟨c, hc⟩ := c
  simp only
  have ha' : a ≤ n := by omega
  have hb' : b ≤ m := by omega
  have hc' : c ≤ n + m - 2 * 0 := by omega
  by_cases h : a + b = c
  · rw [ite_eq_left h]
    congr 1
    rw [cgCoefficient_closed (Nat.zero_le _) (Nat.zero_le _) hc' ha' hb' (by omega), cgSum_zero]
    subst h
    simp only [Nat.mul_zero, Nat.sub_zero, normSq, hwNormNum, Nat.factorial_zero, one_mul]
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_factorial_mul_choose]
    have hcab := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rw [show a + b - a = b by omega] at hcab
    set A : ℝ := ((m.factorial * n.factorial * (a + b).choose a : ℕ) : ℝ) with hA
    have hA0 : 0 ≤ A := Nat.cast_nonneg _
    rw [← Real.sqrt_sq hA0, ← Real.sqrt_mul (sq_nonneg _)]
    congr 1
    have hf : ∀ k : ℕ, (k.factorial : ℝ) ≠ 0 := fun k => by exact_mod_cast (Nat.factorial_pos k).ne'
    have hch : ((n + m).choose (a + b) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hch2 : (((a + b).choose a : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have hcab' : (((a + b).choose a : ℕ) : ℝ) * a.factorial * b.factorial = (a + b).factorial := by
      exact_mod_cast hcab
    rw [hA]
    push_cast
    rw [← hcab']
    field_simp
  · rw [ite_eq_right h]
    have hnm : 0 < n + m := by omega
    rw [cgCoefficient_eq_zero_of_ne hnm (Nat.zero_le _) (Nat.zero_le _) (by omega)]
    simp

/-- **The EPRL map commutes with the flips** `a ↦ n - a` (the invariant forms `ε` of SU(2)):
`⟨e_{n-a} ⊗ e_{m-b} | Y e_{n+m-c}⟩ = ⟨e_a ⊗ e_b | Y e_c⟩`, i.e. `(ε ⊗ ε) Y = Y ε` up to the
signs `(-1)^{a+b} = (-1)^c` of the forms. -/
theorem eprlMap_flip (p : Idx n m) (c : Fin (n + m + 1)) :
    eprlMap n m (Fin.rev p.1, Fin.rev p.2) (Fin.rev c) = eprlMap n m p c := by
  rw [eprlMap_apply, eprlMap_apply]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
  obtain ⟨c, hc⟩ := c
  simp only [Fin.val_rev]
  by_cases h : a + b = c
  · rw [ite_eq_left (by omega), ite_eq_left h, show n + 1 - (a + 1) = n - a by omega,
      show m + 1 - (b + 1) = m - b by omega, show n + m + 1 - (c + 1) = n + m - c by omega,
      Nat.choose_symm (by omega), Nat.choose_symm (by omega), Nat.choose_symm (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-! ## D. Uniqueness and the image -/

variable {k : ℕ}

/-- The adjoint of a Clebsch–Gordan matrix is equivariant as well:
`Cᴴ (D^{n/2}(g) ⊗ D^{m/2}(g)) = D^{(n+m)/2-k}(g) Cᴴ`. -/
theorem cgMatrix_conjTranspose_equivariant (hk : k ≤ n) (hk' : k ≤ m) (g : SU2) :
    (cgMatrix n m k)ᴴ * (spinMat n g ⊗ₖ spinMat m g) =
      spinMat (n + m - 2 * k) g * (cgMatrix n m k)ᴴ := by
  have h := congrArg conjTranspose (cgMatrix_equivariant hk hk' (star g))
  simp only [conjTranspose_mul, conjTranspose_kronecker, spinMat_conjTranspose,
    specialUnitaryGroup.coe_star, star_eq_conjTranspose, conjTranspose_conjTranspose] at h
  exact h

/-- **The EPRL map is the unique equivariant map up to a scalar**: every SU(2)-equivariant
`T : V_{(n+m)/2} → V_{n/2} ⊗ V_{m/2}` is `c Y`. -/
theorem eprlMap_unique {T : Matrix (Idx n m) (Fin (n + m + 1)) ℂ}
    (hT : ∀ g : SU2, (spinMat n g ⊗ₖ spinMat m g) * T = T * spinMat (n + m) g) :
    ∃ c : ℂ, T = c • eprlMap n m := by
  have hS : ∀ k ∈ range (min n m + 1), ∀ g : SU2,
      spinMat (n + m - 2 * k) g * ((cgMatrix n m k)ᴴ * T) =
        ((cgMatrix n m k)ᴴ * T) * spinMat (n + m) g := fun k hk g => by
    have hk' : k ≤ min n m := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [← Matrix.mul_assoc, ← cgMatrix_conjTranspose_equivariant (hk'.trans (min_le_left n m))
      (hk'.trans (min_le_right n m)), Matrix.mul_assoc, hT g, Matrix.mul_assoc]
  obtain ⟨c, hc⟩ := spin_intertwiner_eq_smul (N := n + m) (T := (cgMatrix n m 0)ᴴ * T)
    (hS 0 (by simp))
  refine ⟨c, ?_⟩
  calc T = (∑ k ∈ range (min n m + 1), cgMatrix n m k * (cgMatrix n m k)ᴴ) * T := by
        rw [cgMatrix_complete, Matrix.one_mul]
    _ = ∑ k ∈ range (min n m + 1), cgMatrix n m k * ((cgMatrix n m k)ᴴ * T) := by
        rw [Matrix.sum_mul]
        exact Finset.sum_congr rfl fun k _ => Matrix.mul_assoc _ _ _
    _ = cgMatrix n m 0 * ((cgMatrix n m 0)ᴴ * T) := by
        refine Finset.sum_eq_single 0 (fun k hk hk0 => ?_) (fun h => absurd (by simp) h)
        have hk' : k ≤ min n m := Nat.lt_succ_iff.mp (mem_range.mp hk)
        rw [spin_intertwiner_eq_zero (N := n + m) (M := n + m - 2 * k) (by omega) (hS k hk),
          Matrix.mul_zero]
    _ = c • eprlMap n m := by
        rw [show (cgMatrix n m 0)ᴴ * T = c • (1 : Matrix (Fin (n + m + 1)) (Fin (n + m + 1)) ℂ)
          from hc, Matrix.mul_smul, Matrix.mul_one]
        rfl

/-- The raising and lowering operators are adjoint: `(dSpin n E)ᴴ = dSpin n F`. -/
lemma dSpin_E_conjTranspose : (dSpin n matE)ᴴ = dSpin n matF := by
  ext i j
  rw [conjTranspose_apply, dSpin_E_apply, dSpin_F_apply]
  split_ifs <;> simp [Complex.conj_ofReal]

/-- `(dSpin n F)ᴴ = dSpin n E`. -/
lemma dSpin_F_conjTranspose : (dSpin n matF)ᴴ = dSpin n matE := by
  rw [← dSpin_E_conjTranspose, conjTranspose_conjTranspose]

/-- The weight operator is Hermitian. -/
lemma dSpin_H_conjTranspose : (dSpin n matH)ᴴ = dSpin n matH := by
  ext i j
  rw [conjTranspose_apply, dSpin_H_apply, dSpin_H_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

lemma dDiag_E_conjTranspose : (dDiag n m matE)ᴴ = dDiag n m matF := by
  simp [dDiag, conjTranspose_kronecker, dSpin_E_conjTranspose]

lemma dDiag_F_conjTranspose : (dDiag n m matF)ᴴ = dDiag n m matE := by
  simp [dDiag, conjTranspose_kronecker, dSpin_F_conjTranspose]

lemma dDiag_H_conjTranspose : (dDiag n m matH)ᴴ = dDiag n m matH := by
  simp [dDiag, conjTranspose_kronecker, dSpin_H_conjTranspose]

/-- The rotation-invariant contraction `A · B = Σᵢ Aᵢ Bᵢ` of two vector operators, written with
their values on the basis `E = J₊`, `F = J₋`, `H = 2 J_z` of `sl₂(ℂ)`:
`A · B = ½ (A(E) B(F) + A(F) B(E)) + ¼ A(H) B(H)`. -/
noncomputable def vdot {ι : Type*} [Fintype ι]
    (A B : Matrix (Fin 2) (Fin 2) ℂ → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (A matE * B matF + A matF * B matE) + (1 / 4 : ℂ) • (A matH * B matH)

/-- The Casimir value `(N/2)(N/2 + 1) = j(j+1)` of spin `j = N/2`. -/
noncomputable def casVal (N : ℕ) : ℂ := (N : ℂ) / 2 * ((N : ℂ) / 2 + 1)

/-- The Casimir of the spin-`N/2` representation, in `vdot` form. -/
lemma vdot_dSpin (N : ℕ) : vdot (dSpin N) (dSpin N) = casVal N • 1 := casimir_eq N

/-- The Casimir `L²` of the diagonal SU(2) on `V_{n/2} ⊗ V_{m/2}`. -/
noncomputable def casDiag (n m : ℕ) : Matrix (Idx n m) (Idx n m) ℂ := vdot (dDiag n m) (dDiag n m)

lemma casDiag_conjTranspose : (casDiag n m)ᴴ = casDiag n m := by
  simp only [casDiag, vdot, conjTranspose_add, conjTranspose_smul, conjTranspose_mul,
    dDiag_E_conjTranspose, dDiag_F_conjTranspose, dDiag_H_conjTranspose]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have h4 : star (1 / 4 : ℂ) = 1 / 4 := by simp
  rw [h2, h4, add_comm (dDiag n m matE * dDiag n m matF)]

/-- Intertwining passes to the contraction: if `A(X) C = C B(X)` for `X = E, F, H`, then
`(A · A) C = C (B · B)`. -/
lemma vdot_mul_of_intertwine {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix (Fin 2) (Fin 2) ℂ → Matrix ι ι ℂ} {B : Matrix (Fin 2) (Fin 2) ℂ → Matrix κ κ ℂ}
    {C : Matrix ι κ ℂ} (hE : A matE * C = C * B matE) (hF : A matF * C = C * B matF)
    (hH : A matH * C = C * B matH) : vdot A A * C = C * vdot B B := by
  have h1 : A matE * A matF * C = C * (B matE * B matF) := by
    rw [Matrix.mul_assoc, hF, ← Matrix.mul_assoc, hE, Matrix.mul_assoc]
  have h2 : A matF * A matE * C = C * (B matF * B matE) := by
    rw [Matrix.mul_assoc, hE, ← Matrix.mul_assoc, hF, Matrix.mul_assoc]
  have h3 : A matH * A matH * C = C * (B matH * B matH) := by
    rw [Matrix.mul_assoc, hH, ← Matrix.mul_assoc, hH, Matrix.mul_assoc]
  simp only [vdot, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, h1, h2, h3]

/-- The diagonal Casimir acts on the spin-`(n+m)/2 - k` component as `j(j+1)`. -/
theorem casDiag_mul_cgMatrix (hk : k ≤ n) (hk' : k ≤ m) :
    casDiag n m * cgMatrix n m k = casVal (n + m - 2 * k) • cgMatrix n m k := by
  rw [casDiag, vdot_mul_of_intertwine (cgMatrix_E hk hk') (cgMatrix_F hk hk') (cgMatrix_H hk hk'),
    vdot_dSpin, Matrix.mul_smul, Matrix.mul_one]

lemma conjTranspose_cgMatrix_mul_casDiag (hk : k ≤ n) (hk' : k ≤ m) :
    (cgMatrix n m k)ᴴ * casDiag n m = casVal (n + m - 2 * k) • (cgMatrix n m k)ᴴ := by
  have h := congrArg conjTranspose (casDiag_mul_cgMatrix hk hk')
  rw [conjTranspose_mul, casDiag_conjTranspose, conjTranspose_smul] at h
  rw [h]
  congr 1
  simp [casVal]

lemma casVal_injective {N N' : ℕ} (h : casVal N = casVal N') : N = N' := by
  have h' : ((N * (N + 2) : ℕ) : ℂ) = ((N' * (N' + 2) : ℕ) : ℂ) := by
    push_cast
    simp only [casVal] at h
    linear_combination (4 : ℂ) * h
  have h'' := Nat.cast_injective h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have := Nat.mul_lt_mul'' hl (by omega : N + 2 < N' + 2); omega
  · have := Nat.mul_lt_mul'' hl (by omega : N' + 2 < N + 2); omega

/-- **The image of the EPRL map is the spin-`(n+m)/2` component**: a vector of
`V_{n/2} ⊗ V_{m/2}` lies in the range of `Y` exactly when it is an eigenvector of the diagonal
Casimir `L²` with eigenvalue `j(j+1)`, `j = (n+m)/2` (the highest one). -/
theorem mem_range_eprlMap_iff (v : Idx n m → ℂ) :
    (∃ w, v = eprlMap n m *ᵥ w) ↔ casDiag n m *ᵥ v = casVal (n + m) • v := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [mulVec_mulVec, eprlMap, casDiag_mul_cgMatrix (Nat.zero_le _) (Nat.zero_le _), smul_mulVec]
    rfl
  · intro hv
    refine ⟨(eprlMap n m)ᴴ *ᵥ v, ?_⟩
    have hvan : ∀ k ∈ range (min n m + 1), k ≠ 0 → (cgMatrix n m k)ᴴ *ᵥ v = 0 := by
      intro k hk hk0
      have hk' : k ≤ min n m := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have h1 := congrArg (fun u => (cgMatrix n m k)ᴴ *ᵥ u) hv
      simp only [mulVec_mulVec, conjTranspose_cgMatrix_mul_casDiag (hk'.trans (min_le_left n m))
        (hk'.trans (min_le_right n m)), smul_mulVec, mulVec_smul] at h1
      have hne : casVal (n + m - 2 * k) - casVal (n + m) ≠ 0 :=
        sub_ne_zero.mpr fun h => by have := casVal_injective h; omega
      have h2 : (casVal (n + m - 2 * k) - casVal (n + m)) • ((cgMatrix n m k)ᴴ *ᵥ v) = 0 := by
        rw [sub_smul, h1, sub_self]
      exact (smul_eq_zero.mp h2).resolve_left hne
    calc v = (∑ k ∈ range (min n m + 1), cgMatrix n m k * (cgMatrix n m k)ᴴ) *ᵥ v := by
          rw [cgMatrix_complete, one_mulVec]
      _ = ∑ k ∈ range (min n m + 1), cgMatrix n m k *ᵥ ((cgMatrix n m k)ᴴ *ᵥ v) := by
          rw [Matrix.sum_mulVec]
          exact Finset.sum_congr rfl fun k _ => (mulVec_mulVec _ _ _).symm
      _ = cgMatrix n m 0 *ᵥ ((cgMatrix n m 0)ᴴ *ᵥ v) := by
          refine Finset.sum_eq_single 0 (fun k hk hk0 => ?_) (fun h => absurd (by simp) h)
          rw [hvan k hk hk0, mulVec_zero]
      _ = eprlMap n m *ᵥ ((eprlMap n m)ᴴ *ᵥ v) := rfl

/-! ## E. The linear simplicity constraint holds weakly on the image -/

/-- The self-dual generators `J₊(X) = X ⊗ 1` on `V_{j₊} ⊗ V_{j₋}`. -/
noncomputable def jPlusOp (n m : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Idx n m) (Idx n m) ℂ :=
  dSpin n X ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)

/-- The anti-self-dual generators `J₋(X) = 1 ⊗ X` on `V_{j₊} ⊗ V_{j₋}`. -/
noncomputable def jMinusOp (n m : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Idx n m) (Idx n m) ℂ :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ dSpin m X

/-- The boost generators `K = J₊ - J₋` (the rotation generators are `L = J₊ + J₋ = dDiag`). -/
noncomputable def boostOp (n m : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Idx n m) (Idx n m) ℂ :=
  jPlusOp n m X - jMinusOp n m X

/-- **The linear simplicity constraint** `K - γ L` (for `γ < 1` in the convention where
`j± = |1 ± γ| j / 2`). -/
noncomputable def simplicityOp (γ : ℝ) (n m : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Idx n m) (Idx n m) ℂ :=
  boostOp n m X - (γ : ℂ) • dDiag n m X

lemma dDiag_eq_add (X : Matrix (Fin 2) (Fin 2) ℂ) : dDiag n m X = jPlusOp n m X + jMinusOp n m X :=
  rfl

/-- `K - γ L = (1 - γ) J₊ - (1 + γ) J₋`. -/
lemma simplicityOp_eq (X : Matrix (Fin 2) (Fin 2) ℂ) :
    simplicityOp γ n m X =
      ((1 - γ : ℝ) : ℂ) • jPlusOp n m X - ((1 + γ : ℝ) : ℂ) • jMinusOp n m X := by
  simp only [simplicityOp, boostOp, dDiag_eq_add]
  push_cast
  module

lemma jPlusOp_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    jPlusOp n m (X + Y) = jPlusOp n m X + jPlusOp n m Y := by
  simp [jPlusOp, dSpin_add, add_kronecker]

lemma jPlusOp_smul (c : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    jPlusOp n m (c • X) = c • jPlusOp n m X := by
  simp [jPlusOp, dSpin_smul, smul_kronecker]

/-- The weight operator is diagonal: `H e_a = (n - 2a) e_a`. -/
lemma dSpin_H_eq_diagonal :
    dSpin n matH = diagonal fun i : Fin (n + 1) => (n : ℂ) - 2 * (i : ℕ) := by
  ext i j
  rw [dSpin_H_apply, diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `[H, E] = 2E` in every spin representation. -/
lemma dSpin_bracket_HE :
    dSpin n matH * dSpin n matE - dSpin n matE * dSpin n matH = (2 : ℂ) • dSpin n matE := by
  ext i j
  rw [dSpin_H_eq_diagonal, Matrix.sub_apply, diagonal_mul, mul_diagonal, Matrix.smul_apply,
    dSpin_E_apply]
  split_ifs with h
  · rw [h]; push_cast; ring
  · simp

/-- `[H, F] = -2F` in every spin representation. -/
lemma dSpin_bracket_HF :
    dSpin n matH * dSpin n matF - dSpin n matF * dSpin n matH = (-2 : ℂ) • dSpin n matF := by
  ext i j
  rw [dSpin_H_eq_diagonal, Matrix.sub_apply, diagonal_mul, mul_diagonal, Matrix.smul_apply,
    dSpin_F_apply]
  split_ifs with h
  · rw [h]; push_cast; ring
  · simp

lemma sub_kron {ι κ μ ν : Type*} (A B : Matrix ι κ ℂ) (C : Matrix μ ν ℂ) :
    (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp [kroneckerMap_apply, sub_mul]

/-- `[J₊(H), L(E)] = 2 J₊(E)`. -/
lemma jPlusOp_bracket_E :
    jPlusOp n m matH * dDiag n m matE - dDiag n m matE * jPlusOp n m matH =
      (2 : ℂ) • jPlusOp n m matE := by
  simp only [jPlusOp, dDiag, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul]
  rw [← smul_kronecker, ← dSpin_bracket_HE, sub_kron]
  abel

/-- `[J₊(H), L(F)] = -2 J₊(F)`. -/
lemma jPlusOp_bracket_F :
    jPlusOp n m matH * dDiag n m matF - dDiag n m matF * jPlusOp n m matH =
      (-2 : ℂ) • jPlusOp n m matF := by
  simp only [jPlusOp, dDiag, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul]
  rw [← smul_kronecker, ← dSpin_bracket_HF, sub_kron]
  abel

/-- `Yᴴ L(X) = X^{(n+m)} Yᴴ` for `X = E`. -/
lemma conjTranspose_eprlMap_mul_E :
    (eprlMap n m)ᴴ * dDiag n m matE = dSpin (n + m) matE * (eprlMap n m)ᴴ := by
  have h := congrArg conjTranspose (cgMatrix_F (n := n) (m := m) (Nat.zero_le _) (Nat.zero_le _))
  rw [conjTranspose_mul, conjTranspose_mul, dDiag_F_conjTranspose, dSpin_F_conjTranspose] at h
  exact h

/-- `Yᴴ L(F) = F^{(n+m)} Yᴴ`. -/
lemma conjTranspose_eprlMap_mul_F :
    (eprlMap n m)ᴴ * dDiag n m matF = dSpin (n + m) matF * (eprlMap n m)ᴴ := by
  have h := congrArg conjTranspose (cgMatrix_E (n := n) (m := m) (Nat.zero_le _) (Nat.zero_le _))
  rw [conjTranspose_mul, conjTranspose_mul, dDiag_E_conjTranspose, dSpin_E_conjTranspose] at h
  exact h

/-- The product of two entries of `Y` in the same row. -/
lemma star_eprlMap_mul (p : Idx n m) (c c' : Fin (n + m + 1)) :
    star (eprlMap n m p c) * eprlMap n m p c' =
      if (p.1 : ℕ) + p.2 = c ∧ c = c' then
        (((n.choose p.1 * m.choose p.2 : ℕ) : ℂ) / ((n + m).choose c : ℕ)) else 0 := by
  rw [eprlMap_apply, eprlMap_apply]
  by_cases h1 : (p.1 : ℕ) + p.2 = c
  · by_cases h2 : (p.1 : ℕ) + p.2 = c'
    · have hcc : c = c' := Fin.ext (h1.symm.trans h2)
      subst hcc
      rw [ite_eq_left h1, ite_eq_left ⟨h1, rfl⟩, Complex.star_def,
        Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      rfl
    · have hcc : c ≠ c' := fun h => h2 (h ▸ h1)
      rw [ite_eq_right h2, mul_zero, ite_eq_right (fun h => hcc h.2)]
  · rw [ite_eq_right h1, star_zero, zero_mul, ite_eq_right (fun h => h1 h.1)]

/-- A sum over product states with fixed total weight `a + b = c` is a sum over the
antidiagonal. -/
lemma sum_idx_antidiagonal (c : ℕ) (G : ℕ → ℕ → ℂ) (hG : ∀ a b, G a b ≠ 0 → a ≤ n ∧ b ≤ m) :
    ∑ p : Idx n m, (if (p.1 : ℕ) + p.2 = c then G p.1 p.2 else 0) =
      ∑ ij ∈ antidiagonal c, G ij.1 ij.2 := by
  refine Finset.sum_bij_ne_zero (fun p _ _ => ((p.1 : ℕ), (p.2 : ℕ))) ?_ ?_ ?_ ?_
  · intro p _ hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    by_contra h
    exact hp (ite_eq_right h)
  · intro p _ _ q _ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  · intro ij hij hG0
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    obtain ⟨ha, hb⟩ := hG _ _ hG0
    refine ⟨(⟨ij.1, by omega⟩, ⟨ij.2, by omega⟩), mem_univ _, ?_, rfl⟩
    simp only
    rw [ite_eq_left hij]
    exact hG0
  · intro p _ hp
    by_cases h : (p.1 : ℕ) + p.2 = c
    · rw [ite_eq_left h]
    · exact absurd (ite_eq_right h) hp

/-- The first moment of the hypergeometric distribution:
`(n + m) Σ_{a+b=c} a C(n,a) C(m,b) = n c C(n+m, c)`. -/
lemma sum_antidiagonal_mul_choose (n m c : ℕ) :
    (n + m) * ∑ ij ∈ antidiagonal c, ij.1 * n.choose ij.1 * m.choose ij.2 =
      n * c * (n + m).choose c := by
  rcases c with _ | c
  · simp
  rw [Finset.Nat.sum_antidiagonal_succ]
  rcases n with _ | n
  · simp
  have h1 : ∀ ij : ℕ × ℕ, (ij.1 + 1) * (n + 1).choose (ij.1 + 1) * m.choose ij.2 =
      (n + 1) * (n.choose ij.1 * m.choose ij.2) := fun ij => by
    have := Nat.add_one_mul_choose_eq n ij.1
    rw [show (ij.1 + 1) * (n + 1).choose (ij.1 + 1) = (n + 1).choose (ij.1 + 1) * (ij.1 + 1)
      from Nat.mul_comm _ _, ← this]
    ring
  simp only [zero_mul, zero_add, h1, ← Finset.mul_sum]
  rw [← Nat.add_choose_eq]
  have h2 := Nat.add_one_mul_choose_eq (n + m) c
  rw [show n + 1 + m = n + m + 1 by ring]
  calc (n + m + 1) * ((n + 1) * (n + m).choose c)
      = (n + 1) * ((n + m + 1) * (n + m).choose c) := by ring
    _ = (n + 1) * (c + 1) * (n + m + 1).choose (c + 1) := by rw [h2]; ring

/-- **The weight part of the projection theorem**: `(n+m) Yᴴ (H ⊗ 1) Y = n H^{(n+m)}`. -/
lemma eprlMap_compress_jPlus_H :
    ((n + m : ℕ) : ℂ) • ((eprlMap n m)ᴴ * jPlusOp n m matH * eprlMap n m) =
      (n : ℂ) • dSpin (n + m) matH := by
  have hP : jPlusOp n m matH = diagonal fun p : Idx n m => (n : ℂ) - 2 * (p.1 : ℕ) := by
    ext p q
    simp only [jPlusOp, kroneckerMap_apply, dSpin_H_apply, one_apply, diagonal_apply,
      Prod.ext_iff]
    by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2]
  ext c c'
  rw [hP, Matrix.smul_apply, Matrix.smul_apply, dSpin_H_eq_diagonal, diagonal_apply, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, smul_eq_mul]
  have hterm : ∀ p : Idx n m, star (eprlMap n m p c) * ((n : ℂ) - 2 * (p.1 : ℕ)) *
      eprlMap n m p c' = if (p.1 : ℕ) + p.2 = c ∧ c = c' then
        ((n : ℂ) - 2 * (p.1 : ℕ)) * (((n.choose p.1 * m.choose p.2 : ℕ) : ℂ) /
          ((n + m).choose c : ℕ)) else 0 := fun p => by
    rw [mul_comm (star _), mul_assoc, star_eprlMap_mul, mul_ite, mul_zero]
  simp only [hterm]
  by_cases hcc : c = c'
  swap
  · simp [hcc]
  subst hcc
  simp only [and_true, ↓reduceIte]
  rw [sum_idx_antidiagonal (c : ℕ) (fun a b => ((n : ℂ) - 2 * a) *
    (((n.choose a * m.choose b : ℕ) : ℂ) / ((n + m).choose c : ℕ)))]
  swap
  · intro a b h
    have h' : n.choose a * m.choose b ≠ 0 := fun h0 => h (by simp [h0])
    refine ⟨?_, ?_⟩
    · by_contra ha
      exact h' (by rw [Nat.choose_eq_zero_of_lt (by omega : n < a)]; simp)
    · by_contra hb
      exact h' (by rw [Nat.choose_eq_zero_of_lt (by omega : m < b)]; simp)
  have hch : (((n + m).choose c : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.mp c.2)).ne'
  have hV : ∑ ij ∈ antidiagonal (c : ℕ), ((n.choose ij.1 * m.choose ij.2 : ℕ) : ℂ) =
      ((n + m).choose c : ℕ) := by
    rw [Nat.add_choose_eq]; push_cast; rfl
  have hM : ((n + m : ℕ) : ℂ) * ∑ ij ∈ antidiagonal (c : ℕ),
      ((ij.1 * n.choose ij.1 * m.choose ij.2 : ℕ) : ℂ) = (n * c * (n + m).choose c : ℕ) := by
    rw [← Nat.cast_sum, ← Nat.cast_mul, sum_antidiagonal_mul_choose]
  have hsplit : ∑ ij ∈ antidiagonal (c : ℕ), ((n : ℂ) - 2 * (ij.1 : ℕ)) *
      (((n.choose ij.1 * m.choose ij.2 : ℕ) : ℂ) / ((n + m).choose c : ℕ)) =
      ((n : ℂ) * ∑ ij ∈ antidiagonal (c : ℕ), ((n.choose ij.1 * m.choose ij.2 : ℕ) : ℂ) -
        2 * ∑ ij ∈ antidiagonal (c : ℕ), ((ij.1 * n.choose ij.1 * m.choose ij.2 : ℕ) : ℂ)) /
        ((n + m).choose c : ℕ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun ij _ => ?_
    push_cast
    ring
  rw [hsplit, hV]
  push_cast at hM ⊢
  field_simp
  linear_combination (-2 : ℂ) * hM

/-- **The projection theorem on the image of `Y`**: `(n+m) Yᴴ J₊(X) Y = n X^{(n+m)}` for every
traceless `X`, i.e. on the image `J₊ = (j₊/j) L`. -/
theorem eprlMap_compress_jPlus {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X 1 1 = -X 0 0) :
    ((n + m : ℕ) : ℂ) • ((eprlMap n m)ᴴ * jPlusOp n m X * eprlMap n m) =
      (n : ℂ) • dSpin (n + m) X := by
  set Y := eprlMap n m
  set N : ℂ := ((n + m : ℕ) : ℂ)
  have hH : N • (Yᴴ * jPlusOp n m matH * Y) = (n : ℂ) • dSpin (n + m) matH :=
    eprlMap_compress_jPlus_H
  -- the commutator trick: `J₊(E) = ½ [J₊(H), L(E)]`, `J₊(F) = -½ [J₊(H), L(F)]`
  have hE : N • (Yᴴ * jPlusOp n m matE * Y) = (n : ℂ) • dSpin (n + m) matE := by
    have h1 : jPlusOp n m matE = (1 / 2 : ℂ) •
        (jPlusOp n m matH * dDiag n m matE - dDiag n m matE * jPlusOp n m matH) := by
      rw [jPlusOp_bracket_E, smul_smul]; norm_num
    have h2 : Yᴴ * jPlusOp n m matE * Y = (1 / 2 : ℂ) • ((Yᴴ * jPlusOp n m matH * Y) *
        dSpin (n + m) matE - dSpin (n + m) matE * (Yᴴ * jPlusOp n m matH * Y)) := by
      rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
      congr 2
      · rw [Matrix.mul_assoc, Matrix.mul_assoc, eprlMap_lie (by simp [matE]), ← Matrix.mul_assoc,
          ← Matrix.mul_assoc]
      · rw [← Matrix.mul_assoc, conjTranspose_eprlMap_mul_E, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    calc N • (Yᴴ * jPlusOp n m matE * Y)
        = (1 / 2 : ℂ) • ((N • (Yᴴ * jPlusOp n m matH * Y)) * dSpin (n + m) matE -
            dSpin (n + m) matE * (N • (Yᴴ * jPlusOp n m matH * Y))) := by
          rw [h2, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_comm]
      _ = (n : ℂ) • dSpin (n + m) matE := by
          rw [hH, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, dSpin_bracket_HE, smul_smul,
            smul_smul]
          congr 1
          ring
  have hF : N • (Yᴴ * jPlusOp n m matF * Y) = (n : ℂ) • dSpin (n + m) matF := by
    have h1 : jPlusOp n m matF = (-1 / 2 : ℂ) •
        (jPlusOp n m matH * dDiag n m matF - dDiag n m matF * jPlusOp n m matH) := by
      rw [jPlusOp_bracket_F, smul_smul]; norm_num
    have h2 : Yᴴ * jPlusOp n m matF * Y = (-1 / 2 : ℂ) • ((Yᴴ * jPlusOp n m matH * Y) *
        dSpin (n + m) matF - dSpin (n + m) matF * (Yᴴ * jPlusOp n m matH * Y)) := by
      rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
      congr 2
      · rw [Matrix.mul_assoc, Matrix.mul_assoc, eprlMap_lie (by simp [matF]), ← Matrix.mul_assoc,
          ← Matrix.mul_assoc]
      · rw [← Matrix.mul_assoc, conjTranspose_eprlMap_mul_F, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    calc N • (Yᴴ * jPlusOp n m matF * Y)
        = (-1 / 2 : ℂ) • ((N • (Yᴴ * jPlusOp n m matH * Y)) * dSpin (n + m) matF -
            dSpin (n + m) matF * (N • (Yᴴ * jPlusOp n m matH * Y))) := by
          rw [h2, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_comm]
      _ = (n : ℂ) • dSpin (n + m) matF := by
          rw [hH, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, dSpin_bracket_HF, smul_smul,
            smul_smul]
          congr 1
          ring
  rw [traceless_eq hX, jPlusOp_add, jPlusOp_add, jPlusOp_smul, jPlusOp_smul, jPlusOp_smul,
    dSpin_add, dSpin_add, dSpin_smul, dSpin_smul, dSpin_smul]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  rw [smul_comm N (X 0 0), smul_comm N (X 0 1), smul_comm N (X 1 0), hH, hE, hF]
  simp only [smul_comm (n : ℂ)]

/-- In spin `0` every generator vanishes. -/
lemma dSpin_zero_left (X : Matrix (Fin 2) (Fin 2) ℂ) : dSpin 0 X = 0 := by
  ext i j
  simp [dSpin, dkron, mul_apply]

lemma jMinusOp_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    jMinusOp n m (X + Y) = jMinusOp n m X + jMinusOp n m Y := by
  simp [jMinusOp, dSpin_add, kronecker_add]

/-- `Yᴴ L(X) Y = X^{(n+m)}`. -/
lemma eprlMap_compress_dDiag {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X 1 1 = -X 0 0) :
    (eprlMap n m)ᴴ * dDiag n m X * eprlMap n m = dSpin (n + m) X := by
  rw [Matrix.mul_assoc, eprlMap_lie hX, ← Matrix.mul_assoc, eprlMap_isometry, Matrix.one_mul]

/-- **The projection theorem for `J₋`**: `(n+m) Yᴴ J₋(X) Y = m X^{(n+m)}`. -/
theorem eprlMap_compress_jMinus {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X 1 1 = -X 0 0) :
    ((n + m : ℕ) : ℂ) • ((eprlMap n m)ᴴ * jMinusOp n m X * eprlMap n m) =
      (m : ℂ) • dSpin (n + m) X := by
  have h : jMinusOp n m X = dDiag n m X - jPlusOp n m X := by rw [dDiag_eq_add]; abel
  rw [h, Matrix.mul_sub, Matrix.sub_mul, smul_sub, eprlMap_compress_jPlus hX,
    eprlMap_compress_dDiag hX, ← sub_smul]
  congr 1
  push_cast
  ring

/-- The simplicity constraint compressed to the image:
`(n+m) Yᴴ (K - γL) Y = (n - m - γ(n+m)) X`. -/
theorem eprlMap_compress_simplicity {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X 1 1 = -X 0 0) :
    ((n + m : ℕ) : ℂ) • ((eprlMap n m)ᴴ * simplicityOp γ n m X * eprlMap n m) =
      ((n : ℂ) - m - γ * ((n + m : ℕ) : ℂ)) • dSpin (n + m) X := by
  simp only [simplicityOp, boostOp, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub]
  rw [eprlMap_compress_jPlus hX, eprlMap_compress_jMinus hX, eprlMap_compress_dDiag hX,
    smul_comm, sub_smul, sub_smul, smul_smul]

/-- **Weak linear simplicity**: for `0 < γ < 1` and EPRL labels, the constraint `K - γ L`
vanishes between states of the image of `Y`: `Yᴴ (K - γ L) Y = 0`. -/
theorem eprl_weak_simplicity (hγ : 0 < γ) (hγ1 : γ < 1) (h : IsEPRLLabel γ (n + m) n m)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X 1 1 = -X 0 0) :
    (eprlMap n m)ᴴ * simplicityOp γ n m X * eprlMap n m = 0 := by
  have hd := ((isEPRLLabel_iff hγ hγ1).mp h).2
  push_cast at hd
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
    simp [simplicityOp, boostOp, jPlusOp, jMinusOp, dDiag, dSpin_zero_left]
  · have hc := eprlMap_compress_simplicity (γ := γ) (n := n) (m := m) hX
    have hz : (n : ℂ) - m - γ * ((n + m : ℕ) : ℂ) = 0 := by
      have : ((n : ℝ) - m - γ * ((n + m : ℕ) : ℝ) : ℝ) = 0 := by push_cast; linarith
      exact_mod_cast this
    rw [hz, zero_smul] at hc
    exact (smul_eq_zero.mp hc).resolve_left (by exact_mod_cast hpos.ne')

/-- **Weak simplicity in matrix elements**: `⟨Y v, (K - γ L) Y w⟩ = 0` for all `v, w ∈ V_j`. -/
theorem eprl_weak_simplicity_inner (hγ : 0 < γ) (hγ1 : γ < 1) (h : IsEPRLLabel γ (n + m) n m)
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X 1 1 = -X 0 0) (v w : Fin (n + m + 1) → ℂ) :
    star (eprlMap n m *ᵥ v) ⬝ᵥ (simplicityOp γ n m X *ᵥ (eprlMap n m *ᵥ w)) = 0 := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
    eprl_weak_simplicity hγ hγ1 h hX, zero_mulVec, dotProduct_zero]

/-- **Only the EPRL labels satisfy weak simplicity** on the image of the highest-spin embedding:
for `n + m > 0`, `Yᴴ (K - γ L) Y = 0` for all generators exactly when `n - m = γ (n + m)`. -/
theorem weak_simplicity_iff (hpos : 0 < n + m) :
    (∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 →
        (eprlMap n m)ᴴ * simplicityOp γ n m X * eprlMap n m = 0) ↔
      (n : ℝ) - m = γ * (n + m) := by
  constructor
  · intro hall
    have hc := eprlMap_compress_simplicity (γ := γ) (n := n) (m := m) (X := matH) (by simp [matH])
    rw [hall matH (by simp [matH]), smul_zero] at hc
    have h00 := congrFun (congrFun hc 0) 0
    rw [Matrix.zero_apply, Matrix.smul_apply, dSpin_H_apply, ite_eq_left rfl, smul_eq_mul] at h00
    have hN : (((n + m : ℕ) : ℂ) - 2 * (((0 : Fin (n + m + 1)) : ℕ) : ℂ)) ≠ 0 := by
      simp only [Fin.val_zero, Nat.cast_zero, mul_zero, sub_zero]
      exact_mod_cast hpos.ne'
    have h1 := (mul_eq_zero.mp h00.symm).resolve_right hN
    have h2 : (((n : ℝ) - m - γ * ((n + m : ℕ) : ℝ) : ℝ) : ℂ) = 0 := by
      push_cast at h1 ⊢
      exact h1
    have h3 := Complex.ofReal_eq_zero.mp h2
    push_cast at h3
    linarith
  · intro hd X hX
    have hc := eprlMap_compress_simplicity (γ := γ) (n := n) (m := m) hX
    have hz : (n : ℂ) - m - γ * ((n + m : ℕ) : ℂ) = 0 := by
      have : ((n : ℝ) - m - γ * ((n + m : ℕ) : ℝ) : ℝ) = 0 := by push_cast; linarith
      exact_mod_cast this
    rw [hz, zero_smul] at hc
    exact (smul_eq_zero.mp hc).resolve_left (by exact_mod_cast hpos.ne')

/-! ## F. The master constraint -/

/-- **The master constraint** `M = Σᵢ (K^i - γ L^i)²`. -/
noncomputable def masterOp (γ : ℝ) (n m : ℕ) : Matrix (Idx n m) (Idx n m) ℂ :=
  vdot (simplicityOp γ n m) (simplicityOp γ n m)

/-- The two Spin(4) factors commute: `J₋(Y) J₊(X) = J₊(X) J₋(Y)`. -/
lemma jMinusOp_mul_jPlusOp (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    jMinusOp n m Y * jPlusOp n m X = jPlusOp n m X * jMinusOp n m Y := by
  simp only [jPlusOp, jMinusOp, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

/-- `J₊ · J₊ = j₊(j₊ + 1)`. -/
lemma vdot_jPlusOp : vdot (jPlusOp n m) (jPlusOp n m) = casVal n • 1 := by
  have h : vdot (jPlusOp n m) (jPlusOp n m) =
      vdot (dSpin n) (dSpin n) ⊗ₖ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    simp only [vdot, jPlusOp, add_kronecker, smul_kronecker, ← mul_kronecker_mul, Matrix.mul_one]
  rw [h, vdot_dSpin, smul_kronecker, one_kronecker_one]

/-- `J₋ · J₋ = j₋(j₋ + 1)`. -/
lemma vdot_jMinusOp : vdot (jMinusOp n m) (jMinusOp n m) = casVal m • 1 := by
  have h : vdot (jMinusOp n m) (jMinusOp n m) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ⊗ₖ vdot (dSpin m) (dSpin m) := by
    simp only [vdot, jMinusOp, kronecker_add, kronecker_smul, ← mul_kronecker_mul, Matrix.mul_one]
  rw [h, vdot_dSpin, kronecker_smul, one_kronecker_one]

/-- The master constraint in Casimirs: with `a = 1 - γ`, `b = 1 + γ`,
`M = 2a J₊² + 2b J₋² - ab L²`. -/
lemma masterOp_eq : masterOp γ n m =
    (2 * ((1 - γ : ℝ) : ℂ)) • vdot (jPlusOp n m) (jPlusOp n m) +
      (2 * ((1 + γ : ℝ) : ℂ)) • vdot (jMinusOp n m) (jMinusOp n m) -
      (((1 - γ : ℝ) : ℂ) * ((1 + γ : ℝ) : ℂ)) • casDiag n m := by
  have hc := fun X Y => jMinusOp_mul_jPlusOp (n := n) (m := m) X Y
  simp only [masterOp, casDiag, vdot, simplicityOp_eq, dDiag_eq_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hc]
  push_cast
  module

/-- The scalar value of the master constraint on the image. -/
lemma master_scalar (h : (n : ℝ) - m = γ * (n + m)) :
    2 * (1 - γ) * ((n : ℝ) / 2 * ((n : ℝ) / 2 + 1)) +
      2 * (1 + γ) * ((m : ℝ) / 2 * ((m : ℝ) / 2 + 1))
      - (1 - γ) * (1 + γ) * (((n + m : ℕ) : ℝ) / 2 * (((n + m : ℕ) : ℝ) / 2 + 1)) =
      (1 - γ ^ 2) * ((n + m : ℕ) : ℝ) / 2 := by
  rcases Nat.eq_zero_or_pos (n + m) with h0 | hpos
  · obtain ⟨rfl, rfl⟩ : n = 0 ∧ m = 0 := by omega
    simp
  · have hN : ((n : ℝ) + m) ≠ 0 := by
      have : (0 : ℝ) < n + m := by exact_mod_cast hpos
      exact this.ne'
    have hγ : γ = ((n : ℝ) - m) / (n + m) := by field_simp; linarith
    subst hγ
    push_cast
    field_simp
    ring

/-- **The master constraint on the image of the EPRL map** is the scalar
`Yᴴ M Y = (1 - γ²) j` (`j = (n+m)/2`; equivalently `4 j₊ j₋ / j`). -/
theorem eprl_master_constraint (hγ : 0 < γ) (hγ1 : γ < 1) (h : IsEPRLLabel γ (n + m) n m) :
    (eprlMap n m)ᴴ * masterOp γ n m * eprlMap n m =
      (((1 - γ ^ 2) * ((n + m : ℕ) : ℝ) / 2 : ℝ) : ℂ) • 1 := by
  have hd := ((isEPRLLabel_iff hγ hγ1).mp h).2
  push_cast at hd
  have hL : (eprlMap n m)ᴴ * casDiag n m * eprlMap n m = casVal (n + m) • 1 := by
    rw [Matrix.mul_assoc, eprlMap, casDiag_mul_cgMatrix (Nat.zero_le _) (Nat.zero_le _),
      Matrix.mul_smul, ← eprlMap, eprlMap_isometry]
    rfl
  rw [masterOp_eq, vdot_jPlusOp, vdot_jMinusOp]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    eprlMap_isometry, hL, smul_smul, ← add_smul, ← sub_smul]
  congr 1
  have := master_scalar (n := n) (m := m) (γ := γ) (by linarith)
  have hc : ∀ N : ℕ, casVal N = (((N : ℝ) / 2 * ((N : ℝ) / 2 + 1) : ℝ) : ℂ) := fun N => by
    simp [casVal]
  rw [hc, hc, hc, ← this]
  push_cast
  ring

/-- The EPRL labels of a nonzero spin are both nonzero. -/
lemma IsEPRLLabel.pos (hγ : 0 < γ) (hγ1 : γ < 1) (h : IsEPRLLabel γ J n m) (hJ : 0 < J) :
    0 < n ∧ 0 < m := by
  obtain ⟨hn, hm⟩ := h
  simp only [jPlus, jMinus, abs_of_pos (show (0 : ℝ) < 1 + γ by linarith),
    abs_of_pos (show (0 : ℝ) < 1 - γ by linarith)] at hn hm
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · have : (0 : ℝ) < n := by rw [hn]; nlinarith
    exact_mod_cast this
  · have : (0 : ℝ) < m := by rw [hm]; nlinarith
    exact_mod_cast this

/-- **The constraint does not hold strongly**: for `0 < γ < 1` and a nonzero spin, some component
of `K - γ L` does not annihilate the image of `Y` (otherwise the master constraint would vanish
there). -/
theorem eprl_not_strong_simplicity (hγ : 0 < γ) (hγ1 : γ < 1) (h : IsEPRLLabel γ (n + m) n m)
    (hpos : 0 < n + m) :
    ¬ ∀ X : Matrix (Fin 2) (Fin 2) ℂ, X 1 1 = -X 0 0 → simplicityOp γ n m X * eprlMap n m = 0 := by
  intro hall
  have hE := hall matE (by simp [matE])
  have hF := hall matF (by simp [matF])
  have hH := hall matH (by simp [matH])
  have h0 : masterOp γ n m * eprlMap n m = 0 := by
    simp only [masterOp, vdot, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hE, hF, hH,
      Matrix.mul_zero, add_zero, smul_zero]
  have h1 := eprl_master_constraint hγ hγ1 h
  rw [Matrix.mul_assoc, h0, Matrix.mul_zero] at h1
  have h00 := congrFun (congrFun h1 0) 0
  rw [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h00
  have hγ2 : 0 < 1 - γ ^ 2 := by nlinarith
  have hN : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by exact_mod_cast hpos
  have : ((1 - γ ^ 2) * ((n + m : ℕ) : ℝ) / 2 : ℝ) ≠ 0 := by positivity
  exact this (by exact_mod_cast h00.symm)

end Lightlike.Spin4
