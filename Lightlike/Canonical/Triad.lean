import Mathlib
import Lightlike.Canonical.ADM

/-!
# Triads, densitized triads and the triad form of the extrinsic curvature

Canonical variables of loop quantum gravity on the chart `ℝ³` of `Lightlike/Canonical/ADM.lean`
(Ashtekar–Lewandowski, *Background independent quantum gravity: a status report*, arXiv:gr-qc/0404018, Sec. II C 1,
eqs. (2.16)–(2.21), pp. 16-17):

* a **co-triad** of the spatial metric `h` is a field of invertible matrices `e x` (entries `e^i_a`, row `i` internal,
  column `a` spatial) with `h_ab = Σ_i e^i_a e^i_b`, i.e. `h = eᵀ e` (`IsCoTriad`; `q_ab = e^i_a e^j_b η_ij`, p. 16, with
  `η = δ` for Lorentzian signature);
* the **densitized triad** `E^a_i = √det h · e^a_i` with `e^a_i` the inverse triad (`densTriad`; eq. (2.21), `Ẽ^a_i`),
  stored as the matrix `(e⁻¹)` scaled, row `a` spatial, column `i` internal;
* the **triad extrinsic curvature** `K^i_a = K_ab e^{bi}` (`triadK`; eq. (2.18)), row `a`, column `i`.

The internal rotation part of the Gauss constraint (eq. (2.23)) contracted from the extrinsic curvature,
`ε_ijk K^j_a E^{ak}`, vanishes exactly when `K_ab` is symmetric (`gaussK_eq_zero_iff`).
-/

open Matrix

noncomputable section

namespace Lightlike.Canonical

/-- A co-triad field on the chart: `e x i a = e^i_a(x)`. -/
abbrev CoTriad := (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ

/-- `e` is a **co-triad of the spatial metric** `h`: `e(x)` is invertible and `h = eᵀ e` (`h_ab = Σ_i e^i_a e^i_b`). -/
def IsCoTriad (e : CoTriad) (h : TensorField 3) : Prop :=
  ∀ x, IsUnit (e x).det ∧ (e x)ᵀ * e x = h x

/-- The **densitized triad** `E^a_i = √det h · e^a_i = |det e| (e⁻¹)^a_i` (row `a`, column `i`). -/
def densTriad (e : CoTriad) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := |(e x).det| • (e x)⁻¹

/-- The **triad extrinsic curvature** `K^i_a = K_ab e^b_i` (row `a`, column `i`). -/
def triadK (e : CoTriad) (K : TensorField 3) (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := K x * (e x)⁻¹

/-- `√det h = |det e|` for a co-triad of `h`. -/
theorem sqrt_det_eq (e : CoTriad) {h : TensorField 3} (he : IsCoTriad e h) (x : Fin 3 → ℝ) :
    Real.sqrt (h x).det = |(e x).det| := by
  rw [← (he x).2, det_mul, det_transpose, ← sq, Real.sqrt_sq_eq_abs]

/-- The Levi-Civita symbol `ε_ijk` of `ℝ³`. -/
def eps3 (i j k : Fin 3) : ℝ := (Matrix.of ![Pi.single i 1, Pi.single j 1, Pi.single k 1]).det

/-- The contraction `Σ_{jk} ε_ijk M_jk` vanishes for every `i` iff `M` is symmetric. -/
theorem eps3_contract_eq_zero_iff (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ i, ∑ j, ∑ k, eps3 i j k * M j k = 0) ↔ Mᵀ = M := by
  constructor
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    simp [eps3, Fin.sum_univ_three, Matrix.det_fin_three, Pi.single_apply] at h0 h1 h2
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.transpose_apply] <;> linarith
  · intro hM i
    have e : ∀ a b, M a b = M b a := fun a b => by
      rw [← Matrix.transpose_apply M b a, hM]
    fin_cases i <;> simp [eps3, Fin.sum_univ_three, Matrix.det_fin_three, Pi.single_apply, e 1 2, e 0 2, e 0 1]

/-- **The extrinsic-curvature part of the Gauss constraint**: `Σ_{jk} ε_ijk Σ_a K^j_a E^a_k`, the term that
`A = Γ + γK` adds to `D_a E^a_i` (Ashtekar–Lewandowski (2.20), (2.23)). -/
def gaussK (e : CoTriad) (K : TensorField 3) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  ∑ j, ∑ k, eps3 i j k * ∑ a, triadK e K x a j * densTriad e x a k

/-- **The extrinsic-curvature part of the Gauss constraint vanishes iff `K_ab` is symmetric** (for a co-triad). -/
theorem gaussK_eq_zero_iff (e : CoTriad) (K : TensorField 3) (x : Fin 3 → ℝ) (hu : IsUnit (e x).det) :
    (∀ i, gaussK e K x i = 0) ↔ (K x)ᵀ = K x := by
  set f := (e x)⁻¹ with hf
  have hd : |(e x).det| ≠ 0 := abs_ne_zero.2 (hu.ne_zero)
  -- the contraction is `|det e| ε_ijk (fᵀ K f)_jk`
  have key : ∀ i, gaussK e K x i = |(e x).det| * ∑ j, ∑ k, eps3 i j k * (fᵀ * (K x)ᵀ * f) j k := by
    intro i
    simp only [gaussK, triadK, densTriad, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply,
      Finset.mul_sum, ← hf]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    have hc : ∑ b, K x a b * f b j = ∑ b, f b j * K x a b := Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [hc]
    ring
  have hfu : IsUnit f.det := by rw [hf]; exact Matrix.isUnit_nonsing_inv_det _ hu
  constructor
  · intro h
    have hs : ∀ i, ∑ j, ∑ k, eps3 i j k * (fᵀ * (K x)ᵀ * f) j k = 0 := fun i => by
      have := h i; rw [key i] at this
      exact (mul_eq_zero.1 this).resolve_left hd
    have hsym := (eps3_contract_eq_zero_iff _).1 hs
    -- `fᵀ Kᵀ f` symmetric means `fᵀ K f = fᵀ Kᵀ f`, so `K = Kᵀ` (`f` invertible)
    have h2 : fᵀ * K x * f = fᵀ * (K x)ᵀ * f := by
      rw [← hsym]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have hfT : IsUnit fᵀ.det := by rw [det_transpose]; exact hfu
    have h3 := congrArg (fun A => (fᵀ)⁻¹ * A * f⁻¹) h2
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfT, Matrix.one_mul] at h3
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hfu, Matrix.mul_one] at h3
    exact h3.symm
  · intro hK i
    rw [key i]
    have hsym : (fᵀ * (K x)ᵀ * f)ᵀ = fᵀ * (K x)ᵀ * f := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc, hK]
    rw [(eps3_contract_eq_zero_iff _).2 hsym i, mul_zero]

end Lightlike.Canonical
